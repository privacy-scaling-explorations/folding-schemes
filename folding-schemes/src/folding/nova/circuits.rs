/// contains [Nova](https://eprint.iacr.org/2021/370.pdf) related circuits
use ark_crypto_primitives::crh::{
    poseidon::constraints::{CRHGadget, CRHParametersVar},
    CRHSchemeGadget,
};
use ark_crypto_primitives::sponge::{
    constraints::CryptographicSpongeVar,
    poseidon::{constraints::PoseidonSpongeVar, PoseidonConfig, PoseidonSponge},
    Absorb, CryptographicSponge,
};
use ark_ec::{AffineRepr, CurveGroup, Group};
use ark_ff::{Field, PrimeField};
use ark_r1cs_std::{
    alloc::{AllocVar, AllocationMode},
    boolean::Boolean,
    eq::EqGadget,
    fields::{fp::FpVar, nonnative::NonNativeFieldVar, FieldVar},
    groups::GroupOpsBounds,
    prelude::CurveVar,
    ToBitsGadget, ToConstraintFieldGadget,
};
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, Namespace, SynthesisError};
use ark_std::fmt::Debug;
use ark_std::{One, Zero};
use core::{borrow::Borrow, marker::PhantomData};

use super::{
    cyclefold::{
        CycleFoldChallengeGadget, CycleFoldCommittedInstanceVar, NIFSFullGadget, CF_IO_LEN,
    },
    CommittedInstance,
};
use crate::constants::N_BITS_RO;
use crate::folding::circuits::nonnative::{point_to_nonnative_limbs, NonNativeAffineVar};
use crate::frontend::FCircuit;

/// CF1 represents the ConstraintField used for the main Nova circuit which is over E1::Fr, where
/// E1 is the main curve where we do the folding.
pub type CF1<C> = <<C as CurveGroup>::Affine as AffineRepr>::ScalarField;
/// CF2 represents the ConstraintField used for the CycleFold circuit which is over E2::Fr=E1::Fq,
/// where E2 is the auxiliary curve (from [CycleFold](https://eprint.iacr.org/2023/1192.pdf)
/// approach) where we check the folding of the commitments (elliptic curve points).
pub type CF2<C> = <<C as CurveGroup>::BaseField as Field>::BasePrimeField;

/// CommittedInstanceVar contains the u, x, cmE and cmW values which are folded on the main Nova
/// constraints field (E1::Fr, where E1 is the main curve). The peculiarity is that cmE and cmW are
/// represented non-natively over the constraint field.
#[derive(Debug, Clone)]
pub struct CommittedInstanceVar<C: CurveGroup>
where
    <C as ark_ec::CurveGroup>::BaseField: ark_ff::PrimeField,
{
    pub u: FpVar<C::ScalarField>,
    pub x: Vec<FpVar<C::ScalarField>>,
    pub cmE: NonNativeAffineVar<C>,
    pub cmW: NonNativeAffineVar<C>,
}

impl<C> AllocVar<CommittedInstance<C>, CF1<C>> for CommittedInstanceVar<C>
where
    C: CurveGroup,
    <C as ark_ec::CurveGroup>::BaseField: PrimeField,
{
    fn new_variable<T: Borrow<CommittedInstance<C>>>(
        cs: impl Into<Namespace<CF1<C>>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        f().and_then(|val| {
            let cs = cs.into();

            let u = FpVar::<C::ScalarField>::new_variable(cs.clone(), || Ok(val.borrow().u), mode)?;
            let x: Vec<FpVar<C::ScalarField>> =
                Vec::new_variable(cs.clone(), || Ok(val.borrow().x.clone()), mode)?;

            let cmE =
                NonNativeAffineVar::<C>::new_variable(cs.clone(), || Ok(val.borrow().cmE), mode)?;
            let cmW =
                NonNativeAffineVar::<C>::new_variable(cs.clone(), || Ok(val.borrow().cmW), mode)?;

            Ok(Self { u, x, cmE, cmW })
        })
    }
}

impl<C> CommittedInstanceVar<C>
where
    C: CurveGroup,
    <C as Group>::ScalarField: Absorb,
    <C as ark_ec::CurveGroup>::BaseField: ark_ff::PrimeField,
{
    /// hash implements the committed instance hash compatible with the native implementation from
    /// CommittedInstance.hash.
    /// Returns `H(i, z_0, z_i, U_i)`, where `i` can be `i` but also `i+1`, and `U` is the
    /// `CommittedInstance`.
    /// Additionally it returns the vector of the field elements from the self parameters, so they
    /// can be reused in other gadgets avoiding recalculating (reconstraining) them.
    #[allow(clippy::type_complexity)]
    pub fn hash(
        self,
        crh_params: &CRHParametersVar<CF1<C>>,
        i: FpVar<CF1<C>>,
        z_0: Vec<FpVar<CF1<C>>>,
        z_i: Vec<FpVar<CF1<C>>>,
    ) -> Result<(FpVar<CF1<C>>, Vec<FpVar<CF1<C>>>), SynthesisError> {
        let U_vec = [
            vec![self.u],
            self.x,
            self.cmE.x.to_constraint_field()?,
            self.cmE.y.to_constraint_field()?,
            self.cmE.infinity.to_constraint_field()?,
            self.cmW.x.to_constraint_field()?,
            self.cmW.y.to_constraint_field()?,
            self.cmW.infinity.to_constraint_field()?,
        ]
        .concat();
        let input = [vec![i], z_0, z_i, U_vec.clone()].concat();
        Ok((
            CRHGadget::<C::ScalarField>::evaluate(crh_params, &input)?,
            U_vec,
        ))
    }
}

/// Implements the circuit that does the checks of the Non-Interactive Folding Scheme Verifier
/// described in section 4 of [Nova](https://eprint.iacr.org/2021/370.pdf), where the cmE & cmW checks are
/// delegated to the NIFSCycleFoldGadget.
pub struct NIFSGadget<C: CurveGroup> {
    _c: PhantomData<C>,
}

impl<C: CurveGroup> NIFSGadget<C>
where
    C: CurveGroup,
    <C as ark_ec::CurveGroup>::BaseField: ark_ff::PrimeField,
{
    /// Implements the constraints for NIFS.V for u and x, since cm(E) and cm(W) are delegated to
    /// the CycleFold circuit.
    pub fn verify(
        r: FpVar<CF1<C>>,
        ci1: CommittedInstanceVar<C>, // U_i
        ci2: CommittedInstanceVar<C>, // u_i
        ci3: CommittedInstanceVar<C>, // U_{i+1}
    ) -> Result<Boolean<CF1<C>>, SynthesisError> {
        // ensure that: ci3.u == ci1.u + r * ci2.u
        let first_check = ci3.u.is_eq(&(ci1.u + r.clone() * ci2.u))?;

        // ensure that: ci3.x == ci1.x + r * ci2.x
        let x_rlc = ci1
            .x
            .iter()
            .zip(ci2.x)
            .map(|(a, b)| a + &r * &b)
            .collect::<Vec<FpVar<CF1<C>>>>();
        let second_check = x_rlc.is_eq(&ci3.x)?;

        first_check.and(&second_check)
    }
}

/// ChallengeGadget computes the RO challenge used for the Nova instances NIFS, it contains a
/// rust-native and a in-circuit compatible versions.
pub struct ChallengeGadget<C: CurveGroup> {
    _c: PhantomData<C>,
}
impl<C: CurveGroup> ChallengeGadget<C>
where
    C: CurveGroup,
    <C as CurveGroup>::BaseField: PrimeField,
    <C as Group>::ScalarField: Absorb,
{
    pub fn get_challenge_native(
        poseidon_config: &PoseidonConfig<C::ScalarField>,
        U_i: CommittedInstance<C>,
        u_i: CommittedInstance<C>,
        cmT: C,
    ) -> Result<Vec<bool>, SynthesisError> {
        let (U_cmE_x, U_cmE_y, U_cmE_inf) = point_to_nonnative_limbs::<C>(U_i.cmE)?;
        let (U_cmW_x, U_cmW_y, U_cmW_inf) = point_to_nonnative_limbs::<C>(U_i.cmW)?;
        let (u_cmE_x, u_cmE_y, u_cmE_inf) = point_to_nonnative_limbs::<C>(u_i.cmE)?;
        let (u_cmW_x, u_cmW_y, u_cmW_inf) = point_to_nonnative_limbs::<C>(u_i.cmW)?;
        let (cmT_x, cmT_y, cmT_inf) = point_to_nonnative_limbs::<C>(cmT)?;

        let mut sponge = PoseidonSponge::<C::ScalarField>::new(poseidon_config);
        let input = vec![
            vec![U_i.u],
            U_i.x.clone(),
            U_cmE_x,
            U_cmE_y,
            U_cmE_inf,
            U_cmW_x,
            U_cmW_y,
            U_cmW_inf,
            vec![u_i.u],
            u_i.x.clone(),
            u_cmE_x,
            u_cmE_y,
            u_cmE_inf,
            u_cmW_x,
            u_cmW_y,
            u_cmW_inf,
            cmT_x,
            cmT_y,
            cmT_inf,
        ]
        .concat();
        sponge.absorb(&input);
        let bits = sponge.squeeze_bits(N_BITS_RO);
        Ok(bits)
    }

    // compatible with the native get_challenge_native
    pub fn get_challenge_gadget(
        cs: ConstraintSystemRef<C::ScalarField>,
        poseidon_config: &PoseidonConfig<C::ScalarField>,
        U_i_vec: Vec<FpVar<CF1<C>>>, // apready processed input, so we don't have to recompute these values
        u_i: CommittedInstanceVar<C>,
        cmT: NonNativeAffineVar<C>,
    ) -> Result<Vec<Boolean<C::ScalarField>>, SynthesisError> {
        let mut sponge = PoseidonSpongeVar::<C::ScalarField>::new(cs, poseidon_config);

        let input: Vec<FpVar<C::ScalarField>> = vec![
            U_i_vec,
            vec![u_i.u.clone()],
            u_i.x.clone(),
            u_i.cmE.x.to_constraint_field()?,
            u_i.cmE.y.to_constraint_field()?,
            u_i.cmE.infinity.to_constraint_field()?,
            u_i.cmW.x.to_constraint_field()?,
            u_i.cmW.y.to_constraint_field()?,
            u_i.cmW.infinity.to_constraint_field()?,
            cmT.x.to_constraint_field()?,
            cmT.y.to_constraint_field()?,
            cmT.infinity.to_constraint_field()?,
        ]
        .concat();
        sponge.absorb(&input)?;
        let bits = sponge.squeeze_bits(N_BITS_RO)?;
        Ok(bits)
    }
}

/// AugmentedFCircuit implements the F' circuit (augmented F) defined in
/// [Nova](https://eprint.iacr.org/2021/370.pdf) together with the extra constraints defined in
/// [CycleFold](https://eprint.iacr.org/2023/1192.pdf).
#[derive(Debug, Clone)]
pub struct AugmentedFCircuit<
    C1: CurveGroup,
    C2: CurveGroup,
    GC2: CurveVar<C2, CF2<C2>>,
    FC: FCircuit<CF1<C1>>,
> where
    for<'a> &'a GC2: GroupOpsBounds<'a, C2, GC2>,
{
    pub _gc2: PhantomData<GC2>,
    pub poseidon_config: PoseidonConfig<CF1<C1>>,
    pub i: Option<CF1<C1>>,
    pub i_usize: Option<usize>,
    pub z_0: Option<Vec<C1::ScalarField>>,
    pub z_i: Option<Vec<C1::ScalarField>>,
    pub u_i: Option<CommittedInstance<C1>>,
    pub U_i: Option<CommittedInstance<C1>>,
    pub U_i1: Option<CommittedInstance<C1>>,
    pub r_nonnat: Option<CF2<C1>>,
    pub cmT: Option<C1>,
    pub F: FC,              // F circuit
    pub x: Option<CF1<C1>>, // public inputs (u_{i+1}.x)

    // cyclefold verifier on C1
    // Here 'cf1, cf2' are for each of the CycleFold circuits, corresponding to the fold of cmW and
    // cmE respectively
    pub cf1_u_i: Option<CommittedInstance<C2>>,  // input
    pub cf2_u_i: Option<CommittedInstance<C2>>,  // input
    pub cf_U_i: Option<CommittedInstance<C2>>,   // input
    pub cf1_U_i1: Option<CommittedInstance<C2>>, // intermediate
    pub cf_U_i1: Option<CommittedInstance<C2>>,  // output
    pub cf1_cmT: Option<C2>,
    pub cf2_cmT: Option<C2>,
    pub cf1_r_nonnat: Option<C2::ScalarField>,
    pub cf2_r_nonnat: Option<C2::ScalarField>,
}

impl<C1: CurveGroup, C2: CurveGroup, GC2: CurveVar<C2, CF2<C2>>, FC: FCircuit<CF1<C1>>>
    AugmentedFCircuit<C1, C2, GC2, FC>
where
    for<'a> &'a GC2: GroupOpsBounds<'a, C2, GC2>,
{
    pub fn empty(poseidon_config: &PoseidonConfig<CF1<C1>>, F_circuit: FC) -> Self {
        Self {
            _gc2: PhantomData,
            poseidon_config: poseidon_config.clone(),
            i: None,
            i_usize: None,
            z_0: None,
            z_i: None,
            u_i: None,
            U_i: None,
            U_i1: None,
            r_nonnat: None,
            cmT: None,
            F: F_circuit,
            x: None,
            // cyclefold values
            cf1_u_i: None,
            cf2_u_i: None,
            cf_U_i: None,
            cf1_U_i1: None,
            cf_U_i1: None,
            cf1_cmT: None,
            cf2_cmT: None,
            cf1_r_nonnat: None,
            cf2_r_nonnat: None,
        }
    }
}

impl<C1, C2, GC2, FC> ConstraintSynthesizer<CF1<C1>> for AugmentedFCircuit<C1, C2, GC2, FC>
where
    C1: CurveGroup,
    C2: CurveGroup,
    GC2: CurveVar<C2, CF2<C2>>,
    FC: FCircuit<CF1<C1>>,
    <C1 as CurveGroup>::BaseField: PrimeField,
    <C2 as CurveGroup>::BaseField: PrimeField,
    <C1 as Group>::ScalarField: Absorb,
    <C2 as Group>::ScalarField: Absorb,
    C1: CurveGroup<BaseField = C2::ScalarField, ScalarField = C2::BaseField>,
    for<'a> &'a GC2: GroupOpsBounds<'a, C2, GC2>,
{
    fn generate_constraints(self, cs: ConstraintSystemRef<CF1<C1>>) -> Result<(), SynthesisError> {
        let i = FpVar::<CF1<C1>>::new_witness(cs.clone(), || {
            Ok(self.i.unwrap_or_else(CF1::<C1>::zero))
        })?;
        let z_0 = Vec::<FpVar<CF1<C1>>>::new_witness(cs.clone(), || {
            Ok(self
                .z_0
                .unwrap_or(vec![CF1::<C1>::zero(); self.F.state_len()]))
        })?;
        let z_i = Vec::<FpVar<CF1<C1>>>::new_witness(cs.clone(), || {
            Ok(self
                .z_i
                .unwrap_or(vec![CF1::<C1>::zero(); self.F.state_len()]))
        })?;

        let u_dummy_native = CommittedInstance::<C1>::dummy(1);
        let u_i = CommittedInstanceVar::<C1>::new_witness(cs.clone(), || {
            Ok(self.u_i.unwrap_or(u_dummy_native.clone()))
        })?;
        let U_i = CommittedInstanceVar::<C1>::new_witness(cs.clone(), || {
            Ok(self.U_i.unwrap_or(u_dummy_native.clone()))
        })?;
        let U_i1 = CommittedInstanceVar::<C1>::new_witness(cs.clone(), || {
            Ok(self.U_i1.unwrap_or(u_dummy_native.clone()))
        })?;
        let r_nonnat =
            NonNativeFieldVar::<C1::BaseField, C1::ScalarField>::new_witness(cs.clone(), || {
                Ok(self.r_nonnat.unwrap_or_else(CF2::<C1>::zero))
            })?;
        let cmT =
            NonNativeAffineVar::new_witness(cs.clone(), || Ok(self.cmT.unwrap_or_else(C1::zero)))?;
        let x =
            FpVar::<CF1<C1>>::new_input(cs.clone(), || Ok(self.x.unwrap_or_else(CF1::<C1>::zero)))?;

        let crh_params = CRHParametersVar::<C1::ScalarField>::new_constant(
            cs.clone(),
            self.poseidon_config.clone(),
        )?;

        // get z_{i+1} from the F circuit
        let i_usize = self.i_usize.unwrap_or(0);
        let z_i1 = self
            .F
            .generate_step_constraints(cs.clone(), i_usize, z_i.clone())?;

        let zero = FpVar::<CF1<C1>>::new_constant(cs.clone(), CF1::<C1>::zero())?;
        let is_not_basecase = i.is_neq(&zero)?;

        // 1. u_i.x == H(i, z_0, z_i, U_i)
        let (u_i_x, U_i_vec) =
            U_i.clone()
                .hash(&crh_params, i.clone(), z_0.clone(), z_i.clone())?;
        // check that h == u_i.x
        (u_i.x[0]).conditional_enforce_equal(&u_i_x, &is_not_basecase)?;

        // 2. u_i.cmE==cm(0), u_i.u==1
        let zero_x = NonNativeFieldVar::<C1::BaseField, C1::ScalarField>::new_constant(
            cs.clone(),
            C1::BaseField::zero(),
        )?;
        let zero_y = NonNativeFieldVar::<C1::BaseField, C1::ScalarField>::new_constant(
            cs.clone(),
            C1::BaseField::one(),
        )?;
        (u_i.cmE.x.is_eq(&zero_x)?).conditional_enforce_equal(&Boolean::TRUE, &is_not_basecase)?;
        (u_i.cmE.y.is_eq(&zero_y)?).conditional_enforce_equal(&Boolean::TRUE, &is_not_basecase)?;
        (u_i.u.is_one()?).conditional_enforce_equal(&Boolean::TRUE, &is_not_basecase)?;

        // 3. nifs.verify, checks that folding u_i & U_i obtains U_{i+1}.
        // compute r = H(u_i, U_i, cmT)
        let r_bits = ChallengeGadget::<C1>::get_challenge_gadget(
            cs.clone(),
            &self.poseidon_config,
            U_i_vec,
            u_i.clone(),
            cmT.clone(),
        )?;
        let r = Boolean::le_bits_to_fp_var(&r_bits)?;

        // enforce that the input r_nonnat as bits matches the in-circuit computed r_bits
        let r_nonnat_bits: Vec<Boolean<C1::ScalarField>> =
            r_nonnat.to_bits_le()?.into_iter().take(128).collect();
        r_nonnat_bits.enforce_equal(&r_bits)?;

        // Notice that NIFSGadget::verify is not checking the folding of cmE & cmW, since it will
        // be done on the other curve.
        let nifs_check = NIFSGadget::<C1>::verify(r, U_i.clone(), u_i.clone(), U_i1.clone())?;
        nifs_check.conditional_enforce_equal(&Boolean::TRUE, &is_not_basecase)?;

        // 4. u_{i+1}.x = H(i+1, z_0, z_i+1, U_{i+1}), this is the output of F'
        let (u_i1_x, _) = U_i1.clone().hash(
            &crh_params,
            i + FpVar::<CF1<C1>>::one(),
            z_0.clone(),
            z_i1.clone(),
        )?;

        u_i1_x.enforce_equal(&x)?;

        // CycleFold part
        let cf_u_dummy_native = CommittedInstance::<C2>::dummy(CF_IO_LEN);
        // cf W circuit data
        let cf1_u_i = CycleFoldCommittedInstanceVar::<C2, GC2>::new_witness(cs.clone(), || {
            Ok(self.cf1_u_i.unwrap_or_else(|| cf_u_dummy_native.clone()))
        })?;
        let cf2_u_i = CycleFoldCommittedInstanceVar::<C2, GC2>::new_witness(cs.clone(), || {
            Ok(self.cf2_u_i.unwrap_or_else(|| cf_u_dummy_native.clone()))
        })?;
        let cf_U_i = CycleFoldCommittedInstanceVar::<C2, GC2>::new_witness(cs.clone(), || {
            Ok(self.cf_U_i.unwrap_or_else(|| cf_u_dummy_native.clone()))
        })?;
        let cf1_U_i1 = CycleFoldCommittedInstanceVar::<C2, GC2>::new_witness(cs.clone(), || {
            Ok(self.cf1_U_i1.unwrap_or_else(|| cf_u_dummy_native.clone()))
        })?;
        let cf_U_i1 = CycleFoldCommittedInstanceVar::<C2, GC2>::new_witness(cs.clone(), || {
            Ok(self.cf_U_i1.unwrap_or_else(|| cf_u_dummy_native.clone()))
        })?;
        let cf1_cmT = GC2::new_witness(cs.clone(), || Ok(self.cf1_cmT.unwrap_or_else(C2::zero)))?;
        let cf2_cmT = GC2::new_witness(cs.clone(), || Ok(self.cf2_cmT.unwrap_or_else(C2::zero)))?;
        let cf1_r_nonnat =
            NonNativeFieldVar::<C1::BaseField, C1::ScalarField>::new_witness(cs.clone(), || {
                Ok(self.cf1_r_nonnat.unwrap_or_else(C2::ScalarField::zero))
            })?;
        let cf2_r_nonnat =
            NonNativeFieldVar::<C1::BaseField, C1::ScalarField>::new_witness(cs.clone(), || {
                Ok(self.cf2_r_nonnat.unwrap_or_else(C2::ScalarField::zero))
            })?;

        let cfW_x: Vec<NonNativeFieldVar<C1::BaseField, C1::ScalarField>> = vec![
            r_nonnat.clone(),
            U_i.cmW.x,
            U_i.cmW.y,
            U_i.cmW.infinity,
            u_i.cmW.x,
            u_i.cmW.y,
            u_i.cmW.infinity,
            U_i1.cmW.x,
            U_i1.cmW.y,
            U_i1.cmW.infinity,
        ];
        let cfE_x: Vec<NonNativeFieldVar<C1::BaseField, C1::ScalarField>> = vec![
            r_nonnat,
            U_i.cmE.x,
            U_i.cmE.y,
            U_i.cmE.infinity,
            cmT.x,
            cmT.y,
            cmT.infinity,
            U_i1.cmE.x,
            U_i1.cmE.y,
            U_i1.cmE.infinity,
        ];

        // ensure that cf1_u & cf2_u have as public inputs the cmW & cmE from main instances U_i,
        // u_i, U_i+1 coordinates of the commitments
        cf1_u_i
            .x
            .conditional_enforce_equal(&cfW_x, &is_not_basecase)?;
        cf2_u_i
            .x
            .conditional_enforce_equal(&cfE_x, &is_not_basecase)?;

        // cf_r_bits is denoted by rho* in the paper.
        // assert that cf_r_bits == cf_r_nonnat converted to bits. cf_r_nonnat is just an auxiliary
        // value used to compute RLC of NonNativeFieldVar values, since we can convert
        // NonNativeFieldVar into Vec<Boolean>, but not in the other direction.
        let cf1_r_bits = CycleFoldChallengeGadget::<C2, GC2>::get_challenge_gadget(
            cs.clone(),
            &self.poseidon_config,
            cf_U_i.clone(),
            cf1_u_i.clone(),
            cf1_cmT.clone(),
        )?;
        let cf1_r_nonnat_bits = cf1_r_nonnat.to_bits_le()?;
        cf1_r_bits.conditional_enforce_equal(&cf1_r_nonnat_bits[..N_BITS_RO], &is_not_basecase)?;
        // same for cf2_r:
        let cf2_r_bits = CycleFoldChallengeGadget::<C2, GC2>::get_challenge_gadget(
            cs.clone(),
            &self.poseidon_config,
            cf1_U_i1.clone(),
            cf2_u_i.clone(),
            cf2_cmT.clone(),
        )?;
        let cf2_r_nonnat_bits = cf2_r_nonnat.to_bits_le()?;
        cf2_r_bits.conditional_enforce_equal(&cf2_r_nonnat_bits[..N_BITS_RO], &is_not_basecase)?;

        // check cf_u_i.cmE=0, cf_u_i.u=1
        (cf1_u_i.cmE.is_zero()?).conditional_enforce_equal(&Boolean::TRUE, &is_not_basecase)?;
        (cf1_u_i.u.is_one()?).conditional_enforce_equal(&Boolean::TRUE, &is_not_basecase)?;
        (cf2_u_i.cmE.is_zero()?).conditional_enforce_equal(&Boolean::TRUE, &is_not_basecase)?;
        (cf2_u_i.u.is_one()?).conditional_enforce_equal(&Boolean::TRUE, &is_not_basecase)?;

        // check the fold of all the parameters of the CycleFold instances, where the elliptic
        // curve points relations are checked natively in Curve1 circuit (this one)
        let v1 = NIFSFullGadget::<C2, GC2>::verify(
            cf1_r_bits,
            cf1_r_nonnat,
            cf1_cmT,
            cf_U_i,
            cf1_u_i,
            cf1_U_i1.clone(),
        )?;
        v1.conditional_enforce_equal(&Boolean::TRUE, &is_not_basecase)?;
        let v2 = NIFSFullGadget::<C2, GC2>::verify(
            cf2_r_bits,
            cf2_r_nonnat,
            cf2_cmT,
            cf1_U_i1, // the output from NIFS.V(cf1_r, cf_U, cfE_u)
            cf2_u_i,
            cf_U_i1,
        )?;
        v2.conditional_enforce_equal(&Boolean::TRUE, &is_not_basecase)?;

        Ok(())
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use ark_bn254::{Fr, G1Projective as Projective};
    use ark_ff::BigInteger;
    use ark_r1cs_std::{alloc::AllocVar, R1CSVar};
    use ark_relations::r1cs::ConstraintSystem;
    use ark_std::UniformRand;

    use crate::commitment::pedersen::Pedersen;
    use crate::folding::nova::nifs::tests::prepare_simple_fold_inputs;
    use crate::folding::nova::nifs::NIFS;
    use crate::transcript::poseidon::poseidon_test_config;

    #[test]
    fn test_committed_instance_var() {
        let mut rng = ark_std::test_rng();

        let ci = CommittedInstance::<Projective> {
            cmE: Projective::rand(&mut rng),
            u: Fr::rand(&mut rng),
            cmW: Projective::rand(&mut rng),
            x: vec![Fr::rand(&mut rng); 1],
        };

        let cs = ConstraintSystem::<Fr>::new_ref();
        let ciVar =
            CommittedInstanceVar::<Projective>::new_witness(cs.clone(), || Ok(ci.clone())).unwrap();
        assert_eq!(ciVar.u.value().unwrap(), ci.u);
        assert_eq!(ciVar.x.value().unwrap(), ci.x);
        // the values cmE and cmW are checked in the CycleFold's circuit
        // CommittedInstanceInCycleFoldVar in
        // nova::cyclefold::tests::test_committed_instance_cyclefold_var
    }

    #[test]
    fn test_nifs_gadget() {
        let (_, _, _, _, ci1, _, ci2, _, ci3, _, cmT, _, r_Fr) = prepare_simple_fold_inputs();

        let ci3_verifier = NIFS::<Projective, Pedersen<Projective>>::verify(r_Fr, &ci1, &ci2, &cmT);
        assert_eq!(ci3_verifier, ci3);

        let cs = ConstraintSystem::<Fr>::new_ref();

        let rVar = FpVar::<Fr>::new_witness(cs.clone(), || Ok(r_Fr)).unwrap();
        let ci1Var =
            CommittedInstanceVar::<Projective>::new_witness(cs.clone(), || Ok(ci1.clone()))
                .unwrap();
        let ci2Var =
            CommittedInstanceVar::<Projective>::new_witness(cs.clone(), || Ok(ci2.clone()))
                .unwrap();
        let ci3Var =
            CommittedInstanceVar::<Projective>::new_witness(cs.clone(), || Ok(ci3.clone()))
                .unwrap();

        let nifs_check = NIFSGadget::<Projective>::verify(
            rVar.clone(),
            ci1Var.clone(),
            ci2Var.clone(),
            ci3Var.clone(),
        )
        .unwrap();
        nifs_check.enforce_equal(&Boolean::<Fr>::TRUE).unwrap();
        assert!(cs.is_satisfied().unwrap());
    }

    #[test]
    fn test_committed_instance_hash() {
        let mut rng = ark_std::test_rng();
        let poseidon_config = poseidon_test_config::<Fr>();

        let i = Fr::from(3_u32);
        let z_0 = vec![Fr::from(3_u32)];
        let z_i = vec![Fr::from(3_u32)];
        let ci = CommittedInstance::<Projective> {
            cmE: Projective::rand(&mut rng),
            u: Fr::rand(&mut rng),
            cmW: Projective::rand(&mut rng),
            x: vec![Fr::rand(&mut rng); 1],
        };

        // compute the CommittedInstance hash natively
        let h = ci
            .hash(&poseidon_config, i, z_0.clone(), z_i.clone())
            .unwrap();

        let cs = ConstraintSystem::<Fr>::new_ref();

        let iVar = FpVar::<Fr>::new_witness(cs.clone(), || Ok(i)).unwrap();
        let z_0Var = Vec::<FpVar<Fr>>::new_witness(cs.clone(), || Ok(z_0.clone())).unwrap();
        let z_iVar = Vec::<FpVar<Fr>>::new_witness(cs.clone(), || Ok(z_i.clone())).unwrap();
        let ciVar =
            CommittedInstanceVar::<Projective>::new_witness(cs.clone(), || Ok(ci.clone())).unwrap();

        let crh_params = CRHParametersVar::<Fr>::new_constant(cs.clone(), poseidon_config).unwrap();

        // compute the CommittedInstance hash in-circuit
        let (hVar, _) = ciVar.hash(&crh_params, iVar, z_0Var, z_iVar).unwrap();
        assert!(cs.is_satisfied().unwrap());

        // check that the natively computed and in-circuit computed hashes match
        assert_eq!(hVar.value().unwrap(), h);
    }

    // checks that the gadget and native implementations of the challenge computation match
    #[test]
    fn test_challenge_gadget() {
        let mut rng = ark_std::test_rng();
        let poseidon_config = poseidon_test_config::<Fr>();

        let u_i = CommittedInstance::<Projective> {
            cmE: Projective::rand(&mut rng),
            u: Fr::rand(&mut rng),
            cmW: Projective::rand(&mut rng),
            x: vec![Fr::rand(&mut rng); 1],
        };
        let U_i = CommittedInstance::<Projective> {
            cmE: Projective::rand(&mut rng),
            u: Fr::rand(&mut rng),
            cmW: Projective::rand(&mut rng),
            x: vec![Fr::rand(&mut rng); 1],
        };
        let cmT = Projective::rand(&mut rng);

        // compute the challenge natively
        let r_bits = ChallengeGadget::<Projective>::get_challenge_native(
            &poseidon_config,
            U_i.clone(),
            u_i.clone(),
            cmT,
        )
        .unwrap();
        let r = Fr::from_bigint(BigInteger::from_bits_le(&r_bits)).unwrap();

        let cs = ConstraintSystem::<Fr>::new_ref();
        let u_iVar =
            CommittedInstanceVar::<Projective>::new_witness(cs.clone(), || Ok(u_i.clone()))
                .unwrap();
        let U_iVar =
            CommittedInstanceVar::<Projective>::new_witness(cs.clone(), || Ok(U_i.clone()))
                .unwrap();
        let cmTVar = NonNativeAffineVar::<Projective>::new_witness(cs.clone(), || Ok(cmT)).unwrap();

        // compute the challenge in-circuit
        let U_iVar_vec = [
            vec![U_iVar.u.clone()],
            U_iVar.x.clone(),
            U_iVar.cmE.x.to_constraint_field().unwrap(),
            U_iVar.cmE.y.to_constraint_field().unwrap(),
            U_iVar.cmE.infinity.to_constraint_field().unwrap(),
            U_iVar.cmW.x.to_constraint_field().unwrap(),
            U_iVar.cmW.y.to_constraint_field().unwrap(),
            U_iVar.cmW.infinity.to_constraint_field().unwrap(),
        ]
        .concat();
        let r_bitsVar = ChallengeGadget::<Projective>::get_challenge_gadget(
            cs.clone(),
            &poseidon_config,
            U_iVar_vec,
            u_iVar,
            cmTVar,
        )
        .unwrap();
        assert!(cs.is_satisfied().unwrap());

        // check that the natively computed and in-circuit computed hashes match
        let rVar = Boolean::le_bits_to_fp_var(&r_bitsVar).unwrap();
        assert_eq!(rVar.value().unwrap(), r);
        assert_eq!(r_bitsVar.value().unwrap(), r_bits);
    }
}
