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
pub struct CommittedInstanceVar<C: CurveGroup> {
    pub u: FpVar<C::ScalarField>,
    pub x: Vec<FpVar<C::ScalarField>>,
    pub cmE: NonNativeAffineVar<C::ScalarField>,
    pub cmW: NonNativeAffineVar<C::ScalarField>,
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

            let cmE = NonNativeAffineVar::<C::ScalarField>::new_variable(
                cs.clone(),
                || Ok(val.borrow().cmE),
                mode,
            )?;
            let cmW = NonNativeAffineVar::<C::ScalarField>::new_variable(
                cs.clone(),
                || Ok(val.borrow().cmW),
                mode,
            )?;

            Ok(Self { u, x, cmE, cmW })
        })
    }
}

impl<C> CommittedInstanceVar<C>
where
    C: CurveGroup,
    <C as Group>::ScalarField: Absorb,
{
    /// hash implements the committed instance hash compatible with the native implementation from
    /// CommittedInstance.hash.
    /// Returns `H(i, z_0, z_i, U_i)`, where `i` can be `i` but also `i+1`, and `U` is the
    /// `CommittedInstance`.
    pub fn hash(
        self,
        crh_params: &CRHParametersVar<CF1<C>>,
        i: FpVar<CF1<C>>,
        z_0: Vec<FpVar<CF1<C>>>,
        z_i: Vec<FpVar<CF1<C>>>,
    ) -> Result<FpVar<CF1<C>>, SynthesisError> {
        let input = vec![
            vec![i],
            z_0,
            z_i,
            vec![self.u],
            self.x,
            self.cmE.x,
            self.cmE.y,
            self.cmW.x,
            self.cmW.y,
        ]
        .concat();
        CRHGadget::<C::ScalarField>::evaluate(crh_params, &input)
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
{
    /// Implements the constraints for NIFS.V for u and x, since cm(E) and cm(W) are delegated to
    /// the CycleFold circuit.
    pub fn verify(
        r: FpVar<CF1<C>>,
        ci1: CommittedInstanceVar<C>,
        ci2: CommittedInstanceVar<C>,
        ci3: CommittedInstanceVar<C>,
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
        u_i: CommittedInstance<C>,
        U_i: CommittedInstance<C>,
        cmT: C,
    ) -> Result<Vec<bool>, SynthesisError> {
        let (u_cmE_x, u_cmE_y) = point_to_nonnative_limbs::<C>(u_i.cmE)?;
        let (u_cmW_x, u_cmW_y) = point_to_nonnative_limbs::<C>(u_i.cmW)?;
        let (U_cmE_x, U_cmE_y) = point_to_nonnative_limbs::<C>(U_i.cmE)?;
        let (U_cmW_x, U_cmW_y) = point_to_nonnative_limbs::<C>(U_i.cmW)?;
        let (cmT_x, cmT_y) = point_to_nonnative_limbs::<C>(cmT)?;

        let mut sponge = PoseidonSponge::<C::ScalarField>::new(poseidon_config);
        let input = vec![
            vec![u_i.u],
            u_i.x.clone(),
            u_cmE_x,
            u_cmE_y,
            u_cmW_x,
            u_cmW_y,
            vec![U_i.u],
            U_i.x.clone(),
            U_cmE_x,
            U_cmE_y,
            U_cmW_x,
            U_cmW_y,
            cmT_x,
            cmT_y,
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
        u_i: CommittedInstanceVar<C>,
        U_i: CommittedInstanceVar<C>,
        cmT: NonNativeAffineVar<C::ScalarField>,
    ) -> Result<Vec<Boolean<C::ScalarField>>, SynthesisError> {
        let mut sponge = PoseidonSpongeVar::<C::ScalarField>::new(cs, poseidon_config);

        let input: Vec<FpVar<C::ScalarField>> = vec![
            vec![u_i.u.clone()],
            u_i.x.clone(),
            u_i.cmE.x,
            u_i.cmE.y,
            u_i.cmW.x,
            u_i.cmW.y,
            vec![U_i.u.clone()],
            U_i.x.clone(),
            U_i.cmE.x,
            U_i.cmE.y,
            U_i.cmW.x,
            U_i.cmW.y,
            cmT.x,
            cmT.y,
        ]
        .concat();
        sponge.absorb(&input)?;
        let bits = sponge.squeeze_bits(N_BITS_RO)?;
        Ok(bits)
    }
}

/// FCircuit defines the trait of the circuit of the F function, which is the one being executed
/// inside the agmented F' function.
pub trait FCircuit<F: PrimeField>: Clone + Copy + Debug {
    /// returns a new FCircuit instance
    fn new() -> Self;

    /// computes the next state values in place, assigning z_{i+1} into z_i, and
    /// computing the new z_i
    fn step_native(
        // this method uses self, so that each FCircuit implementation (and different frontends)
        // can hold a state if needed to store data to compute the next state.
        self,
        z_i: Vec<F>,
    ) -> Vec<F>;

    /// generates the constraints for the step of F for the given z_i
    fn generate_step_constraints(
        // this method uses self, so that each FCircuit implementation (and different frontends)
        // can hold a state if needed to store data to generate the constraints.
        self,
        cs: ConstraintSystemRef<F>,
        z_i: Vec<FpVar<F>>,
    ) -> Result<Vec<FpVar<F>>, SynthesisError>;
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
    pub z_0: Option<Vec<C1::ScalarField>>,
    pub z_i: Option<Vec<C1::ScalarField>>,
    pub u_i: Option<CommittedInstance<C1>>,
    pub U_i: Option<CommittedInstance<C1>>,
    pub U_i1: Option<CommittedInstance<C1>>,
    pub cmT: Option<C1>,
    pub F: FC,              // F circuit
    pub x: Option<CF1<C1>>, // public inputs (u_{i+1}.x)

    // cyclefold verifier on C1
    pub cf_u_i: Option<CommittedInstance<C2>>,
    pub cf_U_i: Option<CommittedInstance<C2>>,
    pub cf_U_i1: Option<CommittedInstance<C2>>,
    pub cf_cmT: Option<C2>,
    pub cf_r_nonnat: Option<C2::ScalarField>,
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
            z_0: None,
            z_i: None,
            u_i: None,
            U_i: None,
            U_i1: None,
            cmT: None,
            F: F_circuit,
            x: None,
            // cyclefold values
            cf_u_i: None,
            cf_U_i: None,
            cf_U_i1: None,
            cf_cmT: None,
            cf_r_nonnat: None,
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
            Ok(self.z_0.unwrap_or(vec![CF1::<C1>::zero()]))
        })?;
        let z_i = Vec::<FpVar<CF1<C1>>>::new_witness(cs.clone(), || {
            Ok(self.z_i.unwrap_or(vec![CF1::<C1>::zero()]))
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
        let cmT =
            NonNativeAffineVar::new_witness(cs.clone(), || Ok(self.cmT.unwrap_or_else(C1::zero)))?;
        let x =
            FpVar::<CF1<C1>>::new_input(cs.clone(), || Ok(self.x.unwrap_or_else(CF1::<C1>::zero)))?;

        let crh_params = CRHParametersVar::<C1::ScalarField>::new_constant(
            cs.clone(),
            self.poseidon_config.clone(),
        )?;

        // get z_{i+1} from the F circuit
        let z_i1 = self.F.generate_step_constraints(cs.clone(), z_i.clone())?;

        let zero = FpVar::<CF1<C1>>::new_constant(cs.clone(), CF1::<C1>::zero())?;
        let is_not_basecase = i.is_neq(&zero)?;

        // 1. u_i.x == H(i, z_0, z_i, U_i)
        let u_i_x = U_i
            .clone()
            .hash(&crh_params, i.clone(), z_0.clone(), z_i.clone())?;

        // check that h == u_i.x
        (u_i.x[0]).conditional_enforce_equal(&u_i_x, &is_not_basecase)?;

        // 2. u_i.cmE==cm(0), u_i.u==1
        let zero_x = NonNativeFieldVar::<C1::BaseField, C1::ScalarField>::new_constant(
            cs.clone(),
            C1::BaseField::zero(),
        )?
        .to_constraint_field()?;
        let zero_y = NonNativeFieldVar::<C1::BaseField, C1::ScalarField>::new_constant(
            cs.clone(),
            C1::BaseField::one(),
        )?
        .to_constraint_field()?;
        (u_i.cmE.x.is_eq(&zero_x)?).conditional_enforce_equal(&Boolean::TRUE, &is_not_basecase)?;
        (u_i.cmE.y.is_eq(&zero_y)?).conditional_enforce_equal(&Boolean::TRUE, &is_not_basecase)?;
        (u_i.u.is_one()?).conditional_enforce_equal(&Boolean::TRUE, &is_not_basecase)?;

        // 3. nifs.verify, checks that folding u_i & U_i obtains U_{i+1}.
        // compute r = H(u_i, U_i, cmT)
        let r_bits = ChallengeGadget::<C1>::get_challenge_gadget(
            cs.clone(),
            &self.poseidon_config,
            u_i.clone(),
            U_i.clone(),
            cmT.clone(),
        )?;
        let r = Boolean::le_bits_to_fp_var(&r_bits)?;

        // Notice that NIFSGadget::verify is not checking the folding of cmE & cmW, since it will
        // be done on the other curve.
        let nifs_check = NIFSGadget::<C1>::verify(r, u_i.clone(), U_i.clone(), U_i1.clone())?;
        nifs_check.conditional_enforce_equal(&Boolean::TRUE, &is_not_basecase)?;

        // 4. u_{i+1}.x = H(i+1, z_0, z_i+1, U_{i+1}), this is the output of F'
        let u_i1_x = U_i1.clone().hash(
            &crh_params,
            i + FpVar::<CF1<C1>>::one(),
            z_0.clone(),
            z_i1.clone(),
        )?;

        u_i1_x.enforce_equal(&x)?;

        // CycleFold part
        let cf_u_dummy_native = CommittedInstance::<C2>::dummy(CF_IO_LEN);
        let cf_u_i = CycleFoldCommittedInstanceVar::<C2, GC2>::new_witness(cs.clone(), || {
            Ok(self.cf_u_i.unwrap_or_else(|| cf_u_dummy_native.clone()))
        })?;
        let cf_U_i = CycleFoldCommittedInstanceVar::<C2, GC2>::new_witness(cs.clone(), || {
            Ok(self.cf_U_i.unwrap_or_else(|| cf_u_dummy_native.clone()))
        })?;
        let cf_U_i1 = CycleFoldCommittedInstanceVar::<C2, GC2>::new_witness(cs.clone(), || {
            Ok(self.cf_U_i1.unwrap_or_else(|| cf_u_dummy_native.clone()))
        })?;
        let cf_cmT = GC2::new_witness(cs.clone(), || Ok(self.cf_cmT.unwrap_or_else(C2::zero)))?;
        // cf_r_nonnat is an auxiliary input
        let cf_r_nonnat =
            NonNativeFieldVar::<C2::ScalarField, CF2<C2>>::new_witness(cs.clone(), || {
                Ok(self.cf_r_nonnat.unwrap_or_else(C2::ScalarField::zero))
            })?;

        // check that cf_u_i.x == [u_i, U_i, U_{i+1}]
        let incircuit_x = vec![
            u_i.cmE.x, u_i.cmE.y, u_i.cmW.x, u_i.cmW.y, U_i.cmE.x, U_i.cmE.y, U_i.cmW.x, U_i.cmW.y,
            U_i1.cmE.x, U_i1.cmE.y, U_i1.cmW.x, U_i1.cmW.y,
        ]
        .concat();

        let mut cf_u_i_x: Vec<FpVar<CF2<C2>>> = vec![];
        for x_i in cf_u_i.x.iter() {
            let mut x_fpvar = x_i.to_constraint_field()?;
            cf_u_i_x.append(&mut x_fpvar);
        }
        cf_u_i_x.conditional_enforce_equal(&incircuit_x, &is_not_basecase)?;

        // cf_r_bits is denoted by rho* in the paper
        let cf_r_bits = CycleFoldChallengeGadget::<C2, GC2>::get_challenge_gadget(
            cs.clone(),
            &self.poseidon_config,
            cf_u_i.clone(),
            cf_U_i.clone(),
            cf_cmT.clone(),
        )?;
        // assert that cf_r_bits == cf_r_nonnat converted to bits. cf_r_nonnat is just an auxiliary
        // value used to compute RLC of NonNativeFieldVar values, since we can convert
        // NonNativeFieldVar into Vec<Boolean>, but not in the other direction.
        let cf_r_nonnat_bits = cf_r_nonnat.to_bits_le()?;
        cf_r_bits.conditional_enforce_equal(&cf_r_nonnat_bits[..N_BITS_RO], &is_not_basecase)?;

        // check cf_u_i.cmE=0, cf_u_i.u=1
        (cf_u_i.cmE.is_zero()?).conditional_enforce_equal(&Boolean::TRUE, &is_not_basecase)?;
        (cf_u_i.u.is_one()?).conditional_enforce_equal(&Boolean::TRUE, &is_not_basecase)?;

        // check the fold of all the parameteres of the CycleFold instances, where the elliptic
        // curve points relations are checked natively in Curve1 circuit (this one)
        let v = NIFSFullGadget::<C2, GC2>::verify(
            cf_r_bits,
            cf_r_nonnat,
            cf_cmT,
            cf_U_i,
            cf_u_i,
            cf_U_i1,
        )?;
        v.conditional_enforce_equal(&Boolean::TRUE, &is_not_basecase)?;

        Ok(())
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use ark_ff::BigInteger;
    use ark_pallas::{Fq, Fr, Projective};
    use ark_r1cs_std::{alloc::AllocVar, R1CSVar};
    use ark_relations::r1cs::{ConstraintLayer, ConstraintSystem, TracingMode};
    use ark_std::One;
    use ark_std::UniformRand;
    use ark_vesta::{constraints::GVar as GVar2, Projective as Projective2};
    use tracing_subscriber::layer::SubscriberExt;

    use crate::folding::nova::nifs::tests::prepare_simple_fold_inputs;
    use crate::folding::nova::{
        ivc::get_committed_instance_coordinates, nifs::NIFS, traits::NovaR1CS, Witness,
    };
    use crate::frontend::arkworks::{extract_r1cs, extract_z};
    use crate::pedersen::Pedersen;
    use crate::transcript::poseidon::tests::poseidon_test_config;

    #[derive(Clone, Copy, Debug)]
    /// TestFCircuit is a variation of `x^3 + x + 5 = y` (as in
    /// src/frontend/arkworks/mod.rs#tests::TestCircuit), adapted to have 2 public inputs which are
    /// used as the state. `z_i` is used as `x`, and `z_{i+1}` is used as `y`, and at the next
    /// step, `z_{i+1}` will be assigned to `z_i`, and a new `z+{i+1}` will be computted.
    pub struct TestFCircuit<F: PrimeField> {
        _f: PhantomData<F>,
    }
    impl<F: PrimeField> FCircuit<F> for TestFCircuit<F> {
        fn new() -> Self {
            Self { _f: PhantomData }
        }
        fn step_native(self, z_i: Vec<F>) -> Vec<F> {
            vec![z_i[0] * z_i[0] * z_i[0] + z_i[0] + F::from(5_u32)]
        }
        fn generate_step_constraints(
            self,
            cs: ConstraintSystemRef<F>,
            z_i: Vec<FpVar<F>>,
        ) -> Result<Vec<FpVar<F>>, SynthesisError> {
            let five = FpVar::<F>::new_constant(cs.clone(), F::from(5u32))?;
            let z_i = z_i[0].clone();

            Ok(vec![&z_i * &z_i * &z_i + &z_i + &five])
        }
    }

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

        let ci3_verifier = NIFS::<Projective>::verify(r_Fr, &ci1, &ci2, &cmT);
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
        let hVar = ciVar.hash(&crh_params, iVar, z_0Var, z_iVar).unwrap();
        assert!(cs.is_satisfied().unwrap());

        // check that the natively computed and in-circuit computed hashes match
        assert_eq!(hVar.value().unwrap(), h);
    }

    // checks that the gadget and native implementations of the challenge computation matcbh
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
            u_i.clone(),
            U_i.clone(),
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
        let cmTVar = NonNativeAffineVar::<Fr>::new_witness(cs.clone(), || Ok(cmT)).unwrap();

        // compute the challenge in-circuit
        let r_bitsVar = ChallengeGadget::<Projective>::get_challenge_gadget(
            cs.clone(),
            &poseidon_config,
            u_iVar,
            U_iVar,
            cmTVar,
        )
        .unwrap();
        assert!(cs.is_satisfied().unwrap());

        // check that the natively computed and in-circuit computed hashes match
        let rVar = Boolean::le_bits_to_fp_var(&r_bitsVar).unwrap();
        assert_eq!(rVar.value().unwrap(), r);
        assert_eq!(r_bitsVar.value().unwrap(), r_bits);
    }

    #[test]
    /// test_augmented_f_circuit folds the TestFCircuit circuit in multiple iterations, feeding the
    /// values into the AugmentedFCircuit.
    fn test_augmented_f_circuit() {
        let mut layer = ConstraintLayer::default();
        layer.mode = TracingMode::OnlyConstraints;
        let subscriber = tracing_subscriber::Registry::default().with(layer);
        let _guard = tracing::subscriber::set_default(subscriber);

        let mut rng = ark_std::test_rng();
        let poseidon_config = poseidon_test_config::<Fr>();

        // compute z vector for the initial instance
        let cs = ConstraintSystem::<Fr>::new_ref();

        // prepare the circuit to obtain its R1CS
        let F_circuit = TestFCircuit::<Fr>::new();
        let mut augmented_F_circuit =
            AugmentedFCircuit::<Projective, Projective2, GVar2, TestFCircuit<Fr>>::empty(
                &poseidon_config,
                F_circuit,
            );
        augmented_F_circuit
            .generate_constraints(cs.clone())
            .unwrap();
        cs.finalize();
        println!("num_constraints={:?}", cs.num_constraints());
        let cs = cs.into_inner().unwrap();
        let r1cs = extract_r1cs::<Fr>(&cs);
        let z = extract_z::<Fr>(&cs); // includes 1 and public inputs
        let (w, x) = r1cs.split_z(&z);
        assert_eq!(z.len(), r1cs.A.n_cols);
        assert_eq!(1 + x.len() + w.len(), r1cs.A.n_cols);
        assert_eq!(r1cs.l, x.len());

        let pedersen_params = Pedersen::<Projective>::new_params(&mut rng, r1cs.A.n_rows);

        // first step, set z_i=z_0=3 and z_{i+1}=35 (initial values)
        let z_0 = vec![Fr::from(3_u32)];
        let mut z_i = z_0.clone();
        let mut z_i1 = vec![Fr::from(35_u32)];

        let w_dummy = Witness::<Projective>::new(vec![Fr::zero(); w.len()], r1cs.A.n_rows);
        let u_dummy = CommittedInstance::<Projective>::dummy(x.len());

        // W_i is a 'dummy witness', all zeroes, but with the size corresponding to the R1CS that
        // we're working with.
        // set U_i <-- dummy instance
        let mut W_i = w_dummy.clone();
        let mut U_i = u_dummy.clone();
        r1cs.check_relaxed_instance_relation(&W_i, &U_i).unwrap();

        let mut w_i = w_dummy.clone();
        let mut u_i = u_dummy.clone();
        let (mut W_i1, mut U_i1, mut cmT): (
            Witness<Projective>,
            CommittedInstance<Projective>,
            Projective,
        ) = (w_dummy.clone(), u_dummy.clone(), Projective::generator());
        // as expected, dummy instances pass the relaxed_r1cs check
        r1cs.check_relaxed_instance_relation(&W_i1, &U_i1).unwrap();

        let mut i = Fr::zero();
        let mut u_i1_x: Fr;
        for _ in 0..4 {
            if i == Fr::zero() {
                // base case: i=0, z_i=z_0, U_i = U_d := dummy instance
                // u_1.x = H(1, z_0, z_i, U_i)
                u_i1_x = U_i
                    .hash(&poseidon_config, Fr::one(), z_0.clone(), z_i1.clone())
                    .unwrap();

                // base case
                augmented_F_circuit =
                    AugmentedFCircuit::<Projective, Projective2, GVar2, TestFCircuit<Fr>> {
                        _gc2: PhantomData,
                        poseidon_config: poseidon_config.clone(),
                        i: Some(i),             // = 0
                        z_0: Some(z_0.clone()), // = z_i=3
                        z_i: Some(z_i.clone()),
                        u_i: Some(u_i.clone()),   // = dummy
                        U_i: Some(U_i.clone()),   // = dummy
                        U_i1: Some(U_i1.clone()), // = dummy
                        cmT: Some(cmT),
                        F: F_circuit,
                        x: Some(u_i1_x),
                        // cyclefold instances (not tested in this test)
                        cf_u_i: None,
                        cf_U_i: None,
                        cf_U_i1: None,
                        cf_cmT: None,
                        cf_r_nonnat: None,
                    };
            } else {
                r1cs.check_relaxed_instance_relation(&w_i, &u_i).unwrap();
                r1cs.check_relaxed_instance_relation(&W_i, &U_i).unwrap();

                // U_{i+1}
                let T: Vec<Fr>;
                (T, cmT) = NIFS::<Projective>::compute_cmT(
                    &pedersen_params,
                    &r1cs,
                    &w_i,
                    &u_i,
                    &W_i,
                    &U_i,
                )
                .unwrap();

                // get challenge r
                let r_bits = ChallengeGadget::<Projective>::get_challenge_native(
                    &poseidon_config,
                    u_i.clone(),
                    U_i.clone(),
                    cmT,
                )
                .unwrap();
                let r_Fr = Fr::from_bigint(BigInteger::from_bits_le(&r_bits)).unwrap();

                (W_i1, U_i1) =
                    NIFS::<Projective>::fold_instances(r_Fr, &w_i, &u_i, &W_i, &U_i, &T, cmT)
                        .unwrap();

                r1cs.check_relaxed_instance_relation(&W_i1, &U_i1).unwrap();

                // folded instance output (public input, x)
                // u_{i+1}.x = H(i+1, z_0, z_{i+1}, U_{i+1})
                u_i1_x = U_i1
                    .hash(&poseidon_config, i + Fr::one(), z_0.clone(), z_i1.clone())
                    .unwrap();

                // set up dummy cyclefold instances just for the sake of this test. Warning, this
                // is only because we are in a test were we're not testing the cyclefold side of
                // things.
                let cf_W_i = Witness::<Projective2>::new(vec![Fq::zero(); 1], 1);
                let cf_U_i = CommittedInstance::<Projective2>::dummy(CF_IO_LEN);
                let cf_u_i_x = [
                    get_committed_instance_coordinates(&u_i),
                    get_committed_instance_coordinates(&U_i),
                    get_committed_instance_coordinates(&U_i1),
                ]
                .concat();
                let cf_u_i = CommittedInstance::<Projective2> {
                    cmE: cf_U_i.cmE,
                    u: Fq::one(),
                    cmW: cf_U_i.cmW,
                    x: cf_u_i_x,
                };
                let cf_w_i = cf_W_i.clone();
                let (cf_T, cf_cmT): (Vec<Fq>, Projective2) =
                    (vec![Fq::zero(); cf_W_i.E.len()], Projective2::zero());
                let cf_r_bits =
                    CycleFoldChallengeGadget::<Projective2, GVar2>::get_challenge_native(
                        &poseidon_config,
                        cf_u_i.clone(),
                        cf_U_i.clone(),
                        cf_cmT,
                    )
                    .unwrap();
                let cf_r_Fq = Fq::from_bigint(BigInteger::from_bits_le(&cf_r_bits)).unwrap();
                let (_, cf_U_i1) = NIFS::<Projective2>::fold_instances(
                    cf_r_Fq, &cf_W_i, &cf_U_i, &cf_w_i, &cf_u_i, &cf_T, cf_cmT,
                )
                .unwrap();

                augmented_F_circuit =
                    AugmentedFCircuit::<Projective, Projective2, GVar2, TestFCircuit<Fr>> {
                        _gc2: PhantomData,
                        poseidon_config: poseidon_config.clone(),
                        i: Some(i),
                        z_0: Some(z_0.clone()),
                        z_i: Some(z_i.clone()),
                        u_i: Some(u_i),
                        U_i: Some(U_i.clone()),
                        U_i1: Some(U_i1.clone()),
                        cmT: Some(cmT),
                        F: F_circuit,
                        x: Some(u_i1_x),
                        cf_u_i: Some(cf_u_i),
                        cf_U_i: Some(cf_U_i),
                        cf_U_i1: Some(cf_U_i1),
                        cf_cmT: Some(cf_cmT),
                        cf_r_nonnat: Some(cf_r_Fq),
                    };
            }

            let cs = ConstraintSystem::<Fr>::new_ref();

            augmented_F_circuit
                .generate_constraints(cs.clone())
                .unwrap();
            let is_satisfied = cs.is_satisfied().unwrap();
            if !is_satisfied {
                dbg!(cs.which_is_unsatisfied().unwrap());
            }
            assert!(is_satisfied);

            cs.finalize();
            let cs = cs.into_inner().unwrap();
            // notice that here we use 'Z' (uppercase) to denote the 'z-vector' as in the paper,
            // not the value 'z' (lowercase) which is the state
            let Z_i1 = extract_z::<Fr>(&cs);
            let (w_i1, x_i1) = r1cs.split_z(&Z_i1);
            assert_eq!(x_i1.len(), 1);
            assert_eq!(x_i1[0], u_i1_x);

            // compute committed instances, w_{i+1}, u_{i+1}, which will be used as w_i, u_i, so we
            // assign them directly to w_i, u_i.
            w_i = Witness::<Projective>::new(w_i1.clone(), r1cs.A.n_rows);
            u_i = w_i.commit(&pedersen_params, vec![u_i1_x]).unwrap();

            r1cs.check_relaxed_instance_relation(&w_i, &u_i).unwrap();
            r1cs.check_relaxed_instance_relation(&W_i1, &U_i1).unwrap();

            // set values for next iteration
            i += Fr::one();
            // advance the F circuit state
            z_i = z_i1.clone();
            z_i1 = F_circuit.step_native(z_i.clone());
            U_i = U_i1.clone();
            W_i = W_i1.clone();
        }
    }
}
