/// This file implements the onchain (Ethereum's EVM) decider circuit. For non-ethereum use cases,
/// other more efficient approaches can be used.
use ark_crypto_primitives::crh::poseidon::constraints::CRHParametersVar;
use ark_crypto_primitives::sponge::{poseidon::PoseidonConfig, Absorb};
use ark_ec::{CurveGroup, Group};
use ark_ff::{BigInteger, PrimeField};
use ark_poly::Polynomial;
use ark_r1cs_std::{
    alloc::{AllocVar, AllocationMode},
    boolean::Boolean,
    eq::EqGadget,
    fields::{fp::FpVar, FieldVar},
    groups::GroupOpsBounds,
    poly::{domain::Radix2DomainVar, evaluations::univariate::EvaluationsVar},
    prelude::CurveVar,
    ToConstraintFieldGadget,
};
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, Namespace, SynthesisError};
use ark_std::{log2, Zero};
use core::{borrow::Borrow, marker::PhantomData};

use super::{circuits::ChallengeGadget, nifs::NIFS};
use crate::ccs::r1cs::R1CS;
use crate::commitment::{pedersen::Params as PedersenParams, CommitmentScheme};
use crate::folding::circuits::{
    nonnative::{
        affine::{nonnative_affine_to_field_elements, NonNativeAffineVar},
        uint::NonNativeUintVar,
    },
    CF1, CF2,
};
use crate::folding::nova::{circuits::CommittedInstanceVar, CommittedInstance, Nova, Witness};
use crate::frontend::FCircuit;
use crate::transcript::{
    poseidon::{PoseidonTranscript, PoseidonTranscriptVar},
    Transcript, TranscriptVar,
};
use crate::utils::{
    gadgets::{MatrixGadget, SparseMatrixVar, VectorGadget},
    vec::poly_from_vec,
};
use crate::Error;

#[derive(Debug, Clone)]
pub struct RelaxedR1CSGadget {}
impl RelaxedR1CSGadget {
    /// performs the RelaxedR1CS check for native variables (Az∘Bz==uCz+E)
    pub fn check_native<F: PrimeField>(
        r1cs: R1CSVar<F, F, FpVar<F>>,
        E: Vec<FpVar<F>>,
        u: FpVar<F>,
        z: Vec<FpVar<F>>,
    ) -> Result<(), SynthesisError> {
        let Az = r1cs.A.mul_vector(&z)?;
        let Bz = r1cs.B.mul_vector(&z)?;
        let Cz = r1cs.C.mul_vector(&z)?;
        let uCzE = Cz.mul_scalar(&u)?.add(&E)?;
        let AzBz = Az.hadamard(&Bz)?;
        AzBz.enforce_equal(&uCzE)?;
        Ok(())
    }

    /// performs the RelaxedR1CS check for non-native variables (Az∘Bz==uCz+E)
    pub fn check_nonnative<F: PrimeField, CF: PrimeField>(
        r1cs: R1CSVar<F, CF, NonNativeUintVar<CF>>,
        E: Vec<NonNativeUintVar<CF>>,
        u: NonNativeUintVar<CF>,
        z: Vec<NonNativeUintVar<CF>>,
    ) -> Result<(), SynthesisError> {
        // First we do addition and multiplication without mod F's order
        let Az = r1cs.A.mul_vector(&z)?;
        let Bz = r1cs.B.mul_vector(&z)?;
        let Cz = r1cs.C.mul_vector(&z)?;
        let uCzE = Cz.mul_scalar(&u)?.add(&E)?;
        let AzBz = Az.hadamard(&Bz)?;

        // Then we compare the results by checking if they are congruent
        // modulo the field order
        AzBz.into_iter()
            .zip(uCzE)
            .try_for_each(|(a, b)| a.enforce_congruent::<F>(&b))
    }
}

#[derive(Debug, Clone)]
pub struct R1CSVar<F: PrimeField, CF: PrimeField, FV: AllocVar<F, CF>> {
    _f: PhantomData<F>,
    _cf: PhantomData<CF>,
    _fv: PhantomData<FV>,
    pub A: SparseMatrixVar<F, CF, FV>,
    pub B: SparseMatrixVar<F, CF, FV>,
    pub C: SparseMatrixVar<F, CF, FV>,
}

impl<F, CF, FV> AllocVar<R1CS<F>, CF> for R1CSVar<F, CF, FV>
where
    F: PrimeField,
    CF: PrimeField,
    FV: AllocVar<F, CF>,
{
    fn new_variable<T: Borrow<R1CS<F>>>(
        cs: impl Into<Namespace<CF>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        _mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        f().and_then(|val| {
            let cs = cs.into();

            let A = SparseMatrixVar::<F, CF, FV>::new_constant(cs.clone(), &val.borrow().A)?;
            let B = SparseMatrixVar::<F, CF, FV>::new_constant(cs.clone(), &val.borrow().B)?;
            let C = SparseMatrixVar::<F, CF, FV>::new_constant(cs.clone(), &val.borrow().C)?;

            Ok(Self {
                _f: PhantomData,
                _cf: PhantomData,
                _fv: PhantomData,
                A,
                B,
                C,
            })
        })
    }
}

/// In-circuit representation of the Witness associated to the CommittedInstance.
#[derive(Debug, Clone)]
pub struct WitnessVar<C: CurveGroup> {
    pub E: Vec<FpVar<C::ScalarField>>,
    pub rE: FpVar<C::ScalarField>,
    pub W: Vec<FpVar<C::ScalarField>>,
    pub rW: FpVar<C::ScalarField>,
}

impl<C> AllocVar<Witness<C>, CF1<C>> for WitnessVar<C>
where
    C: CurveGroup,
    <C as ark_ec::CurveGroup>::BaseField: PrimeField,
{
    fn new_variable<T: Borrow<Witness<C>>>(
        cs: impl Into<Namespace<CF1<C>>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        f().and_then(|val| {
            let cs = cs.into();

            let E: Vec<FpVar<C::ScalarField>> =
                Vec::new_variable(cs.clone(), || Ok(val.borrow().E.clone()), mode)?;
            let rE =
                FpVar::<C::ScalarField>::new_variable(cs.clone(), || Ok(val.borrow().rE), mode)?;

            let W: Vec<FpVar<C::ScalarField>> =
                Vec::new_variable(cs.clone(), || Ok(val.borrow().W.clone()), mode)?;
            let rW =
                FpVar::<C::ScalarField>::new_variable(cs.clone(), || Ok(val.borrow().rW), mode)?;

            Ok(Self { E, rE, W, rW })
        })
    }
}

/// In-circuit representation of the Witness associated to the CommittedInstance, but with
/// non-native representation, since it is used to represent the CycleFold witness.
#[derive(Debug, Clone)]
pub struct CycleFoldWitnessVar<C: CurveGroup> {
    pub E: Vec<NonNativeUintVar<CF2<C>>>,
    pub rE: NonNativeUintVar<CF2<C>>,
    pub W: Vec<NonNativeUintVar<CF2<C>>>,
    pub rW: NonNativeUintVar<CF2<C>>,
}

impl<C> AllocVar<Witness<C>, CF2<C>> for CycleFoldWitnessVar<C>
where
    C: CurveGroup,
    <C as ark_ec::CurveGroup>::BaseField: PrimeField,
{
    fn new_variable<T: Borrow<Witness<C>>>(
        cs: impl Into<Namespace<CF2<C>>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        f().and_then(|val| {
            let cs = cs.into();

            let E = Vec::new_variable(cs.clone(), || Ok(val.borrow().E.clone()), mode)?;
            let rE = NonNativeUintVar::new_variable(cs.clone(), || Ok(val.borrow().rE), mode)?;

            let W = Vec::new_variable(cs.clone(), || Ok(val.borrow().W.clone()), mode)?;
            let rW = NonNativeUintVar::new_variable(cs.clone(), || Ok(val.borrow().rW), mode)?;

            Ok(Self { E, rE, W, rW })
        })
    }
}

/// Circuit that implements the in-circuit checks needed for the onchain (Ethereum's EVM)
/// verification.
#[derive(Clone, Debug)]
pub struct DeciderEthCircuit<C1, GC1, C2, GC2, CS1, CS2>
where
    C1: CurveGroup,
    GC1: CurveVar<C1, CF2<C1>>,
    C2: CurveGroup,
    GC2: CurveVar<C2, CF2<C2>>,
    CS1: CommitmentScheme<C1>,
    CS2: CommitmentScheme<C2>,
{
    _c1: PhantomData<C1>,
    _gc1: PhantomData<GC1>,
    _c2: PhantomData<C2>,
    _gc2: PhantomData<GC2>,
    _cs1: PhantomData<CS1>,
    _cs2: PhantomData<CS2>,

    /// E vector's length of the Nova instance witness
    pub E_len: usize,
    /// E vector's length of the CycleFold instance witness
    pub cf_E_len: usize,
    /// R1CS of the Augmented Function circuit
    pub r1cs: R1CS<C1::ScalarField>,
    /// R1CS of the CycleFold circuit
    pub cf_r1cs: R1CS<C2::ScalarField>,
    /// CycleFold PedersenParams over C2
    pub cf_pedersen_params: PedersenParams<C2>,
    pub poseidon_config: PoseidonConfig<CF1<C1>>,
    pub i: Option<CF1<C1>>,
    /// initial state
    pub z_0: Option<Vec<C1::ScalarField>>,
    /// current i-th state
    pub z_i: Option<Vec<C1::ScalarField>>,
    /// Nova instances
    pub u_i: Option<CommittedInstance<C1>>,
    pub w_i: Option<Witness<C1>>,
    pub U_i: Option<CommittedInstance<C1>>,
    pub W_i: Option<Witness<C1>>,
    pub U_i1: Option<CommittedInstance<C1>>,
    pub W_i1: Option<Witness<C1>>,
    pub cmT: Option<C1>,
    pub r: Option<C1::ScalarField>,
    /// CycleFold running instance
    pub cf_U_i: Option<CommittedInstance<C2>>,
    pub cf_W_i: Option<Witness<C2>>,

    /// KZG challenges
    pub kzg_c_W: Option<C1::ScalarField>,
    pub kzg_c_E: Option<C1::ScalarField>,
    pub eval_W: Option<C1::ScalarField>,
    pub eval_E: Option<C1::ScalarField>,
}
impl<C1, GC1, C2, GC2, CS1, CS2> DeciderEthCircuit<C1, GC1, C2, GC2, CS1, CS2>
where
    C1: CurveGroup,
    C2: CurveGroup,
    GC1: CurveVar<C1, CF2<C1>> + ToConstraintFieldGadget<CF2<C1>>,
    GC2: CurveVar<C2, CF2<C2>> + ToConstraintFieldGadget<CF2<C2>>,
    CS1: CommitmentScheme<C1>,
    // enforce that the CS2 is Pedersen commitment scheme, since we're at Ethereum's EVM decider
    CS2: CommitmentScheme<C2, ProverParams = PedersenParams<C2>>,
    <C1 as Group>::ScalarField: Absorb,
    <C1 as CurveGroup>::BaseField: PrimeField,
{
    pub fn from_nova<FC: FCircuit<C1::ScalarField>>(
        nova: Nova<C1, GC1, C2, GC2, FC, CS1, CS2>,
    ) -> Result<Self, Error> {
        // compute the U_{i+1}, W_{i+1}
        let (T, cmT) = NIFS::<C1, CS1>::compute_cmT(
            &nova.cs_pp,
            &nova.r1cs.clone(),
            &nova.w_i.clone(),
            &nova.u_i.clone(),
            &nova.W_i.clone(),
            &nova.U_i.clone(),
        )?;
        let r_bits = ChallengeGadget::<C1>::get_challenge_native(
            &nova.poseidon_config,
            nova.U_i.clone(),
            nova.u_i.clone(),
            cmT,
        )?;
        let r_Fr = C1::ScalarField::from_bigint(BigInteger::from_bits_le(&r_bits))
            .ok_or(Error::OutOfBounds)?;
        let (W_i1, U_i1) = NIFS::<C1, CS1>::fold_instances(
            r_Fr, &nova.W_i, &nova.U_i, &nova.w_i, &nova.u_i, &T, cmT,
        )?;

        // compute the KZG challenges used as inputs in the circuit
        let (kzg_challenge_W, kzg_challenge_E) =
            KZGChallengesGadget::<C1>::get_challenges_native(&nova.poseidon_config, U_i1.clone())?;

        // get KZG evals
        let mut W = W_i1.W.clone();
        W.extend(
            std::iter::repeat(C1::ScalarField::zero())
                .take(W_i1.W.len().next_power_of_two() - W_i1.W.len()),
        );
        let mut E = W_i1.E.clone();
        E.extend(
            std::iter::repeat(C1::ScalarField::zero())
                .take(W_i1.E.len().next_power_of_two() - W_i1.E.len()),
        );
        let p_W = poly_from_vec(W.to_vec())?;
        let eval_W = p_W.evaluate(&kzg_challenge_W);
        let p_E = poly_from_vec(E.to_vec())?;
        let eval_E = p_E.evaluate(&kzg_challenge_E);

        Ok(Self {
            _c1: PhantomData,
            _gc1: PhantomData,
            _c2: PhantomData,
            _gc2: PhantomData,
            _cs1: PhantomData,
            _cs2: PhantomData,

            E_len: nova.W_i.E.len(),
            cf_E_len: nova.cf_W_i.E.len(),
            r1cs: nova.r1cs,
            cf_r1cs: nova.cf_r1cs,
            cf_pedersen_params: nova.cf_cs_pp,
            poseidon_config: nova.poseidon_config,
            i: Some(nova.i),
            z_0: Some(nova.z_0),
            z_i: Some(nova.z_i),
            u_i: Some(nova.u_i),
            w_i: Some(nova.w_i),
            U_i: Some(nova.U_i),
            W_i: Some(nova.W_i),
            U_i1: Some(U_i1),
            W_i1: Some(W_i1),
            cmT: Some(cmT),
            r: Some(r_Fr),
            cf_U_i: Some(nova.cf_U_i),
            cf_W_i: Some(nova.cf_W_i),
            kzg_c_W: Some(kzg_challenge_W),
            kzg_c_E: Some(kzg_challenge_E),
            eval_W: Some(eval_W),
            eval_E: Some(eval_E),
        })
    }
}

impl<C1, GC1, C2, GC2, CS1, CS2> ConstraintSynthesizer<CF1<C1>>
    for DeciderEthCircuit<C1, GC1, C2, GC2, CS1, CS2>
where
    C1: CurveGroup,
    C2: CurveGroup,
    GC1: CurveVar<C1, CF2<C1>>,
    GC2: CurveVar<C2, CF2<C2>> + ToConstraintFieldGadget<CF2<C2>>,
    CS1: CommitmentScheme<C1>,
    CS2: CommitmentScheme<C2>,
    <C1 as CurveGroup>::BaseField: PrimeField,
    <C2 as CurveGroup>::BaseField: PrimeField,
    <C1 as Group>::ScalarField: Absorb,
    <C2 as Group>::ScalarField: Absorb,
    C1: CurveGroup<BaseField = C2::ScalarField, ScalarField = C2::BaseField>,
    for<'b> &'b GC2: GroupOpsBounds<'b, C2, GC2>,
{
    fn generate_constraints(self, cs: ConstraintSystemRef<CF1<C1>>) -> Result<(), SynthesisError> {
        let r1cs =
            R1CSVar::<C1::ScalarField, CF1<C1>, FpVar<CF1<C1>>>::new_witness(cs.clone(), || {
                Ok(self.r1cs.clone())
            })?;

        let i =
            FpVar::<CF1<C1>>::new_input(cs.clone(), || Ok(self.i.unwrap_or_else(CF1::<C1>::zero)))?;
        let z_0 = Vec::<FpVar<CF1<C1>>>::new_input(cs.clone(), || {
            Ok(self.z_0.unwrap_or(vec![CF1::<C1>::zero()]))
        })?;
        let z_i = Vec::<FpVar<CF1<C1>>>::new_input(cs.clone(), || {
            Ok(self.z_i.unwrap_or(vec![CF1::<C1>::zero()]))
        })?;

        let u_dummy_native = CommittedInstance::<C1>::dummy(2);
        let w_dummy_native = Witness::<C1>::new(
            vec![C1::ScalarField::zero(); self.r1cs.A.n_cols - 3 /* (3=2+1, since u_i.x.len=2) */],
            self.E_len,
        );

        let u_i = CommittedInstanceVar::<C1>::new_witness(cs.clone(), || {
            Ok(self.u_i.unwrap_or(u_dummy_native.clone()))
        })?;
        let U_i = CommittedInstanceVar::<C1>::new_witness(cs.clone(), || {
            Ok(self.U_i.unwrap_or(u_dummy_native.clone()))
        })?;
        // here (U_i1, W_i1) = NIFS.P( (U_i,W_i), (u_i,w_i))
        let U_i1 = CommittedInstanceVar::<C1>::new_input(cs.clone(), || {
            Ok(self.U_i1.unwrap_or(u_dummy_native.clone()))
        })?;
        let W_i1 = WitnessVar::<C1>::new_witness(cs.clone(), || {
            Ok(self.W_i1.unwrap_or(w_dummy_native.clone()))
        })?;

        // allocate the inputs for the check 6
        let kzg_c_W = FpVar::<CF1<C1>>::new_input(cs.clone(), || {
            Ok(self.kzg_c_W.unwrap_or_else(CF1::<C1>::zero))
        })?;
        let kzg_c_E = FpVar::<CF1<C1>>::new_input(cs.clone(), || {
            Ok(self.kzg_c_E.unwrap_or_else(CF1::<C1>::zero))
        })?;
        let _eval_W = FpVar::<CF1<C1>>::new_input(cs.clone(), || {
            Ok(self.eval_W.unwrap_or_else(CF1::<C1>::zero))
        })?;
        let _eval_E = FpVar::<CF1<C1>>::new_input(cs.clone(), || {
            Ok(self.eval_E.unwrap_or_else(CF1::<C1>::zero))
        })?;

        let crh_params = CRHParametersVar::<C1::ScalarField>::new_constant(
            cs.clone(),
            self.poseidon_config.clone(),
        )?;

        // 1. check RelaxedR1CS of U_{i+1}
        let z_U1: Vec<FpVar<CF1<C1>>> =
            [vec![U_i1.u.clone()], U_i1.x.to_vec(), W_i1.W.to_vec()].concat();
        RelaxedR1CSGadget::check_native(r1cs, W_i1.E.clone(), U_i1.u.clone(), z_U1)?;

        // 2. u_i.cmE==cm(0), u_i.u==1
        // Here zero is the x & y coordinates of the zero point affine representation.
        let zero = NonNativeUintVar::new_constant(cs.clone(), C1::BaseField::zero())?;
        u_i.cmE.x.enforce_equal_unaligned(&zero)?;
        u_i.cmE.y.enforce_equal_unaligned(&zero)?;
        (u_i.u.is_one()?).enforce_equal(&Boolean::TRUE)?;

        // 3.a u_i.x[0] == H(i, z_0, z_i, U_i)
        let (u_i_x, U_i_vec) =
            U_i.clone()
                .hash(&crh_params, i.clone(), z_0.clone(), z_i.clone())?;
        (u_i.x[0]).enforce_equal(&u_i_x)?;

        #[cfg(feature = "light-test")]
        println!("[WARNING]: Running with the 'light-test' feature, skipping the big part of the DeciderEthCircuit.\n           Only for testing purposes.");

        // The following two checks (and their respective allocations) are disabled for normal
        // tests since they take several millions of constraints and would take several minutes
        // (and RAM) to run the test. It is active by default, and not active only when
        // 'light-test' feature is used.
        #[cfg(not(feature = "light-test"))]
        {
            // imports here instead of at the top of the file, so we avoid having multiple
            // `#[cfg(not(test))]`
            use crate::commitment::pedersen::PedersenGadget;
            use crate::folding::circuits::cyclefold::{CycleFoldCommittedInstanceVar, CF_IO_LEN};
            use ark_r1cs_std::ToBitsGadget;

            let cf_u_dummy_native = CommittedInstance::<C2>::dummy(CF_IO_LEN);
            let w_dummy_native = Witness::<C2>::new(
                vec![C2::ScalarField::zero(); self.cf_r1cs.A.n_cols - 1 - self.cf_r1cs.l],
                self.cf_E_len,
            );
            let cf_U_i = CycleFoldCommittedInstanceVar::<C2, GC2>::new_witness(cs.clone(), || {
                Ok(self.cf_U_i.unwrap_or_else(|| cf_u_dummy_native.clone()))
            })?;
            let cf_W_i = CycleFoldWitnessVar::<C2>::new_witness(cs.clone(), || {
                Ok(self.cf_W_i.unwrap_or(w_dummy_native.clone()))
            })?;

            // 3.b u_i.x[1] == H(cf_U_i)
            let (cf_u_i_x, _) = cf_U_i.clone().hash(&crh_params)?;
            (u_i.x[1]).enforce_equal(&cf_u_i_x)?;

            // 4. check Pedersen commitments of cf_U_i.{cmE, cmW}
            let H = GC2::new_constant(cs.clone(), self.cf_pedersen_params.h)?;
            let G = Vec::<GC2>::new_constant(cs.clone(), self.cf_pedersen_params.generators)?;
            let cf_W_i_E_bits: Result<Vec<Vec<Boolean<CF1<C1>>>>, SynthesisError> =
                cf_W_i.E.iter().map(|E_i| E_i.to_bits_le()).collect();
            let cf_W_i_W_bits: Result<Vec<Vec<Boolean<CF1<C1>>>>, SynthesisError> =
                cf_W_i.W.iter().map(|W_i| W_i.to_bits_le()).collect();

            let computed_cmE = PedersenGadget::<C2, GC2>::commit(
                H.clone(),
                G.clone(),
                cf_W_i_E_bits?,
                cf_W_i.rE.to_bits_le()?,
            )?;
            cf_U_i.cmE.enforce_equal(&computed_cmE)?;
            let computed_cmW =
                PedersenGadget::<C2, GC2>::commit(H, G, cf_W_i_W_bits?, cf_W_i.rW.to_bits_le()?)?;
            cf_U_i.cmW.enforce_equal(&computed_cmW)?;

            let cf_r1cs =
                R1CSVar::<C1::BaseField, CF1<C1>, NonNativeUintVar<CF1<C1>>>::new_witness(
                    cs.clone(),
                    || Ok(self.cf_r1cs.clone()),
                )?;

            // 5. check RelaxedR1CS of cf_U_i
            let cf_z_U = [vec![cf_U_i.u.clone()], cf_U_i.x.to_vec(), cf_W_i.W.to_vec()].concat();
            RelaxedR1CSGadget::check_nonnative(cf_r1cs, cf_W_i.E, cf_U_i.u.clone(), cf_z_U)?;
        }

        // 6. check KZG challenges
        let (incircuit_c_W, incircuit_c_E) = KZGChallengesGadget::<C1>::get_challenges_gadget(
            cs.clone(),
            &self.poseidon_config,
            U_i1.clone(),
        )?;
        incircuit_c_W.enforce_equal(&kzg_c_W)?;
        incircuit_c_E.enforce_equal(&kzg_c_E)?;

        // Check 7 is temporary disabled due
        // https://github.com/privacy-scaling-explorations/sonobe/issues/80
        //
        // 7. check eval_W==p_W(c_W) and eval_E==p_E(c_E)
        // let incircuit_eval_W = evaluate_gadget::<CF1<C1>>(W_i1.W, incircuit_c_W)?;
        // let incircuit_eval_E = evaluate_gadget::<CF1<C1>>(W_i1.E, incircuit_c_E)?;
        // incircuit_eval_W.enforce_equal(&eval_W)?;
        // incircuit_eval_E.enforce_equal(&eval_E)?;

        // 8. compute the NIFS.V challenge and check that matches the one from the public input (so we
        // avoid the verifier computing it)
        let cmT =
            NonNativeAffineVar::new_input(cs.clone(), || Ok(self.cmT.unwrap_or_else(C1::zero)))?;
        let r_bits = ChallengeGadget::<C1>::get_challenge_gadget(
            cs.clone(),
            &self.poseidon_config,
            U_i_vec,
            u_i.clone(),
            cmT.clone(),
        )?;
        let r_Fr = Boolean::le_bits_to_fp_var(&r_bits)?;
        // check that the in-circuit computed r is equal to the inputted r
        let r =
            FpVar::<CF1<C1>>::new_input(cs.clone(), || Ok(self.r.unwrap_or_else(CF1::<C1>::zero)))?;
        r_Fr.enforce_equal(&r)?;

        Ok(())
    }
}

/// Interpolates the polynomial from the given vector, and then returns it's evaluation at the
/// given point.
#[allow(unused)] // unused while check 7 is disabled
fn evaluate_gadget<F: PrimeField>(
    v: Vec<FpVar<F>>,
    point: FpVar<F>,
) -> Result<FpVar<F>, SynthesisError> {
    if !v.len().is_power_of_two() {
        return Err(SynthesisError::Unsatisfiable);
    }
    let n = v.len() as u64;
    let gen = F::get_root_of_unity(n).unwrap();
    let domain = Radix2DomainVar::new(gen, log2(v.len()) as u64, FpVar::one()).unwrap();

    let evaluations_var = EvaluationsVar::from_vec_and_domain(v, domain, true);
    evaluations_var.interpolate_and_evaluate(&point)
}

/// Gadget that computes the KZG challenges, also offers the rust native implementation compatible
/// with the gadget.
pub struct KZGChallengesGadget<C: CurveGroup> {
    _c: PhantomData<C>,
}
#[allow(clippy::type_complexity)]
impl<C> KZGChallengesGadget<C>
where
    C: CurveGroup,
    C::ScalarField: PrimeField,
    <C as CurveGroup>::BaseField: PrimeField,
    C::ScalarField: Absorb,
{
    pub fn get_challenges_native(
        poseidon_config: &PoseidonConfig<C::ScalarField>,
        U_i: CommittedInstance<C>,
    ) -> Result<(C::ScalarField, C::ScalarField), Error> {
        let (cmE_x_limbs, cmE_y_limbs) = nonnative_affine_to_field_elements(U_i.cmE)?;
        let (cmW_x_limbs, cmW_y_limbs) = nonnative_affine_to_field_elements(U_i.cmW)?;

        let transcript = &mut PoseidonTranscript::<C>::new(poseidon_config);
        // compute the KZG challenges, which are computed in-circuit and checked that it matches
        // the inputted one
        transcript.absorb_vec(&cmW_x_limbs);
        transcript.absorb_vec(&cmW_y_limbs);
        let challenge_W = transcript.get_challenge();
        transcript.absorb_vec(&cmE_x_limbs);
        transcript.absorb_vec(&cmE_y_limbs);
        let challenge_E = transcript.get_challenge();

        Ok((challenge_W, challenge_E))
    }
    // compatible with the native get_challenges_native
    pub fn get_challenges_gadget(
        cs: ConstraintSystemRef<C::ScalarField>,
        poseidon_config: &PoseidonConfig<C::ScalarField>,
        U_i: CommittedInstanceVar<C>,
    ) -> Result<(FpVar<C::ScalarField>, FpVar<C::ScalarField>), SynthesisError> {
        let mut transcript =
            PoseidonTranscriptVar::<CF1<C>>::new(cs.clone(), &poseidon_config.clone());

        transcript.absorb_vec(&U_i.cmW.to_constraint_field()?[..])?;
        let challenge_W = transcript.get_challenge()?;

        transcript.absorb_vec(&U_i.cmE.to_constraint_field()?[..])?;
        let challenge_E = transcript.get_challenge()?;

        Ok((challenge_W, challenge_E))
    }
}

#[cfg(test)]
pub mod tests {
    use ark_crypto_primitives::crh::{
        sha256::{
            constraints::{Sha256Gadget, UnitVar},
            Sha256,
        },
        CRHScheme, CRHSchemeGadget,
    };
    use ark_pallas::{constraints::GVar, Fq, Fr, Projective};
    use ark_r1cs_std::bits::uint8::UInt8;
    use ark_relations::r1cs::ConstraintSystem;
    use ark_std::{One, UniformRand};
    use ark_vesta::{constraints::GVar as GVar2, Projective as Projective2};

    use super::*;
    use crate::ccs::r1cs::tests::{get_test_r1cs, get_test_z};
    use crate::ccs::r1cs::{extract_r1cs, extract_w_x};
    use crate::commitment::pedersen::Pedersen;
    use crate::folding::nova::{get_cs_params_len, ProverParams, VerifierParams};
    use crate::frontend::tests::{CubicFCircuit, CustomFCircuit, WrapperCircuit};
    use crate::transcript::poseidon::poseidon_canonical_config;
    use crate::FoldingScheme;

    #[test]
    fn test_relaxed_r1cs_small_gadget_handcrafted() {
        let r1cs: R1CS<Fr> = get_test_r1cs();
        let rel_r1cs = r1cs.clone().relax();
        let z = get_test_z(3);

        let cs = ConstraintSystem::<Fr>::new_ref();

        let zVar = Vec::<FpVar<Fr>>::new_witness(cs.clone(), || Ok(z)).unwrap();
        let EVar = Vec::<FpVar<Fr>>::new_witness(cs.clone(), || Ok(rel_r1cs.E)).unwrap();
        let uVar = FpVar::<Fr>::new_witness(cs.clone(), || Ok(rel_r1cs.u)).unwrap();
        let r1csVar = R1CSVar::<Fr, Fr, FpVar<Fr>>::new_witness(cs.clone(), || Ok(r1cs)).unwrap();

        RelaxedR1CSGadget::check_native(r1csVar, EVar, uVar, zVar).unwrap();
        assert!(cs.is_satisfied().unwrap());
    }

    // gets as input a circuit that implements the ConstraintSynthesizer trait, and that has been
    // initialized.
    fn test_relaxed_r1cs_gadget<CS: ConstraintSynthesizer<Fr>>(circuit: CS) {
        let cs = ConstraintSystem::<Fr>::new_ref();

        circuit.generate_constraints(cs.clone()).unwrap();
        cs.finalize();
        assert!(cs.is_satisfied().unwrap());

        let cs = cs.into_inner().unwrap();

        let r1cs = extract_r1cs::<Fr>(&cs);
        let (w, x) = extract_w_x::<Fr>(&cs);
        let z = [vec![Fr::one()], x, w].concat();
        r1cs.check_relation(&z).unwrap();

        let relaxed_r1cs = r1cs.clone().relax();
        relaxed_r1cs.check_relation(&z).unwrap();

        // set new CS for the circuit that checks the RelaxedR1CS of our original circuit
        let cs = ConstraintSystem::<Fr>::new_ref();
        // prepare the inputs for our circuit
        let zVar = Vec::<FpVar<Fr>>::new_witness(cs.clone(), || Ok(z)).unwrap();
        let EVar = Vec::<FpVar<Fr>>::new_witness(cs.clone(), || Ok(relaxed_r1cs.E)).unwrap();
        let uVar = FpVar::<Fr>::new_witness(cs.clone(), || Ok(relaxed_r1cs.u)).unwrap();
        let r1csVar = R1CSVar::<Fr, Fr, FpVar<Fr>>::new_witness(cs.clone(), || Ok(r1cs)).unwrap();

        RelaxedR1CSGadget::check_native(r1csVar, EVar, uVar, zVar).unwrap();
        assert!(cs.is_satisfied().unwrap());
    }

    #[test]
    fn test_relaxed_r1cs_small_gadget_arkworks() {
        let z_i = vec![Fr::from(3_u32)];
        let cubic_circuit = CubicFCircuit::<Fr>::new(()).unwrap();
        let circuit = WrapperCircuit::<Fr, CubicFCircuit<Fr>> {
            FC: cubic_circuit,
            z_i: Some(z_i.clone()),
            z_i1: Some(cubic_circuit.step_native(0, z_i, vec![]).unwrap()),
        };

        test_relaxed_r1cs_gadget(circuit);
    }

    struct Sha256TestCircuit<F: PrimeField> {
        _f: PhantomData<F>,
        pub x: Vec<u8>,
        pub y: Vec<u8>,
    }
    impl<F: PrimeField> ConstraintSynthesizer<F> for Sha256TestCircuit<F> {
        fn generate_constraints(self, cs: ConstraintSystemRef<F>) -> Result<(), SynthesisError> {
            let x = Vec::<UInt8<F>>::new_witness(cs.clone(), || Ok(self.x))?;
            let y = Vec::<UInt8<F>>::new_input(cs.clone(), || Ok(self.y))?;

            let unitVar = UnitVar::default();
            let comp_y = <Sha256Gadget<F> as CRHSchemeGadget<Sha256, F>>::evaluate(&unitVar, &x)?;
            comp_y.0.enforce_equal(&y)?;
            Ok(())
        }
    }
    #[test]
    fn test_relaxed_r1cs_medium_gadget_arkworks() {
        let x = Fr::from(5_u32).into_bigint().to_bytes_le();
        let y = <Sha256 as CRHScheme>::evaluate(&(), x.clone()).unwrap();

        let circuit = Sha256TestCircuit::<Fr> {
            _f: PhantomData,
            x,
            y,
        };
        test_relaxed_r1cs_gadget(circuit);
    }

    #[test]
    fn test_relaxed_r1cs_custom_circuit() {
        let n_constraints = 10_000;
        let custom_circuit = CustomFCircuit::<Fr>::new(n_constraints).unwrap();
        let z_i = vec![Fr::from(5_u32)];
        let circuit = WrapperCircuit::<Fr, CustomFCircuit<Fr>> {
            FC: custom_circuit,
            z_i: Some(z_i.clone()),
            z_i1: Some(custom_circuit.step_native(0, z_i, vec![]).unwrap()),
        };
        test_relaxed_r1cs_gadget(circuit);
    }

    #[test]
    fn test_relaxed_r1cs_nonnative_circuit() {
        let cs = ConstraintSystem::<Fq>::new_ref();
        // in practice we would use CycleFoldCircuit, but is a very big circuit (when computed
        // non-natively inside the RelaxedR1CS circuit), so in order to have a short test we use a
        // custom circuit.
        let custom_circuit = CustomFCircuit::<Fq>::new(10).unwrap();
        let z_i = vec![Fq::from(5_u32)];
        let circuit = WrapperCircuit::<Fq, CustomFCircuit<Fq>> {
            FC: custom_circuit,
            z_i: Some(z_i.clone()),
            z_i1: Some(custom_circuit.step_native(0, z_i, vec![]).unwrap()),
        };
        circuit.generate_constraints(cs.clone()).unwrap();
        cs.finalize();
        let cs = cs.into_inner().unwrap();
        let r1cs = extract_r1cs::<Fq>(&cs);
        let (w, x) = extract_w_x::<Fq>(&cs);
        let z = [vec![Fq::one()], x, w].concat();

        let relaxed_r1cs = r1cs.clone().relax();

        // natively
        let cs = ConstraintSystem::<Fq>::new_ref();
        let zVar = Vec::<FpVar<Fq>>::new_witness(cs.clone(), || Ok(z.clone())).unwrap();
        let EVar =
            Vec::<FpVar<Fq>>::new_witness(cs.clone(), || Ok(relaxed_r1cs.clone().E)).unwrap();
        let uVar = FpVar::<Fq>::new_witness(cs.clone(), || Ok(relaxed_r1cs.u)).unwrap();
        let r1csVar =
            R1CSVar::<Fq, Fq, FpVar<Fq>>::new_witness(cs.clone(), || Ok(r1cs.clone())).unwrap();
        RelaxedR1CSGadget::check_native(r1csVar, EVar, uVar, zVar).unwrap();

        // non-natively
        let cs = ConstraintSystem::<Fr>::new_ref();
        let zVar = Vec::new_witness(cs.clone(), || Ok(z)).unwrap();
        let EVar = Vec::new_witness(cs.clone(), || Ok(relaxed_r1cs.E)).unwrap();
        let uVar = NonNativeUintVar::<Fr>::new_witness(cs.clone(), || Ok(relaxed_r1cs.u)).unwrap();
        let r1csVar =
            R1CSVar::<Fq, Fr, NonNativeUintVar<Fr>>::new_witness(cs.clone(), || Ok(r1cs)).unwrap();
        RelaxedR1CSGadget::check_nonnative(r1csVar, EVar, uVar, zVar).unwrap();
    }

    #[test]
    fn test_decider_circuit() {
        let mut rng = ark_std::test_rng();
        let poseidon_config = poseidon_canonical_config::<Fr>();

        let F_circuit = CubicFCircuit::<Fr>::new(()).unwrap();
        let z_0 = vec![Fr::from(3_u32)];

        // get the CS & CF_CS len
        let (cs_len, cf_cs_len) =
            get_cs_params_len::<Projective, GVar, Projective2, GVar2, CubicFCircuit<Fr>>(
                &poseidon_config,
                F_circuit,
            )
            .unwrap();
        let (pedersen_params, _) = Pedersen::<Projective>::setup(&mut rng, cs_len).unwrap();
        let (cf_pedersen_params, _) = Pedersen::<Projective2>::setup(&mut rng, cf_cs_len).unwrap();

        let prover_params =
            ProverParams::<Projective, Projective2, Pedersen<Projective>, Pedersen<Projective2>> {
                poseidon_config: poseidon_config.clone(),
                cs_pp: pedersen_params.clone(),
                cf_cs_pp: cf_pedersen_params.clone(),
            };

        type N = Nova<
            Projective,
            GVar,
            Projective2,
            GVar2,
            CubicFCircuit<Fr>,
            Pedersen<Projective>,
            Pedersen<Projective2>,
        >;

        // generate a Nova instance and do a step of it
        let mut nova = N::init(&prover_params, F_circuit, z_0.clone()).unwrap();
        nova.prove_step(&mut rng, vec![]).unwrap();
        let ivc_v = nova.clone();
        let verifier_params = VerifierParams::<
            Projective,
            Projective2,
            Pedersen<Projective>,
            Pedersen<Projective2>,
        > {
            poseidon_config: poseidon_config.clone(),
            r1cs: ivc_v.clone().r1cs,
            cf_r1cs: ivc_v.clone().cf_r1cs,
            cs_vp: pedersen_params,
            cf_cs_vp: cf_pedersen_params,
        };
        let (running_instance, incoming_instance, cyclefold_instance) = ivc_v.instances();
        N::verify(
            verifier_params,
            z_0,
            ivc_v.z_i,
            Fr::one(),
            running_instance,
            incoming_instance,
            cyclefold_instance,
        )
        .unwrap();

        // load the DeciderEthCircuit from the generated Nova instance
        let decider_circuit = DeciderEthCircuit::<
            Projective,
            GVar,
            Projective2,
            GVar2,
            Pedersen<Projective>,
            Pedersen<Projective2>,
        >::from_nova(nova)
        .unwrap();

        let cs = ConstraintSystem::<Fr>::new_ref();

        // generate the constraints and check that are satisfied by the inputs
        decider_circuit.generate_constraints(cs.clone()).unwrap();
        assert!(cs.is_satisfied().unwrap());
    }

    // checks that the gadget and native implementations of the challenge computation match
    #[test]
    fn test_kzg_challenge_gadget() {
        let mut rng = ark_std::test_rng();
        let poseidon_config = poseidon_canonical_config::<Fr>();

        let U_i = CommittedInstance::<Projective> {
            cmE: Projective::rand(&mut rng),
            u: Fr::rand(&mut rng),
            cmW: Projective::rand(&mut rng),
            x: vec![Fr::rand(&mut rng); 1],
        };

        // compute the challenge natively
        let (challenge_W, challenge_E) =
            KZGChallengesGadget::<Projective>::get_challenges_native(&poseidon_config, U_i.clone())
                .unwrap();

        let cs = ConstraintSystem::<Fr>::new_ref();
        let U_iVar =
            CommittedInstanceVar::<Projective>::new_witness(cs.clone(), || Ok(U_i.clone()))
                .unwrap();

        let (challenge_W_Var, challenge_E_Var) =
            KZGChallengesGadget::<Projective>::get_challenges_gadget(
                cs.clone(),
                &poseidon_config,
                U_iVar,
            )
            .unwrap();
        assert!(cs.is_satisfied().unwrap());

        // check that the natively computed and in-circuit computed hashes match
        use ark_r1cs_std::R1CSVar;
        assert_eq!(challenge_W_Var.value().unwrap(), challenge_W);
        assert_eq!(challenge_E_Var.value().unwrap(), challenge_E);
    }

    // The test test_polynomial_interpolation is temporary disabled due
    // https://github.com/privacy-scaling-explorations/sonobe/issues/80
    // for n<=11 it will work, but for n>11 it will fail with stack overflow.
    #[ignore]
    #[test]
    fn test_polynomial_interpolation() {
        let mut rng = ark_std::test_rng();
        let n = 12;
        let l = 1 << n;

        let v: Vec<Fr> = std::iter::repeat_with(|| Fr::rand(&mut rng))
            .take(l)
            .collect();
        let challenge = Fr::rand(&mut rng);

        use ark_poly::Polynomial;
        let polynomial = poly_from_vec(v.to_vec()).unwrap();
        let eval = polynomial.evaluate(&challenge);

        let cs = ConstraintSystem::<Fr>::new_ref();
        let vVar = Vec::<FpVar<Fr>>::new_witness(cs.clone(), || Ok(v)).unwrap();
        let challengeVar = FpVar::<Fr>::new_witness(cs.clone(), || Ok(challenge)).unwrap();

        let evalVar = evaluate_gadget::<Fr>(vVar, challengeVar).unwrap();

        use ark_r1cs_std::R1CSVar;
        assert_eq!(evalVar.value().unwrap(), eval);
        assert!(cs.is_satisfied().unwrap());
    }
}
