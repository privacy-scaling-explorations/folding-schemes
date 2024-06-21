/// Contains [CycleFold](https://eprint.iacr.org/2023/1192.pdf) related circuits and functions that
/// are shared across the different folding schemes
use ark_crypto_primitives::{
    crh::{
        poseidon::constraints::{CRHGadget, CRHParametersVar},
        CRHSchemeGadget,
    },
    sponge::{
        constraints::CryptographicSpongeVar,
        poseidon::{constraints::PoseidonSpongeVar, PoseidonConfig, PoseidonSponge},
        Absorb, CryptographicSponge,
    },
};
use ark_ec::{AffineRepr, CurveGroup, Group};
use ark_ff::{BigInteger, Field, PrimeField, ToConstraintField};
use ark_r1cs_std::{
    alloc::{AllocVar, AllocationMode},
    boolean::Boolean,
    eq::EqGadget,
    fields::{fp::FpVar, FieldVar},
    groups::GroupOpsBounds,
    prelude::CurveVar,
    ToConstraintFieldGadget,
};
use ark_relations::r1cs::{
    ConstraintSynthesizer, ConstraintSystem, ConstraintSystemRef, Namespace, SynthesisError,
};
use ark_std::fmt::Debug;
use ark_std::{One, Zero};
use core::{borrow::Borrow, marker::PhantomData};

use super::{nonnative::uint::NonNativeUintVar, CF2};
use crate::ccs::r1cs::{extract_w_x, R1CS};
use crate::commitment::CommitmentScheme;
use crate::constants::N_BITS_RO;
use crate::folding::nova::{nifs::NIFS, CommittedInstance, Witness};
use crate::frontend::FCircuit;
use crate::Error;

/// Public inputs length for the CycleFoldCircuit: |[r, p1.x,y, p2.x,y, p3.x,y]|
pub(crate) const CF_IO_LEN: usize = 7;

/// CycleFoldCommittedInstanceVar is the CycleFold CommittedInstance representation in the Nova
/// circuit.
#[derive(Debug, Clone)]
pub struct CycleFoldCommittedInstanceVar<C: CurveGroup, GC: CurveVar<C, CF2<C>>>
where
    for<'a> &'a GC: GroupOpsBounds<'a, C, GC>,
{
    pub cmE: GC,
    pub u: NonNativeUintVar<CF2<C>>,
    pub cmW: GC,
    pub x: Vec<NonNativeUintVar<CF2<C>>>,
}
impl<C, GC> AllocVar<CommittedInstance<C>, CF2<C>> for CycleFoldCommittedInstanceVar<C, GC>
where
    C: CurveGroup,
    GC: CurveVar<C, CF2<C>>,
    <C as ark_ec::CurveGroup>::BaseField: ark_ff::PrimeField,
    for<'a> &'a GC: GroupOpsBounds<'a, C, GC>,
{
    fn new_variable<T: Borrow<CommittedInstance<C>>>(
        cs: impl Into<Namespace<CF2<C>>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        f().and_then(|val| {
            let cs = cs.into();

            let cmE = GC::new_variable(cs.clone(), || Ok(val.borrow().cmE), mode)?;
            let cmW = GC::new_variable(cs.clone(), || Ok(val.borrow().cmW), mode)?;
            let u = NonNativeUintVar::new_variable(cs.clone(), || Ok(val.borrow().u), mode)?;
            let x = Vec::new_variable(cs.clone(), || Ok(val.borrow().x.clone()), mode)?;

            Ok(Self { cmE, u, cmW, x })
        })
    }
}

impl<C, GC> ToConstraintFieldGadget<CF2<C>> for CycleFoldCommittedInstanceVar<C, GC>
where
    C: CurveGroup,
    GC: CurveVar<C, CF2<C>> + ToConstraintFieldGadget<CF2<C>>,
    <C as ark_ec::CurveGroup>::BaseField: ark_ff::PrimeField + Absorb,
    for<'a> &'a GC: GroupOpsBounds<'a, C, GC>,
{
    /// Extracts the underlying field elements from `CycleFoldCommittedInstanceVar`, in the order
    /// of `u`, `x`, `cmE.x`, `cmE.y`, `cmW.x`, `cmW.y`, `cmE.is_inf || cmW.is_inf` (|| is for
    /// concat).
    fn to_constraint_field(&self) -> Result<Vec<FpVar<CF2<C>>>, SynthesisError> {
        let mut cmE_elems = self.cmE.to_constraint_field()?;
        let mut cmW_elems = self.cmW.to_constraint_field()?;

        let cmE_is_inf = cmE_elems.pop().unwrap();
        let cmW_is_inf = cmW_elems.pop().unwrap();
        // Concatenate `cmE_is_inf` and `cmW_is_inf` to save constraints for CRHGadget::evaluate
        let is_inf = cmE_is_inf.double()? + cmW_is_inf;

        Ok([
            self.u.to_constraint_field()?,
            self.x
                .iter()
                .map(|i| i.to_constraint_field())
                .collect::<Result<Vec<_>, _>>()?
                .concat(),
            cmE_elems,
            cmW_elems,
            vec![is_inf],
        ]
        .concat())
    }
}

impl<C, GC> CycleFoldCommittedInstanceVar<C, GC>
where
    C: CurveGroup,
    GC: CurveVar<C, CF2<C>> + ToConstraintFieldGadget<CF2<C>>,
    <C as ark_ec::CurveGroup>::BaseField: ark_ff::PrimeField + Absorb,
    for<'a> &'a GC: GroupOpsBounds<'a, C, GC>,
{
    /// hash implements the committed instance hash compatible with the native implementation from
    /// CommittedInstance.hash_cyclefold. Returns `H(U_i)`, where `U` is the `CommittedInstance`
    /// for CycleFold. Additionally it returns the vector of the field elements from the self
    /// parameters, so they can be reused in other gadgets avoiding recalculating (reconstraining)
    /// them.
    #[allow(clippy::type_complexity)]
    pub fn hash(
        self,
        crh_params: &CRHParametersVar<CF2<C>>,
    ) -> Result<(FpVar<CF2<C>>, Vec<FpVar<CF2<C>>>), SynthesisError> {
        let U_vec = self.to_constraint_field()?;
        Ok((CRHGadget::evaluate(crh_params, &U_vec)?, U_vec))
    }
}

/// CommittedInstanceInCycleFoldVar represents the Nova CommittedInstance in the CycleFold circuit,
/// where the commitments to E and W (cmW and cmW) from the CommittedInstance on the E2,
/// represented as native points, which are folded on the auxiliary curve constraints field (E2::Fr
/// = E1::Fq).
#[derive(Debug, Clone)]
pub struct CommittedInstanceInCycleFoldVar<C: CurveGroup, GC: CurveVar<C, CF2<C>>>
where
    for<'a> &'a GC: GroupOpsBounds<'a, C, GC>,
{
    _c: PhantomData<C>,
    pub cmE: GC,
    pub cmW: GC,
}

impl<C, GC> AllocVar<CommittedInstance<C>, CF2<C>> for CommittedInstanceInCycleFoldVar<C, GC>
where
    C: CurveGroup,
    GC: CurveVar<C, CF2<C>>,
    for<'a> &'a GC: GroupOpsBounds<'a, C, GC>,
{
    fn new_variable<T: Borrow<CommittedInstance<C>>>(
        cs: impl Into<Namespace<CF2<C>>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        f().and_then(|val| {
            let cs = cs.into();

            let cmE = GC::new_variable(cs.clone(), || Ok(val.borrow().cmE), mode)?;
            let cmW = GC::new_variable(cs.clone(), || Ok(val.borrow().cmW), mode)?;

            Ok(Self {
                _c: PhantomData,
                cmE,
                cmW,
            })
        })
    }
}

/// This is the gadget used in the AugmentedFCircuit to verify the CycleFold instances folding,
/// which checks the correct RLC of u,x,cmE,cmW (hence the name containing 'Full', since it checks
/// all the RLC values, not only the native ones). It assumes that ci2.cmE=0, ci2.u=1.
pub struct NIFSFullGadget<C: CurveGroup, GC: CurveVar<C, CF2<C>>> {
    _c: PhantomData<C>,
    _gc: PhantomData<GC>,
}

impl<C: CurveGroup, GC: CurveVar<C, CF2<C>>> NIFSFullGadget<C, GC>
where
    C: CurveGroup,
    GC: CurveVar<C, CF2<C>>,
    <C as ark_ec::CurveGroup>::BaseField: ark_ff::PrimeField,
    for<'a> &'a GC: GroupOpsBounds<'a, C, GC>,
{
    pub fn fold_committed_instance(
        // assumes that r_bits is equal to r_nonnat just that in a different format
        r_bits: Vec<Boolean<CF2<C>>>,
        r_nonnat: NonNativeUintVar<CF2<C>>,
        cmT: GC,
        ci1: CycleFoldCommittedInstanceVar<C, GC>,
        // ci2 is assumed to be always with cmE=0, u=1 (checks done previous to this method)
        ci2: CycleFoldCommittedInstanceVar<C, GC>,
    ) -> Result<CycleFoldCommittedInstanceVar<C, GC>, SynthesisError> {
        Ok(CycleFoldCommittedInstanceVar {
            cmE: cmT.scalar_mul_le(r_bits.iter())? + ci1.cmE,
            cmW: ci1.cmW + ci2.cmW.scalar_mul_le(r_bits.iter())?,
            u: ci1.u.add_no_align(&r_nonnat).modulo::<C::ScalarField>()?,
            x: ci1
                .x
                .iter()
                .zip(ci2.x)
                .map(|(a, b)| {
                    a.add_no_align(&r_nonnat.mul_no_align(&b)?)
                        .modulo::<C::ScalarField>()
                })
                .collect::<Result<Vec<_>, _>>()?,
        })
    }

    pub fn verify(
        // assumes that r_bits is equal to r_nonnat just that in a different format
        r_bits: Vec<Boolean<CF2<C>>>,
        r_nonnat: NonNativeUintVar<CF2<C>>,
        cmT: GC,
        ci1: CycleFoldCommittedInstanceVar<C, GC>,
        // ci2 is assumed to be always with cmE=0, u=1 (checks done previous to this method)
        ci2: CycleFoldCommittedInstanceVar<C, GC>,
        ci3: CycleFoldCommittedInstanceVar<C, GC>,
    ) -> Result<(), SynthesisError> {
        let ci = Self::fold_committed_instance(r_bits, r_nonnat, cmT, ci1, ci2)?;

        ci.cmE.enforce_equal(&ci3.cmE)?;
        ci.u.enforce_equal_unaligned(&ci3.u)?;
        ci.cmW.enforce_equal(&ci3.cmW)?;
        for (x, y) in ci.x.iter().zip(ci3.x.iter()) {
            x.enforce_equal_unaligned(y)?;
        }

        Ok(())
    }
}

/// CycleFoldChallengeGadget computes the RO challenge used for the CycleFold instances NIFS, it contains a
/// rust-native and a in-circuit compatible versions.
pub struct CycleFoldChallengeGadget<C: CurveGroup, GC: CurveVar<C, CF2<C>>> {
    _c: PhantomData<C>, // Nova's Curve2, the one used for the CycleFold circuit
    _gc: PhantomData<GC>,
}
impl<C, GC> CycleFoldChallengeGadget<C, GC>
where
    C: CurveGroup,
    GC: CurveVar<C, CF2<C>> + ToConstraintFieldGadget<CF2<C>>,
    <C as CurveGroup>::BaseField: PrimeField,
    <C as CurveGroup>::BaseField: Absorb,
    for<'a> &'a GC: GroupOpsBounds<'a, C, GC>,
{
    pub fn get_challenge_native(
        poseidon_config: &PoseidonConfig<C::BaseField>,
        U_i: CommittedInstance<C>,
        u_i: CommittedInstance<C>,
        cmT: C,
    ) -> Result<Vec<bool>, Error> {
        let mut sponge = PoseidonSponge::<C::BaseField>::new(poseidon_config);

        let mut U_vec = U_i.to_field_elements().unwrap();
        let mut u_vec = u_i.to_field_elements().unwrap();
        let (cmT_x, cmT_y, cmT_is_inf) = match cmT.into_affine().xy() {
            Some((&x, &y)) => (x, y, C::BaseField::zero()),
            None => (
                C::BaseField::zero(),
                C::BaseField::zero(),
                C::BaseField::one(),
            ),
        };

        let U_cm_is_inf = U_vec.pop().unwrap();
        let u_cm_is_inf = u_vec.pop().unwrap();

        // Concatenate `U_i.cmE_is_inf`, `U_i.cmW_is_inf`, `u_i.cmE_is_inf`, `u_i.cmW_is_inf`, `cmT_is_inf`
        // to save constraints for sponge.squeeze_bits in the corresponding circuit
        let is_inf = U_cm_is_inf * CF2::<C>::from(8u8) + u_cm_is_inf.double() + cmT_is_inf;

        let input = [U_vec, u_vec, vec![cmT_x, cmT_y, is_inf]].concat();
        sponge.absorb(&input);
        let bits = sponge.squeeze_bits(N_BITS_RO);
        Ok(bits)
    }

    // compatible with the native get_challenge_native
    pub fn get_challenge_gadget(
        cs: ConstraintSystemRef<C::BaseField>,
        poseidon_config: &PoseidonConfig<C::BaseField>,
        mut U_i_vec: Vec<FpVar<C::BaseField>>,
        u_i: CycleFoldCommittedInstanceVar<C, GC>,
        cmT: GC,
    ) -> Result<Vec<Boolean<C::BaseField>>, SynthesisError> {
        let mut sponge = PoseidonSpongeVar::<C::BaseField>::new(cs, poseidon_config);

        let mut u_i_vec = u_i.to_constraint_field()?;
        let mut cmT_vec = cmT.to_constraint_field()?;

        let U_cm_is_inf = U_i_vec.pop().unwrap();
        let u_cm_is_inf = u_i_vec.pop().unwrap();
        let cmT_is_inf = cmT_vec.pop().unwrap();

        // Concatenate `U_i.cmE_is_inf`, `U_i.cmW_is_inf`, `u_i.cmE_is_inf`, `u_i.cmW_is_inf`, `cmT_is_inf`
        // to save constraints for sponge.squeeze_bits
        let is_inf = U_cm_is_inf * CF2::<C>::from(8u8) + u_cm_is_inf.double()? + cmT_is_inf;

        let input = [U_i_vec, u_i_vec, cmT_vec, vec![is_inf]].concat();
        sponge.absorb(&input)?;
        let bits = sponge.squeeze_bits(N_BITS_RO)?;
        Ok(bits)
    }
}

/// CycleFoldCircuit contains the constraints that check the correct fold of the committed
/// instances from Curve1. Namely, it checks the random linear combinations of the elliptic curve
/// (Curve1) points of u_i, U_i leading to U_{i+1}
#[derive(Debug, Clone)]
pub struct CycleFoldCircuit<C: CurveGroup, GC: CurveVar<C, CF2<C>>> {
    pub _gc: PhantomData<GC>,
    pub r_bits: Option<Vec<bool>>,
    pub p1: Option<C>,
    pub p2: Option<C>,
    pub x: Option<Vec<CF2<C>>>, // public inputs (cf_u_{i+1}.x)
}
impl<C: CurveGroup, GC: CurveVar<C, CF2<C>>> CycleFoldCircuit<C, GC> {
    pub fn empty() -> Self {
        Self {
            _gc: PhantomData,
            r_bits: None,
            p1: None,
            p2: None,
            x: None,
        }
    }
}
impl<C, GC> ConstraintSynthesizer<CF2<C>> for CycleFoldCircuit<C, GC>
where
    C: CurveGroup,
    GC: CurveVar<C, CF2<C>> + ToConstraintFieldGadget<CF2<C>>,
    <C as ark_ec::CurveGroup>::BaseField: ark_ff::PrimeField,
    for<'a> &'a GC: GroupOpsBounds<'a, C, GC>,
{
    fn generate_constraints(self, cs: ConstraintSystemRef<CF2<C>>) -> Result<(), SynthesisError> {
        let r_bits: Vec<Boolean<CF2<C>>> = Vec::new_witness(cs.clone(), || {
            Ok(self.r_bits.unwrap_or(vec![false; N_BITS_RO]))
        })?;
        let p1 = GC::new_witness(cs.clone(), || Ok(self.p1.unwrap_or(C::zero())))?;
        let p2 = GC::new_witness(cs.clone(), || Ok(self.p2.unwrap_or(C::zero())))?;
        // Fold the original Nova instances natively in CycleFold
        // For the cmW we're computing: U_i1.cmW = U_i.cmW + r * u_i.cmW
        // For the cmE we're computing: U_i1.cmE = U_i.cmE + r * cmT + r^2 * u_i.cmE, where u_i.cmE
        // is assumed to be 0, so, U_i1.cmE = U_i.cmE + r * cmT
        let p3 = &p1 + p2.scalar_mul_le(r_bits.iter())?;

        let x = Vec::<FpVar<CF2<C>>>::new_input(cs.clone(), || {
            Ok(self.x.unwrap_or(vec![CF2::<C>::zero(); CF_IO_LEN]))
        })?;
        #[cfg(test)]
        assert_eq!(x.len(), CF_IO_LEN); // non-constrained sanity check

        // check that the points coordinates are placed as the public input x: x == [r, p1, p2, p3]
        let r: FpVar<CF2<C>> = Boolean::le_bits_to_fp_var(&r_bits)?;
        let points_coords: Vec<FpVar<CF2<C>>> = [
            vec![r],
            p1.to_constraint_field()?[..2].to_vec(),
            p2.to_constraint_field()?[..2].to_vec(),
            p3.to_constraint_field()?[..2].to_vec(),
        ]
        .concat();
        points_coords.enforce_equal(&x)?;

        Ok(())
    }
}

/// Folds the given cyclefold circuit and its instances. This method is isolated from any folding
/// scheme struct because it is used both by Nova & HyperNova's CycleFold.
#[allow(clippy::type_complexity)]
pub fn fold_cyclefold_circuit<C1, GC1, C2, GC2, FC, CS1, CS2>(
    poseidon_config: &PoseidonConfig<C1::ScalarField>,
    cf_r1cs: R1CS<C2::ScalarField>,
    cf_cs_params: CS2::ProverParams,
    cf_W_i: Witness<C2>,           // witness of the running instance
    cf_U_i: CommittedInstance<C2>, // running instance
    cf_u_i_x: Vec<C2::ScalarField>,
    cf_circuit: CycleFoldCircuit<C1, GC1>,
) -> Result<
    (
        Witness<C2>,
        CommittedInstance<C2>, // u_i
        Witness<C2>,           // W_i1
        CommittedInstance<C2>, // U_i1
        C2,                    // cmT
        C2::ScalarField,       // r_Fq
    ),
    Error,
>
where
    C1: CurveGroup,
    GC1: CurveVar<C1, CF2<C1>> + ToConstraintFieldGadget<CF2<C1>>,
    C2: CurveGroup,
    GC2: CurveVar<C2, CF2<C2>> + ToConstraintFieldGadget<CF2<C2>>,
    FC: FCircuit<C1::ScalarField>,
    CS1: CommitmentScheme<C1>,
    CS2: CommitmentScheme<C2>,
    <C1 as CurveGroup>::BaseField: PrimeField,
    <C2 as CurveGroup>::BaseField: PrimeField,
    <C1 as Group>::ScalarField: Absorb,
    <C2 as Group>::ScalarField: Absorb,
    C1: CurveGroup<BaseField = C2::ScalarField, ScalarField = C2::BaseField>,
    for<'a> &'a GC1: GroupOpsBounds<'a, C1, GC1>,
    for<'a> &'a GC2: GroupOpsBounds<'a, C2, GC2>,
{
    let cs2 = ConstraintSystem::<C1::BaseField>::new_ref();
    cf_circuit.generate_constraints(cs2.clone())?;

    let cs2 = cs2.into_inner().ok_or(Error::NoInnerConstraintSystem)?;
    let (cf_w_i, cf_x_i) = extract_w_x::<C1::BaseField>(&cs2);
    if cf_x_i != cf_u_i_x {
        return Err(Error::NotEqual);
    }

    #[cfg(test)]
    assert_eq!(cf_x_i.len(), CF_IO_LEN);

    // fold cyclefold instances
    let cf_w_i = Witness::<C2>::new(cf_w_i.clone(), cf_r1cs.A.n_rows);
    let cf_u_i: CommittedInstance<C2> = cf_w_i.commit::<CS2>(&cf_cs_params, cf_x_i.clone())?;

    // compute T* and cmT* for CycleFoldCircuit
    let (cf_T, cf_cmT) = NIFS::<C2, CS2>::compute_cyclefold_cmT(
        &cf_cs_params,
        &cf_r1cs,
        &cf_w_i,
        &cf_u_i,
        &cf_W_i,
        &cf_U_i,
    )?;

    let cf_r_bits = CycleFoldChallengeGadget::<C2, GC2>::get_challenge_native(
        poseidon_config,
        cf_U_i.clone(),
        cf_u_i.clone(),
        cf_cmT,
    )?;
    let cf_r_Fq = C1::BaseField::from_bigint(BigInteger::from_bits_le(&cf_r_bits))
        .expect("cf_r_bits out of bounds");

    let (cf_W_i1, cf_U_i1) = NIFS::<C2, CS2>::fold_instances(
        cf_r_Fq, &cf_W_i, &cf_U_i, &cf_w_i, &cf_u_i, &cf_T, cf_cmT,
    )?;
    Ok((cf_w_i, cf_u_i, cf_W_i1, cf_U_i1, cf_cmT, cf_r_Fq))
}

#[cfg(test)]
pub mod tests {
    use ark_bn254::{constraints::GVar, Fq, Fr, G1Projective as Projective};
    use ark_ff::BigInteger;
    use ark_r1cs_std::R1CSVar;
    use ark_relations::r1cs::ConstraintSystem;
    use ark_std::UniformRand;

    use super::*;
    use crate::folding::nova::nifs::tests::prepare_simple_fold_inputs;
    use crate::transcript::poseidon::poseidon_canonical_config;
    use crate::utils::get_cm_coordinates;

    #[test]
    fn test_committed_instance_cyclefold_var() {
        let mut rng = ark_std::test_rng();

        let ci = CommittedInstance::<Projective> {
            cmE: Projective::rand(&mut rng),
            u: Fr::rand(&mut rng),
            cmW: Projective::rand(&mut rng),
            x: vec![Fr::rand(&mut rng); 1],
        };

        // check the instantiation of the CycleFold side:
        let cs = ConstraintSystem::<Fq>::new_ref();
        let ciVar =
            CommittedInstanceInCycleFoldVar::<Projective, GVar>::new_witness(cs.clone(), || {
                Ok(ci.clone())
            })
            .unwrap();
        assert_eq!(ciVar.cmE.value().unwrap(), ci.cmE);
        assert_eq!(ciVar.cmW.value().unwrap(), ci.cmW);
    }

    #[test]
    fn test_CycleFoldCircuit_constraints() {
        let (_, _, _, _, ci1, _, ci2, _, ci3, _, cmT, r_bits, _) = prepare_simple_fold_inputs();
        let r_Fq = Fq::from_bigint(BigInteger::from_bits_le(&r_bits)).unwrap();

        // cs is the Constraint System on the Curve Cycle auxiliary curve constraints field
        // (E1::Fq=E2::Fr)
        let cs = ConstraintSystem::<Fq>::new_ref();

        let cfW_u_i_x: Vec<Fq> = [
            vec![r_Fq],
            get_cm_coordinates(&ci1.cmW),
            get_cm_coordinates(&ci2.cmW),
            get_cm_coordinates(&ci3.cmW),
        ]
        .concat();
        let cfW_circuit = CycleFoldCircuit::<Projective, GVar> {
            _gc: PhantomData,
            r_bits: Some(r_bits.clone()),
            p1: Some(ci1.clone().cmW),
            p2: Some(ci2.clone().cmW),
            x: Some(cfW_u_i_x.clone()),
        };
        cfW_circuit.generate_constraints(cs.clone()).unwrap();
        assert!(cs.is_satisfied().unwrap());

        // same for E:
        let cs = ConstraintSystem::<Fq>::new_ref();
        let cfE_u_i_x = [
            vec![r_Fq],
            get_cm_coordinates(&ci1.cmE),
            get_cm_coordinates(&cmT),
            get_cm_coordinates(&ci3.cmE),
        ]
        .concat();
        let cfE_circuit = CycleFoldCircuit::<Projective, GVar> {
            _gc: PhantomData,
            r_bits: Some(r_bits.clone()),
            p1: Some(ci1.clone().cmE),
            p2: Some(cmT),
            x: Some(cfE_u_i_x.clone()),
        };
        cfE_circuit.generate_constraints(cs.clone()).unwrap();
        assert!(cs.is_satisfied().unwrap());
    }

    #[test]
    fn test_nifs_full_gadget() {
        let (_, _, _, _, ci1, _, ci2, _, ci3, _, cmT, r_bits, r_Fr) = prepare_simple_fold_inputs();

        let cs = ConstraintSystem::<Fq>::new_ref();

        let r_nonnatVar = NonNativeUintVar::<Fq>::new_witness(cs.clone(), || Ok(r_Fr)).unwrap();
        let r_bitsVar = Vec::<Boolean<Fq>>::new_witness(cs.clone(), || Ok(r_bits)).unwrap();

        let ci1Var =
            CycleFoldCommittedInstanceVar::<Projective, GVar>::new_witness(cs.clone(), || {
                Ok(ci1.clone())
            })
            .unwrap();
        let ci2Var =
            CycleFoldCommittedInstanceVar::<Projective, GVar>::new_witness(cs.clone(), || {
                Ok(ci2.clone())
            })
            .unwrap();
        let ci3Var =
            CycleFoldCommittedInstanceVar::<Projective, GVar>::new_witness(cs.clone(), || {
                Ok(ci3.clone())
            })
            .unwrap();
        let cmTVar = GVar::new_witness(cs.clone(), || Ok(cmT)).unwrap();

        NIFSFullGadget::<Projective, GVar>::verify(
            r_bitsVar,
            r_nonnatVar,
            cmTVar,
            ci1Var,
            ci2Var,
            ci3Var,
        )
        .unwrap();
        assert!(cs.is_satisfied().unwrap());
    }

    #[test]
    fn test_cyclefold_challenge_gadget() {
        let mut rng = ark_std::test_rng();
        let poseidon_config = poseidon_canonical_config::<Fq>();

        let u_i = CommittedInstance::<Projective> {
            cmE: Projective::zero(), // zero on purpose, so we test also the zero point case
            u: Fr::zero(),
            cmW: Projective::rand(&mut rng),
            x: std::iter::repeat_with(|| Fr::rand(&mut rng))
                .take(CF_IO_LEN)
                .collect(),
        };
        let U_i = CommittedInstance::<Projective> {
            cmE: Projective::rand(&mut rng),
            u: Fr::rand(&mut rng),
            cmW: Projective::rand(&mut rng),
            x: std::iter::repeat_with(|| Fr::rand(&mut rng))
                .take(CF_IO_LEN)
                .collect(),
        };
        let cmT = Projective::rand(&mut rng);

        // compute the challenge natively
        let r_bits = CycleFoldChallengeGadget::<Projective, GVar>::get_challenge_native(
            &poseidon_config,
            U_i.clone(),
            u_i.clone(),
            cmT,
        )
        .unwrap();

        let cs = ConstraintSystem::<Fq>::new_ref();
        let u_iVar =
            CycleFoldCommittedInstanceVar::<Projective, GVar>::new_witness(cs.clone(), || {
                Ok(u_i.clone())
            })
            .unwrap();
        let U_iVar =
            CycleFoldCommittedInstanceVar::<Projective, GVar>::new_witness(cs.clone(), || {
                Ok(U_i.clone())
            })
            .unwrap();
        let cmTVar = GVar::new_witness(cs.clone(), || Ok(cmT)).unwrap();

        let r_bitsVar = CycleFoldChallengeGadget::<Projective, GVar>::get_challenge_gadget(
            cs.clone(),
            &poseidon_config,
            U_iVar.to_constraint_field().unwrap(),
            u_iVar,
            cmTVar,
        )
        .unwrap();
        assert!(cs.is_satisfied().unwrap());

        // check that the natively computed and in-circuit computed hashes match
        let rVar = Boolean::le_bits_to_fp_var(&r_bitsVar).unwrap();
        let r = Fq::from_bigint(BigInteger::from_bits_le(&r_bits)).unwrap();
        assert_eq!(rVar.value().unwrap(), r);
        assert_eq!(r_bitsVar.value().unwrap(), r_bits);
    }

    #[test]
    fn test_cyclefold_hash_gadget() {
        let mut rng = ark_std::test_rng();
        let poseidon_config = poseidon_canonical_config::<Fq>();

        let U_i = CommittedInstance::<Projective> {
            cmE: Projective::rand(&mut rng),
            u: Fr::rand(&mut rng),
            cmW: Projective::rand(&mut rng),
            x: std::iter::repeat_with(|| Fr::rand(&mut rng))
                .take(CF_IO_LEN)
                .collect(),
        };
        let h = U_i.hash_cyclefold(&poseidon_config).unwrap();

        let cs = ConstraintSystem::<Fq>::new_ref();
        let U_iVar =
            CycleFoldCommittedInstanceVar::<Projective, GVar>::new_witness(cs.clone(), || {
                Ok(U_i.clone())
            })
            .unwrap();
        let (hVar, _) = U_iVar
            .hash(&CRHParametersVar::new_constant(cs.clone(), poseidon_config).unwrap())
            .unwrap();
        hVar.enforce_equal(&FpVar::new_witness(cs.clone(), || Ok(h)).unwrap())
            .unwrap();
        assert!(cs.is_satisfied().unwrap());
    }
}
