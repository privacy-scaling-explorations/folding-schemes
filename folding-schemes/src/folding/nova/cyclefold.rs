/// contains [CycleFold](https://eprint.iacr.org/2023/1192.pdf) related circuits
use ark_crypto_primitives::sponge::{
    constraints::CryptographicSpongeVar,
    poseidon::{constraints::PoseidonSpongeVar, PoseidonConfig, PoseidonSponge},
    Absorb, CryptographicSponge,
};
use ark_ec::CurveGroup;
use ark_ff::PrimeField;
use ark_r1cs_std::{
    alloc::{AllocVar, AllocationMode},
    bits::uint8::UInt8,
    boolean::Boolean,
    eq::EqGadget,
    fields::{fp::FpVar, nonnative::NonNativeFieldVar},
    groups::GroupOpsBounds,
    prelude::CurveVar,
    ToBytesGadget, ToConstraintFieldGadget,
};
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, Namespace, SynthesisError};
use ark_serialize::CanonicalSerialize;
use ark_std::fmt::Debug;
use ark_std::Zero;
use core::{borrow::Borrow, marker::PhantomData};

use super::circuits::CF2;
use super::CommittedInstance;
use crate::constants::N_BITS_RO;
use crate::Error;

// publi inputs length for the CycleFoldCircuit: |[r, p1.x,y,infinity, p2.x,y,infinity,
// p3.x,y,infinity]|
pub const CF_IO_LEN: usize = 10;

/// CycleFoldCommittedInstanceVar is the CycleFold CommittedInstance representation in the Nova
/// circuit.
#[derive(Debug, Clone)]
pub struct CycleFoldCommittedInstanceVar<C: CurveGroup, GC: CurveVar<C, CF2<C>>>
where
    for<'a> &'a GC: GroupOpsBounds<'a, C, GC>,
{
    _c: PhantomData<C>,
    pub cmE: GC,
    pub u: NonNativeFieldVar<C::ScalarField, CF2<C>>,
    pub cmW: GC,
    pub x: Vec<NonNativeFieldVar<C::ScalarField, CF2<C>>>,
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
            let u = NonNativeFieldVar::<C::ScalarField, CF2<C>>::new_variable(
                cs.clone(),
                || Ok(val.borrow().u),
                mode,
            )?;
            let x = Vec::<NonNativeFieldVar<C::ScalarField, CF2<C>>>::new_variable(
                cs.clone(),
                || Ok(val.borrow().x.clone()),
                mode,
            )?;

            Ok(Self {
                _c: PhantomData,
                cmE,
                u,
                cmW,
                x,
            })
        })
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
    pub fn verify(
        // assumes that r_bits is equal to r_nonnat just that in a different format
        r_bits: Vec<Boolean<CF2<C>>>,
        r_nonnat: NonNativeFieldVar<C::ScalarField, CF2<C>>,
        cmT: GC,
        // ci1 is assumed to be always with cmE=0, u=1 (checks done previous to this method)
        ci1: CycleFoldCommittedInstanceVar<C, GC>,
        ci2: CycleFoldCommittedInstanceVar<C, GC>,
        ci3: CycleFoldCommittedInstanceVar<C, GC>,
    ) -> Result<Boolean<CF2<C>>, SynthesisError> {
        // cm(E) check: ci3.cmE == ci1.cmE + r * cmT (ci2.cmE=0)
        let first_check = ci3
            .cmE
            .is_eq(&(cmT.scalar_mul_le(r_bits.iter())? + ci1.cmE))?;

        // cm(W) check: ci3.cmW == ci1.cmW + r * ci2.cmW
        let second_check = ci3
            .cmW
            .is_eq(&(ci1.cmW + ci2.cmW.scalar_mul_le(r_bits.iter())?))?;

        let u_rlc: NonNativeFieldVar<C::ScalarField, CF2<C>> = ci1.u + r_nonnat.clone();
        let third_check = u_rlc.is_eq(&ci3.u)?;

        // ensure that: ci3.x == ci1.x + r * ci2.x
        let x_rlc: Vec<NonNativeFieldVar<C::ScalarField, CF2<C>>> = ci1
            .x
            .iter()
            .zip(ci2.x)
            .map(|(a, b)| a + &r_nonnat * &b)
            .collect::<Vec<NonNativeFieldVar<C::ScalarField, CF2<C>>>>();
        let fourth_check = x_rlc.is_eq(&ci3.x)?;

        first_check
            .and(&second_check)?
            .and(&third_check)?
            .and(&fourth_check)
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
    GC: CurveVar<C, CF2<C>>,
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

        let U_i_cmE_bytes = point_to_bytes(U_i.cmE)?;
        let U_i_cmW_bytes = point_to_bytes(U_i.cmW)?;
        let u_i_cmE_bytes = point_to_bytes(u_i.cmE)?;
        let u_i_cmW_bytes = point_to_bytes(u_i.cmW)?;
        let cmT_bytes = point_to_bytes(cmT)?;

        let mut U_i_u_bytes = Vec::new();
        U_i.u.serialize_uncompressed(&mut U_i_u_bytes)?;
        let mut U_i_x_bytes = Vec::new();
        U_i.x.serialize_uncompressed(&mut U_i_x_bytes)?;
        U_i_x_bytes = U_i_x_bytes[8..].to_vec();
        let mut u_i_u_bytes = Vec::new();
        u_i.u.serialize_uncompressed(&mut u_i_u_bytes)?;
        let mut u_i_x_bytes = Vec::new();
        u_i.x.serialize_uncompressed(&mut u_i_x_bytes)?;
        u_i_x_bytes = u_i_x_bytes[8..].to_vec();

        let input: Vec<u8> = [
            U_i_cmE_bytes,
            U_i_u_bytes,
            U_i_cmW_bytes,
            U_i_x_bytes,
            u_i_cmE_bytes,
            u_i_u_bytes,
            u_i_cmW_bytes,
            u_i_x_bytes,
            cmT_bytes,
        ]
        .concat();
        sponge.absorb(&input);
        let bits = sponge.squeeze_bits(N_BITS_RO);
        Ok(bits)
    }
    // compatible with the native get_challenge_native
    pub fn get_challenge_gadget(
        cs: ConstraintSystemRef<C::BaseField>,
        poseidon_config: &PoseidonConfig<C::BaseField>,
        U_i: CycleFoldCommittedInstanceVar<C, GC>,
        u_i: CycleFoldCommittedInstanceVar<C, GC>,
        cmT: GC,
    ) -> Result<Vec<Boolean<C::BaseField>>, SynthesisError> {
        let mut sponge = PoseidonSpongeVar::<C::BaseField>::new(cs, poseidon_config);

        let U_i_x_bytes: Vec<UInt8<CF2<C>>> = U_i
            .x
            .iter()
            .flat_map(|e| e.to_bytes().unwrap_or(vec![]))
            .collect::<Vec<UInt8<CF2<C>>>>();
        let u_i_x_bytes: Vec<UInt8<CF2<C>>> = u_i
            .x
            .iter()
            .flat_map(|e| e.to_bytes().unwrap_or(vec![]))
            .collect::<Vec<UInt8<CF2<C>>>>();

        let input: Vec<UInt8<CF2<C>>> = [
            pointvar_to_bytes(U_i.cmE)?,
            U_i.u.to_bytes()?,
            pointvar_to_bytes(U_i.cmW)?,
            U_i_x_bytes,
            pointvar_to_bytes(u_i.cmE)?,
            u_i.u.to_bytes()?,
            pointvar_to_bytes(u_i.cmW)?,
            u_i_x_bytes,
            pointvar_to_bytes(cmT)?,
        ]
        .concat();
        sponge.absorb(&input)?;
        let bits = sponge.squeeze_bits(N_BITS_RO)?;
        Ok(bits)
    }
}

/// returns the bytes being compatible with the pointvar_to_bytes method.
/// These methods are temporary once arkworks has the fix to prevent different to_bytes behaviour
/// across different curves. Eg, in pasta and bn254: pasta returns 65 bytes both native and gadget,
/// whereas bn254 returns 64 bytes native and 65 in gadget, also the penultimate byte is different
/// natively than in gadget.
fn point_to_bytes<C: CurveGroup>(p: C) -> Result<Vec<u8>, Error> {
    let l = p.uncompressed_size();
    let mut b = Vec::new();
    p.serialize_uncompressed(&mut b)?;
    if p.is_zero() {
        b[l / 2] = 1;
        b[l - 1] = 1;
    }
    Ok(b[..63].to_vec())
}
fn pointvar_to_bytes<C: CurveGroup, GC: CurveVar<C, CF2<C>>>(
    p: GC,
) -> Result<Vec<UInt8<CF2<C>>>, SynthesisError> {
    let b = p.to_bytes()?;
    Ok(b[..63].to_vec())
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
    pub p3: Option<C>,
    pub x: Option<Vec<CF2<C>>>, // public inputs (cf_u_{i+1}.x)
}
impl<C: CurveGroup, GC: CurveVar<C, CF2<C>>> CycleFoldCircuit<C, GC> {
    pub fn empty() -> Self {
        Self {
            _gc: PhantomData,
            r_bits: None,
            p1: None,
            p2: None,
            p3: None,
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
        let p3 = GC::new_witness(cs.clone(), || Ok(self.p3.unwrap_or(C::zero())))?;

        let x = Vec::<FpVar<CF2<C>>>::new_input(cs.clone(), || {
            Ok(self.x.unwrap_or(vec![CF2::<C>::zero(); CF_IO_LEN]))
        })?;
        #[cfg(test)]
        assert_eq!(x.len(), CF_IO_LEN); // non-constrained sanity check

        // check that the points coordinates are placed as the public input x: x == [r, p1, p2, p3]
        let r: FpVar<CF2<C>> = Boolean::le_bits_to_fp_var(&r_bits)?;
        let points_coords: Vec<FpVar<CF2<C>>> = [
            vec![r],
            p1.clone().to_constraint_field()?,
            p2.clone().to_constraint_field()?,
            p3.clone().to_constraint_field()?,
        ]
        .concat();
        points_coords.enforce_equal(&x)?;

        // Fold the original Nova instances natively in CycleFold
        // For the cmW we're checking: U_i1.cmW == U_i.cmW + r * u_i.cmW
        // For the cmE we're checking: U_i1.cmE == U_i.cmE + r * cmT + r^2 * u_i.cmE, where u_i.cmE
        // is assumed to be 0, so, U_i1.cmE == U_i.cmE + r * cmT
        p3.enforce_equal(&(p1 + p2.scalar_mul_le(r_bits.iter())?))?;

        Ok(())
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use ark_bn254::{constraints::GVar, Fq, Fr, G1Projective as Projective};
    use ark_ff::BigInteger;
    use ark_r1cs_std::{alloc::AllocVar, R1CSVar};
    use ark_relations::r1cs::ConstraintSystem;
    use ark_std::UniformRand;

    use crate::folding::nova::get_cm_coordinates;
    use crate::folding::nova::nifs::tests::prepare_simple_fold_inputs;
    use crate::transcript::poseidon::poseidon_test_config;

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
            p3: Some(ci3.clone().cmW),
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
            p3: Some(ci3.clone().cmE),
            x: Some(cfE_u_i_x.clone()),
        };
        cfE_circuit.generate_constraints(cs.clone()).unwrap();
        assert!(cs.is_satisfied().unwrap());
    }

    #[test]
    fn test_nifs_full_gadget() {
        let (_, _, _, _, ci1, _, ci2, _, ci3, _, cmT, r_bits, r_Fr) = prepare_simple_fold_inputs();

        let cs = ConstraintSystem::<Fq>::new_ref();

        let r_nonnatVar =
            NonNativeFieldVar::<Fr, Fq>::new_witness(cs.clone(), || Ok(r_Fr)).unwrap();
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

        let nifs_check = NIFSFullGadget::<Projective, GVar>::verify(
            r_bitsVar,
            r_nonnatVar,
            cmTVar,
            ci1Var,
            ci2Var,
            ci3Var,
        )
        .unwrap();
        nifs_check.enforce_equal(&Boolean::<Fq>::TRUE).unwrap();
        assert!(cs.is_satisfied().unwrap());
    }

    #[test]
    fn test_point_bytes() {
        let mut rng = ark_std::test_rng();

        let p = Projective::rand(&mut rng);
        let p_bytes = point_to_bytes(p).unwrap();

        let cs = ConstraintSystem::<Fq>::new_ref();
        let pVar = GVar::new_witness(cs.clone(), || Ok(p)).unwrap();
        assert_eq!(pVar.value().unwrap(), p);

        let p_bytesVar = &pointvar_to_bytes(pVar).unwrap();
        assert_eq!(p_bytesVar.value().unwrap(), p_bytes);
    }

    #[test]
    fn test_cyclefold_challenge_gadget() {
        let mut rng = ark_std::test_rng();
        let poseidon_config = poseidon_test_config::<Fq>();

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
            U_iVar,
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
}
