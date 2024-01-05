use ark_ec::CurveGroup;
use ark_ff::Field;
use ark_r1cs_std::{boolean::Boolean, groups::GroupOpsBounds, prelude::CurveVar};
use ark_relations::r1cs::SynthesisError;
use ark_std::{rand::Rng, UniformRand};
use core::marker::PhantomData;

use crate::utils::vec::{vec_add, vec_scalar_mul};

use crate::transcript::Transcript;
use crate::Error;

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Proof<C: CurveGroup> {
    pub R: C,
    pub u: Vec<C::ScalarField>,
    pub r_u: C::ScalarField,
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Params<C: CurveGroup> {
    pub h: C,
    pub generators: Vec<C::Affine>,
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Pedersen<C: CurveGroup> {
    _c: PhantomData<C>,
}

impl<C: CurveGroup> Pedersen<C> {
    pub fn new_params<R: Rng>(rng: &mut R, max: usize) -> Params<C> {
        let generators: Vec<C::Affine> = std::iter::repeat_with(|| C::Affine::rand(rng))
            .take(max.next_power_of_two())
            .collect();
        let params: Params<C> = Params::<C> {
            h: C::rand(rng),
            generators,
        };
        params
    }

    pub fn commit(
        params: &Params<C>,
        v: &Vec<C::ScalarField>,
        r: &C::ScalarField,
    ) -> Result<C, Error> {
        if params.generators.len() < v.len() {
            return Err(Error::PedersenParamsLen(params.generators.len(), v.len()));
        }
        // h⋅r + <g, v>
        // use msm_unchecked because we already ensured at the if that lengths match
        Ok(params.h.mul(r) + C::msm_unchecked(&params.generators[..v.len()], v))
    }

    pub fn prove(
        params: &Params<C>,
        transcript: &mut impl Transcript<C>,
        cm: &C,
        v: &Vec<C::ScalarField>,
        r: &C::ScalarField,
    ) -> Result<Proof<C>, Error> {
        if params.generators.len() < v.len() {
            return Err(Error::PedersenParamsLen(params.generators.len(), v.len()));
        }

        transcript.absorb_point(cm)?;
        let r1 = transcript.get_challenge();
        let d = transcript.get_challenges(v.len());

        // R = h⋅r_1 + <g, d>
        // use msm_unchecked because we already ensured at the if that lengths match
        let R: C = params.h.mul(r1) + C::msm_unchecked(&params.generators[..d.len()], &d);

        transcript.absorb_point(&R)?;
        let e = transcript.get_challenge();

        // u = d + v⋅e
        let u = vec_add(&vec_scalar_mul(v, &e), &d)?;
        // r_u = e⋅r + r_1
        let r_u = e * r + r1;

        Ok(Proof::<C> { R, u, r_u })
    }

    pub fn verify(
        params: &Params<C>,
        transcript: &mut impl Transcript<C>,
        cm: C,
        proof: Proof<C>,
    ) -> Result<(), Error> {
        if params.generators.len() < proof.u.len() {
            return Err(Error::PedersenParamsLen(
                params.generators.len(),
                proof.u.len(),
            ));
        }

        transcript.absorb_point(&cm)?;
        transcript.get_challenge(); // r_1
        transcript.get_challenges(proof.u.len()); // d
        transcript.absorb_point(&proof.R)?;
        let e = transcript.get_challenge();

        // check that: R + cm == h⋅r_u + <g, u>
        let lhs = proof.R + cm.mul(e);
        // use msm_unchecked because we already ensured at the if that lengths match
        let rhs = params.h.mul(proof.r_u)
            + C::msm_unchecked(&params.generators[..proof.u.len()], &proof.u);
        if lhs != rhs {
            return Err(Error::PedersenVerificationFail);
        }
        Ok(())
    }
}

pub type CF<C> = <<C as CurveGroup>::BaseField as Field>::BasePrimeField;

pub struct PedersenGadget<C, GC>
where
    C: CurveGroup,
    GC: CurveVar<C, CF<C>>,
{
    _cf: PhantomData<CF<C>>,
    _c: PhantomData<C>,
    _gc: PhantomData<GC>,
}

impl<C, GC> PedersenGadget<C, GC>
where
    C: CurveGroup,
    GC: CurveVar<C, CF<C>>,

    <C as ark_ec::CurveGroup>::BaseField: ark_ff::PrimeField,
    for<'a> &'a GC: GroupOpsBounds<'a, C, GC>,
{
    pub fn commit(
        h: GC,
        g: Vec<GC>,
        v: Vec<Vec<Boolean<CF<C>>>>,
        r: Vec<Boolean<CF<C>>>,
    ) -> Result<GC, SynthesisError> {
        let mut res = GC::zero();
        res += h.scalar_mul_le(r.iter())?;
        for (i, v_i) in v.iter().enumerate() {
            res += g[i].scalar_mul_le(v_i.iter())?;
        }
        Ok(res)
    }
}

#[cfg(test)]
mod tests {
    use ark_ff::{BigInteger, PrimeField};
    use ark_pallas::{constraints::GVar, Fq, Fr, Projective};
    use ark_r1cs_std::{alloc::AllocVar, bits::boolean::Boolean, eq::EqGadget};
    use ark_relations::r1cs::ConstraintSystem;
    use ark_std::UniformRand;

    use super::*;
    use crate::transcript::poseidon::{tests::poseidon_test_config, PoseidonTranscript};

    #[test]
    fn test_pedersen_vector() {
        let mut rng = ark_std::test_rng();

        const n: usize = 10;
        // setup params
        let params = Pedersen::<Projective>::new_params(&mut rng, n);
        let poseidon_config = poseidon_test_config::<Fr>();

        // init Prover's transcript
        let mut transcript_p = PoseidonTranscript::<Projective>::new(&poseidon_config);
        // init Verifier's transcript
        let mut transcript_v = PoseidonTranscript::<Projective>::new(&poseidon_config);

        let v: Vec<Fr> = std::iter::repeat_with(|| Fr::rand(&mut rng))
            .take(n)
            .collect();
        let r: Fr = Fr::rand(&mut rng);
        let cm = Pedersen::<Projective>::commit(&params, &v, &r).unwrap();
        let proof = Pedersen::<Projective>::prove(&params, &mut transcript_p, &cm, &v, &r).unwrap();
        Pedersen::<Projective>::verify(&params, &mut transcript_v, cm, proof).unwrap();
    }

    #[test]
    fn test_pedersen_circuit() {
        let mut rng = ark_std::test_rng();

        const n: usize = 10;
        // setup params
        let params = Pedersen::<Projective>::new_params(&mut rng, n);

        let v: Vec<Fr> = std::iter::repeat_with(|| Fr::rand(&mut rng))
            .take(n)
            .collect();
        let r: Fr = Fr::rand(&mut rng);
        let cm = Pedersen::<Projective>::commit(&params, &v, &r).unwrap();

        // circuit
        let cs = ConstraintSystem::<Fq>::new_ref();

        let v_bits: Vec<Vec<bool>> = v.iter().map(|val| val.into_bigint().to_bits_le()).collect();
        let r_bits: Vec<bool> = r.into_bigint().to_bits_le();

        // prepare inputs
        let vVar: Vec<Vec<Boolean<Fq>>> = v_bits
            .iter()
            .map(|val_bits| {
                Vec::<Boolean<Fq>>::new_witness(cs.clone(), || Ok(val_bits.clone())).unwrap()
            })
            .collect();
        let rVar = Vec::<Boolean<Fq>>::new_witness(cs.clone(), || Ok(r_bits)).unwrap();
        let gVar = Vec::<GVar>::new_witness(cs.clone(), || Ok(params.generators)).unwrap();
        let hVar = GVar::new_witness(cs.clone(), || Ok(params.h)).unwrap();
        let expected_cmVar = GVar::new_witness(cs.clone(), || Ok(cm)).unwrap();

        // use the gadget
        let cmVar = PedersenGadget::<Projective, GVar>::commit(hVar, gVar, vVar, rVar).unwrap();
        cmVar.enforce_equal(&expected_cmVar).unwrap();
    }
}
