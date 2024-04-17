/// Heavily inspired from testudo: https://github.com/cryptonetlab/testudo/tree/master
/// Some changes:
/// - Typings to better stick to ark_poly's API
/// - Uses `folding-schemes`' own `TranscriptVar` trait and `PoseidonTranscriptVar` struct
/// - API made closer to gadgets found in `folding-schemes`
use ark_crypto_primitives::sponge::Absorb;
use ark_ec::{CurveGroup, Group};
use ark_ff::PrimeField;
use ark_poly::{univariate::DensePolynomial, DenseUVPolynomial};
use ark_r1cs_std::{
    alloc::{AllocVar, AllocationMode},
    boolean::Boolean,
    eq::EqGadget,
    fields::{fp::FpVar, FieldVar},
};
use ark_relations::r1cs::{Namespace, SynthesisError};
use std::{borrow::Borrow, marker::PhantomData};

use crate::utils::espresso::sum_check::SumCheck;
use crate::utils::virtual_polynomial::VPAuxInfo;
use crate::{
    transcript::{poseidon::PoseidonTranscript, TranscriptVar},
    utils::sum_check::{structs::IOPProof, IOPSumCheck},
};

#[derive(Clone, Debug)]
pub struct DensePolynomialVar<F: PrimeField> {
    pub coeffs: Vec<FpVar<F>>,
}

impl<F: PrimeField> AllocVar<DensePolynomial<F>, F> for DensePolynomialVar<F> {
    fn new_variable<T: Borrow<DensePolynomial<F>>>(
        cs: impl Into<Namespace<F>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        f().and_then(|c| {
            let cs = cs.into();
            let cp: &DensePolynomial<F> = c.borrow();
            let mut coeffs_var = Vec::<FpVar<F>>::with_capacity(cp.coeffs.len());
            for coeff in cp.coeffs.iter() {
                let coeff_var = FpVar::<F>::new_variable(cs.clone(), || Ok(coeff), mode)?;
                coeffs_var.push(coeff_var);
            }
            Ok(Self { coeffs: coeffs_var })
        })
    }
}

impl<F: PrimeField> DensePolynomialVar<F> {
    pub fn eval_at_zero(&self) -> FpVar<F> {
        if self.coeffs.is_empty() {
            return FpVar::<F>::zero();
        }
        self.coeffs[0].clone()
    }

    pub fn eval_at_one(&self) -> FpVar<F> {
        if self.coeffs.is_empty() {
            return FpVar::<F>::zero();
        }
        let mut res = self.coeffs[0].clone();
        for i in 1..self.coeffs.len() {
            res = &res + &self.coeffs[i];
        }
        res
    }

    pub fn evaluate(&self, r: &FpVar<F>) -> FpVar<F> {
        if self.coeffs.is_empty() {
            return FpVar::<F>::zero();
        }
        let mut eval = self.coeffs[0].clone();
        let mut power = r.clone();

        for i in 1..self.coeffs.len() {
            eval += &power * &self.coeffs[i];
            power *= r;
        }
        eval
    }
}

#[derive(Clone, Debug)]
pub struct IOPProofVar<C: CurveGroup> {
    // We have to be generic over a CurveGroup because instantiating a IOPProofVar will call IOPSumCheck which requires a CurveGroup
    pub proofs: Vec<DensePolynomialVar<C::ScalarField>>, // = IOPProof.proofs
    pub claim: FpVar<C::ScalarField>,
}

impl<C: CurveGroup> AllocVar<IOPProof<C::ScalarField>, C::ScalarField> for IOPProofVar<C>
where
    <C as Group>::ScalarField: Absorb,
{
    fn new_variable<T: Borrow<IOPProof<C::ScalarField>>>(
        cs: impl Into<Namespace<C::ScalarField>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        f().and_then(|c| {
            let cs = cs.into();
            let cp: &IOPProof<C::ScalarField> = c.borrow();
            let claim = IOPSumCheck::<C, PoseidonTranscript<C>>::extract_sum(cp);
            let claim = FpVar::<C::ScalarField>::new_variable(cs.clone(), || Ok(claim), mode)?;
            let mut proofs =
                Vec::<DensePolynomialVar<C::ScalarField>>::with_capacity(cp.proofs.len());
            for proof in cp.proofs.iter() {
                let poly = DensePolynomial::from_coefficients_slice(&proof.coeffs);
                let proof = DensePolynomialVar::<C::ScalarField>::new_variable(
                    cs.clone(),
                    || Ok(poly),
                    mode,
                )?;
                proofs.push(proof);
            }
            Ok(Self { proofs, claim })
        })
    }
}

#[derive(Clone, Debug)]
pub struct VPAuxInfoVar<F: PrimeField> {
    pub num_variables: FpVar<F>,
    pub max_degree: FpVar<F>,
}

impl<F: PrimeField> AllocVar<VPAuxInfo<F>, F> for VPAuxInfoVar<F> {
    fn new_variable<T: Borrow<VPAuxInfo<F>>>(
        cs: impl Into<Namespace<F>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        f().and_then(|c| {
            let cs = cs.into();
            let cp: &VPAuxInfo<F> = c.borrow();
            let num_variables = FpVar::<F>::new_variable(
                cs.clone(),
                || Ok(F::from(cp.num_variables as u64)),
                mode,
            )?;
            let max_degree =
                FpVar::<F>::new_variable(cs.clone(), || Ok(F::from(cp.max_degree as u64)), mode)?;
            Ok(Self {
                num_variables,
                max_degree,
            })
        })
    }
}

#[derive(Debug, Clone)]
pub struct SumCheckVerifierGadget<C: CurveGroup> {
    _f: PhantomData<C>,
}

impl<C: CurveGroup> SumCheckVerifierGadget<C> {
    #[allow(clippy::type_complexity)]
    pub fn verify(
        iop_proof_var: &IOPProofVar<C>,
        poly_aux_info_var: &VPAuxInfoVar<C::ScalarField>,
        transcript_var: &mut impl TranscriptVar<C::ScalarField>,
        enabled: Boolean<C::ScalarField>,
    ) -> Result<(Vec<FpVar<C::ScalarField>>, Vec<FpVar<C::ScalarField>>), SynthesisError> {
        let mut e_vars = vec![iop_proof_var.claim.clone()];
        let mut r_vars: Vec<FpVar<C::ScalarField>> = Vec::new();
        transcript_var.absorb(&poly_aux_info_var.num_variables)?;
        transcript_var.absorb(&poly_aux_info_var.max_degree)?;

        for poly_var in iop_proof_var.proofs.iter() {
            let res = poly_var.eval_at_one() + poly_var.eval_at_zero();
            let e_var = e_vars.last().ok_or(SynthesisError::Unsatisfiable)?;
            res.conditional_enforce_equal(e_var, &enabled)?;
            transcript_var.absorb_vec(&poly_var.coeffs)?;
            let r_i_var = transcript_var.get_challenge()?;
            e_vars.push(poly_var.evaluate(&r_i_var));
            r_vars.push(r_i_var);
        }

        Ok((e_vars, r_vars))
    }
}

#[cfg(test)]
mod tests {
    use ark_crypto_primitives::sponge::{poseidon::PoseidonConfig, Absorb};
    use ark_ec::CurveGroup;
    use ark_ff::Field;
    use ark_pallas::{Fr, Projective};
    use ark_poly::{
        univariate::DensePolynomial, DenseMultilinearExtension, DenseUVPolynomial,
        MultilinearExtension, Polynomial,
    };
    use ark_r1cs_std::{alloc::AllocVar, R1CSVar};
    use ark_relations::r1cs::ConstraintSystem;
    use std::sync::Arc;

    use super::*;
    use crate::{
        folding::circuits::sum_check::{IOPProofVar, VPAuxInfoVar},
        transcript::{
            poseidon::{poseidon_canonical_config, PoseidonTranscript, PoseidonTranscriptVar},
            Transcript, TranscriptVar,
        },
        utils::{
            sum_check::{structs::IOPProof, IOPSumCheck, SumCheck},
            virtual_polynomial::VirtualPolynomial,
        },
    };

    pub type TestSumCheckProof<F> = (VirtualPolynomial<F>, PoseidonConfig<F>, IOPProof<F>);

    /// Primarily used for testing the sumcheck gadget
    /// Returns a random virtual polynomial, the poseidon config used and the associated sumcheck proof
    pub fn get_test_sumcheck_proof<C: CurveGroup>(
        num_vars: usize,
    ) -> TestSumCheckProof<C::ScalarField>
    where
        <C as ark_ec::Group>::ScalarField: Absorb,
    {
        let mut rng = ark_std::test_rng();
        let poseidon_config: PoseidonConfig<C::ScalarField> =
            poseidon_canonical_config::<C::ScalarField>();
        let mut poseidon_transcript_prove = PoseidonTranscript::<C>::new(&poseidon_config);
        let poly_mle = DenseMultilinearExtension::rand(num_vars, &mut rng);
        let virtual_poly =
            VirtualPolynomial::new_from_mle(&Arc::new(poly_mle), C::ScalarField::ONE);
        let sum_check: IOPProof<C::ScalarField> = IOPSumCheck::<C, PoseidonTranscript<C>>::prove(
            &virtual_poly,
            &mut poseidon_transcript_prove,
        )
        .unwrap();
        (virtual_poly, poseidon_config, sum_check)
    }

    #[test]
    fn test_sum_check_circuit() {
        for num_vars in 1..15 {
            let cs = ConstraintSystem::<Fr>::new_ref();
            let (virtual_poly, poseidon_config, sum_check) =
                get_test_sumcheck_proof::<Projective>(num_vars);
            let mut poseidon_var: PoseidonTranscriptVar<Fr> =
                PoseidonTranscriptVar::new(cs.clone(), &poseidon_config);
            let iop_proof_var =
                IOPProofVar::<Projective>::new_witness(cs.clone(), || Ok(&sum_check)).unwrap();
            let poly_aux_info_var =
                VPAuxInfoVar::<Fr>::new_witness(cs.clone(), || Ok(virtual_poly.aux_info)).unwrap();
            let enabled = Boolean::<Fr>::new_witness(cs.clone(), || Ok(true)).unwrap();
            let res = SumCheckVerifierGadget::<Projective>::verify(
                &iop_proof_var,
                &poly_aux_info_var,
                &mut poseidon_var,
                enabled,
            );

            assert!(res.is_ok());
            let (circuit_evals, r_challenges) = res.unwrap();

            // 1. assert claim from circuit is equal to the one from the sum-check
            let claim: Fr =
                IOPSumCheck::<Projective, PoseidonTranscript<Projective>>::extract_sum(&sum_check);
            assert_eq!(circuit_evals[0].value().unwrap(), claim);

            // 2. assert that all in-circuit evaluations are equal to the ones from the sum-check
            for ((proof, point), circuit_eval) in sum_check
                .proofs
                .iter()
                .zip(sum_check.point.iter())
                .zip(circuit_evals.iter().skip(1))
            // we skip the first one since it's the above checked claim
            {
                let poly = DensePolynomial::from_coefficients_slice(&proof.coeffs);
                let eval = poly.evaluate(point);
                assert_eq!(eval, circuit_eval.value().unwrap());
            }

            // 3. assert that all challenges are equal to the ones from the sum-check
            for (point, r_challenge) in sum_check.point.iter().zip(r_challenges.iter()) {
                assert_eq!(*point, r_challenge.value().unwrap());
            }

            assert!(cs.is_satisfied().unwrap());
        }
    }
}
