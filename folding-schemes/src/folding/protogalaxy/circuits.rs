use ark_crypto_primitives::sponge::CryptographicSponge;
use ark_ec::CurveGroup;
use ark_poly::{univariate::DensePolynomial, EvaluationDomain, GeneralEvaluationDomain};
use ark_r1cs_std::{
    alloc::AllocVar,
    fields::{fp::FpVar, FieldVar},
    poly::polynomial::univariate::dense::DensePolynomialVar,
};
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};

use super::{
    folding::lagrange_polys,
    utils::{all_powers_var, betas_star_var, exponential_powers_var},
    CommittedInstanceVar,
};
use crate::{
    folding::circuits::nonnative::affine::NonNativeAffineVar, transcript::TranscriptVar,
    utils::gadgets::VectorGadget,
};

pub struct FoldingGadget {}

impl FoldingGadget {
    pub fn fold_committed_instance<C: CurveGroup, S: CryptographicSponge>(
        transcript: &mut impl TranscriptVar<C::ScalarField, S>,
        // running instance
        instance: &CommittedInstanceVar<C>,
        // incoming instances
        vec_instances: &[CommittedInstanceVar<C>],
        // polys from P
        F_coeffs: Vec<FpVar<C::ScalarField>>,
        K_coeffs: Vec<FpVar<C::ScalarField>>,
    ) -> Result<CommittedInstanceVar<C>, SynthesisError> {
        let t = instance.betas.len();
        let n = F_coeffs.len();

        // absorb the committed instances
        transcript.absorb(instance)?;
        transcript.absorb(&vec_instances)?;

        let delta = transcript.get_challenge()?;
        let deltas = exponential_powers_var(delta, t);

        transcript.absorb(&F_coeffs)?;

        let alpha = transcript.get_challenge()?;
        let alphas = all_powers_var(alpha.clone(), n);

        // F(alpha) = e + \sum_t F_i * alpha^i
        let mut F_alpha = instance.e.clone();
        for (i, F_i) in F_coeffs.iter().skip(1).enumerate() {
            F_alpha += F_i * &alphas[i + 1];
        }

        let betas_star = betas_star_var(&instance.betas, &deltas, &alpha);

        let k = vec_instances.len();
        let H = GeneralEvaluationDomain::new(k + 1).unwrap();
        let L_X = lagrange_polys(H)
            .into_iter()
            .map(|poly| {
                DensePolynomialVar::from_coefficients_vec(
                    poly.coeffs
                        .into_iter()
                        .map(FpVar::constant)
                        .collect::<Vec<_>>(),
                )
            })
            .collect::<Vec<_>>();
        let Z_X = DensePolynomialVar::from_coefficients_vec(
            DensePolynomial::from(H.vanishing_polynomial())
                .coeffs
                .into_iter()
                .map(FpVar::constant)
                .collect::<Vec<_>>(),
        );
        let K_X = DensePolynomialVar { coeffs: K_coeffs };

        transcript.absorb(&K_X.coeffs)?;

        let gamma = transcript.get_challenge()?;

        let L_X_evals = L_X
            .iter()
            .take(k + 1)
            .map(|L| L.evaluate(&gamma))
            .collect::<Result<Vec<_>, _>>()?;

        let e_star = F_alpha * &L_X_evals[0] + Z_X.evaluate(&gamma)? * K_X.evaluate(&gamma)?;

        let mut u_star = &instance.u * &L_X_evals[0];
        let mut x_star = instance.x.mul_scalar(&L_X_evals[0])?;
        for i in 0..k {
            u_star += &vec_instances[i].u * &L_X_evals[i + 1];
            x_star = x_star.add(&vec_instances[i].x.mul_scalar(&L_X_evals[i + 1])?)?;
        }

        // return the folded instance
        Ok(CommittedInstanceVar {
            betas: betas_star,
            // phi will be computed in CycleFold
            phi: NonNativeAffineVar::new_constant(ConstraintSystemRef::None, C::zero())?,
            e: e_star,
            u: u_star,
            x: x_star,
        })
    }
}

#[cfg(test)]
mod tests {
    use ark_crypto_primitives::sponge::{constraints::CryptographicSpongeVar, poseidon::{constraints::PoseidonSpongeVar, PoseidonSponge}};
    use ark_pallas::{Fr, Projective};
    use ark_r1cs_std::R1CSVar;
    use ark_relations::r1cs::ConstraintSystem;
    use std::error::Error;

    use super::*;
    use crate::{
        ccs::r1cs::tests::get_test_r1cs,
        folding::protogalaxy::folding::{tests::prepare_inputs, Folding}, transcript::poseidon::poseidon_test_config,
    };

    #[test]
    fn test_fold_nonnative_case() -> Result<(), Box<dyn Error>> {
        let k = 7;
        let (witness, instance, witnesses, instances) = prepare_inputs(k);
        let r1cs = get_test_r1cs::<Fr>();

        // init Prover & Verifier's transcript
        let poseidon_config = poseidon_test_config::<Fr>();
        let mut transcript_p = PoseidonSponge::new(&poseidon_config);
        let mut transcript_v = PoseidonSponge::new(&poseidon_config);

        let (_, _, F_coeffs, K_coeffs) = Folding::<Projective>::prove(
            &mut transcript_p,
            &r1cs,
            &instance,
            &witness,
            &instances,
            &witnesses,
        )?;

        let folded_instance = Folding::<Projective>::verify(
            &mut transcript_v,
            &r1cs,
            &instance,
            &instances,
            F_coeffs.clone(),
            K_coeffs.clone(),
        )?;

        let cs = ConstraintSystem::new_ref();
        let mut transcript_var = PoseidonSpongeVar::new(cs.clone(), &poseidon_config);
        let instance_var = CommittedInstanceVar::new_witness(cs.clone(), || Ok(instance))?;
        let instances_var = Vec::new_witness(cs.clone(), || Ok(instances))?;
        let F_coeffs_var = Vec::new_witness(cs.clone(), || Ok(F_coeffs))?;
        let K_coeffs_var = Vec::new_witness(cs.clone(), || Ok(K_coeffs))?;

        let folded_instance_var = FoldingGadget::fold_committed_instance(
            &mut transcript_var,
            &instance_var,
            &instances_var,
            F_coeffs_var,
            K_coeffs_var,
        )?;
        assert_eq!(folded_instance.betas, folded_instance_var.betas.value()?);
        assert_eq!(folded_instance.e, folded_instance_var.e.value()?);
        assert_eq!(folded_instance.u, folded_instance_var.u.value()?);
        assert_eq!(folded_instance.x, folded_instance_var.x.value()?);
        assert!(cs.is_satisfied()?);

        Ok(())
    }
}
