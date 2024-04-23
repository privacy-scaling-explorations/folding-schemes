use ark_crypto_primitives::sponge::Absorb;
use ark_ec::{CurveGroup, Group};
use ark_ff::{BigInteger, Field, PrimeField};
use ark_poly::univariate::DensePolynomial;
use ark_poly::{DenseUVPolynomial, Polynomial};
use ark_std::{One, Zero};

use super::{
    cccs::CCCS,
    lcccs::LCCCS,
    utils::{compute_c, compute_g, compute_sigmas_thetas},
    Witness,
};
use crate::ccs::CCS;
use crate::constants::N_BITS_RO;
use crate::folding::circuits::nonnative::affine::nonnative_affine_to_field_elements;
use crate::transcript::Transcript;
use crate::utils::sum_check::structs::{IOPProof as SumCheckProof, IOPProverMessage};
use crate::utils::sum_check::{IOPSumCheck, SumCheck};
use crate::utils::virtual_polynomial::VPAuxInfo;
use crate::Error;

use std::fmt::Debug;
use std::marker::PhantomData;

/// NIMFSProof defines a multifolding proof
#[derive(Clone, Debug)]
pub struct NIMFSProof<C: CurveGroup> {
    pub sc_proof: SumCheckProof<C::ScalarField>,
    pub sigmas_thetas: SigmasThetas<C::ScalarField>,
}

impl<C: CurveGroup> NIMFSProof<C> {
    pub fn dummy(ccs: &CCS<C::ScalarField>, mu: usize, nu: usize) -> Self {
        NIMFSProof::<C> {
            sc_proof: SumCheckProof::<C::ScalarField> {
                point: vec![C::ScalarField::zero(); ccs.d],
                proofs: vec![
                    IOPProverMessage {
                        coeffs: vec![C::ScalarField::zero(); ccs.t + 1]
                    };
                    ccs.s
                ],
            },
            sigmas_thetas: SigmasThetas(
                vec![vec![C::ScalarField::zero(); ccs.t]; mu],
                vec![vec![C::ScalarField::zero(); ccs.t]; nu],
            ),
        }
    }
}

#[derive(Clone, Debug)]
pub struct SigmasThetas<F: PrimeField>(pub Vec<Vec<F>>, pub Vec<Vec<F>>);

#[derive(Debug)]
/// Implements the Non-Interactive Multi Folding Scheme described in section 5 of
/// [HyperNova](https://eprint.iacr.org/2023/573.pdf)
pub struct NIMFS<C: CurveGroup, T: Transcript<C::ScalarField>> {
    pub _c: PhantomData<C>,
    pub _t: PhantomData<T>,
}

impl<C: CurveGroup, T: Transcript<C::ScalarField>> NIMFS<C, T>
where
    <C as Group>::ScalarField: Absorb,
    C::BaseField: PrimeField,
{
    pub fn fold(
        lcccs: &[LCCCS<C>],
        cccs: &[CCCS<C>],
        sigmas_thetas: &SigmasThetas<C::ScalarField>,
        r_x_prime: Vec<C::ScalarField>,
        rho: C::ScalarField,
    ) -> LCCCS<C> {
        let (sigmas, thetas) = (sigmas_thetas.0.clone(), sigmas_thetas.1.clone());
        let mut C_folded = C::zero();
        let mut u_folded = C::ScalarField::zero();
        let mut x_folded: Vec<C::ScalarField> = vec![C::ScalarField::zero(); lcccs[0].x.len()];
        let mut v_folded: Vec<C::ScalarField> = vec![C::ScalarField::zero(); sigmas[0].len()];

        let mut rho_i = C::ScalarField::one();
        for i in 0..(lcccs.len() + cccs.len()) {
            let c: C;
            let u: C::ScalarField;
            let x: Vec<C::ScalarField>;
            let v: Vec<C::ScalarField>;
            if i < lcccs.len() {
                c = lcccs[i].C;
                u = lcccs[i].u;
                x = lcccs[i].x.clone();
                v = sigmas[i].clone();
            } else {
                c = cccs[i - lcccs.len()].C;
                u = C::ScalarField::one();
                x = cccs[i - lcccs.len()].x.clone();
                v = thetas[i - lcccs.len()].clone();
            }

            C_folded += c.mul(rho_i);
            u_folded += rho_i * u;
            x_folded = x_folded
                .iter()
                .zip(
                    x.iter()
                        .map(|x_i| *x_i * rho_i)
                        .collect::<Vec<C::ScalarField>>(),
                )
                .map(|(a_i, b_i)| *a_i + b_i)
                .collect();

            v_folded = v_folded
                .iter()
                .zip(
                    v.iter()
                        .map(|x_i| *x_i * rho_i)
                        .collect::<Vec<C::ScalarField>>(),
                )
                .map(|(a_i, b_i)| *a_i + b_i)
                .collect();

            rho_i *= rho;
        }

        LCCCS::<C> {
            C: C_folded,
            u: u_folded,
            x: x_folded,
            r_x: r_x_prime,
            v: v_folded,
        }
    }

    pub fn fold_witness(
        w_lcccs: &[Witness<C::ScalarField>],
        w_cccs: &[Witness<C::ScalarField>],
        rho: C::ScalarField,
    ) -> Witness<C::ScalarField> {
        let mut w_folded: Vec<C::ScalarField> = vec![C::ScalarField::zero(); w_lcccs[0].w.len()];
        let mut r_w_folded = C::ScalarField::zero();

        for i in 0..(w_lcccs.len() + w_cccs.len()) {
            let rho_i = rho.pow([i as u64]);
            let w: Vec<C::ScalarField>;
            let r_w: C::ScalarField;

            if i < w_lcccs.len() {
                w = w_lcccs[i].w.clone();
                r_w = w_lcccs[i].r_w;
            } else {
                w = w_cccs[i - w_lcccs.len()].w.clone();
                r_w = w_cccs[i - w_lcccs.len()].r_w;
            }

            w_folded = w_folded
                .iter()
                .zip(
                    w.iter()
                        .map(|x_i| *x_i * rho_i)
                        .collect::<Vec<C::ScalarField>>(),
                )
                .map(|(a_i, b_i)| *a_i + b_i)
                .collect();

            r_w_folded += rho_i * r_w;
        }
        Witness {
            w: w_folded,
            r_w: r_w_folded,
        }
    }

    /// Performs the multifolding prover. Given μ LCCCS instances and ν CCS instances, fold them
    /// into a single LCCCS instance. Since this is the prover, also fold their witness.
    /// Returns the final folded LCCCS, the folded witness, and the multifolding proof, which
    /// contains the sumcheck proof and the helper sumcheck claim sigmas and thetas.
    #[allow(clippy::type_complexity)]
    pub fn prove(
        transcript: &mut impl Transcript<C::ScalarField>,
        ccs: &CCS<C::ScalarField>,
        running_instances: &[LCCCS<C>],
        new_instances: &[CCCS<C>],
        w_lcccs: &[Witness<C::ScalarField>],
        w_cccs: &[Witness<C::ScalarField>],
    ) -> Result<(NIMFSProof<C>, LCCCS<C>, Witness<C::ScalarField>, Vec<bool>), Error> {
        // absorb instances to transcript
        for U_i in running_instances {
            let (C_x, C_y) = nonnative_affine_to_field_elements::<C>(U_i.C)?;
            let v = [
                C_x,
                C_y,
                vec![U_i.u],
                U_i.x.clone(),
                U_i.r_x.clone(),
                U_i.v.clone(),
            ]
            .concat();
            transcript.absorb(&v);
        }
        for u_i in new_instances {
            let (C_x, C_y) = nonnative_affine_to_field_elements::<C>(u_i.C)?;
            let v = [C_x, C_y, u_i.x.clone()].concat();
            transcript.absorb(&v);
        }

        if running_instances.is_empty() {
            return Err(Error::Empty);
        }
        if new_instances.is_empty() {
            return Err(Error::Empty);
        }

        // construct the LCCCS z vector from the relaxation factor, public IO and witness
        let mut z_lcccs = Vec::new();
        for (i, running_instance) in running_instances.iter().enumerate() {
            let z_1: Vec<C::ScalarField> = [
                vec![running_instance.u],
                running_instance.x.clone(),
                w_lcccs[i].w.to_vec(),
            ]
            .concat();
            z_lcccs.push(z_1);
        }
        // construct the CCCS z vector from the public IO and witness
        let mut z_cccs = Vec::new();
        for (i, new_instance) in new_instances.iter().enumerate() {
            let z_2: Vec<C::ScalarField> = [
                vec![C::ScalarField::one()],
                new_instance.x.clone(),
                w_cccs[i].w.to_vec(),
            ]
            .concat();
            z_cccs.push(z_2);
        }

        // Step 1: Get some challenges
        let gamma_scalar = C::ScalarField::from_le_bytes_mod_order(b"gamma");
        let beta_scalar = C::ScalarField::from_le_bytes_mod_order(b"beta");
        transcript.absorb(&gamma_scalar);
        let gamma: C::ScalarField = transcript.get_challenge();
        transcript.absorb(&beta_scalar);
        let beta: Vec<C::ScalarField> = transcript.get_challenges(ccs.s);

        // Compute g(x)
        let g = compute_g(ccs, running_instances, &z_lcccs, &z_cccs, gamma, &beta)?;

        // Step 3: Run the sumcheck prover
        let sumcheck_proof = IOPSumCheck::<C::ScalarField, T>::prove(&g, transcript)
            .map_err(|err| Error::SumCheckProveError(err.to_string()))?;

        // Step 2: dig into the sumcheck and extract r_x_prime
        let r_x_prime = sumcheck_proof.point.clone();

        // Step 4: compute sigmas and thetas
        let sigmas_thetas = compute_sigmas_thetas(ccs, &z_lcccs, &z_cccs, &r_x_prime)?;

        // Step 6: Get the folding challenge
        let rho_scalar = C::ScalarField::from_le_bytes_mod_order(b"rho");
        transcript.absorb(&rho_scalar);
        let rho_bits: Vec<bool> = transcript.get_challenge_nbits(N_BITS_RO);
        let rho: C::ScalarField =
            C::ScalarField::from_bigint(BigInteger::from_bits_le(&rho_bits)).unwrap();

        // Step 7: Create the folded instance
        let folded_lcccs = Self::fold(
            running_instances,
            new_instances,
            &sigmas_thetas,
            r_x_prime,
            rho,
        );

        // Step 8: Fold the witnesses
        let folded_witness = Self::fold_witness(w_lcccs, w_cccs, rho);

        Ok((
            NIMFSProof::<C> {
                sc_proof: sumcheck_proof,
                sigmas_thetas,
            },
            folded_lcccs,
            folded_witness,
            rho_bits,
        ))
    }

    /// Performs the multifolding verifier. Given μ LCCCS instances and ν CCS instances, fold them
    /// into a single LCCCS instance.
    /// Returns the folded LCCCS instance.
    pub fn verify(
        transcript: &mut impl Transcript<C::ScalarField>,
        ccs: &CCS<C::ScalarField>,
        running_instances: &[LCCCS<C>],
        new_instances: &[CCCS<C>],
        proof: NIMFSProof<C>,
    ) -> Result<LCCCS<C>, Error> {
        // absorb instances to transcript
        for U_i in running_instances {
            let (C_x, C_y) = nonnative_affine_to_field_elements::<C>(U_i.C)?;
            let v = [
                C_x,
                C_y,
                vec![U_i.u],
                U_i.x.clone(),
                U_i.r_x.clone(),
                U_i.v.clone(),
            ]
            .concat();
            transcript.absorb(&v);
        }
        for u_i in new_instances {
            let (C_x, C_y) = nonnative_affine_to_field_elements::<C>(u_i.C)?;
            let v = [C_x, C_y, u_i.x.clone()].concat();
            transcript.absorb(&v);
        }

        if running_instances.is_empty() {
            return Err(Error::Empty);
        }
        if new_instances.is_empty() {
            return Err(Error::Empty);
        }

        // Step 1: Get some challenges
        let gamma_scalar = C::ScalarField::from_le_bytes_mod_order(b"gamma");
        transcript.absorb(&gamma_scalar);
        let gamma: C::ScalarField = transcript.get_challenge();

        let beta_scalar = C::ScalarField::from_le_bytes_mod_order(b"beta");
        transcript.absorb(&beta_scalar);
        let beta: Vec<C::ScalarField> = transcript.get_challenges(ccs.s);

        let vp_aux_info = VPAuxInfo::<C::ScalarField> {
            max_degree: ccs.d + 1,
            num_variables: ccs.s,
            phantom: PhantomData::<C::ScalarField>,
        };

        // Step 3: Start verifying the sumcheck
        // First, compute the expected sumcheck sum: \sum gamma^j v_j
        let mut sum_v_j_gamma = C::ScalarField::zero();
        for (i, running_instance) in running_instances.iter().enumerate() {
            for j in 0..running_instance.v.len() {
                let gamma_j = gamma.pow([(i * ccs.t + j) as u64]);
                sum_v_j_gamma += running_instance.v[j] * gamma_j;
            }
        }

        // Verify the interactive part of the sumcheck
        let sumcheck_subclaim = IOPSumCheck::<C::ScalarField, T>::verify(
            sum_v_j_gamma,
            &proof.sc_proof,
            &vp_aux_info,
            transcript,
        )
        .map_err(|err| Error::SumCheckVerifyError(err.to_string()))?;

        // Step 2: Dig into the sumcheck claim and extract the randomness used
        let r_x_prime = sumcheck_subclaim.point.clone();

        // Step 5: Finish verifying sumcheck (verify the claim c)
        let c = compute_c(
            ccs,
            &proof.sigmas_thetas,
            gamma,
            &beta,
            &running_instances
                .iter()
                .map(|lcccs| lcccs.r_x.clone())
                .collect(),
            &r_x_prime,
        )?;

        // check that the g(r_x') from the sumcheck proof is equal to the computed c from sigmas&thetas
        if c != sumcheck_subclaim.expected_evaluation {
            return Err(Error::NotEqual);
        }

        // Sanity check: we can also compute g(r_x') from the proof last evaluation value, and
        // should be equal to the previously obtained values.
        let g_on_rxprime_from_sumcheck_last_eval = DensePolynomial::from_coefficients_slice(
            &proof.sc_proof.proofs.last().ok_or(Error::Empty)?.coeffs,
        )
        .evaluate(r_x_prime.last().ok_or(Error::Empty)?);
        if g_on_rxprime_from_sumcheck_last_eval != c {
            return Err(Error::NotEqual);
        }
        if g_on_rxprime_from_sumcheck_last_eval != sumcheck_subclaim.expected_evaluation {
            return Err(Error::NotEqual);
        }

        // Step 6: Get the folding challenge
        let rho_scalar = C::ScalarField::from_le_bytes_mod_order(b"rho");
        transcript.absorb(&rho_scalar);
        let rho_bits: Vec<bool> = transcript.get_challenge_nbits(N_BITS_RO);
        let rho: C::ScalarField =
            C::ScalarField::from_bigint(BigInteger::from_bits_le(&rho_bits)).unwrap();

        // Step 7: Compute the folded instance
        Ok(Self::fold(
            running_instances,
            new_instances,
            &proof.sigmas_thetas,
            r_x_prime,
            rho,
        ))
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use crate::ccs::tests::{get_test_ccs, get_test_z};
    use crate::transcript::poseidon::poseidon_canonical_config;
    use ark_crypto_primitives::sponge::poseidon::PoseidonSponge;
    use ark_crypto_primitives::sponge::CryptographicSponge;
    use ark_std::test_rng;
    use ark_std::UniformRand;

    use crate::commitment::{pedersen::Pedersen, CommitmentScheme};
    use ark_pallas::{Fr, Projective};

    #[test]
    fn test_fold() {
        let ccs = get_test_ccs();
        let z1 = get_test_z::<Fr>(3);
        let z2 = get_test_z::<Fr>(4);
        ccs.check_relation(&z1).unwrap();
        ccs.check_relation(&z2).unwrap();

        let mut rng = test_rng();
        let r_x_prime: Vec<Fr> = (0..ccs.s).map(|_| Fr::rand(&mut rng)).collect();

        let sigmas_thetas =
            compute_sigmas_thetas(&ccs, &[z1.clone()], &[z2.clone()], &r_x_prime).unwrap();

        let (pedersen_params, _) =
            Pedersen::<Projective>::setup(&mut rng, ccs.n - ccs.l - 1).unwrap();

        let (lcccs, w1) = ccs.to_lcccs(&mut rng, &pedersen_params, &z1).unwrap();
        let (cccs, w2) = ccs.to_cccs(&mut rng, &pedersen_params, &z2).unwrap();

        lcccs.check_relation(&pedersen_params, &ccs, &w1).unwrap();
        cccs.check_relation(&pedersen_params, &ccs, &w2).unwrap();

        let mut rng = test_rng();
        let rho = Fr::rand(&mut rng);

        let folded = NIMFS::<Projective, PoseidonSponge<Fr>>::fold(
            &[lcccs],
            &[cccs],
            &sigmas_thetas,
            r_x_prime,
            rho,
        );

        let w_folded = NIMFS::<Projective, PoseidonSponge<Fr>>::fold_witness(&[w1], &[w2], rho);

        // check lcccs relation
        folded
            .check_relation(&pedersen_params, &ccs, &w_folded)
            .unwrap();
    }

    /// Perform multifolding of an LCCCS instance with a CCCS instance (as described in the paper)
    #[test]
    pub fn test_basic_multifolding() {
        let mut rng = test_rng();

        // Create a basic CCS circuit
        let ccs = get_test_ccs::<Fr>();
        let (pedersen_params, _) =
            Pedersen::<Projective>::setup(&mut rng, ccs.n - ccs.l - 1).unwrap();

        // Generate a satisfying witness
        let z_1 = get_test_z(3);
        // Generate another satisfying witness
        let z_2 = get_test_z(4);

        // Create the LCCCS instance out of z_1
        let (running_instance, w1) = ccs.to_lcccs(&mut rng, &pedersen_params, &z_1).unwrap();
        // Create the CCCS instance out of z_2
        let (new_instance, w2) = ccs.to_cccs(&mut rng, &pedersen_params, &z_2).unwrap();

        // Prover's transcript
        let poseidon_config = poseidon_canonical_config::<Fr>();
        let mut transcript_p: PoseidonSponge<Fr> = PoseidonSponge::<Fr>::new(&poseidon_config);
        transcript_p.absorb(&Fr::from_le_bytes_mod_order(b"init init"));

        // Run the prover side of the multifolding
        let (proof, folded_lcccs, folded_witness, _) =
            NIMFS::<Projective, PoseidonSponge<Fr>>::prove(
                &mut transcript_p,
                &ccs,
                &[running_instance.clone()],
                &[new_instance.clone()],
                &[w1],
                &[w2],
            )
            .unwrap();

        // Verifier's transcript
        let mut transcript_v: PoseidonSponge<Fr> = PoseidonSponge::<Fr>::new(&poseidon_config);
        transcript_v.absorb(&Fr::from_le_bytes_mod_order(b"init init"));

        // Run the verifier side of the multifolding
        let folded_lcccs_v = NIMFS::<Projective, PoseidonSponge<Fr>>::verify(
            &mut transcript_v,
            &ccs,
            &[running_instance.clone()],
            &[new_instance.clone()],
            proof,
        )
        .unwrap();
        assert_eq!(folded_lcccs, folded_lcccs_v);

        // Check that the folded LCCCS instance is a valid instance with respect to the folded witness
        folded_lcccs
            .check_relation(&pedersen_params, &ccs, &folded_witness)
            .unwrap();
    }

    /// Perform multiple steps of multifolding of an LCCCS instance with a CCCS instance
    #[test]
    pub fn test_multifolding_two_instances_multiple_steps() {
        let mut rng = test_rng();

        let ccs = get_test_ccs::<Fr>();

        let (pedersen_params, _) =
            Pedersen::<Projective>::setup(&mut rng, ccs.n - ccs.l - 1).unwrap();

        // LCCCS witness
        let z_1 = get_test_z(2);
        let (mut running_instance, mut w1) =
            ccs.to_lcccs(&mut rng, &pedersen_params, &z_1).unwrap();

        let poseidon_config = poseidon_canonical_config::<Fr>();

        let mut transcript_p: PoseidonSponge<Fr> = PoseidonSponge::<Fr>::new(&poseidon_config);
        transcript_p.absorb(&Fr::from_le_bytes_mod_order(b"init init"));

        let mut transcript_v: PoseidonSponge<Fr> = PoseidonSponge::<Fr>::new(&poseidon_config);
        transcript_v.absorb(&Fr::from_le_bytes_mod_order(b"init init"));

        let n: usize = 10;
        for i in 3..n {
            // CCS witness
            let z_2 = get_test_z(i);

            let (new_instance, w2) = ccs.to_cccs(&mut rng, &pedersen_params, &z_2).unwrap();

            // run the prover side of the multifolding
            let (proof, folded_lcccs, folded_witness, _) =
                NIMFS::<Projective, PoseidonSponge<Fr>>::prove(
                    &mut transcript_p,
                    &ccs,
                    &[running_instance.clone()],
                    &[new_instance.clone()],
                    &[w1],
                    &[w2],
                )
                .unwrap();

            // run the verifier side of the multifolding
            let folded_lcccs_v = NIMFS::<Projective, PoseidonSponge<Fr>>::verify(
                &mut transcript_v,
                &ccs,
                &[running_instance.clone()],
                &[new_instance.clone()],
                proof,
            )
            .unwrap();
            assert_eq!(folded_lcccs, folded_lcccs_v);

            // check that the folded instance with the folded witness holds the LCCCS relation
            folded_lcccs
                .check_relation(&pedersen_params, &ccs, &folded_witness)
                .unwrap();

            running_instance = folded_lcccs;
            w1 = folded_witness;
        }
    }

    /// Test that generates mu>1 and nu>1 instances, and folds them in a single multifolding step.
    #[test]
    pub fn test_multifolding_mu_nu_instances() {
        let mut rng = test_rng();

        // Create a basic CCS circuit
        let ccs = get_test_ccs::<Fr>();
        let (pedersen_params, _) =
            Pedersen::<Projective>::setup(&mut rng, ccs.n - ccs.l - 1).unwrap();

        let mu = 10;
        let nu = 15;

        // Generate a mu LCCCS & nu CCCS satisfying witness
        let mut z_lcccs = Vec::new();
        for i in 0..mu {
            let z = get_test_z(i + 3);
            z_lcccs.push(z);
        }
        let mut z_cccs = Vec::new();
        for i in 0..nu {
            let z = get_test_z(nu + i + 3);
            z_cccs.push(z);
        }

        // Create the LCCCS instances out of z_lcccs
        let mut lcccs_instances = Vec::new();
        let mut w_lcccs = Vec::new();
        for z_i in z_lcccs.iter() {
            let (running_instance, w) = ccs.to_lcccs(&mut rng, &pedersen_params, z_i).unwrap();
            lcccs_instances.push(running_instance);
            w_lcccs.push(w);
        }
        // Create the CCCS instance out of z_cccs
        let mut cccs_instances = Vec::new();
        let mut w_cccs = Vec::new();
        for z_i in z_cccs.iter() {
            let (new_instance, w) = ccs.to_cccs(&mut rng, &pedersen_params, z_i).unwrap();
            cccs_instances.push(new_instance);
            w_cccs.push(w);
        }

        // Prover's transcript
        let poseidon_config = poseidon_canonical_config::<Fr>();
        let mut transcript_p: PoseidonSponge<Fr> = PoseidonSponge::<Fr>::new(&poseidon_config);
        transcript_p.absorb(&Fr::from_le_bytes_mod_order(b"init init"));

        // Run the prover side of the multifolding
        let (proof, folded_lcccs, folded_witness, _) =
            NIMFS::<Projective, PoseidonSponge<Fr>>::prove(
                &mut transcript_p,
                &ccs,
                &lcccs_instances,
                &cccs_instances,
                &w_lcccs,
                &w_cccs,
            )
            .unwrap();

        // Verifier's transcript
        let mut transcript_v: PoseidonSponge<Fr> = PoseidonSponge::<Fr>::new(&poseidon_config);
        transcript_v.absorb(&Fr::from_le_bytes_mod_order(b"init init"));

        // Run the verifier side of the multifolding
        let folded_lcccs_v = NIMFS::<Projective, PoseidonSponge<Fr>>::verify(
            &mut transcript_v,
            &ccs,
            &lcccs_instances,
            &cccs_instances,
            proof,
        )
        .unwrap();
        assert_eq!(folded_lcccs, folded_lcccs_v);

        // Check that the folded LCCCS instance is a valid instance with respect to the folded witness
        folded_lcccs
            .check_relation(&pedersen_params, &ccs, &folded_witness)
            .unwrap();
    }

    /// Test that generates mu>1 and nu>1 instances, and folds them in a single multifolding step
    /// and repeats the process doing multiple steps.
    #[test]
    pub fn test_multifolding_mu_nu_instances_multiple_steps() {
        let mut rng = test_rng();

        // Create a basic CCS circuit
        let ccs = get_test_ccs::<Fr>();
        let (pedersen_params, _) =
            Pedersen::<Projective>::setup(&mut rng, ccs.n - ccs.l - 1).unwrap();

        let poseidon_config = poseidon_canonical_config::<Fr>();
        // Prover's transcript
        let mut transcript_p: PoseidonSponge<Fr> = PoseidonSponge::<Fr>::new(&poseidon_config);
        transcript_p.absorb(&Fr::from_le_bytes_mod_order(b"init init"));

        // Verifier's transcript
        let mut transcript_v: PoseidonSponge<Fr> = PoseidonSponge::<Fr>::new(&poseidon_config);
        transcript_v.absorb(&Fr::from_le_bytes_mod_order(b"init init"));

        let n_steps = 3;

        // number of LCCCS & CCCS instances in each multifolding step
        let mu = 10;
        let nu = 15;

        // Generate a mu LCCCS & nu CCCS satisfying witness, for each step
        for step in 0..n_steps {
            let mut z_lcccs = Vec::new();
            for i in 0..mu {
                let z = get_test_z(step + i + 3);
                z_lcccs.push(z);
            }
            let mut z_cccs = Vec::new();
            for i in 0..nu {
                let z = get_test_z(nu + i + 3);
                z_cccs.push(z);
            }

            // Create the LCCCS instances out of z_lcccs
            let mut lcccs_instances = Vec::new();
            let mut w_lcccs = Vec::new();
            for z_i in z_lcccs.iter() {
                let (running_instance, w) = ccs.to_lcccs(&mut rng, &pedersen_params, z_i).unwrap();
                lcccs_instances.push(running_instance);
                w_lcccs.push(w);
            }
            // Create the CCCS instance out of z_cccs
            let mut cccs_instances = Vec::new();
            let mut w_cccs = Vec::new();
            for z_i in z_cccs.iter() {
                let (new_instance, w) = ccs.to_cccs(&mut rng, &pedersen_params, z_i).unwrap();
                cccs_instances.push(new_instance);
                w_cccs.push(w);
            }

            // Run the prover side of the multifolding
            let (proof, folded_lcccs, folded_witness, _) =
                NIMFS::<Projective, PoseidonSponge<Fr>>::prove(
                    &mut transcript_p,
                    &ccs,
                    &lcccs_instances,
                    &cccs_instances,
                    &w_lcccs,
                    &w_cccs,
                )
                .unwrap();

            // Run the verifier side of the multifolding
            let folded_lcccs_v = NIMFS::<Projective, PoseidonSponge<Fr>>::verify(
                &mut transcript_v,
                &ccs,
                &lcccs_instances,
                &cccs_instances,
                proof,
            )
            .unwrap();

            assert_eq!(folded_lcccs, folded_lcccs_v);

            // Check that the folded LCCCS instance is a valid instance with respect to the folded witness
            folded_lcccs
                .check_relation(&pedersen_params, &ccs, &folded_witness)
                .unwrap();
        }
    }
}
