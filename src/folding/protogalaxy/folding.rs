/// Implements the scheme described in [ProtoGalaxy](https://eprint.iacr.org/2023/1106.pdf)
use ark_crypto_primitives::sponge::Absorb;
use ark_ec::{CurveGroup, Group};
use ark_ff::PrimeField;
use ark_poly::{
    univariate::{DensePolynomial, SparsePolynomial},
    DenseUVPolynomial, EvaluationDomain, Evaluations, GeneralEvaluationDomain, Polynomial,
};
use ark_std::log2;
use ark_std::{cfg_into_iter, Zero};
use rayon::iter::{IntoParallelIterator, ParallelIterator};
use std::marker::PhantomData;

use super::traits::ProtoGalaxyTranscript;
use super::utils::{all_powers, betas_star, exponential_powers};
use super::ProtoGalaxyError;
use super::{CommittedInstance, Witness};

use crate::ccs::r1cs::R1CS;
use crate::transcript::Transcript;
use crate::utils::{bit::bit_decompose, vec::*};
use crate::Error;

#[derive(Clone, Debug)]
/// Implements the protocol described in section 4 of
/// [ProtoGalaxy](https://eprint.iacr.org/2023/1106.pdf)
pub struct Folding<C: CurveGroup> {
    _phantom: PhantomData<C>,
}
impl<C: CurveGroup> Folding<C>
where
    <C as Group>::ScalarField: Absorb,
    <C as CurveGroup>::BaseField: Absorb,
{
    #![allow(clippy::type_complexity)]
    /// implements the non-interactive Prover from the folding scheme described in section 4
    pub fn prove(
        transcript: &mut (impl Transcript<C> + ProtoGalaxyTranscript<C>),
        r1cs: &R1CS<C::ScalarField>,
        // running instance
        instance: &CommittedInstance<C>,
        w: &Witness<C::ScalarField>,
        // incomming instances
        vec_instances: &[CommittedInstance<C>],
        vec_w: &[Witness<C::ScalarField>],
    ) -> Result<
        (
            CommittedInstance<C>,
            Witness<C::ScalarField>,
            Vec<C::ScalarField>, // F_X coeffs
            Vec<C::ScalarField>, // K_X coeffs
        ),
        Error,
    > {
        if vec_instances.len() != vec_w.len() {
            return Err(Error::NotSameLength(
                "vec_instances.len()".to_string(),
                vec_instances.len(),
                "vec_w.len()".to_string(),
                vec_w.len(),
            ));
        }
        let d = 2; // for the moment hardcoded to 2 since it only supports R1CS
        let k = vec_instances.len();
        let t = instance.betas.len();
        let n = r1cs.A.n_cols;
        if w.w.len() != n {
            return Err(Error::NotSameLength(
                "w.w.len()".to_string(),
                w.w.len(),
                "n".to_string(),
                n,
            ));
        }
        if log2(n) as usize != t {
            return Err(Error::NotEqual);
        }
        if !(k + 1).is_power_of_two() {
            return Err(Error::ProtoGalaxy(ProtoGalaxyError::WrongNumInstances(k)));
        }

        // absorb the committed instances
        transcript.absorb_committed_instance(instance)?;
        for ci in vec_instances.iter() {
            transcript.absorb_committed_instance(ci)?;
        }

        let delta = transcript.get_challenge();
        let deltas = exponential_powers(delta, t);

        let f_w = eval_f(r1cs, &w.w)?;

        // F(X)
        let F_X: SparsePolynomial<C::ScalarField> =
            calc_f_from_btree(&f_w, &instance.betas, &deltas);
        let F_X_dense = DensePolynomial::from(F_X.clone());
        transcript.absorb_vec(&F_X_dense.coeffs);

        let alpha = transcript.get_challenge();

        // eval F(alpha)
        let F_alpha = F_X.evaluate(&alpha);

        // betas*
        let betas_star = betas_star(&instance.betas, &deltas, alpha);

        // sanity check: check that the new randomized instance (the original instance but with
        // 'refreshed' randomness) satisfies the relation.
        #[cfg(test)]
        tests::check_instance(
            r1cs,
            &CommittedInstance {
                phi: instance.phi,
                betas: betas_star.clone(),
                e: F_alpha,
            },
            w,
        )?;

        let ws: Vec<Vec<C::ScalarField>> = std::iter::once(w.w.clone())
            .chain(
                vec_w
                    .iter()
                    .map(|wj| {
                        if wj.w.len() != n {
                            return Err(Error::NotSameLength(
                                "wj.w.len()".to_string(),
                                wj.w.len(),
                                "n".to_string(),
                                n,
                            ));
                        }
                        Ok(wj.w.clone())
                    })
                    .collect::<Result<Vec<Vec<C::ScalarField>>, Error>>()?,
            )
            .collect::<Vec<Vec<C::ScalarField>>>();

        let H =
            GeneralEvaluationDomain::<C::ScalarField>::new(k + 1).ok_or(Error::NewDomainFail)?;
        let G_domain = GeneralEvaluationDomain::<C::ScalarField>::new((d * k) + 1)
            .ok_or(Error::NewDomainFail)?;
        let L_X: Vec<DensePolynomial<C::ScalarField>> = lagrange_polys(H);

        // K(X) computation in a naive way, next iterations will compute K(X) as described in Claim
        // 4.5 of the paper.
        let mut G_evals: Vec<C::ScalarField> = vec![C::ScalarField::zero(); G_domain.size()];
        for (hi, h) in G_domain.elements().enumerate() {
            // each iteration evaluates G(h)
            // inner = L_0(x) * w + \sum_k L_i(x) * w_j
            let mut inner: Vec<C::ScalarField> = vec![C::ScalarField::zero(); ws[0].len()];
            for (i, w) in ws.iter().enumerate() {
                // Li_w_h = (Li(X)*wj)(h) = Li(h) * wj
                let mut Liw_h: Vec<C::ScalarField> = vec![C::ScalarField::zero(); w.len()];
                for (j, wj) in w.iter().enumerate() {
                    Liw_h[j] = (&L_X[i] * *wj).evaluate(&h);
                }

                for j in 0..inner.len() {
                    inner[j] += Liw_h[j];
                }
            }
            let f_ev = eval_f(r1cs, &inner)?;

            let mut Gsum = C::ScalarField::zero();
            for (i, f_ev_i) in f_ev.iter().enumerate() {
                let pow_i_betas = pow_i(i, &betas_star);
                let curr = pow_i_betas * f_ev_i;
                Gsum += curr;
            }
            G_evals[hi] = Gsum;
        }
        let G_X: DensePolynomial<C::ScalarField> =
            Evaluations::<C::ScalarField>::from_vec_and_domain(G_evals, G_domain).interpolate();
        let Z_X: DensePolynomial<C::ScalarField> = H.vanishing_polynomial().into();
        // K(X) = (G(X) - F(alpha)*L_0(X)) / Z(X)
        // Notice that L0(X)*F(a) will be 0 in the native case (the instance of the first folding
        // iteration case).
        let L0_e = &L_X[0] * F_alpha;
        let G_L0e = &G_X - &L0_e;
        // Pending optimization: move division by Z_X to the prev loop
        let (K_X, remainder) = G_L0e.divide_by_vanishing_poly(H).ok_or(Error::ProtoGalaxy(
            ProtoGalaxyError::CouldNotDivideByVanishing,
        ))?;
        if !remainder.is_zero() {
            return Err(Error::ProtoGalaxy(ProtoGalaxyError::RemainderNotZero));
        }

        transcript.absorb_vec(&K_X.coeffs);

        let gamma = transcript.get_challenge();

        let e_star =
            F_alpha * L_X[0].evaluate(&gamma) + Z_X.evaluate(&gamma) * K_X.evaluate(&gamma);

        let mut phi_star: C = instance.phi * L_X[0].evaluate(&gamma);
        for i in 0..k {
            phi_star += vec_instances[i].phi * L_X[i + 1].evaluate(&gamma);
        }
        let mut w_star: Vec<C::ScalarField> = vec_scalar_mul(&w.w, &L_X[0].evaluate(&gamma));
        let mut r_w_star: C::ScalarField = w.r_w * L_X[0].evaluate(&gamma);
        for i in 0..k {
            let L_X_at_i1 = L_X[i + 1].evaluate(&gamma);
            w_star = vec_add(&w_star, &vec_scalar_mul(&vec_w[i].w, &L_X_at_i1))?;
            r_w_star += vec_w[i].r_w * L_X_at_i1;
        }

        Ok((
            CommittedInstance {
                betas: betas_star,
                phi: phi_star,
                e: e_star,
            },
            Witness {
                w: w_star,
                r_w: r_w_star,
            },
            F_X_dense.coeffs,
            K_X.coeffs,
        ))
    }

    /// implements the non-interactive Verifier from the folding scheme described in section 4
    pub fn verify(
        transcript: &mut (impl Transcript<C> + ProtoGalaxyTranscript<C>),
        r1cs: &R1CS<C::ScalarField>,
        // running instance
        instance: &CommittedInstance<C>,
        // incomming instances
        vec_instances: &[CommittedInstance<C>],
        // polys from P
        F_coeffs: Vec<C::ScalarField>,
        K_coeffs: Vec<C::ScalarField>,
    ) -> Result<CommittedInstance<C>, Error> {
        let t = instance.betas.len();
        let n = r1cs.A.n_cols;

        // absorb the committed instances
        transcript.absorb_committed_instance(instance)?;
        for ci in vec_instances.iter() {
            transcript.absorb_committed_instance(ci)?;
        }

        let delta = transcript.get_challenge();
        let deltas = exponential_powers(delta, t);

        transcript.absorb_vec(&F_coeffs);

        let alpha = transcript.get_challenge();
        let alphas = all_powers(alpha, n);

        // F(alpha) = e + \sum_t F_i * alpha^i
        let mut F_alpha = instance.e;
        for (i, F_i) in F_coeffs.iter().skip(1).enumerate() {
            F_alpha += *F_i * alphas[i + 1];
        }

        let betas_star = betas_star(&instance.betas, &deltas, alpha);

        let k = vec_instances.len();
        let H =
            GeneralEvaluationDomain::<C::ScalarField>::new(k + 1).ok_or(Error::NewDomainFail)?;
        let L_X: Vec<DensePolynomial<C::ScalarField>> = lagrange_polys(H);
        let Z_X: DensePolynomial<C::ScalarField> = H.vanishing_polynomial().into();
        let K_X: DensePolynomial<C::ScalarField> =
            DensePolynomial::<C::ScalarField>::from_coefficients_vec(K_coeffs);

        transcript.absorb_vec(&K_X.coeffs);

        let gamma = transcript.get_challenge();

        let e_star =
            F_alpha * L_X[0].evaluate(&gamma) + Z_X.evaluate(&gamma) * K_X.evaluate(&gamma);

        let mut phi_star: C = instance.phi * L_X[0].evaluate(&gamma);
        for i in 0..k {
            phi_star += vec_instances[i].phi * L_X[i + 1].evaluate(&gamma);
        }

        // return the folded instance
        Ok(CommittedInstance {
            betas: betas_star,
            phi: phi_star,
            e: e_star,
        })
    }
}

// naive impl of pow_i for betas, assuming that betas=(b, b^2, b^4, ..., b^{2^{t-1}})
fn pow_i<F: PrimeField>(i: usize, betas: &Vec<F>) -> F {
    // WIP check if makes more sense to do it with ifs instead of arithmetic

    let n = 2_u64.pow(betas.len() as u32);
    let b = bit_decompose(i as u64, n as usize);

    let mut r: F = F::one();
    for (j, beta_j) in betas.iter().enumerate() {
        let mut b_j = F::zero();
        if b[j] {
            b_j = F::one();
        }
        r *= (F::one() - b_j) + b_j * beta_j;
    }
    r
}

fn calc_f_from_btree<F: PrimeField>(fw: &[F], betas: &[F], deltas: &[F]) -> SparsePolynomial<F> {
    assert_eq!(fw.len() & (fw.len() - 1), 0);
    assert_eq!(betas.len(), deltas.len());
    let mut layers: Vec<Vec<SparsePolynomial<F>>> = Vec::new();
    let leaves: Vec<SparsePolynomial<F>> = fw
        .iter()
        .enumerate()
        .map(|e| SparsePolynomial::<F>::from_coefficients_slice(&[(0, *e.1)]))
        .collect();
    layers.push(leaves.to_vec());
    let mut currentNodes = leaves.clone();
    while currentNodes.len() > 1 {
        let index = layers.len();
        let limit: usize = (2 * currentNodes.len())
            - 2usize.pow(
                (currentNodes.len() & (currentNodes.len() - 1))
                    .try_into()
                    .unwrap(),
            );
        layers.push(vec![]);
        for (i, ni) in currentNodes.iter().enumerate().step_by(2) {
            if i >= limit {
                layers[index] = currentNodes[0..limit].to_vec();
                break;
            }
            let left = ni.clone();
            let right = SparsePolynomial::<F>::from_coefficients_vec(vec![
                (0, betas[layers.len() - 2]),  // FIXME
                (1, deltas[layers.len() - 2]), // FIXME
            ])
            .mul(&currentNodes[i + 1]);

            layers[index].push(left + right);
        }
        currentNodes = layers[index].clone();
    }
    let root_index = layers.len() - 1;
    layers[root_index][0].clone()
}

// lagrange_polys method from caulk: https://github.com/caulk-crypto/caulk/tree/8210b51fb8a9eef4335505d1695c44ddc7bf8170/src/multi/setup.rs#L300
fn lagrange_polys<F: PrimeField>(domain_n: GeneralEvaluationDomain<F>) -> Vec<DensePolynomial<F>> {
    let mut lagrange_polynomials: Vec<DensePolynomial<F>> = Vec::new();
    for i in 0..domain_n.size() {
        let evals: Vec<F> = cfg_into_iter!(0..domain_n.size())
            .map(|k| if k == i { F::one() } else { F::zero() })
            .collect();
        lagrange_polynomials.push(Evaluations::from_vec_and_domain(evals, domain_n).interpolate());
    }
    lagrange_polynomials
}

// f(w) in R1CS context. For the moment we use R1CS, in the future we will abstract this with a
// trait
fn eval_f<F: PrimeField>(r1cs: &R1CS<F>, w: &[F]) -> Result<Vec<F>, Error> {
    let Az = mat_vec_mul_sparse(&r1cs.A, w)?;
    let Bz = mat_vec_mul_sparse(&r1cs.B, w)?;
    let Cz = mat_vec_mul_sparse(&r1cs.C, w)?;
    let AzBz = hadamard(&Az, &Bz)?;
    vec_sub(&AzBz, &Cz)
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_pallas::{Fr, Projective};
    use ark_std::UniformRand;

    use crate::ccs::r1cs::tests::{get_test_r1cs, get_test_z};
    use crate::pedersen::Pedersen;
    use crate::transcript::poseidon::{tests::poseidon_test_config, PoseidonTranscript};

    pub(crate) fn check_instance<C: CurveGroup>(
        r1cs: &R1CS<C::ScalarField>,
        instance: &CommittedInstance<C>,
        w: &Witness<C::ScalarField>,
    ) -> Result<(), Error> {
        if instance.betas.len() != log2(w.w.len()) as usize {
            return Err(Error::NotSameLength(
                "instance.betas.len()".to_string(),
                instance.betas.len(),
                "log2(w.w.len())".to_string(),
                log2(w.w.len()) as usize,
            ));
        }

        let f_w = eval_f(r1cs, &w.w)?; // f(w)

        let mut r = C::ScalarField::zero();
        for (i, f_w_i) in f_w.iter().enumerate() {
            r += pow_i(i, &instance.betas) * f_w_i;
        }
        if instance.e == r {
            return Ok(());
        }
        Err(Error::NotSatisfied)
    }

    #[test]
    fn test_pow_i() {
        let mut rng = ark_std::test_rng();
        let t = 4;
        let n = 16;
        let beta = Fr::rand(&mut rng);
        let betas = exponential_powers(beta, t);
        let not_betas = all_powers(beta, n);

        #[allow(clippy::needless_range_loop)]
        for i in 0..n {
            assert_eq!(pow_i(i, &betas), not_betas[i]);
        }
    }


    #[test]
    fn test_eval_f() {
        let r1cs = get_test_r1cs::<Fr>();
        let mut z = get_test_z::<Fr>(3);

        let f_w = eval_f(&r1cs, &z).unwrap();
        assert!(is_zero_vec(&f_w));

        z[1] = Fr::from(111);
        let f_w = eval_f(&r1cs, &z).unwrap();
        assert!(!is_zero_vec(&f_w));
    }

    // k represents the number of instances to be fold, appart from the running instance
    #[allow(clippy::type_complexity)]
    fn prepare_inputs(
        k: usize,
    ) -> (
        Witness<Fr>,
        CommittedInstance<Projective>,
        Vec<Witness<Fr>>,
        Vec<CommittedInstance<Projective>>,
    ) {
        let mut rng = ark_std::test_rng();
        let pedersen_params = Pedersen::<Projective>::new_params(&mut rng, 100); // 100 is wip, will get it from actual vec

        let z = get_test_z::<Fr>(3);
        let mut zs: Vec<Vec<Fr>> = Vec::new();
        for i in 0..k {
            let z_i = get_test_z::<Fr>(i + 4);
            zs.push(z_i);
        }

        let n = z.len();
        let t = log2(n) as usize;

        let beta = Fr::rand(&mut rng);
        let betas = exponential_powers(beta, t);

        let witness = Witness::<Fr> {
            w: z.clone(),
            r_w: Fr::rand(&mut rng),
        };
        let phi =
            Pedersen::<Projective>::commit(&pedersen_params, &witness.w, &witness.r_w).unwrap();
        let instance = CommittedInstance::<Projective> {
            phi,
            betas: betas.clone(),
            e: Fr::zero(),
        };
        // same for the other instances
        let mut witnesses: Vec<Witness<Fr>> = Vec::new();
        let mut instances: Vec<CommittedInstance<Projective>> = Vec::new();
        #[allow(clippy::needless_range_loop)]
        for i in 0..k {
            let witness_i = Witness::<Fr> {
                w: zs[i].clone(),
                r_w: Fr::rand(&mut rng),
            };
            let phi_i =
                Pedersen::<Projective>::commit(&pedersen_params, &witness_i.w, &witness_i.r_w)
                    .unwrap();
            let instance_i = CommittedInstance::<Projective> {
                phi: phi_i,
                betas: betas.clone(),
                e: Fr::zero(),
            };
            witnesses.push(witness_i);
            instances.push(instance_i);
        }

        (witness, instance, witnesses, instances)
    }

    #[test]
    fn test_fold_native_case() {
        let k = 7;
        let (witness, instance, witnesses, instances) = prepare_inputs(k);
        let r1cs = get_test_r1cs::<Fr>();

        // init Prover & Verifier's transcript
        let poseidon_config = poseidon_test_config::<Fr>();
        let mut transcript_p = PoseidonTranscript::<Projective>::new(&poseidon_config);
        let mut transcript_v = PoseidonTranscript::<Projective>::new(&poseidon_config);

        let (folded_instance, folded_witness, F_coeffs, K_coeffs) = Folding::<Projective>::prove(
            &mut transcript_p,
            &r1cs,
            &instance,
            &witness,
            &instances,
            &witnesses,
        )
        .unwrap();

        // veriier
        let folded_instance_v = Folding::<Projective>::verify(
            &mut transcript_v,
            &r1cs,
            &instance,
            &instances,
            F_coeffs,
            K_coeffs,
        )
        .unwrap();

        // check that prover & verifier folded instances are the same values
        assert_eq!(folded_instance.phi, folded_instance_v.phi);
        assert_eq!(folded_instance.betas, folded_instance_v.betas);
        assert_eq!(folded_instance.e, folded_instance_v.e);
        assert!(!folded_instance.e.is_zero());

        // check that the folded instance satisfies the relation
        check_instance(&r1cs, &folded_instance, &folded_witness).unwrap();
    }

    #[test]
    fn test_fold_various_iterations() {
        let r1cs = get_test_r1cs::<Fr>();

        // init Prover & Verifier's transcript
        let poseidon_config = poseidon_test_config::<Fr>();
        let mut transcript_p = PoseidonTranscript::<Projective>::new(&poseidon_config);
        let mut transcript_v = PoseidonTranscript::<Projective>::new(&poseidon_config);

        let (mut running_witness, mut running_instance, _, _) = prepare_inputs(0);

        // fold k instances on each of num_iters iterations
        let k = 7;
        let num_iters = 10;
        for _ in 0..num_iters {
            // generate the instances to be fold
            let (_, _, witnesses, instances) = prepare_inputs(k);

            let (folded_instance, folded_witness, F_coeffs, K_coeffs) =
                Folding::<Projective>::prove(
                    &mut transcript_p,
                    &r1cs,
                    &running_instance,
                    &running_witness,
                    &instances,
                    &witnesses,
                )
                .unwrap();

            // veriier
            let folded_instance_v = Folding::<Projective>::verify(
                &mut transcript_v,
                &r1cs,
                &running_instance,
                &instances,
                F_coeffs,
                K_coeffs,
            )
            .unwrap();

            // check that prover & verifier folded instances are the same values
            assert_eq!(folded_instance.phi, folded_instance_v.phi);
            assert_eq!(folded_instance.betas, folded_instance_v.betas);
            assert_eq!(folded_instance.e, folded_instance_v.e);
            assert!(!folded_instance.e.is_zero());

            // check that the folded instance satisfies the relation
            check_instance(&r1cs, &folded_instance, &folded_witness).unwrap();

            running_witness = folded_witness;
            running_instance = folded_instance;
        }
    }
}
