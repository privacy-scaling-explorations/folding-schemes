use ark_ec::CurveGroup;
use ark_ff::PrimeField;
use ark_poly::DenseMultilinearExtension;
use ark_poly::MultilinearExtension;
use ark_std::One;
use std::sync::Arc;

use super::lcccs::LCCCS;
use super::nimfs::SigmasThetas;
use crate::ccs::CCS;
use crate::utils::mle::dense_vec_to_dense_mle;
use crate::utils::vec::mat_vec_mul;
use crate::utils::virtual_polynomial::{build_eq_x_r_vec, eq_eval, VirtualPolynomial};
use crate::Error;

/// Compute the arrays of sigma_i and theta_i from step 4 corresponding to the LCCCS and CCCS
/// instances
pub fn compute_sigmas_thetas<F: PrimeField>(
    ccs: &CCS<F>,
    z_lcccs: &[Vec<F>],
    z_cccs: &[Vec<F>],
    r_x_prime: &[F],
) -> Result<SigmasThetas<F>, Error> {
    let mut sigmas: Vec<Vec<F>> = Vec::new();
    for z_lcccs_i in z_lcccs {
        let mut Mzs: Vec<DenseMultilinearExtension<F>> = vec![];
        for M_j in ccs.M.iter() {
            Mzs.push(dense_vec_to_dense_mle(ccs.s, &mat_vec_mul(M_j, z_lcccs_i)?));
        }
        let sigma_i = Mzs
            .iter()
            .map(|Mz| Mz.evaluate(r_x_prime).ok_or(Error::EvaluationFail))
            .collect::<Result<_, Error>>()?;
        sigmas.push(sigma_i);
    }

    let mut thetas: Vec<Vec<F>> = Vec::new();
    for z_cccs_i in z_cccs {
        let mut Mzs: Vec<DenseMultilinearExtension<F>> = vec![];
        for M_j in ccs.M.iter() {
            Mzs.push(dense_vec_to_dense_mle(ccs.s, &mat_vec_mul(M_j, z_cccs_i)?));
        }
        let theta_i = Mzs
            .iter()
            .map(|Mz| Mz.evaluate(r_x_prime).ok_or(Error::EvaluationFail))
            .collect::<Result<_, Error>>()?;
        thetas.push(theta_i);
    }
    Ok(SigmasThetas(sigmas, thetas))
}

/// Computes c from the step 5 in section 5 of HyperNova, adapted to multiple LCCCS & CCCS
/// instances:
/// $$
/// c = \sum_{i \in [\mu]} \left(\sum_{j \in [t]} \gamma^{i \cdot t + j} \cdot e_i \cdot \sigma_{i,j} \right)
/// + \sum_{k \in [\nu]} \gamma^{\mu \cdot t+k} \cdot e_k \cdot \left( \sum_{i=1}^q c_i \cdot \prod_{j \in S_i}
/// \theta_{k,j} \right)
/// $$
pub fn compute_c<F: PrimeField>(
    ccs: &CCS<F>,
    st: &SigmasThetas<F>,
    gamma: F,
    beta: &[F],
    vec_r_x: &Vec<Vec<F>>,
    r_x_prime: &[F],
) -> Result<F, Error> {
    let (vec_sigmas, vec_thetas) = (st.0.clone(), st.1.clone());
    let mut c = F::zero();

    let mut e_lcccs = Vec::new();
    for r_x in vec_r_x {
        e_lcccs.push(eq_eval(r_x, r_x_prime)?);
    }
    for (i, sigmas) in vec_sigmas.iter().enumerate() {
        // (sum gamma^j * e_i * sigma_j)
        for (j, sigma_j) in sigmas.iter().enumerate() {
            let gamma_j = gamma.pow([((i * ccs.t + j) as u64)]);
            c += gamma_j * e_lcccs[i] * sigma_j;
        }
    }

    let mu = vec_sigmas.len();
    let e2 = eq_eval(beta, r_x_prime)?;
    for (k, thetas) in vec_thetas.iter().enumerate() {
        // + gamma^{t+1} * e2 * sum c_i * prod theta_j
        let mut lhs = F::zero();
        for i in 0..ccs.q {
            let mut prod = F::one();
            for j in ccs.S[i].clone() {
                prod *= thetas[j];
            }
            lhs += ccs.c[i] * prod;
        }
        let gamma_t1 = gamma.pow([(mu * ccs.t + k) as u64]);
        c += gamma_t1 * e2 * lhs;
    }
    Ok(c)
}

/// Compute g(x) polynomial for the given inputs.
pub fn compute_g<C: CurveGroup>(
    ccs: &CCS<C::ScalarField>,
    running_instances: &[LCCCS<C>],
    z_lcccs: &[Vec<C::ScalarField>],
    z_cccs: &[Vec<C::ScalarField>],
    gamma: C::ScalarField,
    beta: &[C::ScalarField],
) -> Result<VirtualPolynomial<C::ScalarField>, Error>
where
    C::ScalarField: PrimeField,
{
    assert_eq!(running_instances.len(), z_lcccs.len());

    let mut g = VirtualPolynomial::<C::ScalarField>::new(ccs.s);

    let mu = z_lcccs.len();
    let nu = z_cccs.len();

    let mut gamma_pow = C::ScalarField::one();
    for i in 0..mu {
        // L_j
        let eq_rx = build_eq_x_r_vec(&running_instances[i].r_x)?;
        let eq_rx_mle = dense_vec_to_dense_mle(ccs.s, &eq_rx);
        for M_j in ccs.M.iter() {
            let mut L_i_j = vec![dense_vec_to_dense_mle(
                ccs.s,
                &mat_vec_mul(M_j, &z_lcccs[i])?,
            )];
            L_i_j.push(eq_rx_mle.clone());
            g.add_mle_list(L_i_j.iter().map(|v| Arc::new(v.clone())), gamma_pow)?;
            gamma_pow *= gamma;
        }
    }

    let eq_beta = build_eq_x_r_vec(beta)?;
    let eq_beta_mle = dense_vec_to_dense_mle(ccs.s, &eq_beta);

    #[allow(clippy::needless_range_loop)]
    for k in 0..nu {
        // Q_k
        for i in 0..ccs.q {
            let mut Q_k = vec![];
            for &j in ccs.S[i].iter() {
                Q_k.push(dense_vec_to_dense_mle(
                    ccs.s,
                    &mat_vec_mul(&ccs.M[j], &z_cccs[k])?,
                ));
            }
            Q_k.push(eq_beta_mle.clone());
            g.add_mle_list(
                Q_k.iter().map(|v| Arc::new(v.clone())),
                ccs.c[i] * gamma_pow,
            )?;
        }
        gamma_pow *= gamma;
    }

    Ok(g)
}

#[cfg(test)]
pub mod tests {
    use ark_ff::Field;
    use ark_pallas::{Fr, Projective};
    use ark_std::test_rng;
    use ark_std::UniformRand;
    use ark_std::Zero;

    use super::*;
    use crate::ccs::tests::{get_test_ccs, get_test_z};
    use crate::commitment::{pedersen::Pedersen, CommitmentScheme};
    use crate::folding::hypernova::lcccs::tests::compute_Ls;
    use crate::utils::hypercube::BooleanHypercube;
    use crate::utils::mle::matrix_to_dense_mle;
    use crate::utils::multilinear_polynomial::tests::fix_last_variables;
    use crate::utils::virtual_polynomial::eq_eval;

    /// Given M(x,y) matrix and a random field element `r`, test that ~M(r,y) is is an s'-variable polynomial which
    /// compresses every column j of the M(x,y) matrix by performing a random linear combination between the elements
    /// of the column and the values eq_i(r) where i is the row of that element
    ///
    /// For example, for matrix M:
    ///
    /// [2, 3, 4, 4
    ///  4, 4, 3, 2
    ///  2, 8, 9, 2
    ///  9, 4, 2, 0]
    ///
    /// The polynomial ~M(r,y) is a polynomial in F^2 which evaluates to the following values in the hypercube:
    /// - M(00) = 2*eq_00(r) + 4*eq_10(r) + 2*eq_01(r) + 9*eq_11(r)
    /// - M(10) = 3*eq_00(r) + 4*eq_10(r) + 8*eq_01(r) + 4*eq_11(r)
    /// - M(01) = 4*eq_00(r) + 3*eq_10(r) + 9*eq_01(r) + 2*eq_11(r)
    /// - M(11) = 4*eq_00(r) + 2*eq_10(r) + 2*eq_01(r) + 0*eq_11(r)
    ///
    /// This is used by HyperNova in LCCCS to perform a verifier-chosen random linear combination between the columns
    /// of the matrix and the z vector. This technique is also used extensively in "An Algebraic Framework for
    /// Universal and Updatable SNARKs".
    #[test]
    fn test_compute_M_r_y_compression() {
        let mut rng = test_rng();

        // s = 2, s' = 3
        let ccs = get_test_ccs::<Fr>();

        let M = ccs.M[0].clone().to_dense();
        let M_mle = matrix_to_dense_mle(ccs.M[0].clone());

        // Fix the polynomial ~M(r,y)
        let r: Vec<Fr> = (0..ccs.s).map(|_| Fr::rand(&mut rng)).collect();
        let M_r_y = fix_last_variables(&M_mle, &r);

        // compute M_r_y the other way around
        for j in 0..M[0].len() {
            // Go over every column of M
            let column_j: Vec<Fr> = M.clone().iter().map(|x| x[j]).collect();
            // and perform the random lincomb between the elements of the column and eq_i(r)
            let rlc = BooleanHypercube::new(ccs.s)
                .enumerate()
                .map(|(i, x)| column_j[i] * eq_eval(&x, &r).unwrap())
                .fold(Fr::zero(), |acc, result| acc + result);

            assert_eq!(M_r_y.evaluations[j], rlc);
        }
    }

    #[test]
    fn test_compute_sigmas_thetas() {
        let ccs = get_test_ccs();
        let z1 = get_test_z(3);
        let z2 = get_test_z(4);
        ccs.check_relation(&z1).unwrap();
        ccs.check_relation(&z2).unwrap();

        let mut rng = test_rng();
        let gamma: Fr = Fr::rand(&mut rng);
        let beta: Vec<Fr> = (0..ccs.s).map(|_| Fr::rand(&mut rng)).collect();
        let r_x_prime: Vec<Fr> = (0..ccs.s).map(|_| Fr::rand(&mut rng)).collect();

        // Initialize a multifolding object
        let (pedersen_params, _) =
            Pedersen::<Projective>::setup(&mut rng, ccs.n - ccs.l - 1).unwrap();
        let (lcccs_instance, _) = ccs
            .to_lcccs::<_, _, Pedersen<Projective>>(&mut rng, &pedersen_params, &z1)
            .unwrap();

        let sigmas_thetas =
            compute_sigmas_thetas(&ccs, &[z1.clone()], &[z2.clone()], &r_x_prime).unwrap();

        let g = compute_g(
            &ccs,
            &[lcccs_instance.clone()],
            &[z1.clone()],
            &[z2.clone()],
            gamma,
            &beta,
        )
        .unwrap();

        // we expect g(r_x_prime) to be equal to:
        // c = (sum gamma^j * e1 * sigma_j) + gamma^{t+1} * e2 * sum c_i * prod theta_j
        // from compute_c
        let expected_c = g.evaluate(&r_x_prime).unwrap();
        let c = compute_c::<Fr>(
            &ccs,
            &sigmas_thetas,
            gamma,
            &beta,
            &vec![lcccs_instance.r_x],
            &r_x_prime,
        )
        .unwrap();
        assert_eq!(c, expected_c);
    }

    #[test]
    fn test_compute_g() {
        let mut rng = test_rng();

        // generate test CCS & z vectors
        let ccs: CCS<Fr> = get_test_ccs();
        let z1 = get_test_z(3);
        let z2 = get_test_z(4);
        ccs.check_relation(&z1).unwrap();
        ccs.check_relation(&z2).unwrap();

        let gamma: Fr = Fr::rand(&mut rng);
        let beta: Vec<Fr> = (0..ccs.s).map(|_| Fr::rand(&mut rng)).collect();

        // Initialize a multifolding object
        let (pedersen_params, _) =
            Pedersen::<Projective>::setup(&mut rng, ccs.n - ccs.l - 1).unwrap();
        let (lcccs_instance, _) = ccs
            .to_lcccs::<_, _, Pedersen<Projective>>(&mut rng, &pedersen_params, &z1)
            .unwrap();

        // Compute g(x) with that r_x
        let g = compute_g::<Projective>(
            &ccs,
            &[lcccs_instance.clone()],
            &[z1.clone()],
            &[z2.clone()],
            gamma,
            &beta,
        )
        .unwrap();

        // evaluate g(x) over x \in {0,1}^s
        let mut g_on_bhc = Fr::zero();
        for x in BooleanHypercube::new(ccs.s) {
            g_on_bhc += g.evaluate(&x).unwrap();
        }

        // Q(x) over bhc is assumed to be zero, as checked in the test 'test_compute_Q'
        assert_ne!(g_on_bhc, Fr::zero());

        let mut sum_v_j_gamma = Fr::zero();
        for j in 0..lcccs_instance.v.len() {
            let gamma_j = gamma.pow([j as u64]);
            sum_v_j_gamma += lcccs_instance.v[j] * gamma_j;
        }

        // evaluating g(x) over the boolean hypercube should give the same result as evaluating the
        // sum of gamma^j * v_j over j \in [t]
        assert_eq!(g_on_bhc, sum_v_j_gamma);

        // evaluate sum_{j \in [t]} (gamma^j * Lj(x)) over x \in {0,1}^s
        let mut sum_Lj_on_bhc = Fr::zero();
        let vec_L = compute_Ls(&ccs, &lcccs_instance, &z1);
        for x in BooleanHypercube::new(ccs.s) {
            for (j, Lj) in vec_L.iter().enumerate() {
                let gamma_j = gamma.pow([j as u64]);
                sum_Lj_on_bhc += Lj.evaluate(&x).unwrap() * gamma_j;
            }
        }

        // evaluating g(x) over the boolean hypercube should give the same result as evaluating the
        // sum of gamma^j * Lj(x) over the boolean hypercube
        assert_eq!(g_on_bhc, sum_Lj_on_bhc);
    }
}
