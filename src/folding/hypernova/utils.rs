use ark_ec::CurveGroup;
use ark_ff::{Field, PrimeField};
use ark_poly::DenseMultilinearExtension;
use ark_poly::MultilinearExtension;
use ark_std::{One, Zero};
use std::ops::Add;

use crate::utils::multilinear_polynomial::fix_variables;
use crate::utils::multilinear_polynomial::scalar_mul;

use super::lcccs::LCCCS;
use super::nimfs::SigmasThetas;
use crate::ccs::CCS;
use crate::utils::hypercube::BooleanHypercube;
use crate::utils::mle::dense_vec_to_mle;
use crate::utils::mle::matrix_to_mle;
use crate::utils::vec::SparseMatrix;
use crate::utils::virtual_polynomial::{eq_eval, VirtualPolynomial};

/// Return a vector of evaluations p_j(r) = \sum_{y \in {0,1}^s'} M_j(r, y) * z(y) for all j values
/// in 0..self.t
pub fn compute_all_sum_Mz_evals<F: PrimeField>(
    vec_M: &[SparseMatrix<F>],
    z: &Vec<F>,
    r: &[F],
    s_prime: usize,
) -> Vec<F> {
    // Convert z to MLE
    let z_y_mle = dense_vec_to_mle(s_prime, z);
    // Convert all matrices to MLE
    let M_x_y_mle: Vec<DenseMultilinearExtension<F>> =
        vec_M.iter().cloned().map(matrix_to_mle).collect();

    let mut v = Vec::with_capacity(M_x_y_mle.len());
    for M_i in M_x_y_mle {
        let sum_Mz = compute_sum_Mz(M_i, &z_y_mle, s_prime);
        let v_i = sum_Mz.evaluate(r).unwrap();
        v.push(v_i);
    }
    v
}

/// Return the multilinear polynomial p(x) = \sum_{y \in {0,1}^s'} M_j(x, y) * z(y)
pub fn compute_sum_Mz<F: PrimeField>(
    M_j: DenseMultilinearExtension<F>,
    z: &DenseMultilinearExtension<F>,
    s_prime: usize,
) -> DenseMultilinearExtension<F> {
    let mut sum_Mz = DenseMultilinearExtension {
        evaluations: vec![F::zero(); M_j.evaluations.len()],
        num_vars: M_j.num_vars - s_prime,
    };

    let bhc = BooleanHypercube::new(s_prime);
    for y in bhc.into_iter() {
        // In a slightly counter-intuitive fashion fix_variables() fixes the right-most variables of the polynomial. So
        // for a polynomial M(x,y) and a random field element r, if we do fix_variables(M,r) we will get M(x,r).
        let M_j_y = fix_variables(&M_j, &y);
        let z_y = z.evaluate(&y).unwrap();
        let M_j_z = scalar_mul(&M_j_y, &z_y);
        sum_Mz = sum_Mz.add(M_j_z);
    }
    sum_Mz
}

/// Compute the arrays of sigma_i and theta_i from step 4 corresponding to the LCCCS and CCCS
/// instances
pub fn compute_sigmas_and_thetas<C: CurveGroup>(
    ccs: &CCS<C>,
    z_lcccs: &[Vec<C::ScalarField>],
    z_cccs: &[Vec<C::ScalarField>],
    r_x_prime: &[C::ScalarField],
) -> SigmasThetas<C::ScalarField> {
    let mut sigmas: Vec<Vec<C::ScalarField>> = Vec::new();
    for z_lcccs_i in z_lcccs {
        // sigmas
        let sigma_i = compute_all_sum_Mz_evals(&ccs.M, z_lcccs_i, r_x_prime, ccs.s_prime);
        sigmas.push(sigma_i);
    }
    let mut thetas: Vec<Vec<C::ScalarField>> = Vec::new();
    for z_cccs_i in z_cccs {
        // thetas
        let theta_i = compute_all_sum_Mz_evals(&ccs.M, z_cccs_i, r_x_prime, ccs.s_prime);
        thetas.push(theta_i);
    }
    SigmasThetas(sigmas, thetas)
}

/// Computes the sum $\Sigma_{j = 0}^{n} \gamma^{\text{pow} + j} \cdot eq_eval \cdot \sigma_{j}$
/// `pow` corresponds to `i * ccs.t` in `compute_c_from_sigmas_and_thetas`
pub fn sum_muls_gamma_pows_eq_sigma<F: PrimeField>(
    gamma: F,
    eq_eval: F,
    sigmas: &Vec<F>,
    pow: u64,
) -> F {
    let mut result = F::zero();
    for (j, sigma_j) in sigmas.iter().enumerate() {
        let gamma_j = gamma.pow([(pow + (j as u64)) as u64]);
        result += gamma_j * eq_eval * sigma_j;
    }
    result
}

/// Compute the right-hand-side of step 5 of the multifolding scheme
pub fn compute_c_from_sigmas_and_thetas<C: CurveGroup>(
    ccs: &CCS<C>,
    st: &SigmasThetas<C::ScalarField>,
    gamma: C::ScalarField,
    beta: &[C::ScalarField],
    vec_r_x: &Vec<Vec<C::ScalarField>>,
    r_x_prime: &[C::ScalarField],
) -> C::ScalarField {
    let (vec_sigmas, vec_thetas) = (st.0.clone(), st.1.clone());
    let mut c = C::ScalarField::zero();

    let mut e_lcccs = Vec::new();
    for r_x in vec_r_x {
        e_lcccs.push(eq_eval(r_x, r_x_prime).unwrap());
    }
    for (i, sigmas) in vec_sigmas.iter().enumerate() {
        // (sum gamma^j * e_i * sigma_j)
        c += sum_muls_gamma_pows_eq_sigma(gamma, e_lcccs[i], sigmas, (i * ccs.t) as u64);
    }

    let mu = vec_sigmas.len();
    let e2 = eq_eval(beta, r_x_prime).unwrap();
    for (k, thetas) in vec_thetas.iter().enumerate() {
        // + gamma^{t+1} * e2 * sum c_i * prod theta_j
        let mut lhs = C::ScalarField::zero();
        for i in 0..ccs.q {
            let mut prod = C::ScalarField::one();
            for j in ccs.S[i].clone() {
                prod *= thetas[j];
            }
            lhs += ccs.c[i] * prod;
        }
        let gamma_t1 = gamma.pow([(mu * ccs.t + k) as u64]);
        c += gamma_t1 * e2 * lhs;
    }
    c
}

/// Compute g(x) polynomial for the given inputs.
pub fn compute_g<C: CurveGroup>(
    ccs: &CCS<C>,
    running_instances: &[LCCCS<C>],
    z_lcccs: &[Vec<C::ScalarField>],
    z_cccs: &[Vec<C::ScalarField>],
    gamma: C::ScalarField,
    beta: &[C::ScalarField],
) -> VirtualPolynomial<C::ScalarField> {
    let mu = running_instances.len();
    let mut vec_Ls: Vec<VirtualPolynomial<C::ScalarField>> = Vec::new();
    for (i, running_instance) in running_instances.iter().enumerate() {
        let mut Ls = running_instance.compute_Ls(ccs, &z_lcccs[i]);
        vec_Ls.append(&mut Ls);
    }
    let mut vec_Q: Vec<VirtualPolynomial<C::ScalarField>> = Vec::new();
    // for (i, _) in cccs_instances.iter().enumerate() {
    for z_cccs_i in z_cccs.iter() {
        let Q = ccs.compute_Q(z_cccs_i, beta);
        vec_Q.push(Q);
    }
    let mut g = vec_Ls[0].clone();

    // note: the following two loops can be integrated in the previous two loops, but left
    // separated for clarity in the PoC implementation.
    for (j, L_j) in vec_Ls.iter_mut().enumerate().skip(1) {
        let gamma_j = gamma.pow([j as u64]);
        L_j.scalar_mul(&gamma_j);
        g = g.add(L_j);
    }
    for (i, Q_i) in vec_Q.iter_mut().enumerate() {
        let gamma_mut_i = gamma.pow([(mu * ccs.t + i) as u64]);
        Q_i.scalar_mul(&gamma_mut_i);
        g = g.add(Q_i);
    }
    g
}

#[cfg(test)]
pub mod tests {
    use super::*;

    use ark_pallas::{Fr, Projective};
    use ark_std::test_rng;
    use ark_std::One;
    use ark_std::UniformRand;
    use ark_std::Zero;

    use crate::ccs::tests::{get_test_ccs, get_test_z};
    use crate::pedersen::Pedersen;
    use crate::utils::multilinear_polynomial::tests::fix_last_variables;
    use crate::utils::virtual_polynomial::eq_eval;

    #[test]
    fn test_compute_sum_Mz_over_boolean_hypercube() {
        let ccs = get_test_ccs::<Projective>();
        let z = get_test_z(3);
        ccs.check_relation(&z).unwrap();
        let z_mle = dense_vec_to_mle(ccs.s_prime, &z);

        // check that evaluating over all the values x over the boolean hypercube, the result of
        // the next for loop is equal to 0
        for x in BooleanHypercube::new(ccs.s) {
            let mut r = Fr::zero();
            for i in 0..ccs.q {
                let mut Sj_prod = Fr::one();
                for j in ccs.S[i].clone() {
                    let M_j = matrix_to_mle(ccs.M[j].clone());
                    let sum_Mz = compute_sum_Mz(M_j, &z_mle, ccs.s_prime);
                    let sum_Mz_x = sum_Mz.evaluate(&x).unwrap();
                    Sj_prod *= sum_Mz_x;
                }
                r += Sj_prod * ccs.c[i];
            }
            assert_eq!(r, Fr::zero());
        }
    }

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
    /// This is used by Hypernova in LCCCS to perform a verifier-chosen random linear combination between the columns
    /// of the matrix and the z vector. This technique is also used extensively in "An Algebraic Framework for
    /// Universal and Updatable SNARKs".
    #[test]
    fn test_compute_M_r_y_compression() {
        let mut rng = test_rng();

        // s = 2, s' = 3
        let ccs = get_test_ccs::<Projective>();

        let M = ccs.M[0].clone().to_dense();
        let M_mle = matrix_to_mle(ccs.M[0].clone());

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
    fn test_compute_sigmas_and_thetas() {
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
        let pedersen_params = Pedersen::new_params(&mut rng, ccs.n - ccs.l - 1);
        let (lcccs_instance, _) = ccs.to_lcccs(&mut rng, &pedersen_params, &z1).unwrap();

        let sigmas_thetas =
            compute_sigmas_and_thetas(&ccs, &[z1.clone()], &[z2.clone()], &r_x_prime);

        let g = compute_g(
            &ccs,
            &[lcccs_instance.clone()],
            &[z1.clone()],
            &[z2.clone()],
            gamma,
            &beta,
        );

        // we expect g(r_x_prime) to be equal to:
        // c = (sum gamma^j * e1 * sigma_j) + gamma^{t+1} * e2 * sum c_i * prod theta_j
        // from compute_c_from_sigmas_and_thetas
        let expected_c = g.evaluate(&r_x_prime).unwrap();
        let c = compute_c_from_sigmas_and_thetas::<Projective>(
            &ccs,
            &sigmas_thetas,
            gamma,
            &beta,
            &vec![lcccs_instance.r_x],
            &r_x_prime,
        );
        assert_eq!(c, expected_c);
    }

    #[test]
    fn test_compute_g() {
        let ccs = get_test_ccs();
        let z1 = get_test_z(3);
        let z2 = get_test_z(4);
        ccs.check_relation(&z1).unwrap();
        ccs.check_relation(&z2).unwrap();

        let mut rng = test_rng(); // TMP
        let gamma: Fr = Fr::rand(&mut rng);
        let beta: Vec<Fr> = (0..ccs.s).map(|_| Fr::rand(&mut rng)).collect();

        // Initialize a multifolding object
        let pedersen_params = Pedersen::new_params(&mut rng, ccs.n - ccs.l - 1);
        let (lcccs_instance, _) = ccs.to_lcccs(&mut rng, &pedersen_params, &z1).unwrap();

        let mut sum_v_j_gamma = Fr::zero();
        for j in 0..lcccs_instance.v.len() {
            let gamma_j = gamma.pow([j as u64]);
            sum_v_j_gamma += lcccs_instance.v[j] * gamma_j;
        }

        // Compute g(x) with that r_x
        let g = compute_g::<Projective>(
            &ccs,
            &[lcccs_instance.clone()],
            &[z1.clone()],
            &[z2.clone()],
            gamma,
            &beta,
        );

        // evaluate g(x) over x \in {0,1}^s
        let mut g_on_bhc = Fr::zero();
        for x in BooleanHypercube::new(ccs.s) {
            g_on_bhc += g.evaluate(&x).unwrap();
        }

        // evaluate sum_{j \in [t]} (gamma^j * Lj(x)) over x \in {0,1}^s
        let mut sum_Lj_on_bhc = Fr::zero();
        let vec_L = lcccs_instance.compute_Ls(&ccs, &z1);
        for x in BooleanHypercube::new(ccs.s) {
            for (j, Lj) in vec_L.iter().enumerate() {
                let gamma_j = gamma.pow([j as u64]);
                sum_Lj_on_bhc += Lj.evaluate(&x).unwrap() * gamma_j;
            }
        }

        // Q(x) over bhc is assumed to be zero, as checked in the test 'test_compute_Q'
        assert_ne!(g_on_bhc, Fr::zero());

        // evaluating g(x) over the boolean hypercube should give the same result as evaluating the
        // sum of gamma^j * Lj(x) over the boolean hypercube
        assert_eq!(g_on_bhc, sum_Lj_on_bhc);

        // evaluating g(x) over the boolean hypercube should give the same result as evaluating the
        // sum of gamma^j * v_j over j \in [t]
        assert_eq!(g_on_bhc, sum_v_j_gamma);
    }
}
