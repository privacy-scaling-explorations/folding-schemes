use ark_ff::PrimeField;
use ark_poly::{univariate::DensePolynomial, DenseUVPolynomial};

/// Computes the lagrange interpolated polynomial from the given points `p_i`
pub fn compute_lagrange_interpolated_poly<F: PrimeField>(p_i: &[F]) -> DensePolynomial<F> {
    // domain is 0..p_i.len(), to fit `interpolate_uni_poly` from hyperplonk
    let domain: Vec<usize> = (0..p_i.len()).collect();

    // compute l(x), common to every basis polynomial
    let mut l_x = DensePolynomial::from_coefficients_vec(vec![F::ONE]);
    for x_m in domain.clone() {
        let prod_m = DensePolynomial::from_coefficients_vec(vec![-F::from(x_m as u64), F::ONE]);
        l_x = &l_x * &prod_m;
    }

    // compute each w_j - barycentric weights
    let mut w_j_vector: Vec<F> = vec![];
    for x_j in domain.clone() {
        let mut w_j = F::ONE;
        for x_m in domain.clone() {
            if x_m != x_j {
                let prod = (F::from(x_j as u64) - F::from(x_m as u64))
                    .inverse()
                    .unwrap(); // an inverse always exists since x_j != x_m (!=0)
                               // hence, we call unwrap() here without checking the Option's content
                w_j *= prod;
            }
        }
        w_j_vector.push(w_j);
    }

    // compute each polynomial within the sum L(x)
    let mut lagrange_poly = DensePolynomial::from_coefficients_vec(vec![F::ZERO]);
    for (j, w_j) in w_j_vector.iter().enumerate() {
        let x_j = domain[j];
        let y_j = p_i[j];
        // we multiply by l(x) here, otherwise the below division will not work - deg(0)/deg(d)
        let poly_numerator = &(&l_x * (*w_j)) * (y_j);
        let poly_denominator =
            DensePolynomial::from_coefficients_vec(vec![-F::from(x_j as u64), F::ONE]);
        let poly = &poly_numerator / &poly_denominator;
        lagrange_poly = &lagrange_poly + &poly;
    }

    lagrange_poly
}

#[cfg(test)]
mod tests {

    use crate::utils::espresso::sum_check::verifier::interpolate_uni_poly;
    use crate::utils::lagrange_poly::compute_lagrange_interpolated_poly;
    use ark_pallas::Fr;
    use ark_poly::{univariate::DensePolynomial, DenseUVPolynomial, Polynomial};
    use ark_std::UniformRand;
    use espresso_subroutines::poly_iop::prelude::PolyIOPErrors;

    #[test]
    fn test_compute_lagrange_interpolated_poly() {
        let mut prng = ark_std::test_rng();
        for degree in 1..30 {
            let poly = DensePolynomial::<Fr>::rand(degree, &mut prng);
            // range (which is exclusive) is from 0 to degree + 1, since we need degree + 1 evaluations
            let evals = (0..(degree + 1))
                .map(|i| poly.evaluate(&Fr::from(i as u64)))
                .collect::<Vec<Fr>>();
            let lagrange_poly = compute_lagrange_interpolated_poly(&evals);
            for _ in 0..10 {
                let query = Fr::rand(&mut prng);
                let lagrange_eval = lagrange_poly.evaluate(&query);
                let eval = poly.evaluate(&query);
                assert_eq!(eval, lagrange_eval);
                assert_eq!(lagrange_poly.degree(), poly.degree());
            }
        }
    }

    #[test]
    fn test_interpolation() -> Result<(), PolyIOPErrors> {
        let mut prng = ark_std::test_rng();

        // test a polynomial with 20 known points, i.e., with degree 19
        let poly = DensePolynomial::<Fr>::rand(20 - 1, &mut prng);
        let evals = (0..20)
            .map(|i| poly.evaluate(&Fr::from(i)))
            .collect::<Vec<Fr>>();
        let query = Fr::rand(&mut prng);

        assert_eq!(poly.evaluate(&query), interpolate_uni_poly(&evals, query)?);
        assert_eq!(
            compute_lagrange_interpolated_poly(&evals).evaluate(&query),
            interpolate_uni_poly(&evals, query)?
        );

        // test a polynomial with 33 known points, i.e., with degree 32
        let poly = DensePolynomial::<Fr>::rand(33 - 1, &mut prng);
        let evals = (0..33)
            .map(|i| poly.evaluate(&Fr::from(i)))
            .collect::<Vec<Fr>>();
        let query = Fr::rand(&mut prng);

        assert_eq!(poly.evaluate(&query), interpolate_uni_poly(&evals, query)?);
        assert_eq!(
            compute_lagrange_interpolated_poly(&evals).evaluate(&query),
            interpolate_uni_poly(&evals, query)?
        );

        // test a polynomial with 64 known points, i.e., with degree 63
        let poly = DensePolynomial::<Fr>::rand(64 - 1, &mut prng);
        let evals = (0..64)
            .map(|i| poly.evaluate(&Fr::from(i)))
            .collect::<Vec<Fr>>();
        let query = Fr::rand(&mut prng);

        assert_eq!(poly.evaluate(&query), interpolate_uni_poly(&evals, query)?);
        assert_eq!(
            compute_lagrange_interpolated_poly(&evals).evaluate(&query),
            interpolate_uni_poly(&evals, query)?
        );

        Ok(())
    }
}
