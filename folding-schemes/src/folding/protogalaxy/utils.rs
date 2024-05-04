use ark_ff::PrimeField;
use ark_r1cs_std::fields::{fp::FpVar, FieldVar};

/// Returns (b, b^2, b^4, ..., b^{2^{t-1}})
pub fn exponential_powers<F: PrimeField>(b: F, t: usize) -> Vec<F> {
    let mut r = vec![F::zero(); t];
    r[0] = b;
    for i in 1..t {
        r[i] = r[i - 1].square();
    }
    r
}

/// The in-circuit version of `exponential_powers`
pub fn exponential_powers_var<F: PrimeField>(b: FpVar<F>, t: usize) -> Vec<FpVar<F>> {
    let mut r = vec![FpVar::zero(); t];
    r[0] = b;
    for i in 1..t {
        r[i] = &r[i - 1] * &r[i - 1];
    }
    r
}

/// Returns (a, a^2, a^3, ..., a^{n-1})
pub fn all_powers<F: PrimeField>(a: F, n: usize) -> Vec<F> {
    let mut r = vec![F::zero(); n];
    for (i, r_i) in r.iter_mut().enumerate() {
        *r_i = a.pow([i as u64]);
    }
    r
}

/// The in-circuit version of `all_powers`
pub fn all_powers_var<F: PrimeField>(a: FpVar<F>, n: usize) -> Vec<FpVar<F>> {
    if n == 0 {
        return vec![];
    }
    let mut r = vec![FpVar::zero(); n];
    r[0] = FpVar::one();
    for i in 1..n {
        r[i] = &r[i - 1] * &a;
    }
    r
}

/// returns a vector containing βᵢ* = βᵢ + α ⋅ δᵢ
pub fn betas_star<F: PrimeField>(betas: &[F], deltas: &[F], alpha: F) -> Vec<F> {
    betas
        .iter()
        .zip(
            deltas
                .iter()
                .map(|delta_i| alpha * delta_i)
                .collect::<Vec<F>>(),
        )
        .map(|(beta_i, delta_i_alpha)| *beta_i + delta_i_alpha)
        .collect()
}

/// The in-circuit version of `betas_star`
pub fn betas_star_var<F: PrimeField>(
    betas: &[FpVar<F>],
    deltas: &[FpVar<F>],
    alpha: &FpVar<F>,
) -> Vec<FpVar<F>> {
    betas
        .iter()
        .zip(deltas)
        .map(|(beta_i, delta_i)| beta_i + alpha * delta_i)
        .collect::<Vec<FpVar<F>>>()
}

#[cfg(test)]
mod tests {
    use std::error::Error;

    use ark_bn254::Fr;
    use ark_r1cs_std::{alloc::AllocVar, R1CSVar};
    use ark_relations::r1cs::ConstraintSystem;
    use ark_std::{test_rng, UniformRand};

    use super::*;

    #[test]
    fn test_exponential_powers() -> Result<(), Box<dyn Error>> {
        let rng = &mut test_rng();

        for t in 1..10 {
            let cs = ConstraintSystem::<Fr>::new_ref();

            let b = Fr::rand(rng);
            let b_var = FpVar::new_witness(cs.clone(), || Ok(b))?;

            let r = exponential_powers(b, t);
            let r_var = exponential_powers_var(b_var, t);

            assert_eq!(r, r_var.value()?);
            assert!(cs.is_satisfied()?);
        }

        Ok(())
    }

    #[test]
    fn test_all_powers() -> Result<(), Box<dyn Error>> {
        let rng = &mut test_rng();

        for n in 1..10 {
            let cs = ConstraintSystem::<Fr>::new_ref();

            let a = Fr::rand(rng);
            let a_var = FpVar::new_witness(cs.clone(), || Ok(a))?;

            let r = all_powers(a, n);
            let r_var = all_powers_var(a_var, n);

            assert_eq!(r, r_var.value()?);
            assert!(cs.is_satisfied()?);
        }

        Ok(())
    }

    #[test]
    fn test_betas_star() -> Result<(), Box<dyn Error>> {
        let rng = &mut test_rng();

        for t in 1..10 {
            let cs = ConstraintSystem::<Fr>::new_ref();

            let betas = (0..t).map(|_| Fr::rand(rng)).collect::<Vec<_>>();
            let deltas = (0..t).map(|_| Fr::rand(rng)).collect::<Vec<_>>();
            let alpha = Fr::rand(rng);

            let betas_var = Vec::new_witness(cs.clone(), || Ok(betas.clone()))?;
            let deltas_var = Vec::new_witness(cs.clone(), || Ok(deltas.clone()))?;
            let alpha_var = FpVar::new_witness(cs.clone(), || Ok(alpha))?;

            let r = betas_star(&betas, &deltas, alpha);
            let r_var = betas_star_var(&betas_var, &deltas_var, &alpha_var);
            assert_eq!(r, r_var.value()?);
            assert!(cs.is_satisfied()?);
        }

        Ok(())
    }
}
