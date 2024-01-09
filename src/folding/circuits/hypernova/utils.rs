use crate::folding::circuits::utils::VecFpVar;
use ark_ff::PrimeField;
use ark_r1cs_std::{
    alloc::{AllocVar, AllocationMode},
    fields::{fp::FpVar, FieldVar},
    ToBitsGadget,
};
use ark_relations::r1cs::{Namespace, SynthesisError};
use std::{borrow::Borrow, marker::PhantomData};

/// `GammaVar` is a wrapper around an `FpVar` for $\gamma$.
#[derive(Clone)]
pub struct GammaVar<F: PrimeField> {
    pub value: FpVar<F>,
}

impl<F: PrimeField> AllocVar<F, F> for GammaVar<F> {
    fn new_variable<T: Borrow<F>>(
        cs: impl Into<Namespace<F>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        FpVar::new_variable(cs, f, mode).map(|value| Self { value })
    }
}

impl<F: PrimeField> GammaVar<F> {
    /// An helper to compute $\gamma^{pow}$
    pub fn pow(&self, pow: FpVar<F>) -> Result<FpVar<F>, SynthesisError> {
        let pow = pow.to_bits_le()?;
        self.value.pow_le(&pow)
    }
}

/// Gadget to compute the sum of all $\gamma^{j} \cdot eq(r_{x_j}, r_x^{\prime}) \cdot \sigma_j$.
pub struct SumMulsGammaPowsEqSigmaGadget<F: PrimeField> {
    _f: PhantomData<F>,
}

impl<F: PrimeField> SumMulsGammaPowsEqSigmaGadget<F> {
    /// Computes the sum $\Sigma_{j}^{j + n} \gamma^{j} \cdot eq_eval \cdot \sigma_{j}$, where $n$ is the length of the `sigmas` vector
    /// It corresponds to the first term of the sum that $\mathcal{V}$ has to compute at section 5, step 5 of "A multi-folding scheme for CCS".
    ///
    /// # Arguments
    /// - `sigmas`: vector of $\sigma_j$ values
    /// - `eq_eval`: the value of $\tilde{eq}(x_j, x^{\prime})$
    /// - `gamma`: a `GammaVar`, which supports a `pow` method, representing $\gamma$
    /// - `j`: the power at which we start to compute $\gamma^{j}$. This is needed in the contexxt of multifolding.
    ///
    /// # Notes
    /// In the context of multifolding, `j` corresponds to `ccs.t` in `compute_c_from_sigmas_and_thetas`
    pub fn sum_muls_gamma_pows_eq_sigma(
        sigmas: VecFpVar<F>,
        eq_eval: FpVar<F>,
        gamma: GammaVar<F>,
        j: FpVar<F>,
    ) -> Result<FpVar<F>, SynthesisError> {
        let mut result = FpVar::<F>::zero();
        let mut gamma_pow = gamma.pow(j).map_err(|_| SynthesisError::Unsatisfiable)?;
        for sigma in sigmas {
            result += gamma_pow.clone() * eq_eval.clone() * sigma;
            gamma_pow *= gamma.value.clone();
        }
        Ok(result)
    }
}

#[cfg(test)]
mod tests {
    use super::{GammaVar, SumMulsGammaPowsEqSigmaGadget};
    use crate::{
        ccs::{
            tests::{get_test_ccs, get_test_z},
            CCS,
        },
        folding::{
            circuits::utils::VecFpVar,
            hypernova::utils::{compute_sigmas_and_thetas, sum_muls_gamma_pows_eq_sigma},
        },
        pedersen::Pedersen,
        utils::virtual_polynomial::eq_eval,
    };
    use ark_pallas::{Fr, Projective};
    use ark_r1cs_std::{alloc::AllocVar, fields::fp::FpVar, R1CSVar};
    use ark_relations::r1cs::ConstraintSystem;
    use ark_std::{test_rng, UniformRand};

    #[test]
    pub fn test_sum_muls_gamma_pow_eq_sigma_gadget() {
        let mut rng = test_rng();
        let ccs: CCS<Projective> = get_test_ccs();
        let z1 = get_test_z(3);
        let z2 = get_test_z(4);

        let gamma: Fr = Fr::rand(&mut rng);
        let r_x_prime: Vec<Fr> = (0..ccs.s).map(|_| Fr::rand(&mut rng)).collect();

        // Initialize a multifolding object
        let pedersen_params = Pedersen::new_params(&mut rng, ccs.n - ccs.l - 1);
        let (lcccs_instance, _) = ccs.to_lcccs(&mut rng, &pedersen_params, &z1).unwrap();
        let sigmas_thetas =
            compute_sigmas_and_thetas(&ccs, &[z1.clone()], &[z2.clone()], &r_x_prime);

        let mut e_lcccs = Vec::new();
        for r_x in &vec![lcccs_instance.r_x] {
            e_lcccs.push(eq_eval(r_x, &r_x_prime).unwrap());
        }

        // Initialize cs and gamma
        let cs = ConstraintSystem::<Fr>::new_ref();
        let gamma_var = GammaVar::<Fr>::new_constant(cs.clone(), gamma).unwrap();

        for (i, sigmas) in sigmas_thetas.0.iter().enumerate() {
            let expected =
                sum_muls_gamma_pows_eq_sigma(gamma, e_lcccs[i], sigmas, (i * ccs.t) as u64);
            let sigmas_var = VecFpVar::<Fr>::new_constant(cs.clone(), sigmas).unwrap();
            let eq_var = FpVar::<Fr>::new_constant(cs.clone(), e_lcccs[i]).unwrap();
            let pow = FpVar::<Fr>::new_constant(cs.clone(), Fr::from((i * ccs.t) as u64)).unwrap();
            let computed = SumMulsGammaPowsEqSigmaGadget::sum_muls_gamma_pows_eq_sigma(
                sigmas_var,
                eq_var,
                gamma_var.clone(),
                pow,
            )
            .unwrap();
            assert_eq!(expected, computed.value().unwrap());
        }
    }
}
