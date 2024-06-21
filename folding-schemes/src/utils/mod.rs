use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::PrimeField;
use ark_std::Zero;

pub mod gadgets;
pub mod hypercube;
pub mod lagrange_poly;
pub mod mle;
pub mod vec;

// expose espresso local modules
pub mod espresso;
pub use crate::utils::espresso::multilinear_polynomial;
pub use crate::utils::espresso::sum_check;
pub use crate::utils::espresso::virtual_polynomial;

/// For a given x, returns [1, x^1, x^2, ..., x^n-1];
pub fn powers_of<F: PrimeField>(x: F, n: usize) -> Vec<F> {
    let mut c: Vec<F> = vec![F::zero(); n];
    c[0] = F::one();
    for i in 1..n {
        c[i] = c[i - 1] * x;
    }
    c
}

/// returns the coordinates of a commitment point. This is compatible with the arkworks
/// GC.to_constraint_field()[..2]
pub fn get_cm_coordinates<C: CurveGroup>(cm: &C) -> Vec<C::BaseField> {
    let zero = (&C::BaseField::zero(), &C::BaseField::zero());
    let cm = cm.into_affine();
    let (cm_x, cm_y) = cm.xy().unwrap_or(zero);
    vec![*cm_x, *cm_y]
}
