/// Circuits and gadgets shared across the different folding schemes.
use ark_ec::CurveGroup;
use ark_ff::Field;

pub mod hypernova;
pub mod nonnative;
pub mod sum_check;
pub mod utils;

// CF represents the constraints field
pub type CF<C> = <<C as CurveGroup>::BaseField as Field>::BasePrimeField;
