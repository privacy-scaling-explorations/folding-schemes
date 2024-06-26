use ark_ff::PrimeField;

use crate::Error;

pub mod ccs;
pub mod r1cs;

pub trait Arith<F: PrimeField> {
    /// Checks that the given Arith structure is satisfied by a z vector. Used only for testing.
    fn check_relation(&self, z: &[F]) -> Result<(), Error>;

    /// Returns the bytes that represent the parameters, that is, the matrices sizes, the amount of
    /// public inputs, etc, without the matrices/polynomials values.
    fn params_to_bytes(&self) -> Vec<u8>;
}
