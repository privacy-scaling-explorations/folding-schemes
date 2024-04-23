use crate::{folding::circuits::nonnative::affine::NonNativeAffineVar, Error};
use ark_crypto_primitives::sponge::{constraints::CryptographicSpongeVar, CryptographicSponge};
use ark_ec::CurveGroup;
use ark_ff::PrimeField;
use ark_r1cs_std::{boolean::Boolean, fields::fp::FpVar};
use ark_relations::r1cs::SynthesisError;

pub mod poseidon;

pub trait Transcript<F: PrimeField>: CryptographicSponge {
    fn absorb_point<C: CurveGroup<ScalarField = F>>(&mut self, v: &C) -> Result<(), Error>;

    fn get_challenge(&mut self) -> F;
    /// get_challenge_nbits returns a field element of size nbits
    fn get_challenge_nbits(&mut self, nbits: usize) -> Vec<bool>;
    fn get_challenges(&mut self, n: usize) -> Vec<F>;
}

pub trait TranscriptVar<F: PrimeField, S: CryptographicSponge>:
    CryptographicSpongeVar<F, S>
{
    fn absorb_point<C: CurveGroup<ScalarField = F>>(
        &mut self,
        v: &NonNativeAffineVar<C>,
    ) -> Result<(), SynthesisError>;

    fn get_challenge(&mut self) -> Result<FpVar<F>, SynthesisError>;
    /// returns the bit representation of the challenge, we use its output in-circuit for the
    /// `GC.scalar_mul_le` method.
    fn get_challenge_nbits(&mut self, nbits: usize) -> Result<Vec<Boolean<F>>, SynthesisError>;
    fn get_challenges(&mut self, n: usize) -> Result<Vec<FpVar<F>>, SynthesisError>;
}
