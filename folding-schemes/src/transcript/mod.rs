use crate::{folding::circuits::nonnative::affine::NonNativeAffineVar, Error};
use ark_ec::CurveGroup;
use ark_ff::PrimeField;
use ark_r1cs_std::{boolean::Boolean, fields::fp::FpVar};
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};
use ark_std::fmt::Debug;

pub mod poseidon;

pub trait Transcript<C: CurveGroup> {
    type TranscriptConfig: Debug;

    fn new(config: &Self::TranscriptConfig) -> Self;
    fn absorb(&mut self, v: &C::ScalarField);
    fn absorb_vec(&mut self, v: &[C::ScalarField]);
    fn absorb_point(&mut self, v: &C) -> Result<(), Error>;
    fn get_challenge(&mut self) -> C::ScalarField;
    /// get_challenge_nbits returns a field element of size nbits
    fn get_challenge_nbits(&mut self, nbits: usize) -> Vec<bool>;
    fn get_challenges(&mut self, n: usize) -> Vec<C::ScalarField>;
}

pub trait TranscriptVar<F: PrimeField> {
    type TranscriptVarConfig: Debug;

    fn new(cs: ConstraintSystemRef<F>, poseidon_config: &Self::TranscriptVarConfig) -> Self;
    fn absorb(&mut self, v: &FpVar<F>) -> Result<(), SynthesisError>;
    fn absorb_vec(&mut self, v: &[FpVar<F>]) -> Result<(), SynthesisError>;
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
