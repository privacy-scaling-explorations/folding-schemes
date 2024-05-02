use ark_crypto_primitives::sponge::{constraints::CryptographicSpongeVar, CryptographicSponge};
use ark_ec::CurveGroup;
use ark_ff::PrimeField;
use ark_r1cs_std::{
    boolean::Boolean, fields::fp::FpVar, groups::CurveVar, ToConstraintFieldGadget,
};
use ark_relations::r1cs::SynthesisError;

pub mod poseidon;

pub trait AbsorbNonNative<F: PrimeField> {
    /// Converts the object into field elements that can be absorbed by a `CryptographicSponge`.
    /// Append the list to `dest`
    fn to_native_sponge_field_elements(&self, dest: &mut Vec<F>);

    /// Converts the object into field elements that can be absorbed by a `CryptographicSponge`.
    /// Return the list as `Vec`
    fn to_native_sponge_field_elements_as_vec(&self) -> Vec<F> {
        let mut result = Vec::new();
        self.to_native_sponge_field_elements(&mut result);
        result
    }
}

pub trait AbsorbNonNativeGadget<F: PrimeField> {
    /// Converts the object into field elements that can be absorbed by a `CryptographicSpongeVar`.
    fn to_native_sponge_field_elements(&self) -> Result<Vec<FpVar<F>>, SynthesisError>;
}

pub trait Transcript<F: PrimeField>: CryptographicSponge {
    /// `absorb_point` is only for points whose `BaseField` is the field of the
    /// sponge.
    ///
    /// If sponge field is `C::ScalarField`, call `absorb_nonnative` instead.
    fn absorb_point<C: CurveGroup<BaseField = F>>(&mut self, v: &C);
    fn absorb_nonnative<V: AbsorbNonNative<F>>(&mut self, v: &V);

    fn get_challenge(&mut self) -> F;
    /// get_challenge_nbits returns a field element of size nbits
    fn get_challenge_nbits(&mut self, nbits: usize) -> Vec<bool>;
    fn get_challenges(&mut self, n: usize) -> Vec<F>;
}

pub trait TranscriptVar<F: PrimeField, S: CryptographicSponge>:
    CryptographicSpongeVar<F, S>
{
    /// `absorb_point` is only for points whose `BaseField` is the field of the
    /// sponge.
    ///
    /// If sponge field is `C::ScalarField`, call `absorb_nonnative` instead.
    fn absorb_point<C: CurveGroup<BaseField = F>, GC: CurveVar<C, F> + ToConstraintFieldGadget<F>>(
        &mut self,
        v: &GC,
    ) -> Result<(), SynthesisError>;
    fn absorb_nonnative<V: AbsorbNonNativeGadget<F>>(
        &mut self,
        v: &V,
    ) -> Result<(), SynthesisError>;

    fn get_challenge(&mut self) -> Result<FpVar<F>, SynthesisError>;
    /// returns the bit representation of the challenge, we use its output in-circuit for the
    /// `GC.scalar_mul_le` method.
    fn get_challenge_nbits(&mut self, nbits: usize) -> Result<Vec<Boolean<F>>, SynthesisError>;
    fn get_challenges(&mut self, n: usize) -> Result<Vec<FpVar<F>>, SynthesisError>;
}
