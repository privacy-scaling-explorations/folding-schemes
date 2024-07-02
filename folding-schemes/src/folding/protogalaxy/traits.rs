use ark_crypto_primitives::sponge::{constraints::AbsorbGadget, Absorb};
use ark_ec::CurveGroup;
use ark_ff::PrimeField;
use ark_r1cs_std::{fields::fp::FpVar, uint8::UInt8, ToConstraintFieldGadget};
use ark_relations::r1cs::SynthesisError;

use super::{CommittedInstance, CommittedInstanceVar};
use crate::folding::circuits::nonnative::affine::nonnative_affine_to_field_elements;

// Implements the trait for absorbing ProtoGalaxy's CommittedInstance.
impl<C: CurveGroup<ScalarField: Absorb>> Absorb for CommittedInstance<C> {
    fn to_sponge_bytes(&self, _dest: &mut Vec<u8>) {
        unimplemented!()
    }

    fn to_sponge_field_elements<F: PrimeField>(&self, dest: &mut Vec<F>) {
        let (x, y) = nonnative_affine_to_field_elements(self.phi);
        x.to_sponge_field_elements(dest);
        y.to_sponge_field_elements(dest);
        self.betas.to_sponge_field_elements(dest);
        self.e.to_sponge_field_elements(dest);
    }
}

// Implements the trait for absorbing ProtoGalaxy's CommittedInstanceVar in-circuit.
impl<C: CurveGroup> AbsorbGadget<C::ScalarField> for CommittedInstanceVar<C> {
    fn to_sponge_bytes(&self) -> Result<Vec<UInt8<C::ScalarField>>, SynthesisError> {
        unimplemented!()
    }

    fn to_sponge_field_elements(&self) -> Result<Vec<FpVar<C::ScalarField>>, SynthesisError> {
        Ok([
            self.phi.to_constraint_field()?,
            self.betas.to_sponge_field_elements()?,
            self.e.to_sponge_field_elements()?,
        ]
        .concat())
    }
}
