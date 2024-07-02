//! Solidity templates for the verifier contracts.
//! We use askama for templating and define which variables are required for each template.

// Pragma statements for verifiers
pub const PRAGMA_GROTH16_VERIFIER: &str = "pragma solidity >=0.7.0 <0.9.0;"; // from snarkjs, avoid changing
pub const PRAGMA_KZG10_VERIFIER: &str = "pragma solidity >=0.8.1 <=0.8.4;";

/// Default SDPX License identifier
pub const GPL3_SDPX_IDENTIFIER: &str = "// SPDX-License-Identifier: GPL-3.0";
pub const MIT_SDPX_IDENTIFIER: &str = "// SPDX-License-Identifier: MIT";
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, Read, SerializationError, Write};

pub mod g16;
pub mod kzg;
pub mod nova_cyclefold;

pub use g16::Groth16VerifierKey;
pub use kzg::KZG10VerifierKey;
pub use nova_cyclefold::{get_decider_template_for_cyclefold_decider, NovaCycleFoldVerifierKey};

pub trait ProtocolVerifierKey: CanonicalDeserialize + CanonicalSerialize {
    const PROTOCOL_NAME: &'static str;

    fn serialize_name<W: Write>(&self, writer: &mut W) -> Result<(), SerializationError> {
        Self::PROTOCOL_NAME
            .to_string()
            .serialize_uncompressed(writer)
    }

    fn serialize_protocol_verifier_key<W: Write>(
        &self,
        writer: &mut W,
    ) -> Result<(), SerializationError> {
        self.serialize_name(writer)?;
        self.serialize_compressed(writer)
    }
    fn deserialize_protocol_verifier_key<R: Read + Copy>(
        mut reader: R,
    ) -> Result<Self, SerializationError> {
        let name: String = String::deserialize_uncompressed(&mut reader)?;
        let data = Self::deserialize_compressed(&mut reader)?;

        if name != Self::PROTOCOL_NAME {
            return Err(SerializationError::InvalidData);
        }

        Ok(data)
    }

    fn render_as_template(self, pragma: Option<String>) -> Vec<u8>;
}

#[cfg(test)]
pub mod tests {
    use ark_bn254::{Bn254, Fr, G1Projective as G1};
    use ark_crypto_primitives::snark::CircuitSpecificSetupSNARK;
    use ark_ff::PrimeField;
    use ark_groth16::Groth16;
    use ark_poly_commit::kzg10::VerifierKey as KZGVerifierKey;
    use ark_r1cs_std::alloc::AllocVar;
    use ark_r1cs_std::eq::EqGadget;
    use ark_r1cs_std::fields::fp::FpVar;
    use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError};
    use ark_std::rand::{RngCore, SeedableRng};
    use ark_std::test_rng;
    use std::marker::PhantomData;

    use folding_schemes::commitment::{
        kzg::{ProverKey as KZGProverKey, KZG},
        CommitmentScheme,
    };

    /// Default setup length for testing.
    pub const DEFAULT_SETUP_LEN: usize = 5;

    /// Test circuit used to test the Groth16 proof generation
    #[derive(Debug, Clone, Copy)]
    pub struct TestAddCircuit<F: PrimeField> {
        _f: PhantomData<F>,
        pub x: u8,
        pub y: u8,
        pub z: u8,
    }

    impl<F: PrimeField> ConstraintSynthesizer<F> for TestAddCircuit<F> {
        fn generate_constraints(self, cs: ConstraintSystemRef<F>) -> Result<(), SynthesisError> {
            let x = FpVar::<F>::new_witness(cs.clone(), || Ok(F::from(self.x)))?;
            let y = FpVar::<F>::new_witness(cs.clone(), || Ok(F::from(self.y)))?;
            let z = FpVar::<F>::new_input(cs.clone(), || Ok(F::from(self.z)))?;
            let comp_z = x.clone() + y.clone();
            comp_z.enforce_equal(&z)?;
            Ok(())
        }
    }

    #[allow(clippy::type_complexity)]
    pub fn setup<'a>(
        n: usize,
    ) -> (
        Fr, // public params hash
        KZGProverKey<'a, G1>,
        KZGVerifierKey<Bn254>,
        ark_groth16::ProvingKey<Bn254>,
        ark_groth16::VerifyingKey<Bn254>,
        TestAddCircuit<Fr>,
    ) {
        let mut rng = ark_std::rand::rngs::StdRng::seed_from_u64(test_rng().next_u64());
        let (x, y, z) = (21, 21, 42);
        let circuit = TestAddCircuit::<Fr> {
            _f: PhantomData,
            x,
            y,
            z,
        };
        let (g16_pk, g16_vk) = Groth16::<Bn254>::setup(circuit, &mut rng).unwrap();

        let (kzg_pk, kzg_vk): (KZGProverKey<G1>, KZGVerifierKey<Bn254>) =
            KZG::<Bn254>::setup(&mut rng, n).unwrap();
        let pp_hash = Fr::from(42u32); // only for test
        (pp_hash, kzg_pk, kzg_vk, g16_pk, g16_vk, circuit)
    }
}
