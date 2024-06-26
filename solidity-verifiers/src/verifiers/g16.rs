use crate::utils::encoding::{g1_to_fq_repr, g2_to_fq_repr};
use crate::utils::encoding::{G1Repr, G2Repr};
use crate::utils::HeaderInclusion;
use crate::{ProtocolVerifierKey, GPL3_SDPX_IDENTIFIER};
use ark_bn254::Bn254;
use ark_groth16::VerifyingKey as ArkVerifyingKey;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use askama::Template;

use super::PRAGMA_GROTH16_VERIFIER;

#[derive(Template, Default)]
#[template(path = "groth16_verifier.askama.sol", ext = "sol")]
pub struct Groth16Verifier {
    /// The `alpha * G`, where `G` is the generator of `G1`.
    pub vkey_alpha_g1: G1Repr,
    /// The `alpha * H`, where `H` is the generator of `G2`.
    pub vkey_beta_g2: G2Repr,
    /// The `gamma * H`, where `H` is the generator of `G2`.
    pub vkey_gamma_g2: G2Repr,
    /// The `delta * H`, where `H` is the generator of `G2`.
    pub vkey_delta_g2: G2Repr,
    /// Length of the `gamma_abc_g1` vector.
    pub gamma_abc_len: usize,
    /// The `gamma^{-1} * (beta * a_i + alpha * b_i + c_i) * H`, where `H` is the generator of `E::G1`.
    pub gamma_abc_g1: Vec<G1Repr>,
}

impl From<Groth16VerifierKey> for Groth16Verifier {
    fn from(g16_vk: Groth16VerifierKey) -> Self {
        Self {
            vkey_alpha_g1: g1_to_fq_repr(g16_vk.0.alpha_g1),
            vkey_beta_g2: g2_to_fq_repr(g16_vk.0.beta_g2),
            vkey_gamma_g2: g2_to_fq_repr(g16_vk.0.gamma_g2),
            vkey_delta_g2: g2_to_fq_repr(g16_vk.0.delta_g2),
            gamma_abc_len: g16_vk.0.gamma_abc_g1.len(),
            gamma_abc_g1: g16_vk
                .0
                .gamma_abc_g1
                .iter()
                .copied()
                .map(g1_to_fq_repr)
                .collect(),
        }
    }
}

// Ideally this would be linked to the `Decider` trait in FoldingSchemes.
// For now, this is the easiest as NovaCycleFold isn't clear target from where we can get all it's needed arguments.
#[derive(CanonicalDeserialize, CanonicalSerialize, Clone, PartialEq, Debug)]
pub struct Groth16VerifierKey(pub(crate) ArkVerifyingKey<Bn254>);

impl From<ArkVerifyingKey<Bn254>> for Groth16VerifierKey {
    fn from(value: ArkVerifyingKey<Bn254>) -> Self {
        Self(value)
    }
}

impl ProtocolVerifierKey for Groth16VerifierKey {
    const PROTOCOL_NAME: &'static str = "Groth16";

    fn render_as_template(self, pragma: Option<String>) -> Vec<u8> {
        HeaderInclusion::<Groth16Verifier>::builder()
            .sdpx(GPL3_SDPX_IDENTIFIER.to_string())
            .pragma_version(pragma.unwrap_or(PRAGMA_GROTH16_VERIFIER.to_string()))
            .template(self)
            .build()
            .render()
            .unwrap()
            .into_bytes()
    }
}

#[cfg(test)]
mod tests {
    use super::Groth16VerifierKey;
    use crate::{
        evm::{compile_solidity, save_solidity, Evm},
        ProtocolVerifierKey,
    };
    use ark_bn254::{Bn254, Fr};
    use ark_crypto_primitives::snark::SNARK;
    use ark_ec::AffineRepr;
    use ark_ff::{BigInt, BigInteger, PrimeField};
    use ark_groth16::Groth16;
    use ark_std::rand::{RngCore, SeedableRng};
    use ark_std::test_rng;
    use askama::Template;
    use itertools::chain;

    use super::Groth16Verifier;
    use crate::verifiers::tests::{setup, DEFAULT_SETUP_LEN};

    pub const FUNCTION_SELECTOR_GROTH16_VERIFY_PROOF: [u8; 4] = [0x43, 0x75, 0x3b, 0x4d];

    #[test]
    fn groth16_vk_serde_roundtrip() {
        let (_, _, _, _, vk, _) = setup(DEFAULT_SETUP_LEN);

        let g16_vk = Groth16VerifierKey::from(vk);
        let mut bytes = vec![];
        g16_vk.serialize_protocol_verifier_key(&mut bytes).unwrap();
        let obtained_g16_vk =
            Groth16VerifierKey::deserialize_protocol_verifier_key(bytes.as_slice()).unwrap();

        assert_eq!(g16_vk, obtained_g16_vk)
    }

    #[test]
    fn test_groth16_verifier_accepts_and_rejects_proofs() {
        let mut rng = ark_std::rand::rngs::StdRng::seed_from_u64(test_rng().next_u64());
        let (_, _, _, g16_pk, g16_vk, circuit) = setup(DEFAULT_SETUP_LEN);
        let g16_vk = Groth16VerifierKey::from(g16_vk);

        let proof = Groth16::<Bn254>::prove(&g16_pk, circuit, &mut rng).unwrap();
        let res = Groth16Verifier::from(g16_vk).render().unwrap();
        save_solidity("groth16_verifier.sol", &res);
        let groth16_verifier_bytecode = compile_solidity(&res, "Verifier");
        let mut evm = Evm::default();
        let verifier_address = evm.create(groth16_verifier_bytecode);
        let (a_x, a_y) = proof.a.xy().unwrap();
        let (b_x, b_y) = proof.b.xy().unwrap();
        let (c_x, c_y) = proof.c.xy().unwrap();
        let mut calldata: Vec<u8> = chain![
            FUNCTION_SELECTOR_GROTH16_VERIFY_PROOF,
            a_x.into_bigint().to_bytes_be(),
            a_y.into_bigint().to_bytes_be(),
            b_x.c1.into_bigint().to_bytes_be(),
            b_x.c0.into_bigint().to_bytes_be(),
            b_y.c1.into_bigint().to_bytes_be(),
            b_y.c0.into_bigint().to_bytes_be(),
            c_x.into_bigint().to_bytes_be(),
            c_y.into_bigint().to_bytes_be(),
            BigInt::from(Fr::from(circuit.z)).to_bytes_be(),
        ]
        .collect();
        let (_, output) = evm.call(verifier_address, calldata.clone());
        assert_eq!(*output.last().unwrap(), 1);

        // change calldata to make it invalid
        let last_calldata_element = calldata.last_mut().unwrap();
        *last_calldata_element = 0;
        let (_, output) = evm.call(verifier_address, calldata);
        assert_eq!(*output.last().unwrap(), 0);
    }
}
