use crate::utils::encoding::{g1_to_fq_repr, g2_to_fq_repr};
use crate::utils::encoding::{G1Repr, G2Repr};
use crate::utils::HeaderInclusion;
use crate::{ProtocolVerifierKey, MIT_SDPX_IDENTIFIER};
use ark_bn254::{Bn254, G1Affine};
use ark_poly_commit::kzg10::VerifierKey;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use askama::Template;

use super::PRAGMA_KZG10_VERIFIER;

#[derive(Template, Default)]
#[template(path = "kzg10_verifier.askama.sol", ext = "sol")]
pub struct KZG10Verifier {
    /// The generator of `G1`.
    pub(crate) g1: G1Repr,
    /// The generator of `G2`.
    pub(crate) g2: G2Repr,
    /// The verification key
    pub(crate) vk: G2Repr,
    /// Length of the trusted setup vector.
    pub(crate) g1_crs_len: usize,
    /// The trusted setup vector.
    pub(crate) g1_crs: Vec<G1Repr>,
}

impl From<KZG10VerifierKey> for KZG10Verifier {
    fn from(data: KZG10VerifierKey) -> Self {
        Self {
            g1: g1_to_fq_repr(data.vk.g),
            g2: g2_to_fq_repr(data.vk.h),
            vk: g2_to_fq_repr(data.vk.beta_h),
            g1_crs_len: data.g1_crs_batch_points.len(),
            g1_crs: data
                .g1_crs_batch_points
                .iter()
                .map(|g1| g1_to_fq_repr(*g1))
                .collect(),
        }
    }
}

#[derive(CanonicalDeserialize, CanonicalSerialize, Clone, PartialEq, Debug)]
pub struct KZG10VerifierKey {
    pub vk: VerifierKey<Bn254>,
    pub g1_crs_batch_points: Vec<G1Affine>,
}

impl From<(VerifierKey<Bn254>, Vec<G1Affine>)> for KZG10VerifierKey {
    fn from(value: (VerifierKey<Bn254>, Vec<G1Affine>)) -> Self {
        Self {
            vk: value.0,
            g1_crs_batch_points: value.1,
        }
    }
}

impl ProtocolVerifierKey for KZG10VerifierKey {
    const PROTOCOL_NAME: &'static str = "KZG";

    fn render_as_template(self, pragma: Option<String>) -> Vec<u8> {
        HeaderInclusion::<KZG10Verifier>::builder()
            .sdpx(MIT_SDPX_IDENTIFIER.to_string())
            .pragma_version(pragma.unwrap_or(PRAGMA_KZG10_VERIFIER.to_string()))
            .template(self)
            .build()
            .render()
            .unwrap()
            .into_bytes()
    }
}

#[cfg(test)]
mod tests {
    use super::KZG10VerifierKey;
    use crate::{
        evm::{compile_solidity, Evm},
        utils::HeaderInclusion,
        ProtocolVerifierKey,
    };
    use ark_bn254::{Bn254, Fr, G1Projective as G1};
    use ark_ec::{AffineRepr, CurveGroup};
    use ark_ff::{BigInteger, PrimeField};
    use ark_std::rand::{RngCore, SeedableRng};
    use ark_std::Zero;
    use ark_std::{test_rng, UniformRand};
    use askama::Template;
    use itertools::chain;

    use folding_schemes::{
        commitment::{kzg::KZG, CommitmentScheme},
        transcript::{
            poseidon::{poseidon_canonical_config, PoseidonTranscript},
            Transcript,
        },
    };

    use super::KZG10Verifier;
    use crate::verifiers::tests::{setup, DEFAULT_SETUP_LEN};

    const FUNCTION_SELECTOR_KZG10_CHECK: [u8; 4] = [0x9e, 0x78, 0xcc, 0xf7];

    #[test]
    fn kzg_vk_serde_roundtrip() {
        let (_, pk, vk, _, _, _) = setup(DEFAULT_SETUP_LEN);

        let kzg_vk = KZG10VerifierKey::from((vk, pk.powers_of_g[0..3].to_vec()));
        let mut bytes = vec![];
        kzg_vk.serialize_protocol_verifier_key(&mut bytes).unwrap();
        let obtained_kzg_vk =
            KZG10VerifierKey::deserialize_protocol_verifier_key(bytes.as_slice()).unwrap();

        assert_eq!(kzg_vk, obtained_kzg_vk)
    }

    #[test]
    fn kzg_verifier_compiles() {
        let (_, kzg_pk, kzg_vk, _, _, _) = setup(DEFAULT_SETUP_LEN);
        let kzg_vk = KZG10VerifierKey::from((kzg_vk.clone(), kzg_pk.powers_of_g[0..3].to_vec()));

        let res = HeaderInclusion::<KZG10Verifier>::builder()
            .template(kzg_vk)
            .build()
            .render()
            .unwrap();

        let kzg_verifier_bytecode = compile_solidity(res, "KZG10");
        let mut evm = Evm::default();
        _ = evm.create(kzg_verifier_bytecode);
    }

    #[test]
    fn kzg_verifier_accepts_and_rejects_proofs() {
        let mut rng = ark_std::rand::rngs::StdRng::seed_from_u64(test_rng().next_u64());
        let poseidon_config = poseidon_canonical_config::<Fr>();
        let transcript_p = &mut PoseidonTranscript::<G1>::new(&poseidon_config);
        let transcript_v = &mut PoseidonTranscript::<G1>::new(&poseidon_config);

        let (_, kzg_pk, kzg_vk, _, _, _) = setup(DEFAULT_SETUP_LEN);
        let kzg_vk = KZG10VerifierKey::from((kzg_vk.clone(), kzg_pk.powers_of_g[0..3].to_vec()));

        let v: Vec<Fr> = std::iter::repeat_with(|| Fr::rand(&mut rng))
            .take(DEFAULT_SETUP_LEN)
            .collect();
        let cm = KZG::<Bn254>::commit(&kzg_pk, &v, &Fr::zero()).unwrap();
        let proof = KZG::<Bn254>::prove(&kzg_pk, transcript_p, &cm, &v, &Fr::zero(), None).unwrap();
        let template = HeaderInclusion::<KZG10Verifier>::builder()
            .template(kzg_vk)
            .build()
            .render()
            .unwrap();

        let kzg_verifier_bytecode = compile_solidity(template, "KZG10");
        let mut evm = Evm::default();
        let verifier_address = evm.create(kzg_verifier_bytecode);

        let (cm_affine, proof_affine) = (cm.into_affine(), proof.proof.into_affine());
        let (x_comm, y_comm) = cm_affine.xy().unwrap();
        let (x_proof, y_proof) = proof_affine.xy().unwrap();
        let y = proof.eval.into_bigint().to_bytes_be();

        transcript_v.absorb_point(&cm).unwrap();
        let x = transcript_v.get_challenge();

        let x = x.into_bigint().to_bytes_be();
        let mut calldata: Vec<u8> = chain![
            FUNCTION_SELECTOR_KZG10_CHECK,
            x_comm.into_bigint().to_bytes_be(),
            y_comm.into_bigint().to_bytes_be(),
            x_proof.into_bigint().to_bytes_be(),
            y_proof.into_bigint().to_bytes_be(),
            x.clone(),
            y,
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
