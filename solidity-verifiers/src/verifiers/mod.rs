//! Solidity templates for the verifier contracts.
//! We use askama for templating and define which variables are required for each template.

// Pragma statements for verifiers
pub(crate) const PRAGMA_GROTH16_VERIFIER: &str = "pragma solidity >=0.7.0 <0.9.0;"; // from snarkjs, avoid changing
pub(crate) const PRAGMA_KZG10_VERIFIER: &str = "pragma solidity >=0.8.1 <=0.8.4;";

/// Default SDPX License identifier
pub(crate) const GPL3_SDPX_IDENTIFIER: &str = "// SPDX-License-Identifier: GPL-3.0";
pub(crate) const MIT_SDPX_IDENTIFIER: &str = "// SPDX-License-Identifier: MIT";
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, Read, SerializationError, Write};

mod g16;
mod kzg;
mod nova_cyclefold;

pub use g16::Groth16Data;
pub use kzg::KzgData;
pub use nova_cyclefold::NovaCyclefoldData;

pub trait ProtocolData: CanonicalDeserialize + CanonicalSerialize {
    const PROTOCOL_NAME: &'static str;

    fn serialize_name<W: Write>(&self, writer: &mut W) -> Result<(), SerializationError> {
        Self::PROTOCOL_NAME
            .to_string()
            .serialize_uncompressed(writer)
    }

    fn serialize_protocol_data<W: Write>(&self, writer: &mut W) -> Result<(), SerializationError> {
        self.serialize_name(writer)?;
        self.serialize_compressed(writer)
    }
    fn deserialize_protocol_data<R: Read + Copy>(
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
mod tests {
    use crate::evm::{compile_solidity, save_solidity, Evm};
    use crate::utils::HeaderInclusion;
    use crate::{Groth16Data, KzgData, NovaCyclefoldData, ProtocolData};
    use ark_bn254::{constraints::GVar, Bn254, Fr, G1Projective as G1};
    use ark_crypto_primitives::snark::{CircuitSpecificSetupSNARK, SNARK};
    use ark_ec::{AffineRepr, CurveGroup};
    use ark_ff::{BigInt, BigInteger, PrimeField};
    use ark_groth16::Groth16;
    use ark_groth16::VerifyingKey as G16VerifierKey;
    use ark_grumpkin::{constraints::GVar as GVar2, Projective as G2};
    use ark_poly_commit::kzg10::VerifierKey as KZGVerifierKey;
    use ark_r1cs_std::alloc::AllocVar;
    use ark_r1cs_std::eq::EqGadget;
    use ark_r1cs_std::fields::fp::FpVar;
    use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError};
    use ark_std::rand::{RngCore, SeedableRng};
    use ark_std::Zero;
    use ark_std::{test_rng, UniformRand};
    use askama::Template;
    use itertools::chain;
    use std::marker::PhantomData;
    use std::time::Instant;

    use folding_schemes::{
        commitment::{
            kzg::{ProverKey as KZGProverKey, KZG},
            pedersen::Pedersen,
            CommitmentScheme,
        },
        folding::nova::{
            decider_eth::{prepare_calldata, Decider as DeciderEth, Proof as DeciderProof},
            decider_eth_circuit::DeciderEthCircuit,
            get_cs_params_len, Nova, ProverParams,
        },
        frontend::FCircuit,
        transcript::{
            poseidon::{poseidon_test_config, PoseidonTranscript},
            Transcript,
        },
        Decider, Error, FoldingScheme,
    };

    use super::g16::Groth16Verifier;
    use super::kzg::KZG10Verifier;
    use super::nova_cyclefold::NovaCyclefoldDecider;

    // Function signatures for proof verification on kzg10 and groth16 contracts
    pub const FUNCTION_SIGNATURE_KZG10_CHECK: [u8; 4] = [0x9e, 0x78, 0xcc, 0xf7];
    pub const FUNCTION_SIGNATURE_GROTH16_VERIFY_PROOF: [u8; 4] = [0x43, 0x75, 0x3b, 0x4d];
    pub const FUNCTION_SIGNATURE_NOVA_CYCLEFOLD_CHECK: [u8; 4] = [0x37, 0x98, 0x0b, 0xb6];

    /// Default setup length for testing.
    const DEFAULT_SETUP_LEN: usize = 5;

    /// Test circuit used to test the Groth16 proof generation
    #[derive(Debug, Clone, Copy)]
    struct TestAddCircuit<F: PrimeField> {
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
    /// Test circuit to be folded
    #[derive(Clone, Copy, Debug)]
    pub struct CubicFCircuit<F: PrimeField> {
        _f: PhantomData<F>,
    }
    impl<F: PrimeField> FCircuit<F> for CubicFCircuit<F> {
        type Params = ();
        fn new(_params: Self::Params) -> Self {
            Self { _f: PhantomData }
        }
        fn state_len(&self) -> usize {
            1
        }
        fn step_native(&self, _i: usize, z_i: Vec<F>) -> Result<Vec<F>, Error> {
            Ok(vec![z_i[0] * z_i[0] * z_i[0] + z_i[0] + F::from(5_u32)])
        }
        fn generate_step_constraints(
            &self,
            cs: ConstraintSystemRef<F>,
            _i: usize,
            z_i: Vec<FpVar<F>>,
        ) -> Result<Vec<FpVar<F>>, SynthesisError> {
            let five = FpVar::<F>::new_constant(cs.clone(), F::from(5u32))?;
            let z_i = z_i[0].clone();

            Ok(vec![&z_i * &z_i * &z_i + &z_i + &five])
        }
    }

    #[allow(clippy::type_complexity)]
    fn setup<'a>(
        n: usize,
    ) -> (
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
        (kzg_pk, kzg_vk, g16_pk, g16_vk, circuit)
    }

    #[test]
    fn groth16_data_serde_roundtrip() {
        let (_, _, _, vk, _) = setup(DEFAULT_SETUP_LEN);

        let g16_data = Groth16Data::from(vk);
        let mut bytes = vec![];
        g16_data.serialize_protocol_data(&mut bytes).unwrap();
        let obtained_g16_data = Groth16Data::deserialize_protocol_data(bytes.as_slice()).unwrap();

        assert_eq!(g16_data, obtained_g16_data)
    }

    #[test]
    fn kzg_data_serde_roundtrip() {
        let (pk, vk, _, _, _) = setup(DEFAULT_SETUP_LEN);

        let kzg_data = KzgData::from((vk, Some(pk.powers_of_g[0..3].to_vec())));
        let mut bytes = vec![];
        kzg_data.serialize_protocol_data(&mut bytes).unwrap();
        let obtained_kzg_data = KzgData::deserialize_protocol_data(bytes.as_slice()).unwrap();

        assert_eq!(kzg_data, obtained_kzg_data)
    }

    #[test]
    fn nova_cyclefold_data_serde_roundtrip() {
        let (kzg_pk, kzg_vk, _, g16_vk, _) = setup(DEFAULT_SETUP_LEN);
        let g16_data = Groth16Data::from(g16_vk);
        let kzg_data = KzgData::from((kzg_vk, Some(kzg_pk.powers_of_g[0..3].to_vec())));

        let mut bytes = vec![];
        let nova_cyclefold_data = NovaCyclefoldData::from((g16_data, kzg_data));

        nova_cyclefold_data
            .serialize_protocol_data(&mut bytes)
            .unwrap();
        let obtained_nova_cyclefold_data =
            NovaCyclefoldData::deserialize_protocol_data(bytes.as_slice()).unwrap();

        assert_eq!(nova_cyclefold_data, obtained_nova_cyclefold_data)
    }

    #[test]
    fn nova_cyclefold_decider_template_renders() {
        let (kzg_pk, kzg_vk, _, g16_vk, _) = setup(DEFAULT_SETUP_LEN);
        let g16_data = Groth16Data::from(g16_vk);
        let kzg_data = KzgData::from((kzg_vk, Some(kzg_pk.powers_of_g[0..3].to_vec())));
        let nova_cyclefold_data = NovaCyclefoldData::from((g16_data, kzg_data));

        let decider_template = HeaderInclusion::<NovaCyclefoldDecider>::builder()
            .template(nova_cyclefold_data)
            .build();

        save_solidity("NovaDecider.sol", &decider_template.render().unwrap());
    }

    #[test]
    fn nova_cyclefold_decider_template_compiles() {
        let (kzg_pk, kzg_vk, _, g16_vk, _) = setup(DEFAULT_SETUP_LEN);
        let g16_data = Groth16Data::from(g16_vk);
        let kzg_data = KzgData::from((kzg_vk, Some(kzg_pk.powers_of_g[0..3].to_vec())));
        let nova_cyclefold_data = NovaCyclefoldData::from((g16_data, kzg_data));

        let decider_template = HeaderInclusion::<NovaCyclefoldDecider>::builder()
            .template(nova_cyclefold_data)
            .build();
        let decider_verifier_bytecode =
            compile_solidity(decider_template.render().unwrap(), "NovaDecider");
        let mut evm = Evm::default();
        _ = evm.create(decider_verifier_bytecode);
    }

    #[test]
    fn test_groth16_verifier_accepts_and_rejects_proofs() {
        let mut rng = ark_std::rand::rngs::StdRng::seed_from_u64(test_rng().next_u64());
        let (_, _, g16_pk, g16_vk, circuit) = setup(DEFAULT_SETUP_LEN);
        let g16_data = Groth16Data::from(g16_vk);

        let proof = Groth16::<Bn254>::prove(&g16_pk, circuit, &mut rng).unwrap();
        let res = Groth16Verifier::from(g16_data).render().unwrap();
        save_solidity("groth16_verifier.sol", &res);
        let groth16_verifier_bytecode = compile_solidity(&res, "Verifier");
        let mut evm = Evm::default();
        let verifier_address = evm.create(groth16_verifier_bytecode);
        let (a_x, a_y) = proof.a.xy().unwrap();
        let (b_x, b_y) = proof.b.xy().unwrap();
        let (c_x, c_y) = proof.c.xy().unwrap();
        let mut calldata: Vec<u8> = chain![
            FUNCTION_SIGNATURE_GROTH16_VERIFY_PROOF,
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

    #[test]
    fn kzg_verifier_template_renders() {
        let (kzg_pk, kzg_vk, _, _, _) = setup(DEFAULT_SETUP_LEN);
        let kzg_data = KzgData::from((kzg_vk.clone(), Some(kzg_pk.powers_of_g[0..3].to_vec())));

        let res = HeaderInclusion::<KZG10Verifier>::builder()
            .template(kzg_data)
            .build()
            .render()
            .unwrap();

        // TODO: Unsure what this is testing. If we want to test correct rendering,
        // we should first check that it COMPLETELY renders to what we expect.
        assert!(res.contains(&kzg_vk.g.x.to_string()));
    }

    #[test]
    fn kzg_verifier_compiles() {
        let (kzg_pk, kzg_vk, _, _, _) = setup(DEFAULT_SETUP_LEN);
        let kzg_data = KzgData::from((kzg_vk.clone(), Some(kzg_pk.powers_of_g[0..3].to_vec())));

        let res = HeaderInclusion::<KZG10Verifier>::builder()
            .template(kzg_data)
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
        let poseidon_config = poseidon_test_config::<Fr>();
        let transcript_p = &mut PoseidonTranscript::<G1>::new(&poseidon_config);
        let transcript_v = &mut PoseidonTranscript::<G1>::new(&poseidon_config);

        let (kzg_pk, kzg_vk, _, _, _) = setup(DEFAULT_SETUP_LEN);
        let kzg_data = KzgData::from((kzg_vk.clone(), Some(kzg_pk.powers_of_g[0..3].to_vec())));

        let v: Vec<Fr> = std::iter::repeat_with(|| Fr::rand(&mut rng))
            .take(DEFAULT_SETUP_LEN)
            .collect();
        let cm = KZG::<Bn254>::commit(&kzg_pk, &v, &Fr::zero()).unwrap();
        let proof = KZG::<Bn254>::prove(&kzg_pk, transcript_p, &cm, &v, &Fr::zero(), None).unwrap();
        let template = HeaderInclusion::<KZG10Verifier>::builder()
            .template(kzg_data)
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
            FUNCTION_SIGNATURE_KZG10_CHECK,
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

    #[test]
    fn nova_cyclefold_verifier_compiles() {
        let (kzg_pk, kzg_vk, _, g16_vk, _) = setup(DEFAULT_SETUP_LEN);
        let g16_data = Groth16Data::from(g16_vk);
        let kzg_data = KzgData::from((kzg_vk, Some(kzg_pk.powers_of_g[0..3].to_vec())));
        let nova_cyclefold_data = NovaCyclefoldData::from((g16_data, kzg_data));

        let decider_template = HeaderInclusion::<NovaCyclefoldDecider>::builder()
            .template(nova_cyclefold_data)
            .build()
            .render()
            .unwrap();

        let nova_cyclefold_verifier_bytecode = compile_solidity(decider_template, "NovaDecider");
        let mut evm = Evm::default();
        _ = evm.create(nova_cyclefold_verifier_bytecode);
    }

    #[test]
    fn nova_cyclefold_verifier_accepts_and_rejects_proofs() {
        // Nova+CycleFold DeciderEth proof generation
        let (nova, kzg_pk, kzg_vk, g16_vk, proof) = prepare_nova();

        let g16_data = Groth16Data::from(g16_vk);
        let kzg_data = KzgData::from((kzg_vk, Some(kzg_pk.powers_of_g[0..3].to_vec())));
        let nova_cyclefold_data = NovaCyclefoldData::from((g16_data, kzg_data));

        // generate the calldata out of the proof
        dbg!("generating calldata...");
        let mut calldata: Vec<u8> = prepare_calldata(
            FUNCTION_SIGNATURE_NOVA_CYCLEFOLD_CHECK,
            nova.i,
            nova.z_0,
            nova.z_i,
            &nova.U_i,
            &nova.u_i,
            proof,
        )
        .unwrap();
        dbg!("...calldata generated");

        let decider_template = HeaderInclusion::<NovaCyclefoldDecider>::builder()
            .template(nova_cyclefold_data)
            .build()
            .render()
            .unwrap();
        let nova_cyclefold_verifier_bytecode = compile_solidity(decider_template, "NovaDecider");

        let mut evm = Evm::default();
        let verifier_address = evm.create(nova_cyclefold_verifier_bytecode);

        let (_, output) = evm.call(verifier_address, calldata.clone());
        assert_eq!(*output.last().unwrap(), 1);

        // change calldata to make it invalid
        let last_calldata_element = calldata.last_mut().unwrap();
        *last_calldata_element = 0;
        let (_, output) = evm.call(verifier_address, calldata);
        assert_eq!(*output.last().unwrap(), 0);
    }

    /// prepare_nova returns a Nova instance, and the KZGProverKey, KZGVerifierKey,
    /// Groth16VerifierKey and Nova Proof
    #[allow(clippy::type_complexity)]
    #[allow(clippy::upper_case_acronyms)]
    fn prepare_nova() -> (
        Nova<G1, GVar, G2, GVar2, CubicFCircuit<Fr>, KZG<'static, Bn254>, Pedersen<G2>>,
        KZGProverKey<'static, G1>,
        KZGVerifierKey<Bn254>,
        G16VerifierKey<Bn254>,
        DeciderProof<G1, KZG<'static, Bn254>, Groth16<Bn254>>,
    ) {
        type NOVA = Nova<G1, GVar, G2, GVar2, CubicFCircuit<Fr>, KZG<'static, Bn254>, Pedersen<G2>>;
        type DECIDER = DeciderEth<
            G1,
            GVar,
            G2,
            GVar2,
            CubicFCircuit<Fr>,
            KZG<'static, Bn254>,
            Pedersen<G2>,
            Groth16<Bn254>,
            NOVA,
        >;

        let mut rng = ark_std::test_rng();
        let poseidon_config = poseidon_test_config::<Fr>();

        let f_circuit = CubicFCircuit::<Fr>::new(());
        let z_0 = vec![Fr::from(3_u32)];

        let (cs_len, cf_cs_len) = get_cs_params_len::<G1, GVar, G2, GVar2, CubicFCircuit<Fr>>(
            &poseidon_config,
            f_circuit,
        )
        .unwrap();
        let start = Instant::now();
        let (kzg_pk, kzg_vk): (KZGProverKey<G1>, KZGVerifierKey<Bn254>) =
            KZG::<Bn254>::setup(&mut rng, cs_len).unwrap();
        let (cf_pedersen_params, _) = Pedersen::<G2>::setup(&mut rng, cf_cs_len).unwrap();
        println!("generated KZG params, {:?}", start.elapsed());

        let prover_params = ProverParams::<G1, G2, KZG<Bn254>, Pedersen<G2>> {
            poseidon_config: poseidon_config.clone(),
            cs_params: kzg_pk.clone(),
            cf_cs_params: cf_pedersen_params,
        };

        let start = Instant::now();
        let mut nova = NOVA::init(&prover_params, f_circuit, z_0.clone()).unwrap();
        println!("Nova initialized, {:?}", start.elapsed());
        let start = Instant::now();
        nova.prove_step().unwrap();
        println!("prove_step, {:?}", start.elapsed());

        // generate Groth16 setup
        let circuit =
            DeciderEthCircuit::<G1, GVar, G2, GVar2, KZG<Bn254>, Pedersen<G2>>::from_nova::<
                CubicFCircuit<Fr>,
            >(nova.clone())
            .unwrap();
        let mut rng = rand::rngs::OsRng;

        let start = Instant::now();
        let (g16_pk, g16_vk) =
            Groth16::<Bn254>::circuit_specific_setup(circuit.clone(), &mut rng).unwrap();
        println!("Groth16 setup, {:?}", start.elapsed());

        // decider proof generation
        let start = Instant::now();
        let decider_pp = (poseidon_config.clone(), g16_pk, kzg_pk.clone());
        let proof = DECIDER::prove(decider_pp, rng, nova.clone()).unwrap();
        println!("Decider prove, {:?}", start.elapsed());

        // decider proof verification
        let start = Instant::now();
        let decider_vp = (g16_vk.clone(), kzg_vk.clone());
        let verified = DECIDER::verify(
            decider_vp,
            nova.i,
            nova.z_0.clone(),
            nova.z_i.clone(),
            &nova.U_i,
            &nova.u_i,
            &proof,
        )
        .unwrap();
        assert!(verified);
        println!("Decider verify, {:?}", start.elapsed());
        (nova, kzg_pk, kzg_vk, g16_vk, proof)
    }
}
