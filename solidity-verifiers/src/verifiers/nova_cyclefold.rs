#![allow(non_snake_case)]
#![allow(non_camel_case_types)]
#![allow(clippy::upper_case_acronyms)]

use ark_bn254::{Bn254, Fq, Fr, G1Affine};
use ark_groth16::VerifyingKey as ArkG16VerifierKey;
use ark_poly_commit::kzg10::VerifierKey as ArkKZG10VerifierKey;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use askama::Template;

use folding_schemes::folding::circuits::nonnative::uint::NonNativeUintVar;

use super::g16::Groth16Verifier;
use super::kzg::KZG10Verifier;
use crate::utils::HeaderInclusion;
use crate::{Groth16VerifierKey, KZG10VerifierKey, ProtocolVerifierKey, PRAGMA_GROTH16_VERIFIER};

pub fn get_decider_template_for_cyclefold_decider(
    nova_cyclefold_vk: NovaCycleFoldVerifierKey,
) -> String {
    HeaderInclusion::<NovaCycleFoldDecider>::builder()
        .template(nova_cyclefold_vk)
        .build()
        .render()
        .unwrap()
}

#[derive(Template, Default)]
#[template(path = "nova_cyclefold_decider.askama.sol", ext = "sol")]
pub struct NovaCycleFoldDecider {
    pp_hash: Fr, // public params hash
    groth16_verifier: Groth16Verifier,
    kzg10_verifier: KZG10Verifier,
    // z_len denotes the FCircuit state (z_i) length
    z_len: usize,
    public_inputs_len: usize,
    num_limbs: usize,
    bits_per_limb: usize,
}

impl From<NovaCycleFoldVerifierKey> for NovaCycleFoldDecider {
    fn from(value: NovaCycleFoldVerifierKey) -> Self {
        let groth16_verifier = Groth16Verifier::from(value.g16_vk);
        let public_inputs_len = groth16_verifier.gamma_abc_len;
        let bits_per_limb = NonNativeUintVar::<Fq>::bits_per_limb();
        Self {
            pp_hash: value.pp_hash,
            groth16_verifier,
            kzg10_verifier: KZG10Verifier::from(value.kzg_vk),
            z_len: value.z_len,
            public_inputs_len,
            num_limbs: (250_f32 / (bits_per_limb as f32)).ceil() as usize,
            bits_per_limb,
        }
    }
}

#[derive(CanonicalDeserialize, CanonicalSerialize, PartialEq, Debug, Clone)]
pub struct NovaCycleFoldVerifierKey {
    pp_hash: Fr,
    g16_vk: Groth16VerifierKey,
    kzg_vk: KZG10VerifierKey,
    z_len: usize,
}

impl ProtocolVerifierKey for NovaCycleFoldVerifierKey {
    const PROTOCOL_NAME: &'static str = "NovaCycleFold";

    fn render_as_template(self, pragma: Option<String>) -> Vec<u8> {
        HeaderInclusion::<NovaCycleFoldDecider>::builder()
            .pragma_version(pragma.unwrap_or(PRAGMA_GROTH16_VERIFIER.to_string()))
            .template(self)
            .build()
            .render()
            .unwrap()
            .into_bytes()
    }
}

impl From<(Fr, Groth16VerifierKey, KZG10VerifierKey, usize)> for NovaCycleFoldVerifierKey {
    fn from(value: (Fr, Groth16VerifierKey, KZG10VerifierKey, usize)) -> Self {
        Self {
            pp_hash: value.0,
            g16_vk: value.1,
            kzg_vk: value.2,
            z_len: value.3,
        }
    }
}

// implements From assuming that the 'batchCheck' method from the KZG10 template will not be used
// in the NovaCycleFoldDecider verifier contract
impl
    From<(
        (Fr, ArkG16VerifierKey<Bn254>, ArkKZG10VerifierKey<Bn254>),
        usize,
    )> for NovaCycleFoldVerifierKey
{
    fn from(
        value: (
            (Fr, ArkG16VerifierKey<Bn254>, ArkKZG10VerifierKey<Bn254>),
            usize,
        ),
    ) -> Self {
        let decider_vp = value.0;
        let g16_vk = Groth16VerifierKey::from(decider_vp.1);
        // pass `Vec::new()` since batchCheck will not be used
        let kzg_vk = KZG10VerifierKey::from((decider_vp.2, Vec::new()));
        Self {
            pp_hash: decider_vp.0,
            g16_vk,
            kzg_vk,
            z_len: value.1,
        }
    }
}

impl NovaCycleFoldVerifierKey {
    pub fn new(
        pp_hash: Fr,
        vkey_g16: ArkG16VerifierKey<Bn254>,
        vkey_kzg: ArkKZG10VerifierKey<Bn254>,
        crs_points: Vec<G1Affine>,
        z_len: usize,
    ) -> Self {
        Self {
            pp_hash,
            g16_vk: Groth16VerifierKey::from(vkey_g16),
            kzg_vk: KZG10VerifierKey::from((vkey_kzg, crs_points)),
            z_len,
        }
    }
}

#[cfg(test)]
mod tests {
    use ark_bn254::{constraints::GVar, Bn254, Fr, G1Projective as G1};
    use ark_ff::PrimeField;
    use ark_groth16::Groth16;
    use ark_grumpkin::{constraints::GVar as GVar2, Projective as G2};
    use ark_r1cs_std::alloc::AllocVar;
    use ark_r1cs_std::fields::fp::FpVar;
    use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};
    use ark_std::Zero;
    use askama::Template;
    use std::marker::PhantomData;
    use std::time::Instant;

    use folding_schemes::{
        commitment::{kzg::KZG, pedersen::Pedersen},
        folding::nova::{
            decider_eth::{prepare_calldata, Decider as DeciderEth},
            Nova, PreprocessorParam,
        },
        frontend::FCircuit,
        transcript::poseidon::poseidon_canonical_config,
        Decider, Error, FoldingScheme,
    };

    use super::NovaCycleFoldDecider;
    use crate::verifiers::tests::{setup, DEFAULT_SETUP_LEN};
    use crate::{
        evm::{compile_solidity, save_solidity, Evm},
        utils::{get_function_selector_for_nova_cyclefold_verifier, HeaderInclusion},
        verifiers::nova_cyclefold::get_decider_template_for_cyclefold_decider,
        NovaCycleFoldVerifierKey, ProtocolVerifierKey,
    };

    type NOVA<FC> = Nova<G1, GVar, G2, GVar2, FC, KZG<'static, Bn254>, Pedersen<G2>>;
    type DECIDER<FC> = DeciderEth<
        G1,
        GVar,
        G2,
        GVar2,
        FC,
        KZG<'static, Bn254>,
        Pedersen<G2>,
        Groth16<Bn254>,
        NOVA<FC>,
    >;

    type FS_PP<FC> = <NOVA<FC> as FoldingScheme<G1, G2, FC>>::ProverParam;
    type FS_VP<FC> = <NOVA<FC> as FoldingScheme<G1, G2, FC>>::VerifierParam;
    type DECIDER_PP<FC> = <DECIDER<FC> as Decider<G1, G2, FC, NOVA<FC>>>::ProverParam;
    type DECIDER_VP<FC> = <DECIDER<FC> as Decider<G1, G2, FC, NOVA<FC>>>::VerifierParam;

    /// Test circuit to be folded
    #[derive(Clone, Copy, Debug)]
    pub struct CubicFCircuit<F: PrimeField> {
        _f: PhantomData<F>,
    }
    impl<F: PrimeField> FCircuit<F> for CubicFCircuit<F> {
        type Params = ();
        fn new(_params: Self::Params) -> Result<Self, Error> {
            Ok(Self { _f: PhantomData })
        }
        fn state_len(&self) -> usize {
            1
        }
        fn external_inputs_len(&self) -> usize {
            0
        }
        fn step_native(
            &self,
            _i: usize,
            z_i: Vec<F>,
            _external_inputs: Vec<F>,
        ) -> Result<Vec<F>, Error> {
            Ok(vec![z_i[0] * z_i[0] * z_i[0] + z_i[0] + F::from(5_u32)])
        }
        fn generate_step_constraints(
            &self,
            cs: ConstraintSystemRef<F>,
            _i: usize,
            z_i: Vec<FpVar<F>>,
            _external_inputs: Vec<FpVar<F>>,
        ) -> Result<Vec<FpVar<F>>, SynthesisError> {
            let five = FpVar::<F>::new_constant(cs.clone(), F::from(5u32))?;
            let z_i = z_i[0].clone();

            Ok(vec![&z_i * &z_i * &z_i + &z_i + &five])
        }
    }

    /// This is the circuit that we want to fold, it implements the FCircuit trait. The parameter z_i
    /// denotes the current state which contains 5 elements, and z_{i+1} denotes the next state which
    /// we get by applying the step.
    /// In this example we set z_i and z_{i+1} to have five elements, and at each step we do different
    /// operations on each of them.
    #[derive(Clone, Copy, Debug)]
    pub struct MultiInputsFCircuit<F: PrimeField> {
        _f: PhantomData<F>,
    }
    impl<F: PrimeField> FCircuit<F> for MultiInputsFCircuit<F> {
        type Params = ();

        fn new(_params: Self::Params) -> Result<Self, Error> {
            Ok(Self { _f: PhantomData })
        }
        fn state_len(&self) -> usize {
            5
        }
        fn external_inputs_len(&self) -> usize {
            0
        }

        /// computes the next state values in place, assigning z_{i+1} into z_i, and computing the new
        /// z_{i+1}
        fn step_native(
            &self,
            _i: usize,
            z_i: Vec<F>,
            _external_inputs: Vec<F>,
        ) -> Result<Vec<F>, Error> {
            let a = z_i[0] + F::from(4_u32);
            let b = z_i[1] + F::from(40_u32);
            let c = z_i[2] * F::from(4_u32);
            let d = z_i[3] * F::from(40_u32);
            let e = z_i[4] + F::from(100_u32);

            Ok(vec![a, b, c, d, e])
        }

        /// generates the constraints for the step of F for the given z_i
        fn generate_step_constraints(
            &self,
            cs: ConstraintSystemRef<F>,
            _i: usize,
            z_i: Vec<FpVar<F>>,
            _external_inputs: Vec<FpVar<F>>,
        ) -> Result<Vec<FpVar<F>>, SynthesisError> {
            let four = FpVar::<F>::new_constant(cs.clone(), F::from(4u32))?;
            let forty = FpVar::<F>::new_constant(cs.clone(), F::from(40u32))?;
            let onehundred = FpVar::<F>::new_constant(cs.clone(), F::from(100u32))?;
            let a = z_i[0].clone() + four.clone();
            let b = z_i[1].clone() + forty.clone();
            let c = z_i[2].clone() * four;
            let d = z_i[3].clone() * forty;
            let e = z_i[4].clone() + onehundred;

            Ok(vec![a, b, c, d, e])
        }
    }

    #[test]
    fn nova_cyclefold_vk_serde_roundtrip() {
        let (pp_hash, _, kzg_vk, _, g16_vk, _) = setup(DEFAULT_SETUP_LEN);

        let mut bytes = vec![];
        let nova_cyclefold_vk = NovaCycleFoldVerifierKey::from(((pp_hash, g16_vk, kzg_vk), 1));

        nova_cyclefold_vk
            .serialize_protocol_verifier_key(&mut bytes)
            .unwrap();
        let obtained_nova_cyclefold_vk =
            NovaCycleFoldVerifierKey::deserialize_protocol_verifier_key(bytes.as_slice()).unwrap();

        assert_eq!(nova_cyclefold_vk, obtained_nova_cyclefold_vk)
    }

    #[test]
    fn nova_cyclefold_decider_template_renders() {
        let (pp_hash, _, kzg_vk, _, g16_vk, _) = setup(DEFAULT_SETUP_LEN);
        let nova_cyclefold_vk = NovaCycleFoldVerifierKey::from(((pp_hash, g16_vk, kzg_vk), 1));

        let decider_solidity_code = HeaderInclusion::<NovaCycleFoldDecider>::builder()
            .template(nova_cyclefold_vk)
            .build();

        save_solidity("NovaDecider.sol", &decider_solidity_code.render().unwrap());
    }

    /// Initializes Nova parameters and DeciderEth parameters. Only for test purposes.
    #[allow(clippy::type_complexity)]
    fn init_params<FC: FCircuit<Fr, Params = ()>>(
    ) -> ((FS_PP<FC>, FS_VP<FC>), (DECIDER_PP<FC>, DECIDER_VP<FC>)) {
        let mut rng = rand::rngs::OsRng;
        let poseidon_config = poseidon_canonical_config::<Fr>();

        let f_circuit = FC::new(()).unwrap();
        let prep_param = PreprocessorParam::<G1, G2, FC, KZG<'static, Bn254>, Pedersen<G2>>::new(
            poseidon_config,
            f_circuit.clone(),
        );
        let nova_params = NOVA::preprocess(&mut rng, &prep_param).unwrap();
        let nova = NOVA::init(
            nova_params.clone(),
            f_circuit.clone(),
            vec![Fr::zero(); f_circuit.state_len()].clone(),
        )
        .unwrap();
        let decider_params =
            DECIDER::preprocess(&mut rng, &nova_params.clone(), nova.clone()).unwrap();

        (nova_params, decider_params)
    }

    /// This function allows to define which FCircuit to use for the test, and how many prove_step
    /// rounds to perform.
    /// Actions performed by this test:
    /// - runs the NovaCycleFold folding scheme for the given FCircuit and n_steps times
    /// - generates a DeciderEth proof, and executes it through the EVM
    /// - modifies the calldata and checks that it does not pass the EVM check
    /// - modifies the z_0 and checks that it does not pass the EVM check
    #[allow(clippy::type_complexity)]
    fn nova_cyclefold_solidity_verifier_opt<FC: FCircuit<Fr, Params = ()>>(
        fs_params: (FS_PP<FC>, FS_VP<FC>),
        decider_params: (DECIDER_PP<FC>, DECIDER_VP<FC>),
        z_0: Vec<Fr>,
        n_steps: usize,
    ) {
        let (decider_pp, decider_vp) = decider_params;

        let f_circuit = FC::new(()).unwrap();

        let nova_cyclefold_vk =
            NovaCycleFoldVerifierKey::from((decider_vp.clone(), f_circuit.state_len()));

        let mut rng = rand::rngs::OsRng;

        let mut nova = NOVA::<FC>::init(fs_params, f_circuit, z_0).unwrap();
        for _ in 0..n_steps {
            nova.prove_step(&mut rng, vec![], ()).unwrap();
        }

        let start = Instant::now();
        let proof = DECIDER::<FC>::prove(rng, decider_pp, nova.clone()).unwrap();
        println!("generated Decider proof: {:?}", start.elapsed());

        let verified = DECIDER::<FC>::verify(
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

        let function_selector =
            get_function_selector_for_nova_cyclefold_verifier(nova.z_0.len() * 2 + 1);

        let calldata: Vec<u8> = prepare_calldata(
            function_selector,
            nova.i,
            nova.z_0,
            nova.z_i,
            &nova.U_i,
            &nova.u_i,
            proof,
        )
        .unwrap();

        let decider_solidity_code = get_decider_template_for_cyclefold_decider(nova_cyclefold_vk);

        let nova_cyclefold_verifier_bytecode =
            compile_solidity(decider_solidity_code, "NovaDecider");

        let mut evm = Evm::default();
        let verifier_address = evm.create(nova_cyclefold_verifier_bytecode);

        let (_, output) = evm.call(verifier_address, calldata.clone());
        assert_eq!(*output.last().unwrap(), 1);

        // change i to make calldata invalid, placed between bytes 4 - 35
        let mut invalid_calldata = calldata.clone();
        invalid_calldata[35] += 1;
        let (_, output) = evm.call(verifier_address, invalid_calldata.clone());
        assert_eq!(*output.last().unwrap(), 0);

        // change z_0 to make the EVM check fail, placed between bytes 35 - 67
        let mut invalid_calldata = calldata.clone();
        invalid_calldata[67] += 1;
        let (_, output) = evm.call(verifier_address, invalid_calldata.clone());
        assert_eq!(*output.last().unwrap(), 0);

        // change z_i to make the EVM check fail, placed between bytes 68 - 100
        let mut invalid_calldata = calldata.clone();
        invalid_calldata[99] += 1;
        let (_, output) = evm.call(verifier_address, invalid_calldata.clone());
        assert_eq!(*output.last().unwrap(), 0);
    }

    #[test]
    fn nova_cyclefold_solidity_verifier() {
        let (nova_params, decider_params) = init_params::<CubicFCircuit<Fr>>();
        let z_0 = vec![Fr::from(3_u32)];
        nova_cyclefold_solidity_verifier_opt::<CubicFCircuit<Fr>>(
            nova_params.clone(),
            decider_params.clone(),
            z_0.clone(),
            2,
        );
        nova_cyclefold_solidity_verifier_opt::<CubicFCircuit<Fr>>(
            nova_params,
            decider_params,
            z_0,
            3,
        );

        let (nova_params, decider_params) = init_params::<MultiInputsFCircuit<Fr>>();
        let z_0 = vec![
            Fr::from(1_u32),
            Fr::from(1_u32),
            Fr::from(1_u32),
            Fr::from(1_u32),
            Fr::from(1_u32),
        ];
        nova_cyclefold_solidity_verifier_opt::<MultiInputsFCircuit<Fr>>(
            nova_params.clone(),
            decider_params.clone(),
            z_0.clone(),
            2,
        );
        nova_cyclefold_solidity_verifier_opt::<MultiInputsFCircuit<Fr>>(
            nova_params,
            decider_params,
            z_0.clone(),
            3,
        );
    }
}
