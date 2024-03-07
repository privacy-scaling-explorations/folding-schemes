/// This file implements the onchain (Ethereum's EVM) decider.
use ark_crypto_primitives::sponge::{poseidon::PoseidonConfig, Absorb};
use ark_ec::{CurveGroup, Group};
use ark_ff::{BigInteger, PrimeField};
use ark_r1cs_std::fields::nonnative::params::OptimizationType;
use ark_r1cs_std::{groups::GroupOpsBounds, prelude::CurveVar, ToConstraintFieldGadget};
use ark_snark::SNARK;
use ark_std::rand::{CryptoRng, RngCore};
use ark_std::Zero;
use core::marker::PhantomData;

pub use super::decider_eth_circuit::{DeciderEthCircuit, KZGChallengesGadget};
use super::{
    circuits::{ChallengeGadget, CF2},
    nifs::NIFS,
    CommittedInstance, Nova, Witness,
};
use crate::commitment::{
    kzg::Proof as KZGProof, pedersen::Params as PedersenParams, CommitmentScheme,
};
use crate::folding::circuits::nonnative::point_to_nonnative_limbs_custom_opt;
use crate::frontend::FCircuit;
use crate::Error;
use crate::{Decider as DeciderTrait, FoldingScheme};

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Proof<C1, CS1, S>
where
    C1: CurveGroup,
    CS1: CommitmentScheme<C1, ProverChallenge = C1::ScalarField, Challenge = C1::ScalarField>,
    S: SNARK<C1::ScalarField>,
{
    snark_proof: S::Proof,
    kzg_proofs: [CS1::Proof; 2],
    // cmT and r are values for the last fold, U_{i+1}=NIFS.V(r, U_i, u_i, cmT), and they are
    // checked in-circuit
    cmT: C1,
    r: C1::ScalarField,
    // the KZG challenges are provided by the prover, but in-circuit they are checked to match
    // the in-circuit computed computed ones.
    kzg_challenges: [C1::ScalarField; 2],
}

/// Onchain Decider, for ethereum use cases
#[derive(Clone, Debug)]
pub struct Decider<C1, GC1, C2, GC2, FC, CS1, CS2, S, FS> {
    _c1: PhantomData<C1>,
    _gc1: PhantomData<GC1>,
    _c2: PhantomData<C2>,
    _gc2: PhantomData<GC2>,
    _fc: PhantomData<FC>,
    _cs1: PhantomData<CS1>,
    _cs2: PhantomData<CS2>,
    _s: PhantomData<S>,
    _fs: PhantomData<FS>,
}

impl<C1, GC1, C2, GC2, FC, CS1, CS2, S, FS> DeciderTrait<C1, C2, FC, FS>
    for Decider<C1, GC1, C2, GC2, FC, CS1, CS2, S, FS>
where
    C1: CurveGroup,
    C2: CurveGroup,
    GC1: CurveVar<C1, CF2<C1>> + ToConstraintFieldGadget<CF2<C1>>,
    GC2: CurveVar<C2, CF2<C2>>,
    FC: FCircuit<C1::ScalarField>,
    CS1: CommitmentScheme<
        C1,
        ProverChallenge = C1::ScalarField,
        Challenge = C1::ScalarField,
        Proof = KZGProof<C1>,
    >, // KZG commitment, where challenge is C1::Fr elem
    // enforce that the CS2 is Pedersen commitment scheme, since we're at Ethereum's EVM decider
    CS2: CommitmentScheme<C2, ProverParams = PedersenParams<C2>>,
    S: SNARK<C1::ScalarField>,
    FS: FoldingScheme<C1, C2, FC>,
    <C1 as CurveGroup>::BaseField: PrimeField,
    <C2 as CurveGroup>::BaseField: PrimeField,
    <C1 as Group>::ScalarField: Absorb,
    <C2 as Group>::ScalarField: Absorb,
    C1: CurveGroup<BaseField = C2::ScalarField, ScalarField = C2::BaseField>,
    for<'b> &'b GC2: GroupOpsBounds<'b, C2, GC2>,
    // constrain FS into Nova, since this is a Decider specifically for Nova
    Nova<C1, GC1, C2, GC2, FC, CS1, CS2>: From<FS>,
{
    type ProverParam = (
        PoseidonConfig<C1::ScalarField>,
        S::ProvingKey,
        CS1::ProverParams,
    );
    type Proof = Proof<C1, CS1, S>;
    type VerifierParam = (S::VerifyingKey, CS1::VerifierParams);
    type PublicInput = Vec<C1::ScalarField>;
    type CommittedInstanceWithWitness = ();
    type CommittedInstance = CommittedInstance<C1>;

    fn prove(
        pp: Self::ProverParam,
        mut rng: impl RngCore + CryptoRng,
        folding_scheme: FS,
    ) -> Result<Self::Proof, Error> {
        let (poseidon_config, snark_pk, cs_pk): (
            PoseidonConfig<C1::ScalarField>,
            S::ProvingKey,
            CS1::ProverParams,
        ) = pp;

        let circuit = DeciderEthCircuit::<C1, GC1, C2, GC2, CS1, CS2>::from_nova::<FC>(
            folding_scheme.into(),
        )?;

        let snark_proof = S::prove(&snark_pk, circuit.clone(), &mut rng)
            .map_err(|e| Error::Other(e.to_string()))?;

        let U_i = circuit
            .U_i
            .clone()
            .ok_or(Error::MissingValue("U_i".to_string()))?;
        let W_i = circuit
            .W_i
            .clone()
            .ok_or(Error::MissingValue("W_i".to_string()))?;
        let u_i = circuit
            .u_i
            .clone()
            .ok_or(Error::MissingValue("u_i".to_string()))?;
        let w_i = circuit
            .w_i
            .clone()
            .ok_or(Error::MissingValue("w_i".to_string()))?;

        // compute NIFS.P((U_d, W_d), (u_d, w_d)) = (U_{d+1}, W_{d+1}, cmT)
        let (T, cmT) = NIFS::<C1, CS1>::compute_cmT(&cs_pk, &circuit.r1cs, &w_i, &u_i, &W_i, &U_i)?;
        let r_bits = ChallengeGadget::<C1>::get_challenge_native(
            &poseidon_config,
            U_i.clone(),
            u_i.clone(),
            cmT,
        )?;
        let r_Fr = C1::ScalarField::from_bigint(BigInteger::from_bits_le(&r_bits))
            .ok_or(Error::OutOfBounds)?;
        let (W_i1, _): (Witness<C1>, CommittedInstance<C1>) =
            NIFS::<C1, CS1>::fold_instances(r_Fr, &W_i, &U_i, &w_i, &u_i, &T, cmT)?;

        // get the challenges that have been already computed when preparing the circuit inputs in
        // the above `from_nova` call
        let challenge_W = circuit
            .kzg_c_W
            .ok_or(Error::MissingValue("kzg_c_W".to_string()))?;
        let challenge_E = circuit
            .kzg_c_E
            .ok_or(Error::MissingValue("kzg_c_E".to_string()))?;

        // generate KZG proofs
        let U_cmW_proof = CS1::prove_with_challenge(
            &cs_pk,
            challenge_W,
            &W_i1.W,
            &C1::ScalarField::zero(),
            None,
        )?;
        let U_cmE_proof = CS1::prove_with_challenge(
            &cs_pk,
            challenge_E,
            &W_i1.E,
            &C1::ScalarField::zero(),
            None,
        )?;

        Ok(Self::Proof {
            snark_proof,
            kzg_proofs: [U_cmW_proof, U_cmE_proof],
            cmT,
            r: r_Fr,
            kzg_challenges: [challenge_W, challenge_E],
        })
    }

    fn verify(
        vp: Self::VerifierParam,
        i: C1::ScalarField,
        z_0: Vec<C1::ScalarField>,
        z_i: Vec<C1::ScalarField>,
        running_instance: &Self::CommittedInstance,
        incoming_instance: &Self::CommittedInstance,
        proof: Self::Proof,
    ) -> Result<bool, Error> {
        let (snark_vk, cs_vk): (S::VerifyingKey, CS1::VerifierParams) = vp;

        // compute U = U_{d+1}= NIFS.V(U_d, u_d, cmT)
        let U = NIFS::<C1, CS1>::verify(proof.r, running_instance, incoming_instance, &proof.cmT);

        let (cmE_x, cmE_y) =
            point_to_nonnative_limbs_custom_opt::<C1>(U.cmE, OptimizationType::Constraints)?;
        let (cmW_x, cmW_y) =
            point_to_nonnative_limbs_custom_opt::<C1>(U.cmW, OptimizationType::Constraints)?;
        let (cmT_x, cmT_y) =
            point_to_nonnative_limbs_custom_opt::<C1>(proof.cmT, OptimizationType::Constraints)?;

        let public_input: Vec<C1::ScalarField> = vec![
            vec![i],
            z_0,
            z_i,
            vec![U.u],
            U.x.clone(),
            cmE_x,
            cmE_y,
            cmW_x,
            cmW_y,
            proof.kzg_challenges.to_vec(),
            vec![
                proof.kzg_proofs[0].eval, // eval_W
                proof.kzg_proofs[1].eval, // eval_E
            ],
            cmT_x,
            cmT_y,
            vec![proof.r],
        ]
        .concat();

        let snark_v = S::verify(&snark_vk, &public_input, &proof.snark_proof)
            .map_err(|e| Error::Other(e.to_string()))?;
        if !snark_v {
            return Err(Error::SNARKVerificationFail);
        }

        // we're at the Ethereum EVM case, so the CS1 is KZG commitments
        CS1::verify_with_challenge(
            &cs_vk,
            proof.kzg_challenges[0],
            &U.cmW,
            &proof.kzg_proofs[0],
        )?;
        CS1::verify_with_challenge(
            &cs_vk,
            proof.kzg_challenges[1],
            &U.cmE,
            &proof.kzg_proofs[1],
        )?;

        Ok(true)
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use ark_bn254::{constraints::GVar, Bn254, Fr, G1Projective as Projective};
    use ark_groth16::Groth16;
    use ark_grumpkin::{constraints::GVar as GVar2, Projective as Projective2};
    use ark_poly_commit::kzg10::VerifierKey as KZGVerifierKey;
    use std::time::Instant;

    use crate::commitment::kzg::{ProverKey as KZGProverKey, KZG};
    use crate::commitment::pedersen::Pedersen;
    use crate::folding::nova::{get_cs_params_len, ProverParams};
    use crate::frontend::tests::CubicFCircuit;
    use crate::transcript::poseidon::poseidon_test_config;

    #[test]
    fn test_decider() {
        // use Nova as FoldingScheme
        type NOVA = Nova<
            Projective,
            GVar,
            Projective2,
            GVar2,
            CubicFCircuit<Fr>,
            KZG<'static, Bn254>,
            Pedersen<Projective2>,
        >;
        type DECIDER = Decider<
            Projective,
            GVar,
            Projective2,
            GVar2,
            CubicFCircuit<Fr>,
            KZG<'static, Bn254>,
            Pedersen<Projective2>,
            Groth16<Bn254>, // here we define the Snark to use in the decider
            NOVA,           // here we define the FoldingScheme to use
        >;

        let mut rng = ark_std::test_rng();
        let poseidon_config = poseidon_test_config::<Fr>();

        let F_circuit = CubicFCircuit::<Fr>::new(());
        let z_0 = vec![Fr::from(3_u32)];

        let (cs_len, cf_cs_len) =
            get_cs_params_len::<Projective, GVar, Projective2, GVar2, CubicFCircuit<Fr>>(
                &poseidon_config,
                F_circuit,
            )
            .unwrap();
        let start = Instant::now();
        let (kzg_pk, kzg_vk): (KZGProverKey<Projective>, KZGVerifierKey<Bn254>) =
            KZG::<Bn254>::setup(&mut rng, cs_len).unwrap();
        let (cf_pedersen_params, _) = Pedersen::<Projective2>::setup(&mut rng, cf_cs_len).unwrap();
        println!("generated KZG params, {:?}", start.elapsed());

        let prover_params =
            ProverParams::<Projective, Projective2, KZG<Bn254>, Pedersen<Projective2>> {
                poseidon_config: poseidon_config.clone(),
                cs_params: kzg_pk.clone(),
                cf_cs_params: cf_pedersen_params,
            };

        let start = Instant::now();
        let mut nova = NOVA::init(&prover_params, F_circuit, z_0.clone()).unwrap();
        println!("Nova initialized, {:?}", start.elapsed());
        let start = Instant::now();
        nova.prove_step().unwrap();
        println!("prove_step, {:?}", start.elapsed());
        nova.prove_step().unwrap(); // do a 2nd step

        // generate Groth16 setup
        let circuit = DeciderEthCircuit::<
            Projective,
            GVar,
            Projective2,
            GVar2,
            KZG<Bn254>,
            Pedersen<Projective2>,
        >::from_nova::<CubicFCircuit<Fr>>(nova.clone())
        .unwrap();
        let mut rng = rand::rngs::OsRng;

        let start = Instant::now();
        let (g16_pk, g16_vk) =
            Groth16::<Bn254>::circuit_specific_setup(circuit.clone(), &mut rng).unwrap();
        println!("Groth16 setup, {:?}", start.elapsed());

        // decider proof generation
        let start = Instant::now();
        let decider_pp = (poseidon_config.clone(), g16_pk, kzg_pk);
        let proof = DECIDER::prove(decider_pp, rng, nova.clone()).unwrap();
        println!("Decider prove, {:?}", start.elapsed());

        // decider proof verification
        let start = Instant::now();
        let decider_vp = (g16_vk, kzg_vk);
        let verified = DECIDER::verify(
            decider_vp, nova.i, nova.z_0, nova.z_i, &nova.U_i, &nova.u_i, proof,
        )
        .unwrap();
        assert!(verified);
        println!("Decider verify, {:?}", start.elapsed());
    }
}
