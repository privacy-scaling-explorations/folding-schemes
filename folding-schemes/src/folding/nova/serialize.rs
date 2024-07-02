use ark_crypto_primitives::sponge::{poseidon::PoseidonConfig, Absorb};
use ark_ec::{CurveGroup, Group};
use ark_ff::PrimeField;
use ark_r1cs_std::{
    groups::{CurveVar, GroupOpsBounds},
    ToConstraintFieldGadget,
};
use ark_relations::r1cs::ConstraintSynthesizer;
use ark_relations::r1cs::ConstraintSystem;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, SerializationError, Write};
use std::marker::PhantomData;

use super::{circuits::AugmentedFCircuit, Nova, ProverParams};
use super::{CommittedInstance, Witness};
use crate::folding::circuits::{cyclefold::CycleFoldCircuit, CF2};
use crate::{
    ccs::r1cs::extract_r1cs, commitment::CommitmentScheme, folding::circuits::CF1,
    frontend::FCircuit,
};

impl<C1, GC1, C2, GC2, FC, CS1, CS2> CanonicalSerialize for Nova<C1, GC1, C2, GC2, FC, CS1, CS2>
where
    C1: CurveGroup,
    C2: CurveGroup,
    FC: FCircuit<C1::ScalarField>,
    CS1: CommitmentScheme<C1>,
    CS2: CommitmentScheme<C2>,
    <C1 as CurveGroup>::BaseField: PrimeField,
    <C2 as CurveGroup>::BaseField: PrimeField,
    <C1 as Group>::ScalarField: Absorb,
    <C2 as Group>::ScalarField: Absorb,
    C1: CurveGroup<BaseField = C2::ScalarField, ScalarField = C2::BaseField>,
    for<'a> &'a GC1: GroupOpsBounds<'a, C1, GC1>,
    for<'a> &'a GC2: GroupOpsBounds<'a, C2, GC2>,
    GC1: CurveVar<C1, <C2 as Group>::ScalarField>,
    GC1: ToConstraintFieldGadget<<C2 as Group>::ScalarField>,
    GC2: CurveVar<C2, <C2 as CurveGroup>::BaseField>,
{
    fn serialize_with_mode<W: Write>(
        &self,
        mut writer: W,
        compress: ark_serialize::Compress,
    ) -> Result<(), ark_serialize::SerializationError> {
        self.i.serialize_with_mode(&mut writer, compress)?;
        self.z_0.serialize_with_mode(&mut writer, compress)?;
        self.z_i.serialize_with_mode(&mut writer, compress)?;
        self.w_i.serialize_with_mode(&mut writer, compress)?;
        self.u_i.serialize_with_mode(&mut writer, compress)?;
        self.W_i.serialize_with_mode(&mut writer, compress)?;
        self.U_i.serialize_with_mode(&mut writer, compress)?;
        self.cf_W_i.serialize_with_mode(&mut writer, compress)?;
        self.cf_U_i.serialize_with_mode(&mut writer, compress)
    }

    fn serialized_size(&self, compress: ark_serialize::Compress) -> usize {
        self.i.serialized_size(compress)
            + self.z_0.serialized_size(compress)
            + self.z_i.serialized_size(compress)
            + self.w_i.serialized_size(compress)
            + self.u_i.serialized_size(compress)
            + self.W_i.serialized_size(compress)
            + self.U_i.serialized_size(compress)
            + self.cf_W_i.serialized_size(compress)
            + self.cf_U_i.serialized_size(compress)
    }

    fn serialize_compressed<W: Write>(
        &self,
        writer: W,
    ) -> Result<(), ark_serialize::SerializationError> {
        self.serialize_with_mode(writer, ark_serialize::Compress::Yes)
    }

    fn compressed_size(&self) -> usize {
        self.serialized_size(ark_serialize::Compress::Yes)
    }

    fn serialize_uncompressed<W: Write>(
        &self,
        writer: W,
    ) -> Result<(), ark_serialize::SerializationError> {
        self.serialize_with_mode(writer, ark_serialize::Compress::No)
    }

    fn uncompressed_size(&self) -> usize {
        self.serialized_size(ark_serialize::Compress::No)
    }
}

// Note that we can't derive or implement `CanonicalDeserialize` directly.
// This is because `CurveVar` notably does not implement the `Sync` trait.
impl<C1, GC1, C2, GC2, FC, CS1, CS2> Nova<C1, GC1, C2, GC2, FC, CS1, CS2>
where
    C1: CurveGroup,
    C2: CurveGroup,
    FC: FCircuit<CF1<C1>, Params = ()>,
    CS1: CommitmentScheme<C1>,
    CS2: CommitmentScheme<C2>,
    <C1 as CurveGroup>::BaseField: PrimeField,
    <C2 as CurveGroup>::BaseField: PrimeField,
    <C1 as Group>::ScalarField: Absorb,
    <C2 as Group>::ScalarField: Absorb,
    C1: CurveGroup<BaseField = C2::ScalarField, ScalarField = C2::BaseField>,
    for<'a> &'a GC1: GroupOpsBounds<'a, C1, GC1>,
    for<'a> &'a GC2: GroupOpsBounds<'a, C2, GC2>,
    GC1: CurveVar<C1, <C2 as Group>::ScalarField>,
    GC1: ToConstraintFieldGadget<<C2 as Group>::ScalarField>,
    GC2: CurveVar<C2, CF2<C2>>,
    GC2: ToConstraintFieldGadget<<C2 as CurveGroup>::BaseField>,
{
    pub fn deserialize_nova<R: std::io::prelude::Read>(
        mut reader: R,
        compress: ark_serialize::Compress,
        validate: ark_serialize::Validate,
        prover_params: ProverParams<C1, C2, CS1, CS2>,
        poseidon_config: PoseidonConfig<C1::ScalarField>,
    ) -> Result<Self, ark_serialize::SerializationError> {
        let i = C1::ScalarField::deserialize_with_mode(&mut reader, compress, validate)?;
        let z_0 = Vec::<C1::ScalarField>::deserialize_with_mode(&mut reader, compress, validate)?;
        let z_i = Vec::<C1::ScalarField>::deserialize_with_mode(&mut reader, compress, validate)?;
        let w_i = Witness::<C1>::deserialize_with_mode(&mut reader, compress, validate)?;
        let u_i = CommittedInstance::<C1>::deserialize_with_mode(&mut reader, compress, validate)?;
        let W_i = Witness::<C1>::deserialize_with_mode(&mut reader, compress, validate)?;
        let U_i = CommittedInstance::<C1>::deserialize_with_mode(&mut reader, compress, validate)?;
        let cf_W_i = Witness::<C2>::deserialize_with_mode(&mut reader, compress, validate)?;
        let cf_U_i =
            CommittedInstance::<C2>::deserialize_with_mode(&mut reader, compress, validate)?;

        let f_circuit = FC::new(()).unwrap();
        let cs = ConstraintSystem::<C1::ScalarField>::new_ref();
        let cs2 = ConstraintSystem::<C1::BaseField>::new_ref();
        let augmented_F_circuit =
            AugmentedFCircuit::<C1, C2, GC2, FC>::empty(&poseidon_config, f_circuit.clone());
        let cf_circuit = CycleFoldCircuit::<C1, GC1>::empty();

        augmented_F_circuit
            .generate_constraints(cs.clone())
            .map_err(|_| SerializationError::InvalidData)?;
        cs.finalize();
        let cs = cs.into_inner().ok_or(SerializationError::InvalidData)?;
        let r1cs = extract_r1cs::<C1::ScalarField>(&cs);

        cf_circuit
            .generate_constraints(cs2.clone())
            .map_err(|_| SerializationError::InvalidData)?;
        cs2.finalize();
        let cs2 = cs2.into_inner().ok_or(SerializationError::InvalidData)?;
        let cf_r1cs = extract_r1cs::<C1::BaseField>(&cs2);

        Ok(Nova {
            _gc1: PhantomData,
            _c2: PhantomData,
            _gc2: PhantomData,
            cs_pp: prover_params.cs_pp,
            cf_cs_pp: prover_params.cf_cs_pp,
            i,
            z_0,
            z_i,
            w_i,
            u_i,
            W_i,
            U_i,
            cf_W_i,
            cf_U_i,
            r1cs,
            cf_r1cs,
            poseidon_config,
            F: f_circuit,
        })
    }
}

#[cfg(test)]
pub mod tests {
    use ark_bn254::{constraints::GVar, Bn254, Fr, G1Projective as Projective};
    use ark_grumpkin::{constraints::GVar as GVar2, Projective as Projective2};
    use ark_poly_commit::kzg10::VerifierKey as KZGVerifierKey;
    use ark_serialize::{CanonicalSerialize, Compress, Validate};
    use std::{fs, io::Write};

    use crate::{
        commitment::{
            kzg::{ProverKey as KZGProverKey, KZG},
            pedersen::Pedersen,
            CommitmentScheme,
        },
        folding::nova::{get_cs_params_len, Nova, ProverParams},
        frontend::{tests::CubicFCircuit, FCircuit},
        transcript::poseidon::poseidon_canonical_config,
        FoldingScheme,
    };

    #[test]
    fn test_serde_nova() {
        let mut rng = ark_std::test_rng();
        let poseidon_config = poseidon_canonical_config::<Fr>();
        let F_circuit = CubicFCircuit::<Fr>::new(()).unwrap();
        let (cs_len, cf_cs_len) =
            get_cs_params_len::<Projective, GVar, Projective2, GVar2, CubicFCircuit<Fr>>(
                &poseidon_config,
                F_circuit,
            )
            .unwrap();
        let (kzg_pk, _): (KZGProverKey<Projective>, KZGVerifierKey<Bn254>) =
            KZG::<Bn254>::setup(&mut rng, cs_len).unwrap();
        let (cf_pedersen_params, _) = Pedersen::<Projective2>::setup(&mut rng, cf_cs_len).unwrap();

        // Initialize nova and make multiple `prove_step()`
        type N = Nova<
            Projective,
            GVar,
            Projective2,
            GVar2,
            CubicFCircuit<Fr>,
            KZG<'static, Bn254>,
            Pedersen<Projective2>,
        >;
        let prover_params =
            ProverParams::<Projective, Projective2, KZG<Bn254>, Pedersen<Projective2>> {
                poseidon_config: poseidon_config.clone(),
                cs_pp: kzg_pk.clone(),
                cf_cs_pp: cf_pedersen_params.clone(),
            };

        let z_0 = vec![Fr::from(3_u32)];
        let mut nova = N::init(&prover_params, F_circuit, z_0.clone()).unwrap();

        let num_steps: usize = 3;
        for _ in 0..num_steps {
            nova.prove_step(&mut rng, vec![]).unwrap();
        }

        let mut writer = vec![];
        assert!(nova
            .serialize_with_mode(&mut writer, ark_serialize::Compress::No)
            .is_ok());

        let mut file = fs::OpenOptions::new()
            .create(true)
            .write(true)
            .open("./nova.serde")
            .unwrap();

        file.write_all(&writer).unwrap();

        let bytes = fs::read("./nova.serde").unwrap();

        let mut deserialized_nova = Nova::<
            Projective,
            GVar,
            Projective2,
            GVar2,
            CubicFCircuit<Fr>,
            KZG<Bn254>,
            Pedersen<Projective2>,
        >::deserialize_nova(
            bytes.as_slice(),
            Compress::No,
            Validate::No,
            prover_params,
            poseidon_config,
        )
        .unwrap();

        assert_eq!(nova.i, deserialized_nova.i);

        let num_steps: usize = 3;
        for _ in 0..num_steps {
            deserialized_nova.prove_step(&mut rng, vec![]).unwrap();
            nova.prove_step(&mut rng, vec![]).unwrap();
        }

        assert_eq!(deserialized_nova.w_i, nova.w_i);
    }
}
