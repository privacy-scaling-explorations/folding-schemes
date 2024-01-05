#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]

use ark_ec::CurveGroup;
use ark_ff::PrimeField;
use ark_std::{fmt::Debug, rand::RngCore};
use thiserror::Error;

pub mod transcript;
use transcript::Transcript;
pub mod ccs;
pub mod constants;
pub mod folding;
pub mod frontend;
pub mod pedersen;
pub mod utils;

#[derive(Debug, Error)]
pub enum Error {
    #[error("ark_relations::r1cs::SynthesisError")]
    SynthesisError(#[from] ark_relations::r1cs::SynthesisError),
    #[error("ark_serialize::SerializationError")]
    SerializationError(#[from] ark_serialize::SerializationError),
    #[error("{0}")]
    Other(String),

    #[error("Relation not satisfied")]
    NotSatisfied,
    #[error("Not equal")]
    NotEqual,
    #[error("Vectors should have the same length ({0}: {1}, {2}: {3})")]
    NotSameLength(String, usize, String, usize),
    #[error("Vector's length ({0}) is not the expected ({1})")]
    NotExpectedLength(usize, usize),
    #[error("Can not be empty")]
    Empty,
    #[error("Pedersen parameters length is not suficient (generators.len={0} < vector.len={1} unsatisfied)")]
    PedersenParamsLen(usize, usize),
    #[error("Pedersen verification failed")]
    PedersenVerificationFail,
    #[error("IVC verification failed")]
    IVCVerificationFail,
    #[error("R1CS instance is expected to not be relaxed")]
    R1CSUnrelaxedFail,
    #[error("Could not find the inner ConstraintSystem")]
    NoInnerConstraintSystem,
    #[error("Sum-check prove failed: {0}")]
    SumCheckProveError(String),
    #[error("Sum-check verify failed: {0}")]
    SumCheckVerifyError(String),
    #[error("Value out of bounds")]
    OutOfBounds,
    #[error("Could not construct the Evaluation Domain")]
    NewDomainFail,

    #[error(transparent)]
    ProtoGalaxy(folding::protogalaxy::ProtoGalaxyError),
}

/// FoldingScheme defines trait that is implemented by the diverse folding schemes. It is defined
/// over a cycle of curves (C1, C2), where:
/// - C1 is the main curve, which ScalarField we use as our F for al the field operations
/// - C2 is the auxiliary curve, which we use for the commitments, whose BaseField (for point
/// coordinates) are in the C1::ScalarField.
/// In other words, C1.Fq == C2.Fr, and C1.Fr == C2.Fq.
pub trait FoldingScheme<C1: CurveGroup, C2: CurveGroup>: Clone + Debug
where
    C1: CurveGroup<BaseField = C2::ScalarField, ScalarField = C2::BaseField>,
    C2::BaseField: PrimeField,
{
    type PreprocessorParam: Debug;
    type ProverParam: Debug;
    type VerifierParam: Debug;
    type Witness: Debug;
    type CommittedInstanceWithWitness: Debug;
    type CommittedInstance: Clone + Debug;

    fn preprocess(
        prep_param: &Self::PreprocessorParam,
    ) -> Result<(Self::ProverParam, Self::VerifierParam), Error>;

    fn init_accumulator(
        pp: &Self::ProverParam,
    ) -> Result<Self::CommittedInstanceWithWitness, Error>;

    fn prove(
        pp: &Self::ProverParam,
        running_instance: &mut Self::CommittedInstanceWithWitness,
        incomming_instances: &[Self::Witness],
        transcript: &mut impl Transcript<C1>,
    ) -> Result<(), Error>;

    fn verify(
        vp: &Self::VerifierParam,
        running_instance: &mut Self::CommittedInstance,
        incomming_instances: &[Self::CommittedInstance],
        transcript: &mut impl Transcript<C1>,
    ) -> Result<(), Error>;
}

pub trait Decider<C: CurveGroup>: Clone + Debug {
    type PreprocessorParam: Debug;
    type ProverParam: Debug;
    type VerifierParam: Debug;
    type FreshInstance: Debug;
    type PublicInput: Debug;
    type CommittedInstanceWithWitness: Debug;
    type CommittedInstance: Clone + Debug;

    fn prove(
        pp: &Self::ProverParam,
        running_instance: &Self::CommittedInstanceWithWitness,
        transcript: &mut impl Transcript<C>,
        rng: impl RngCore,
    ) -> Result<(), Error>;

    fn verify(
        vp: &Self::VerifierParam,
        running_instance: &Self::CommittedInstance,
        transcript: &mut impl Transcript<C>,
        rng: impl RngCore,
    ) -> Result<(), Error>;
}
