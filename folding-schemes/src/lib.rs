#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]

use ark_ec::{pairing::Pairing, CurveGroup};
use ark_ff::PrimeField;
use ark_std::rand::CryptoRng;
use ark_std::{fmt::Debug, rand::RngCore};
use thiserror::Error;

use crate::frontend::FCircuit;

pub mod arith;
pub mod commitment;
pub mod constants;
pub mod folding;
pub mod frontend;
pub mod transcript;
pub mod utils;

#[derive(Debug, Error)]
pub enum Error {
    // Wrappers on top of other errors
    #[error("ark_relations::r1cs::SynthesisError")]
    SynthesisError(#[from] ark_relations::r1cs::SynthesisError),
    #[error("ark_serialize::SerializationError")]
    SerializationError(#[from] ark_serialize::SerializationError),
    #[error("ark_poly_commit::Error")]
    PolyCommitError(#[from] ark_poly_commit::Error),
    #[error("crate::utils::espresso::virtual_polynomial::ArithErrors")]
    ArithError(#[from] utils::espresso::virtual_polynomial::ArithErrors),
    #[error(transparent)]
    ProtoGalaxy(folding::protogalaxy::ProtoGalaxyError),
    #[error("std::io::Error")]
    IOError(#[from] std::io::Error),

    // Relation errors
    #[error("Relation not satisfied")]
    NotSatisfied,
    #[error("SNARK verification failed")]
    SNARKVerificationFail,
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

    // Comparators errors
    #[error("Not equal")]
    NotEqual,
    #[error("Vectors should have the same length ({0}: {1}, {2}: {3})")]
    NotSameLength(String, usize, String, usize),
    #[error("Vector's length ({0}) is not the expected ({1})")]
    NotExpectedLength(usize, usize),
    #[error("Vector ({0}) length ({1}) is not a power of two")]
    NotPowerOfTwo(String, usize),
    #[error("Can not be empty")]
    Empty,
    #[error("Value out of bounds")]
    OutOfBounds,
    #[error("Could not construct the Evaluation Domain")]
    NewDomainFail,
    #[error("The number of folded steps must be greater than 1")]
    NotEnoughSteps,
    #[error("Evaluation failed")]
    EvaluationFail,

    // Commitment errors
    #[error("Pedersen parameters length is not sufficient (generators.len={0} < vector.len={1} unsatisfied)")]
    PedersenParamsLen(usize, usize),
    #[error("Blinding factor not 0 for Commitment without hiding")]
    BlindingNotZero,
    #[error("Commitment verification failed")]
    CommitmentVerificationFail,

    // Other
    #[error("{0}")]
    Other(String),
    #[error("Randomness for blinding not found")]
    MissingRandomness,
    #[error("Missing value: {0}")]
    MissingValue(String),
    #[error("Feature '{0}' not supported yet")]
    NotSupportedYet(String),
    #[error("Feature '{0}' is not supported and it will not be")]
    NotSupported(String),
    #[error("max i-th step reached (usize limit reached)")]
    MaxStep,
    #[error("Circom Witness calculation error: {0}")]
    WitnessCalculationError(String),
    #[error("BigInt to PrimeField conversion error: {0}")]
    BigIntConversionError(String),
}

/// FoldingScheme defines trait that is implemented by the diverse folding schemes. It is defined
/// over a cycle of curves (C1, C2), where:
/// - C1 is the main curve, which ScalarField we use as our F for all the field operations
/// - C2 is the auxiliary curve, which we use for the commitments, whose BaseField (for point
/// coordinates) are in the C1::ScalarField.
/// In other words, C1.Fq == C2.Fr, and C1.Fr == C2.Fq.
pub trait FoldingScheme<C1: CurveGroup, C2: CurveGroup, FC>: Clone + Debug
where
    C1: CurveGroup<BaseField = C2::ScalarField, ScalarField = C2::BaseField>,
    C2::BaseField: PrimeField,
    FC: FCircuit<C1::ScalarField>,
{
    type PreprocessorParam: Debug + Clone;
    type ProverParam: Debug + Clone;
    type VerifierParam: Debug + Clone;
    type RunningInstance: Debug; // contains the CommittedInstance + Witness
    type IncomingInstance: Debug; // contains the CommittedInstance + Witness
    type CFInstance: Debug; // CycleFold CommittedInstance & Witness

    fn preprocess(
        rng: impl RngCore,
        prep_param: &Self::PreprocessorParam,
    ) -> Result<(Self::ProverParam, Self::VerifierParam), Error>;

    fn init(
        params: (Self::ProverParam, Self::VerifierParam),
        step_circuit: FC,
        z_0: Vec<C1::ScalarField>, // initial state
    ) -> Result<Self, Error>;

    fn prove_step(
        &mut self,
        rng: impl RngCore,
        external_inputs: Vec<C1::ScalarField>,
    ) -> Result<(), Error>;

    // returns the state at the current step
    fn state(&self) -> Vec<C1::ScalarField>;

    // returns the instances at the current step, in the following order:
    // (running_instance, incoming_instance, cyclefold_instance)
    fn instances(
        &self,
    ) -> (
        Self::RunningInstance,
        Self::IncomingInstance,
        Self::CFInstance,
    );

    fn verify(
        vp: Self::VerifierParam,
        z_0: Vec<C1::ScalarField>, // initial state
        z_i: Vec<C1::ScalarField>, // last state
        // number of steps between the initial state and the last state
        num_steps: C1::ScalarField,
        running_instance: Self::RunningInstance,
        incoming_instance: Self::IncomingInstance,
        cyclefold_instance: Self::CFInstance,
    ) -> Result<(), Error>;
}

pub trait Decider<
    C1: CurveGroup,
    C2: CurveGroup,
    FC: FCircuit<C1::ScalarField>,
    FS: FoldingScheme<C1, C2, FC>,
> where
    C1: CurveGroup<BaseField = C2::ScalarField, ScalarField = C2::BaseField>,
    C2::BaseField: PrimeField,
{
    type PreprocessorParam: Debug;
    type ProverParam: Clone;
    type Proof;
    type VerifierParam;
    type PublicInput: Debug;
    type CommittedInstance: Clone + Debug;

    fn preprocess(
        rng: impl RngCore + CryptoRng,
        prep_param: &Self::PreprocessorParam,
        fs: FS,
    ) -> Result<(Self::ProverParam, Self::VerifierParam), Error>;

    fn prove(
        rng: impl RngCore + CryptoRng,
        pp: Self::ProverParam,
        folding_scheme: FS,
    ) -> Result<Self::Proof, Error>;

    fn verify(
        vp: Self::VerifierParam,
        i: C1::ScalarField,
        z_0: Vec<C1::ScalarField>,
        z_i: Vec<C1::ScalarField>,
        running_instance: &Self::CommittedInstance,
        incoming_instance: &Self::CommittedInstance,
        proof: &Self::Proof,
        // returns `Result<bool, Error>` to differentiate between an error occurred while performing
        // the verification steps, and the verification logic of the scheme not passing.
    ) -> Result<bool, Error>;
}

/// DeciderOnchain extends the Decider into preparing the calldata
pub trait DeciderOnchain<E: Pairing, C1: CurveGroup, C2: CurveGroup>
where
    C1: CurveGroup<BaseField = C2::ScalarField, ScalarField = C2::BaseField>,
    C2::BaseField: PrimeField,
{
    type Proof;
    type CommittedInstance: Clone + Debug;

    fn prepare_calldata(
        i: C1::ScalarField,
        z_0: Vec<C1::ScalarField>,
        z_i: Vec<C1::ScalarField>,
        running_instance: &Self::CommittedInstance,
        incoming_instance: &Self::CommittedInstance,
        proof: Self::Proof,
    ) -> Result<Vec<u8>, Error>;
}
