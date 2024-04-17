/// Implements the scheme described in [ProtoGalaxy](https://eprint.iacr.org/2023/1106.pdf)
use ark_ec::CurveGroup;
use ark_ff::PrimeField;
use ark_r1cs_std::fields::fp::FpVar;
use thiserror::Error;

use super::circuits::nonnative::affine::NonNativeAffineVar;

pub mod folding;
pub mod traits;
pub(crate) mod utils;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CommittedInstance<C: CurveGroup> {
    phi: C,
    betas: Vec<C::ScalarField>,
    e: C::ScalarField,
    u: C::ScalarField,
    x: Vec<C::ScalarField>,
}

#[derive(Clone, Debug)]
pub struct CommittedInstanceVar<C: CurveGroup> {
    phi: NonNativeAffineVar<C>,
    betas: Vec<FpVar<C::ScalarField>>,
    e: FpVar<C::ScalarField>,
    u: FpVar<C::ScalarField>,
    x: Vec<FpVar<C::ScalarField>>,
}

#[derive(Clone, Debug)]
pub struct Witness<F: PrimeField> {
    w: Vec<F>,
    r_w: F,
}

#[derive(Debug, Error, PartialEq)]
pub enum ProtoGalaxyError {
    #[error("The remainder from G(X)-F(α)*L_0(X)) / Z(X) should be zero")]
    RemainderNotZero,
    #[error("Could not divide by vanishing polynomial")]
    CouldNotDivideByVanishing,
    #[error("The number of incoming instances + 1 should be a power of two, current number of instances: {0}")]
    WrongNumInstances(usize),
    #[error("The number of incoming items should be a power of two, current number of coefficients: {0}")]
    BTreeNotFull(usize),
    #[error("The lengths of β and δ do not equal: |β| = {0}, |δ|={0}")]
    WrongLenBetas(usize, usize),
}
