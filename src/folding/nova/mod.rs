/// Implements the scheme described in [Nova](https://eprint.iacr.org/2021/370.pdf)
use ark_crypto_primitives::{
    crh::{poseidon::CRH, CRHScheme},
    sponge::{poseidon::PoseidonConfig, Absorb},
};
use ark_ec::{CurveGroup, Group};
use ark_std::fmt::Debug;
use ark_std::{One, Zero};

use crate::folding::circuits::nonnative::point_to_nonnative_limbs;
use crate::pedersen::{Params as PedersenParams, Pedersen};
use crate::utils::vec::is_zero_vec;
use crate::Error;

pub mod circuits;
pub mod cyclefold;
pub mod decider;
pub mod ivc;
pub mod nifs;
pub mod traits;

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct CommittedInstance<C: CurveGroup> {
    pub cmE: C,
    pub u: C::ScalarField,
    pub cmW: C,
    pub x: Vec<C::ScalarField>,
}

impl<C: CurveGroup> CommittedInstance<C> {
    pub fn dummy(io_len: usize) -> Self {
        Self {
            cmE: C::zero(),
            u: C::ScalarField::zero(),
            cmW: C::zero(),
            x: vec![C::ScalarField::zero(); io_len],
        }
    }
}

impl<C: CurveGroup> CommittedInstance<C>
where
    <C as Group>::ScalarField: Absorb,
    <C as ark_ec::CurveGroup>::BaseField: ark_ff::PrimeField,
{
    /// hash implements the committed instance hash compatible with the gadget implemented in
    /// nova/circuits.rs::CommittedInstanceVar.hash.
    /// Returns `H(i, z_0, z_i, U_i)`, where `i` can be `i` but also `i+1`, and `U` is the
    /// `CommittedInstance`.
    pub fn hash(
        &self,
        poseidon_config: &PoseidonConfig<C::ScalarField>,
        i: C::ScalarField,
        z_0: Vec<C::ScalarField>,
        z_i: Vec<C::ScalarField>,
    ) -> Result<C::ScalarField, Error> {
        let (cmE_x, cmE_y) = point_to_nonnative_limbs::<C>(self.cmE)?;
        let (cmW_x, cmW_y) = point_to_nonnative_limbs::<C>(self.cmW)?;

        CRH::<C::ScalarField>::evaluate(
            poseidon_config,
            vec![
                vec![i],
                z_0,
                z_i,
                vec![self.u],
                self.x.clone(),
                cmE_x,
                cmE_y,
                cmW_x,
                cmW_y,
            ]
            .concat(),
        )
        .map_err(|e| Error::Other(e.to_string()))
    }
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Witness<C: CurveGroup> {
    pub E: Vec<C::ScalarField>,
    pub rE: C::ScalarField,
    pub W: Vec<C::ScalarField>,
    pub rW: C::ScalarField,
}

impl<C: CurveGroup> Witness<C>
where
    <C as Group>::ScalarField: Absorb,
{
    pub fn new(w: Vec<C::ScalarField>, e_len: usize) -> Self {
        Self {
            E: vec![C::ScalarField::zero(); e_len],
            rE: C::ScalarField::zero(), // because we use C::zero() as cmE
            W: w,
            rW: C::ScalarField::one(),
        }
    }
    pub fn commit(
        &self,
        params: &PedersenParams<C>,
        x: Vec<C::ScalarField>,
    ) -> Result<CommittedInstance<C>, Error> {
        let mut cmE = C::zero();
        if !is_zero_vec::<C::ScalarField>(&self.E) {
            cmE = Pedersen::commit(params, &self.E, &self.rE)?;
        }
        let cmW = Pedersen::commit(params, &self.W, &self.rW)?;
        Ok(CommittedInstance {
            cmE,
            u: C::ScalarField::one(),
            cmW,
            x,
        })
    }
}
