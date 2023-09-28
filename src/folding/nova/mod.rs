/// Implements the scheme described in [Nova](https://eprint.iacr.org/2021/370.pdf)
use ark_crypto_primitives::sponge::Absorb;
use ark_ec::{CurveGroup, Group};
use ark_std::fmt::Debug;
use ark_std::{One, Zero};

use crate::pedersen::{Params as PedersenParams, Pedersen};
use crate::transcript::Transcript;

pub mod circuits;
pub mod nifs;

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct CommittedInstance<C: CurveGroup> {
    pub cmE: C,
    pub u: C::ScalarField,
    pub cmW: C,
    pub x: Vec<C::ScalarField>,
}

impl<C: CurveGroup> CommittedInstance<C> {
    pub fn empty() -> Self {
        CommittedInstance {
            cmE: C::zero(),
            u: C::ScalarField::one(),
            cmW: C::zero(),
            x: Vec::new(),
        }
    }

    pub(crate) fn absorb_in_tr(&self, tr: &mut impl Transcript<C>) {
        tr.absorb_point(&self.cmW);
        for c in &self.x {
            tr.absorb(&c)
        }
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
            rE: C::ScalarField::one(),
            W: w,
            rW: C::ScalarField::one(),
        }
    }

    pub fn commit(
        &self,
        params: &PedersenParams<C>,
        x: Vec<C::ScalarField>,
    ) -> CommittedInstance<C> {
        let cmE = Pedersen::commit(params, &self.E, &self.rE);
        let cmW = Pedersen::commit(params, &self.W, &self.rW);
        CommittedInstance {
            cmE,
            u: C::ScalarField::one(),
            cmW,
            x,
        }
    }
}
