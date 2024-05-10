use std::marker::PhantomData;

/// Implements the scheme described in [HyperNova](https://eprint.iacr.org/2023/573.pdf)
use crate::{ccs::CCS, constants::N_BITS_RO};
use ark_ec::CurveGroup;
use ark_ff::PrimeField;

use super::{circuits::cyclefold::CycleFoldConfig, nova::serialize::CycleFoldCircuit};

pub mod cccs;
pub mod circuits;
pub mod lcccs;
pub mod nimfs;
pub mod utils;

struct HyperNovaCycleFoldConfig<C: CurveGroup> {
    _c: PhantomData<C>,
}

impl<C: CurveGroup> CycleFoldConfig for HyperNovaCycleFoldConfig<C> {
    const N_BITS_RO: usize = N_BITS_RO;
    type C = C;
    type F = C::BaseField;
}

type HyperNovaCycleFoldCircuit<C, GC> = CycleFoldCircuit<HyperNovaCycleFoldConfig<C>, GC>;

/// Witness for the LCCCS & CCCS, containing the w vector, and the r_w used as randomness in the Pedersen commitment.
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Witness<F: PrimeField> {
    pub w: Vec<F>,
    pub r_w: F,
}

impl<F: PrimeField> Witness<F> {
    pub fn new(w: Vec<F>) -> Self {
        // note: at the current version, we don't use the blinding factors and we set them to 0
        // always.
        Self { w, r_w: F::zero() }
    }
    pub fn dummy(ccs: &CCS<F>) -> Self {
        Witness::<F>::new(vec![F::zero(); ccs.n - ccs.l - 1])
    }
}
