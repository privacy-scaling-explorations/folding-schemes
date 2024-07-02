use ark_crypto_primitives::sponge::poseidon::PoseidonConfig;
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::PrimeField;
use ark_serialize::CanonicalSerialize;
use ark_std::Zero;
use sha3::{Digest, Sha3_256};

use crate::arith::Arith;
use crate::commitment::CommitmentScheme;
use crate::Error;

pub mod gadgets;
pub mod hypercube;
pub mod lagrange_poly;
pub mod mle;
pub mod vec;

// expose espresso local modules
pub mod espresso;
pub use crate::utils::espresso::multilinear_polynomial;
pub use crate::utils::espresso::sum_check;
pub use crate::utils::espresso::virtual_polynomial;

/// For a given x, returns [1, x^1, x^2, ..., x^n-1];
pub fn powers_of<F: PrimeField>(x: F, n: usize) -> Vec<F> {
    let mut c: Vec<F> = vec![F::zero(); n];
    c[0] = F::one();
    for i in 1..n {
        c[i] = c[i - 1] * x;
    }
    c
}

/// returns the coordinates of a commitment point. This is compatible with the arkworks
/// GC.to_constraint_field()[..2]
pub fn get_cm_coordinates<C: CurveGroup>(cm: &C) -> Vec<C::BaseField> {
    let zero = (&C::BaseField::zero(), &C::BaseField::zero());
    let cm = cm.into_affine();
    let (cm_x, cm_y) = cm.xy().unwrap_or(zero);
    vec![*cm_x, *cm_y]
}

/// returns the hash of the given public parameters of the Folding Scheme
pub fn pp_hash<C1, C2, CS1, CS2>(
    arith: &impl Arith<C1::ScalarField>,
    cf_arith: &impl Arith<C2::ScalarField>,
    cs_vp: &CS1::VerifierParams,
    cf_cs_vp: &CS2::VerifierParams,
    poseidon_config: &PoseidonConfig<C1::ScalarField>,
) -> Result<C1::ScalarField, Error>
where
    C1: CurveGroup,
    C2: CurveGroup,
    CS1: CommitmentScheme<C1>,
    CS2: CommitmentScheme<C2>,
{
    let mut hasher = Sha3_256::new();

    // Fr & Fq modulus bit size
    hasher.update(C1::ScalarField::MODULUS_BIT_SIZE.to_le_bytes());
    hasher.update(C2::ScalarField::MODULUS_BIT_SIZE.to_le_bytes());
    // AugmentedFCircuit Arith params
    hasher.update(arith.params_to_bytes());
    // CycleFold Circuit Arith params
    hasher.update(cf_arith.params_to_bytes());
    // cs_vp & cf_cs_vp (commitments setup)
    let mut cs_vp_bytes = Vec::new();
    cs_vp.serialize_uncompressed(&mut cs_vp_bytes)?;
    hasher.update(cs_vp_bytes);
    let mut cf_cs_vp_bytes = Vec::new();
    cf_cs_vp.serialize_uncompressed(&mut cf_cs_vp_bytes)?;
    hasher.update(cf_cs_vp_bytes);
    // poseidon params
    let mut poseidon_config_bytes = Vec::new();
    poseidon_config
        .full_rounds
        .serialize_uncompressed(&mut poseidon_config_bytes)?;
    poseidon_config
        .partial_rounds
        .serialize_uncompressed(&mut poseidon_config_bytes)?;
    poseidon_config
        .alpha
        .serialize_uncompressed(&mut poseidon_config_bytes)?;
    poseidon_config
        .ark
        .serialize_uncompressed(&mut poseidon_config_bytes)?;
    poseidon_config
        .mds
        .serialize_uncompressed(&mut poseidon_config_bytes)?;
    poseidon_config
        .rate
        .serialize_uncompressed(&mut poseidon_config_bytes)?;
    poseidon_config
        .capacity
        .serialize_uncompressed(&mut poseidon_config_bytes)?;
    hasher.update(poseidon_config_bytes);

    let public_params_hash = hasher.finalize();
    Ok(C1::ScalarField::from_le_bytes_mod_order(
        &public_params_hash,
    ))
}
