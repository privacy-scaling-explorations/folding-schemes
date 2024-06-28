#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(clippy::upper_case_acronyms)]

use ark_ff::PrimeField;
use ark_r1cs_std::alloc::AllocVar;
use ark_r1cs_std::fields::fp::FpVar;
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};
use core::marker::PhantomData;
use frontend_macro::Flatten;
use std::time::Instant;

use ark_bn254::{constraints::GVar, Bn254, Fr, G1Projective as Projective};
use ark_grumpkin::{constraints::GVar as GVar2, Projective as Projective2};

use folding_schemes::commitment::{kzg::KZG, pedersen::Pedersen};
use folding_schemes::folding::nova::Nova;
use folding_schemes::frontend::FCircuit;
use folding_schemes::{Error, FoldingScheme};
mod utils;
use utils::init_nova_ivc_params;

/// This is the circuit that we want to fold, it implements the FCircuit trait. The parameter z_i
/// denotes the current state which contains 5 elements, and z_{i+1} denotes the next state which
/// we get by applying the step.
/// In this example we set z_i and z_{i+1} to have five elements, and at each step we do different
/// operations on each of them.
///

#[derive(Flatten)]
pub struct State<F: PrimeField> {
    pub a: F,
    pub b: F,
    pub c: F,
    pub d: F,
    pub e: F,
}

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
        State::<F>::state_number()
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
        let state = State::from(z_i);

        let next_state = State {
            a: state.a + F::from(4_u32),
            b: state.b + F::from(40_u32),
            c: state.c * F::from(4_u32),
            d: state.d * F::from(40_u32),
            e: state.e + F::from(100_u32),
        };
        Ok(Vec::from(next_state))
    }

    /// generates the constraints for the step of F for the given z_i
    fn generate_step_constraints(
        &self,
        cs: ConstraintSystemRef<F>,
        _i: usize,
        z_i: Vec<FpVar<F>>,
        _external_inputs: Vec<FpVar<F>>,
    ) -> Result<Vec<FpVar<F>>, SynthesisError> {
        let cs_state = State::cs_state(z_i.clone());

        let four = FpVar::<F>::new_constant(cs.clone(), F::from(4u32))?;
        let forty = FpVar::<F>::new_constant(cs.clone(), F::from(40u32))?;
        let onehundred = FpVar::<F>::new_constant(cs.clone(), F::from(100u32))?;

        let next_cs_state = StateConstraint {
            a: cs_state.a.clone() + four.clone(),
            b: cs_state.b.clone() + forty.clone(),
            c: cs_state.c.clone() * four,
            d: cs_state.d.clone() * forty,
            e: cs_state.e.clone() + onehundred,
        };

        Ok(Vec::from(next_cs_state))
    }
}

/// cargo test --example multi_inputs
#[cfg(test)]
pub mod tests {
    use super::*;
    use ark_r1cs_std::{alloc::AllocVar, R1CSVar};
    use ark_relations::r1cs::ConstraintSystem;

    // test to check that the MultiInputsFCircuit computes the same values inside and outside the circuit
    #[test]
    fn test_f_circuit() {
        let cs = ConstraintSystem::<Fr>::new_ref();

        let circuit = MultiInputsFCircuit::<Fr>::new(()).unwrap();
        let z_i = vec![
            Fr::from(1_u32),
            Fr::from(1_u32),
            Fr::from(1_u32),
            Fr::from(1_u32),
            Fr::from(1_u32),
        ];

        let z_i1 = circuit.step_native(0, z_i.clone(), vec![]).unwrap();

        let z_iVar = Vec::<FpVar<Fr>>::new_witness(cs.clone(), || Ok(z_i)).unwrap();
        let computed_z_i1Var = circuit
            .generate_step_constraints(cs.clone(), 0, z_iVar.clone(), vec![])
            .unwrap();
        assert_eq!(computed_z_i1Var.value().unwrap(), z_i1);
    }
}

/// cargo run --release --example multi_inputs
fn main() {
    let num_steps = 10;
    let initial_state = vec![
        Fr::from(1_u32),
        Fr::from(1_u32),
        Fr::from(1_u32),
        Fr::from(1_u32),
        Fr::from(1_u32),
    ];

    let F_circuit = MultiInputsFCircuit::<Fr>::new(()).unwrap();

    println!("Prepare Nova ProverParams & VerifierParams");
    let (prover_params, verifier_params, _) =
        init_nova_ivc_params::<MultiInputsFCircuit<Fr>>(F_circuit);

    /// The idea here is that eventually we could replace the next line chunk that defines the
    /// `type NOVA = Nova<...>` by using another folding scheme that fulfills the `FoldingScheme`
    /// trait, and the rest of our code would be working without needing to be updated.
    type NOVA = Nova<
        Projective,
        GVar,
        Projective2,
        GVar2,
        MultiInputsFCircuit<Fr>,
        KZG<'static, Bn254>,
        Pedersen<Projective2>,
    >;

    println!("Initialize FoldingScheme");
    let mut folding_scheme = NOVA::init(&prover_params, F_circuit, initial_state.clone()).unwrap();

    // compute a step of the IVC
    for i in 0..num_steps {
        let start = Instant::now();
        folding_scheme.prove_step(vec![]).unwrap();
        println!("Nova::prove_step {}: {:?}", i, start.elapsed());
    }

    let (running_instance, incoming_instance, cyclefold_instance) = folding_scheme.instances();

    println!("Run the Nova's IVC verifier");
    NOVA::verify(
        verifier_params,
        initial_state.clone(),
        folding_scheme.state(), // latest state
        Fr::from(num_steps as u32),
        running_instance,
        incoming_instance,
        cyclefold_instance,
    )
    .unwrap();
}
