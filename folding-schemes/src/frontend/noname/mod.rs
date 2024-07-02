use crate::Error;
use ark_noname::sonobe::NoNameSonobeCircuit;
use ark_r1cs_std::alloc::AllocVar;
use ark_r1cs_std::fields::fp::FpVar;
use ark_relations::r1cs::{ConstraintSynthesizer, SynthesisError};
use num_bigint::BigUint;
use std::marker::PhantomData;

use super::FCircuit;
use ark_ff::PrimeField;
use ark_noname::utils::compile_source_code;
use noname::backends::{r1cs::R1CS as R1CSNoName, BackendField};
use noname::witness::CompiledCircuit;

pub mod utils;

use utils::*;

#[derive(Debug, Clone)]
pub struct NoNameFCircuit<F: PrimeField, BF: BackendField> {
    pub state_len: usize,
    pub external_inputs_len: usize,
    pub circuit: CompiledCircuit<R1CSNoName<BF>>,
    _f: PhantomData<F>,
}

impl<F: PrimeField, BF: BackendField> FCircuit<F> for NoNameFCircuit<F, BF> {
    type Params = (String, usize, usize);

    fn new(params: Self::Params) -> Result<Self, crate::Error> {
        let (code, state_len, external_inputs_len) = params;
        let compiled_circuit = compile_source_code::<BF>(&code).map_err(|_| {
            Error::Other("Encountered an error while compiling a noname circuit".to_owned())
        })?;
        Ok(NoNameFCircuit {
            state_len,
            external_inputs_len,
            circuit: compiled_circuit,
            _f: PhantomData,
        })
    }

    fn state_len(&self) -> usize {
        self.state_len
    }

    fn external_inputs_len(&self) -> usize {
        self.external_inputs_len
    }

    fn step_native(
        // this method uses self, so that each FCircuit implementation (and different frontends)
        // can hold a state if needed to store data to compute the next state.
        &self,
        i: usize,
        z_i: Vec<F>,
        external_inputs: Vec<F>, // inputs that are not part of the state
    ) -> Result<Vec<F>, crate::Error> {
        todo!()
    }

    fn generate_step_constraints(
        // this method uses self, so that each FCircuit implementation (and different frontends)
        // can hold a state if needed to store data to generate the constraints.
        &self,
        cs: ark_relations::r1cs::ConstraintSystemRef<F>,
        i: usize,
        z_i: Vec<ark_r1cs_std::fields::fp::FpVar<F>>,
        external_inputs: Vec<ark_r1cs_std::fields::fp::FpVar<F>>, // inputs that are not part of the state
    ) -> Result<Vec<ark_r1cs_std::fields::fp::FpVar<F>>, ark_relations::r1cs::SynthesisError> {
        // fpvars -> String -> formatted json -> noname JsonInputs
        let external_inputs_json = match external_inputs.len() != 0 {
            false => None,
            true => {
                let json = serde_json::to_string(&NoNameJSONExternalInputs::from_fpvars(
                    &external_inputs.clone(),
                )?)
                .map_err(|_| SynthesisError::Unsatisfiable)?;
                Some(json)
            }
        };

        let ivc_inputs = serde_json::to_string(&NoNameJSONIVCInput::from_fpvars(&z_i)?)
            .map_err(|_| SynthesisError::Unsatisfiable)?;
        let noname_inputs = NoNameIVCInputs::<F>::try_from((ivc_inputs, external_inputs_json))
            .map_err(|_| SynthesisError::Unsatisfiable)?;
        let (ivc_inputs, noname_external_inputs) = noname_inputs
            .try_into()
            .map_err(|_| SynthesisError::Unsatisfiable)?;
        let noname_witness = self
            .circuit
            .generate_witness(ivc_inputs, noname_external_inputs)
            .map_err(|_| SynthesisError::Unsatisfiable)?;

        let mut assigned_z_i1 = vec![];
        let z_i1_end_index = z_i.len() + 1;
        for idx in 1..z_i1_end_index {
            // the assigned zi1 is of the same size than the initial zi and is located in the
            // output of the witness vector
            // we prefer to assign z_i1 here since (1) we have to return it, (2) we cant return
            // anything with the `generate_constraints` method used below
            let value: BigUint = Into::into(noname_witness.witness[idx]);
            let field_element = F::from(value);
            assigned_z_i1.push(FpVar::<F>::new_witness(cs.clone(), || Ok(field_element))?);
        }

        let noname_circuit = NoNameSonobeCircuit {
            compiled_circuit: self.circuit.clone(),
            witness: noname_witness,
            assigned_z_i: &z_i,
            assigned_external_inputs: &external_inputs,
            assigned_z_i1: &assigned_z_i1,
        };
        noname_circuit.generate_constraints(cs.clone())?;
        Ok(assigned_z_i1)
    }
}

#[cfg(test)]
mod tests {

    use ark_bn254::Fr;
    use ark_r1cs_std::{alloc::AllocVar, fields::fp::FpVar, R1CSVar};
    use noname::backends::r1cs::R1csBn254Field;

    use crate::frontend::{
        noname::{NONAME_CIRCUIT_EXTERNAL_INPUTS, NONAME_CIRCUIT_NO_EXTERNAL_INPUTS},
        FCircuit,
    };

    use super::{NoNameFCircuit, NoNameIVCInputs};
    use ark_relations::r1cs::ConstraintSystem;

    #[test]
    fn test_noname_step_native() {}

    #[test]
    fn test_step_constraints() {
        let cs = ConstraintSystem::<Fr>::new_ref();
        let params = (NONAME_CIRCUIT_EXTERNAL_INPUTS.to_owned(), 2, 2);
        let circuit = NoNameFCircuit::<Fr, R1csBn254Field>::new(params).unwrap();
        let inputs_public = r#"{"ivc_input":["2","5"]}"#;
        let inputs_private = r#"{"external_inputs":["8","2"]}"#;
        let ivc_inputs =
            NoNameIVCInputs::try_from((inputs_public.to_owned(), Some(inputs_private.to_owned())))
                .unwrap();

        let ivc_inputs_var =
            Vec::<FpVar<Fr>>::new_witness(cs.clone(), || Ok(ivc_inputs.ivc_input)).unwrap();
        let external_inputs_var =
            Vec::<FpVar<Fr>>::new_witness(cs.clone(), || Ok(ivc_inputs.external_inputs.unwrap()))
                .unwrap();

        let z_i1 = circuit
            .generate_step_constraints(cs.clone(), 0, ivc_inputs_var, external_inputs_var)
            .unwrap();
        assert!(cs.is_satisfied().unwrap());
        assert_eq!(z_i1[0].value().unwrap(), Fr::from(10 as u8));
        assert_eq!(z_i1[1].value().unwrap(), Fr::from(10 as u8));
    }

    #[test]
    fn test_generate_constraints_no_external_inputs() {
        let cs = ConstraintSystem::<Fr>::new_ref();
        let params = (NONAME_CIRCUIT_NO_EXTERNAL_INPUTS.to_owned(), 2, 0);
        let inputs_public = r#"{"ivc_input":["2","5"]}"#;
        let ivc_inputs = NoNameIVCInputs::try_from((inputs_public.to_owned(), None)).unwrap();

        let ivc_inputs_var =
            Vec::<FpVar<Fr>>::new_witness(cs.clone(), || Ok(ivc_inputs.ivc_input)).unwrap();

        let f_circuit = NoNameFCircuit::<Fr, R1csBn254Field>::new(params).unwrap();
        f_circuit
            .generate_step_constraints(cs.clone(), 0, ivc_inputs_var, vec![])
            .unwrap();
        assert!(cs.is_satisfied().unwrap());
    }
}
