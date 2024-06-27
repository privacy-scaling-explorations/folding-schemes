use std::marker::PhantomData;

use crate::Error;

use super::FCircuit;
use ark_ff::PrimeField;
use ark_noname::utils::compile_source_code;
use noname::backends::{
    r1cs::{GeneratedWitness, R1CS as R1CSNoName},
    BackendField,
};
use noname::witness::CompiledCircuit;

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
        // build json input values from the z_i vec vector and the external inputs
        // we will also need to slice the witneess vector but for this, we need to be able to
        // output public values as arrays
        //let generated_witness = self
        //    .circuit
        //    .generate_witness(json_public, json_private)
        //    .unwrap();
        todo!()
    }
}

#[cfg(test)]
mod tests {
    use std::u128;

    use ark_bn254::Fr;
    use ark_ff::PrimeField;
    use ark_r1cs_std::fields::fp::FpVar;
    use color_eyre::eyre::Ok;
    use noname::{
        backends::r1cs::R1csBn254Field,
        inputs::{parse_inputs, JsonInputs},
    };
    use serde_json::Number;

    use crate::{frontend::FCircuit, Error};

    use super::NoNameFCircuit;
    use ark_relations::r1cs::{ConstraintSystem, ConstraintSystemRef};
    use serde::{Deserialize, Serialize};

    const CIRCUIT_EXTERNAL_INPUTS: &str =
        "fn main(pub ivc_input: [Field; 2], external_inputs: [Field; 2]) -> [Field; 2]{
    let xx = external_inputs[0] + ivc_input[0];
    let yy = external_inputs[1] * ivc_input[1];
    assert_eq(yy, xx);
    return [xx, yy];
}";

    #[test]
    fn test_noname_step_native() {}

    #[derive(Serialize, Deserialize)]
    pub struct NoNameIVCInputs {
        pub ivc_inputs: Vec<usize>,
    }

    #[derive(Serialize, Deserialize)]
    pub struct NoNameExternalInputs {
        pub external_inputs: Vec<usize>,
    }

    #[test]
    fn test_noname_step_constraints() {
        let cs = ConstraintSystem::<Fr>::new_ref();
        let params = (CIRCUIT_EXTERNAL_INPUTS.to_owned(), 2, 2);
        let circuit = NoNameFCircuit::<Fr, R1csBn254Field>::new(params).unwrap();
        let inputs_public = r#"{"ivc_input": ["2", "5"]}"#;
        let inputs_private = r#"{"external_inputs": ["8", "2"]}"#;
        let ivc_inputs: Vec<Fr> = serde_json::from_str::<NoNameIVCInputs>(inputs_public)
            .unwrap()
            .ivc_inputs
            .into_iter()
            .map(|value| Fr::from(value as u128))
            .collect();
        let external_inputs: Vec<Fr> = serde_json::from_str::<NoNameExternalInputs>(inputs_private)
            .unwrap()
            .external_inputs
            .into_iter()
            .map(|value| Fr::from(value as u128))
            .collect();

        let json_public = parse_inputs(inputs_public).unwrap();
        let json_private = parse_inputs(inputs_private).unwrap();

        // convert json inputs to fp vars
    }

    //fn assign_json_inputs_as_fpvars<F: PrimeField>(
    //    cs: ConstraintSystemRef<F>,
    //    json_input: &JsonInputs,
    //) -> Result<(Vec<FpVar<F>>, Vec<FpVar<F>>), Error> {
    //    let ivc_inputs = match json_input.0.get("ivc_input") {
    //        Some(ivc_input_array) => {
    //            let fp_vars_public_inputs = match ivc_input_array {
    //                serde_json::Value::Array(ivc_values) => {
    //                    let ivc_field_elements: Vec<F> = Vec::with_capacity(ivc_values.len());
    //                    for value in ivc_values {
    //                        match value {
    //                            serde_json::Value::Number(element)=> {
    //                                let element = element.n;
    //                            },
    //                            _ => return Err(Error::Other("Can not accept a type different from number for IVC inputs".to_owned()))
    //                        }
    //                    }

    //                }
    //                _ => return Err(Error::Other("IVC inputs should be an array".to_owned())),
    //            };
    //        }
    //        None => {
    //            return Err(Error::Other(
    //                "There should at least be public IVC inputs set!".to_owned(),
    //            ))
    //        }
    //    };

    //    let external_inputs = match json_input.0.get("external_inputs") {
    //        Some(external_inputs) => {}
    //        None => Ok(),
    //    }
    //}

    #[test]
    fn test_external_inputs() {}

    #[test]
    fn test_no_external_inputs() {}
}
