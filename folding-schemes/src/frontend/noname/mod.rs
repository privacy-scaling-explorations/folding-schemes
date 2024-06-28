use std::marker::PhantomData;
use std::str::FromStr;

use crate::Error;
use ark_r1cs_std::fields::fp::FpVar;
use ark_r1cs_std::R1CSVar;
use noname::inputs::{parse_inputs, JsonInputs};
use num_bigint::BigUint;
use serde::{Deserialize, Serialize};

use super::FCircuit;
use ark_ff::PrimeField;
use ark_noname::utils::compile_source_code;
use noname::backends::{r1cs::R1CS as R1CSNoName, BackendField};
use noname::witness::CompiledCircuit;

#[derive(Serialize, Deserialize)]
struct NoNameJSONIVCInput {
    pub ivc_input: Vec<String>,
}

#[derive(Serialize, Deserialize)]
struct NoNameJSONExternalInputs {
    pub external_inputs: Vec<String>,
}

impl<F: PrimeField> From<Vec<F>> for NoNameJSONIVCInput {
    fn from(value: Vec<F>) -> Self {
        let mut ivc_input = Vec::with_capacity(value.len());
        for field_element in value {
            ivc_input.push(field_element.to_string());
        }
        NoNameJSONIVCInput { ivc_input }
    }
}

impl NoNameJSONIVCInput {
    fn from_fpvars<F: PrimeField>(value: &Vec<FpVar<F>>) -> Self {
        let field_elements = Vec::<F>::with_capacity(value.len());
        for var in value {
            let val = var.value().unwrap();
        }
        NoNameJSONIVCInput::from(field_elements)
    }
}

impl<F: PrimeField> From<Vec<F>> for NoNameJSONExternalInputs {
    fn from(value: Vec<F>) -> Self {
        let mut external_inputs = Vec::with_capacity(value.len());
        for field_element in value {
            external_inputs.push(field_element.to_string());
        }
        NoNameJSONExternalInputs { external_inputs }
    }
}

impl NoNameJSONExternalInputs {
    fn from_fpvars<F: PrimeField>(value: &Vec<FpVar<F>>) -> Self {
        let field_elements = Vec::<F>::with_capacity(value.len());
        for var in value {
            let val = var.value().unwrap();
        }
        NoNameJSONExternalInputs::from(field_elements)
    }
}

pub struct NoNameIVCInputs<F: PrimeField> {
    pub ivc_input: Vec<F>,
    pub external_inputs: Vec<F>,
}

impl<F: PrimeField> TryFrom<(&str, &str)> for NoNameIVCInputs<F> {
    type Error = Error;

    fn try_from(value: (&str, &str)) -> Result<Self, Error> {
        let (ivc_public_inputs, external_inputs) = value;
        let json_ivc_inputs = serde_json::from_str::<NoNameJSONIVCInput>(ivc_public_inputs)
            .map_err(|e| Error::Other(format!("{:?}", e)))?;
        let json_external_inputs =
            serde_json::from_str::<NoNameJSONExternalInputs>(external_inputs)
                .map_err(|e| Error::Other(format!("{:?}", e)))?;

        let mut ivc_input = Vec::with_capacity(json_ivc_inputs.ivc_input.len());
        let mut external_inputs = Vec::with_capacity(json_external_inputs.external_inputs.len());

        for str_input in json_ivc_inputs.ivc_input.iter() {
            let parsed_biguint =
                BigUint::from_str(&str_input).map_err(|e| Error::Other(format!("{:?}", e)))?;
            let field_element = F::from_le_bytes_mod_order(&parsed_biguint.to_bytes_be());
            ivc_input.push(field_element);
        }
        for str_input in json_external_inputs.external_inputs.iter() {
            let parsed_biguint =
                BigUint::from_str(&str_input).map_err(|e| Error::Other(format!("{:?}", e)))?;
            let field_element = F::from_le_bytes_mod_order(&parsed_biguint.to_bytes_be());
            external_inputs.push(field_element);
        }

        Ok(NoNameIVCInputs {
            ivc_input,
            external_inputs,
        })
    }
}

impl<F: PrimeField> TryInto<(JsonInputs, JsonInputs)> for NoNameIVCInputs<F> {
    type Error = Error;

    fn try_into(self) -> Result<(JsonInputs, JsonInputs), Error> {
        let ivc_inputs = serde_json::to_string(&NoNameJSONIVCInput::from(self.ivc_input))
            .map_err(|e| Error::Other(format!("{:?}", e)))?;
        let external_inputs =
            serde_json::to_string(&NoNameJSONIVCInput::from(self.external_inputs))
                .map_err(|e| Error::Other(format!("{:?}", e)))?;
        Ok((
            parse_inputs(&ivc_inputs).map_err(|e| Error::Other(format!("{:?}", e)))?,
            parse_inputs(&external_inputs).map_err(|e| Error::Other(format!("{:?}", e)))?,
        ))
    }
}

#[derive(Serialize, Deserialize)]
pub struct NoNameExternalInputs {
    pub external_inputs: Vec<usize>,
}

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
        let external_inputs =
            serde_json::to_string(&NoNameJSONExternalInputs::from_fpvars(&external_inputs))
                .unwrap();
        let ivc_inputs = serde_json::to_string(&NoNameJSONIVCInput::from_fpvars(&z_i)).unwrap();
        let noname_inputs =
            NoNameIVCInputs::try_from((ivc_inputs.as_str(), external_inputs.as_str())).unwrap();
        let (ivc_inputs, external_inputs) = noname_inputs.try_into().unwrap();
        let noname_witness = self
            .circuit
            .generate_witness(ivc_inputs, external_inputs)
            .unwrap();
    }
}

#[cfg(test)]
mod tests {

    use ark_bn254::Fr;
    use ark_r1cs_std::{alloc::AllocVar, fields::fp::FpVar};
    use noname::{
        backends::r1cs::R1csBn254Field,
        inputs::{parse_inputs, JsonInputs},
    };

    use crate::frontend::FCircuit;

    use super::{NoNameExternalInputs, NoNameFCircuit, NoNameIVCInputs};
    use ark_relations::r1cs::ConstraintSystem;

    const CIRCUIT_EXTERNAL_INPUTS: &str =
        "fn main(pub ivc_input: [Field; 2], external_inputs: [Field; 2]) -> [Field; 2]{
    let xx = external_inputs[0] + ivc_input[0];
    let yy = external_inputs[1] * ivc_input[1];
    assert_eq(yy, xx);
    return [xx, yy];
}";

    #[test]
    fn test_noname_step_native() {}

    #[test]
    fn test_noname_step_constraints() {
        let cs = ConstraintSystem::<Fr>::new_ref();
        let params = (CIRCUIT_EXTERNAL_INPUTS.to_owned(), 2, 2);
        let circuit = NoNameFCircuit::<Fr, R1csBn254Field>::new(params).unwrap();
        let inputs_public = r#"{"ivc_input":["2","5"]}"#;
        let inputs_private = r#"{"external_inputs":["8","2"]}"#;
        let ivc_inputs = NoNameIVCInputs::try_from((inputs_public, inputs_private)).unwrap();

        let ivc_inputs_var =
            Vec::<FpVar<Fr>>::new_witness(cs.clone(), || Ok(ivc_inputs.ivc_input)).unwrap();

        let json_public = parse_inputs(inputs_public).unwrap();
        let json_private = parse_inputs(inputs_private).unwrap();
        //let witness = circuit
        //    .circuit
        //    .generate_witness(json_public, json_private)
        //    .unwrap();
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
