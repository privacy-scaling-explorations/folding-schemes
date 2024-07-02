use crate::Error;
use ark_ff::PrimeField;
use ark_r1cs_std::fields::fp::FpVar;
use ark_r1cs_std::R1CSVar;
use ark_relations::r1cs::SynthesisError;
use noname::inputs::{parse_inputs, JsonInputs};
use num_bigint::BigUint;
use serde::{Deserialize, Serialize};
use std::str::FromStr;

pub const NONAME_CIRCUIT_EXTERNAL_INPUTS: &str =
    "fn main(pub ivc_input: [Field; 2], external_inputs: [Field; 2]) -> [Field; 2] {
    let xx = external_inputs[0] + ivc_input[0];
    let yy = external_inputs[1] * ivc_input[1];
    assert_eq(yy, xx);
    return [xx, yy];
}";

pub const NONAME_CIRCUIT_NO_EXTERNAL_INPUTS: &str =
    "fn main(pub ivc_input: [Field; 2]) -> [Field; 2] {
    let out = ivc_input[0] * ivc_input[1];
    return [out, ivc_input[1]];
}";

#[derive(Serialize, Deserialize)]
pub struct NoNameJSONIVCInput {
    pub ivc_input: Vec<String>,
}

#[derive(Serialize, Deserialize)]
pub struct NoNameJSONExternalInputs {
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
    pub fn from_fpvars<F: PrimeField>(value: &Vec<FpVar<F>>) -> Result<Self, SynthesisError> {
        let mut field_elements = Vec::<F>::with_capacity(value.len());
        for var in value {
            let val = var.value()?;
            field_elements.push(val);
        }
        Ok(NoNameJSONIVCInput::from(field_elements))
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
    pub fn from_fpvars<F: PrimeField>(value: &Vec<FpVar<F>>) -> Result<Self, SynthesisError> {
        let mut field_elements = Vec::<F>::with_capacity(value.len());
        for var in value {
            let val = var.value()?;
            field_elements.push(val);
        }
        Ok(NoNameJSONExternalInputs::from(field_elements))
    }
}

pub struct NoNameIVCInputs<F: PrimeField> {
    pub ivc_input: Vec<F>,
    pub external_inputs: Option<Vec<F>>,
}

impl<F: PrimeField> TryFrom<(String, Option<String>)> for NoNameIVCInputs<F> {
    type Error = Error;

    fn try_from(value: (String, Option<String>)) -> Result<Self, Error> {
        let (ivc_public_inputs, external_inputs) = value;
        let json_ivc_inputs = serde_json::from_str::<NoNameJSONIVCInput>(&ivc_public_inputs)
            .map_err(|e| Error::Other(format!("{:?}", e)))?;

        let json_external_inputs = match external_inputs {
            Some(inputs) => Some(
                serde_json::from_str::<NoNameJSONExternalInputs>(&inputs)
                    .map_err(|e| Error::Other(format!("{:?}", e)))?,
            ),
            None => None,
        };

        let mut ivc_input = Vec::with_capacity(json_ivc_inputs.ivc_input.len());
        for str_input in json_ivc_inputs.ivc_input.iter() {
            let parsed_biguint =
                BigUint::from_str(&str_input).map_err(|e| Error::Other(format!("{:?}", e)))?;
            let field_element = F::from_le_bytes_mod_order(&parsed_biguint.to_bytes_be());
            ivc_input.push(field_element);
        }

        let external_inputs = match json_external_inputs {
            Some(inputs) => {
                let mut external_inputs = Vec::with_capacity(inputs.external_inputs.len());
                for str_input in inputs.external_inputs.iter() {
                    let parsed_biguint = BigUint::from_str(&str_input)
                        .map_err(|e| Error::Other(format!("{:?}", e)))?;
                    let field_element = F::from_le_bytes_mod_order(&parsed_biguint.to_bytes_be());
                    external_inputs.push(field_element);
                }
                Some(external_inputs)
            }
            None => None,
        };

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
        let external_inputs = match self.external_inputs {
            Some(inputs) => {
                let parsed_inputs = parse_inputs(
                    &serde_json::to_string(&NoNameJSONExternalInputs::from(inputs))
                        .map_err(|e| Error::Other(format!("{:?}", e)))?,
                )
                .map_err(|e| Error::Other(format!("{:?}", e)))?;
                parsed_inputs
            }
            None => parse_inputs(r#"{}"#).map_err(|e| Error::Other(format!("{:?}", e)))?,
        };
        Ok((
            parse_inputs(&ivc_inputs).map_err(|e| Error::Other(format!("{:?}", e)))?,
            external_inputs,
        ))
    }
}

#[derive(Serialize, Deserialize)]
pub struct NoNameExternalInputs {
    pub external_inputs: Vec<usize>,
}
