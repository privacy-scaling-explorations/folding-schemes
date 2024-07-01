use crate::Error;
use ark_noname::NoNameCircuit;
use ark_r1cs_std::alloc::AllocVar;
use ark_r1cs_std::fields::fp::FpVar;
use ark_r1cs_std::R1CSVar;
use ark_relations::r1cs::ConstraintSynthesizer;
use noname::inputs::{parse_inputs, JsonInputs};
use num_bigint::BigUint;
use serde::{Deserialize, Serialize};
use std::marker::PhantomData;
use std::str::FromStr;

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
        let mut field_elements = Vec::<F>::with_capacity(value.len());
        for var in value {
            let val = var.value().unwrap();
            field_elements.push(val);
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
        let mut field_elements = Vec::<F>::with_capacity(value.len());
        for var in value {
            let val = var.value().unwrap();
            field_elements.push(val);
        }
        NoNameJSONExternalInputs::from(field_elements)
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
            None => parse_inputs(&serde_json::to_string("{blank: []}").unwrap()).unwrap(),
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
        // fpvars -> String -> formatted json -> JsonInputs
        let external_inputs_present = external_inputs.len() != 0;
        let external_inputs_json = match external_inputs_present {
            false => None,
            true => {
                let json = serde_json::to_string(&NoNameJSONExternalInputs::from_fpvars(
                    &external_inputs.clone(),
                ))
                .unwrap();
                Some(json)
            }
        };
        let ivc_inputs = serde_json::to_string(&NoNameJSONIVCInput::from_fpvars(&z_i)).unwrap();
        let noname_inputs =
            NoNameIVCInputs::<F>::try_from((ivc_inputs, external_inputs_json)).unwrap();
        let (ivc_inputs, external_inputs) = noname_inputs.try_into().unwrap();
        let noname_witness = self
            .circuit
            .generate_witness(ivc_inputs, external_inputs)
            .unwrap();

        let noname_circuit = NoNameCircuit {
            compiled_circuit: self.circuit.clone(),
            witness: noname_witness,
        };
        noname_circuit.generate_constraints(cs.clone())?;

        assert!(cs.is_satisfied()?);
        // let z_i1: Vec<FpVar<F>> = Vec::<FpVar<F>>::new_witness(cs.clone(), || {
        //     Ok(witness[1..1 + self.state_len()].to_vec())
        // })?;

        Ok(vec![FpVar::new_witness(cs.clone(), || Ok(F::one()))?])
    }
}

#[cfg(test)]
mod tests {

    use ark_bn254::Fr;
    use ark_noname::circuits::WITH_PUBLIC_OUTPUT_ARRAY;
    use ark_r1cs_std::{alloc::AllocVar, fields::fp::FpVar};
    use noname::{backends::r1cs::R1csBn254Field, inputs::parse_inputs};

    use crate::frontend::FCircuit;

    use super::{NoNameExternalInputs, NoNameFCircuit, NoNameIVCInputs};
    use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystem};

    const CIRCUIT_EXTERNAL_INPUTS: &str =
        "fn main(pub ivc_input: [Field; 2], external_inputs: [Field; 2]) -> [Field; 2] {
    let xx = external_inputs[0] + ivc_input[0];
    let yy = external_inputs[1] * ivc_input[1];
    assert_eq(yy, xx);
    return [xx, yy];
}";

    const CIRCUIT_NO_EXTERNAL_INPUTS: &str = "fn main(pub ivc_input: [Field; 2]) -> [Field; 2] {
    let out = ivc_input[0] * ivc_input[1];
    return [out, ivc_input[1]];
}";

    #[test]
    fn test_noname_step_native() {}

    #[test]
    fn test_step_constraints() {
        let cs = ConstraintSystem::<Fr>::new_ref();
        let params = (CIRCUIT_EXTERNAL_INPUTS.to_owned(), 2, 2);
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

        circuit.generate_step_constraints(cs.clone(), 0, ivc_inputs_var, external_inputs_var);
    }

    #[test]
    fn test_wrapper_to_nonamecircuit() {
        let params = (CIRCUIT_NO_EXTERNAL_INPUTS.to_string(), 2, 2);
        let noname_fcircuit = NoNameFCircuit::<Fr, R1csBn254Field>::new(params).unwrap();

        // Allocates z_i1 by using step_native function.
        let z_i = vec![Fr::from(2_u32), Fr::from(5_u32)];
        //let wrapper_circuit = crate::frontend::tests::WrapperCircuit {
        //    FC: noname_fcircuit.clone(),
        //    z_i: Some(z_i.clone()),
        //    z_i1: Some(noname_fcircuit.step_native(0, z_i.clone(), vec![]).unwrap()),
        //};

        //let cs = ConstraintSystem::<Fr>::new_ref();

        //wrapper_circuit.generate_constraints(cs.clone()).unwrap();
        //assert!(
        //    cs.is_satisfied().unwrap(),
        //    "Constraint system is not satisfied"
        //);
    }

    #[test]
    fn test_external_inputs() {}

    #[test]
    fn test_no_external_inputs() {
        let cs = ConstraintSystem::<Fr>::new_ref();
        let params = (CIRCUIT_NO_EXTERNAL_INPUTS.to_owned(), 2, 2);
        let circuit = NoNameFCircuit::<Fr, R1csBn254Field>::new(params).unwrap();
        let inputs_public = r#"{"ivc_input":["2","5"]}"#;
        let ivc_inputs = NoNameIVCInputs::try_from((inputs_public.to_owned(), None)).unwrap();

        let ivc_inputs_var =
            Vec::<FpVar<Fr>>::new_witness(cs.clone(), || Ok(ivc_inputs.ivc_input)).unwrap();

        let json_public = parse_inputs(inputs_public).unwrap();

        let params = (WITH_PUBLIC_OUTPUT_ARRAY.to_string(), 2, 2);
        let f_circuit = NoNameFCircuit::<Fr, R1csBn254Field>::new(params).unwrap();
    }
}
