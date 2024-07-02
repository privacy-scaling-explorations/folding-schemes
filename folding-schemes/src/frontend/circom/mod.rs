use crate::frontend::FCircuit;
use crate::frontend::FpVar::Var;
use crate::Error;
use ark_circom::circom::{CircomCircuit, R1CS as CircomR1CS};
use ark_ff::PrimeField;
use ark_r1cs_std::alloc::AllocVar;
use ark_r1cs_std::fields::fp::FpVar;
use ark_r1cs_std::R1CSVar;
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError};
use ark_std::fmt::Debug;
use num_bigint::BigInt;
use std::path::PathBuf;
use std::rc::Rc;
use std::{fmt, usize};

pub mod utils;
use utils::CircomWrapper;

type ClosurePointer<F> = Rc<dyn Fn(usize, Vec<F>, Vec<F>) -> Result<Vec<F>, Error>>;

#[derive(Clone)]
struct CustomStepNative<F: PrimeField> {
    func: ClosurePointer<F>,
}

impl<F: PrimeField> fmt::Debug for CustomStepNative<F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "Function pointer: {:?}",
            std::any::type_name::<fn(usize, Vec<F>, Vec<F>) -> Result<Vec<F>, Error>>()
        )
    }
}

/// Define CircomFCircuit
#[derive(Clone, Debug)]
pub struct CircomFCircuit<F: PrimeField> {
    circom_wrapper: CircomWrapper<F>,
    pub state_len: usize,
    pub external_inputs_len: usize,
    r1cs: CircomR1CS<F>,
    custom_step_native_code: Option<CustomStepNative<F>>,
}

impl<F: PrimeField> CircomFCircuit<F> {
    pub fn set_custom_step_native(&mut self, func: ClosurePointer<F>) {
        self.custom_step_native_code = Some(CustomStepNative::<F> { func });
    }

    pub fn execute_custom_step_native(
        &self,
        _i: usize,
        z_i: Vec<F>,
        external_inputs: Vec<F>,
    ) -> Result<Vec<F>, Error> {
        if let Some(code) = &self.custom_step_native_code {
            (code.func)(_i, z_i, external_inputs)
        } else {
            #[cfg(test)]
            assert_eq!(z_i.len(), self.state_len());
            #[cfg(test)]
            assert_eq!(external_inputs.len(), self.external_inputs_len());

            let inputs_bi = z_i
                .iter()
                .map(|val| self.circom_wrapper.ark_primefield_to_num_bigint(*val))
                .collect::<Vec<BigInt>>();
            let mut inputs_map = vec![("ivc_input".to_string(), inputs_bi)];

            if self.external_inputs_len() > 0 {
                let external_inputs_bi = external_inputs
                    .iter()
                    .map(|val| self.circom_wrapper.ark_primefield_to_num_bigint(*val))
                    .collect::<Vec<BigInt>>();
                inputs_map.push(("external_inputs".to_string(), external_inputs_bi));
            }

            // Computes witness
            let witness = self
                .circom_wrapper
                .extract_witness(&inputs_map)
                .map_err(|e| {
                    Error::WitnessCalculationError(format!("Failed to calculate witness: {}", e))
                })?;

            // Extracts the z_i1(next state) from the witness vector.
            let z_i1 = witness[1..1 + self.state_len()].to_vec();
            Ok(z_i1)
        }
    }
}

impl<F: PrimeField> FCircuit<F> for CircomFCircuit<F> {
    /// (r1cs_path, wasm_path, state_len, external_inputs_len)
    type Params = (PathBuf, PathBuf, usize, usize);

    fn new(params: Self::Params) -> Result<Self, Error> {
        let (r1cs_path, wasm_path, state_len, external_inputs_len) = params;
        let circom_wrapper = CircomWrapper::new(r1cs_path, wasm_path);

        let r1cs = circom_wrapper.extract_r1cs()?;
        Ok(Self {
            circom_wrapper,
            state_len,
            external_inputs_len,
            r1cs,
            custom_step_native_code: None,
        })
    }

    fn state_len(&self) -> usize {
        self.state_len
    }
    fn external_inputs_len(&self) -> usize {
        self.external_inputs_len
    }

    fn step_native(
        &self,
        _i: usize,
        z_i: Vec<F>,
        external_inputs: Vec<F>,
    ) -> Result<Vec<F>, Error> {
        self.execute_custom_step_native(_i, z_i, external_inputs)
    }

    fn generate_step_constraints(
        &self,
        cs: ConstraintSystemRef<F>,
        _i: usize,
        z_i: Vec<FpVar<F>>,
        external_inputs: Vec<FpVar<F>>,
    ) -> Result<Vec<FpVar<F>>, SynthesisError> {
        #[cfg(test)]
        assert_eq!(z_i.len(), self.state_len());
        #[cfg(test)]
        assert_eq!(external_inputs.len(), self.external_inputs_len());

        let input_values = self.fpvars_to_bigints(&z_i)?;
        let mut inputs_map = vec![("ivc_input".to_string(), input_values)];

        if self.external_inputs_len() > 0 {
            let external_inputs_bi = self.fpvars_to_bigints(&external_inputs)?;
            inputs_map.push(("external_inputs".to_string(), external_inputs_bi));
        }

        let witness = self
            .circom_wrapper
            .extract_witness(&inputs_map)
            .map_err(|_| SynthesisError::AssignmentMissing)?;

        // Since public inputs are already allocated variables, we will tell `circom-compat` to not re-allocate those
        let mut already_allocated_public_inputs = vec![];
        for var in z_i.iter() {
            match var {
                Var(var) => already_allocated_public_inputs.push(var.variable),
                _ => return Err(SynthesisError::Unsatisfiable), // allocated z_i should be Var
            }
        }

        // Initializes the CircomCircuit.
        let circom_circuit = CircomCircuit {
            r1cs: self.r1cs.clone(),
            witness: Some(witness.clone()),
            public_inputs_indexes: already_allocated_public_inputs,
            allocate_inputs_as_witnesses: true,
        };

        // Generates the constraints for the circom_circuit.
        circom_circuit.generate_constraints(cs.clone())?;

        // TODO: https://github.com/privacy-scaling-explorations/sonobe/issues/104
        // We disable checking constraints for now
        // Checks for constraint satisfaction.
        // if !cs.is_satisfied().unwrap() {
        //     return Err(SynthesisError::Unsatisfiable);
        // }

        // Extracts the z_i1(next state) from the witness vector.
        let z_i1: Vec<FpVar<F>> = Vec::<FpVar<F>>::new_witness(cs.clone(), || {
            Ok(witness[1..1 + self.state_len()].to_vec())
        })?;

        Ok(z_i1)
    }
}

impl<F: PrimeField> CircomFCircuit<F> {
    fn fpvars_to_bigints(&self, fpVars: &[FpVar<F>]) -> Result<Vec<BigInt>, SynthesisError> {
        let mut input_values = Vec::new();
        // converts each FpVar to PrimeField value, then to num_bigint::BigInt.
        for fp_var in fpVars.iter() {
            // extracts the PrimeField value from FpVar.
            let primefield_value = fp_var.value()?;
            // converts the PrimeField value to num_bigint::BigInt.
            let num_bigint_value = self
                .circom_wrapper
                .ark_primefield_to_num_bigint(primefield_value);
            input_values.push(num_bigint_value);
        }
        Ok(input_values)
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use ark_bn254::Fr;
    use ark_relations::r1cs::ConstraintSystem;

    // Tests the step_native function of CircomFCircuit.
    #[test]
    fn test_circom_step_native() {
        let r1cs_path = PathBuf::from("./src/frontend/circom/test_folder/cubic_circuit.r1cs");
        let wasm_path =
            PathBuf::from("./src/frontend/circom/test_folder/cubic_circuit_js/cubic_circuit.wasm");

        let circom_fcircuit = CircomFCircuit::<Fr>::new((r1cs_path, wasm_path, 1, 0)).unwrap(); // state_len:1, external_inputs_len:0

        let z_i = vec![Fr::from(3u32)];
        let z_i1 = circom_fcircuit.step_native(1, z_i, vec![]).unwrap();
        assert_eq!(z_i1, vec![Fr::from(35u32)]);
    }

    // Tests the generate_step_constraints function of CircomFCircuit.
    #[test]
    fn test_circom_step_constraints() {
        let r1cs_path = PathBuf::from("./src/frontend/circom/test_folder/cubic_circuit.r1cs");
        let wasm_path =
            PathBuf::from("./src/frontend/circom/test_folder/cubic_circuit_js/cubic_circuit.wasm");

        let circom_fcircuit = CircomFCircuit::<Fr>::new((r1cs_path, wasm_path, 1, 0)).unwrap(); // state_len:1, external_inputs_len:0

        let cs = ConstraintSystem::<Fr>::new_ref();

        let z_i = vec![Fr::from(3u32)];

        let z_i_var = Vec::<FpVar<Fr>>::new_witness(cs.clone(), || Ok(z_i)).unwrap();
        let z_i1_var = circom_fcircuit
            .generate_step_constraints(cs.clone(), 1, z_i_var, vec![])
            .unwrap();
        assert_eq!(z_i1_var.value().unwrap(), vec![Fr::from(35u32)]);
    }

    // Tests the WrapperCircuit with CircomFCircuit.
    #[test]
    fn test_wrapper_circomtofcircuit() {
        let r1cs_path = PathBuf::from("./src/frontend/circom/test_folder/cubic_circuit.r1cs");
        let wasm_path =
            PathBuf::from("./src/frontend/circom/test_folder/cubic_circuit_js/cubic_circuit.wasm");

        let circom_fcircuit = CircomFCircuit::<Fr>::new((r1cs_path, wasm_path, 1, 0)).unwrap(); // state_len:1, external_inputs_len:0

        // Allocates z_i1 by using step_native function.
        let z_i = vec![Fr::from(3_u32)];
        let wrapper_circuit = crate::frontend::tests::WrapperCircuit {
            FC: circom_fcircuit.clone(),
            z_i: Some(z_i.clone()),
            z_i1: Some(circom_fcircuit.step_native(0, z_i.clone(), vec![]).unwrap()),
        };

        let cs = ConstraintSystem::<Fr>::new_ref();

        wrapper_circuit.generate_constraints(cs.clone()).unwrap();
        assert!(
            cs.is_satisfied().unwrap(),
            "Constraint system is not satisfied"
        );
    }

    #[test]
    fn test_circom_external_inputs() {
        let r1cs_path =
            PathBuf::from("./src/frontend/circom/test_folder/with_external_inputs.r1cs");
        let wasm_path = PathBuf::from(
            "./src/frontend/circom/test_folder/with_external_inputs_js/with_external_inputs.wasm",
        );
        let circom_fcircuit = CircomFCircuit::<Fr>::new((r1cs_path, wasm_path, 1, 2)).unwrap(); // state_len:1, external_inputs_len:2
        let cs = ConstraintSystem::<Fr>::new_ref();
        let z_i = vec![Fr::from(3u32)];
        let external_inputs = vec![Fr::from(6u32), Fr::from(7u32)];

        // run native step
        let z_i1_native = circom_fcircuit
            .step_native(1, z_i.clone(), external_inputs.clone())
            .unwrap();

        // run gadget step
        let z_i_var = Vec::<FpVar<Fr>>::new_witness(cs.clone(), || Ok(z_i)).unwrap();
        let external_inputs_var =
            Vec::<FpVar<Fr>>::new_witness(cs.clone(), || Ok(external_inputs.clone())).unwrap();
        let z_i1_var = circom_fcircuit
            .generate_step_constraints(cs.clone(), 1, z_i_var, external_inputs_var)
            .unwrap();

        assert_eq!(z_i1_var.value().unwrap(), z_i1_native);

        // re-init cs and run gadget step with wrong ivc inputs (first ivc should not be zero)
        let cs = ConstraintSystem::<Fr>::new_ref();
        let wrong_z_i = vec![Fr::from(0)];
        let wrong_z_i_var = Vec::<FpVar<Fr>>::new_witness(cs.clone(), || Ok(wrong_z_i)).unwrap();
        let external_inputs_var =
            Vec::<FpVar<Fr>>::new_witness(cs.clone(), || Ok(external_inputs)).unwrap();
        let _z_i1_var = circom_fcircuit.generate_step_constraints(
            cs.clone(),
            1,
            wrong_z_i_var,
            external_inputs_var,
        );
        // TODO:: https://github.com/privacy-scaling-explorations/sonobe/issues/104
        // Disable check for now
        // assert!(z_i1_var.is_err());
    }

    #[test]
    fn test_circom_no_external_inputs() {
        let r1cs_path = PathBuf::from("./src/frontend/circom/test_folder/no_external_inputs.r1cs");
        let wasm_path = PathBuf::from(
            "./src/frontend/circom/test_folder/no_external_inputs_js/no_external_inputs.wasm",
        );
        let circom_fcircuit = CircomFCircuit::<Fr>::new((r1cs_path, wasm_path, 3, 0)).unwrap();
        let cs = ConstraintSystem::<Fr>::new_ref();
        let z_i = vec![Fr::from(3u32), Fr::from(4u32), Fr::from(5u32)];
        let z_i_var = Vec::<FpVar<Fr>>::new_witness(cs.clone(), || Ok(z_i.clone())).unwrap();

        // run native step
        let z_i1_native = circom_fcircuit.step_native(1, z_i.clone(), vec![]).unwrap();

        // run gadget step
        let z_i1_var = circom_fcircuit
            .generate_step_constraints(cs.clone(), 1, z_i_var, vec![])
            .unwrap();

        assert_eq!(z_i1_var.value().unwrap(), z_i1_native);

        // re-init cs and run gadget step with wrong ivc inputs (first ivc input should not be zero)
        let cs = ConstraintSystem::<Fr>::new_ref();
        let wrong_z_i = vec![Fr::from(0u32), Fr::from(4u32), Fr::from(5u32)];
        let wrong_z_i_var = Vec::<FpVar<Fr>>::new_witness(cs.clone(), || Ok(wrong_z_i)).unwrap();
        let _z_i1_var =
            circom_fcircuit.generate_step_constraints(cs.clone(), 1, wrong_z_i_var, vec![]);
        // TODO:: https://github.com/privacy-scaling-explorations/sonobe/issues/104
        // Disable check for now
        // assert!(z_i1_var.is_err())
    }

    #[test]
    fn test_custom_code() {
        let r1cs_path = PathBuf::from("./src/frontend/circom/test_folder/cubic_circuit.r1cs");
        let wasm_path =
            PathBuf::from("./src/frontend/circom/test_folder/cubic_circuit_js/cubic_circuit.wasm");

        let mut circom_fcircuit = CircomFCircuit::<Fr>::new((r1cs_path, wasm_path, 1, 0)).unwrap(); // state_len:1, external_inputs_len:0

        circom_fcircuit.set_custom_step_native(Rc::new(|_i, z_i, _external| {
            let z = z_i[0];
            Ok(vec![z * z * z + z + Fr::from(5)])
        }));

        // Allocates z_i1 by using step_native function.
        let z_i = vec![Fr::from(3_u32)];
        let wrapper_circuit = crate::frontend::tests::WrapperCircuit {
            FC: circom_fcircuit.clone(),
            z_i: Some(z_i.clone()),
            z_i1: Some(circom_fcircuit.step_native(0, z_i.clone(), vec![]).unwrap()),
        };

        let cs = ConstraintSystem::<Fr>::new_ref();

        wrapper_circuit.generate_constraints(cs.clone()).unwrap();
        assert!(
            cs.is_satisfied().unwrap(),
            "Constraint system is not satisfied"
        );
    }
}
