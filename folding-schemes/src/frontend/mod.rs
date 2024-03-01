pub mod circom;

use crate::Error;
use ark_ff::PrimeField;
use ark_r1cs_std::fields::fp::FpVar;
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError, ConstraintSynthesizer};
use ark_r1cs_std::alloc::AllocVar;
use ark_std::fmt::Debug;
use ark_r1cs_std::R1CSVar;

use crate::frontend::circom::CircomWrapper;
use std::path::PathBuf;
use num_bigint::BigInt;
use ark_circom::circom::CircomCircuit;

/// FCircuit defines the trait of the circuit of the F function, which is the one being folded (ie.
/// inside the agmented F' function).
/// The parameter z_i denotes the current state, and z_{i+1} denotes the next state after applying
/// the step.
pub trait FCircuit<F: PrimeField>: Clone + Debug {
    type Params: Debug;

    /// returns a new FCircuit instance
    fn new(params: Self::Params) -> Self;

    /// returns the number of elements in the state of the FCircuit, which corresponds to the
    /// FCircuit inputs.
    fn state_len(self) -> usize;

    /// computes the next state values in place, assigning z_{i+1} into z_i, and computing the new
    /// z_{i+1}
    fn step_native(
        // this method uses self, so that each FCircuit implementation (and different frontends)
        // can hold a state if needed to store data to compute the next state.
        self,
        z_i: Vec<F>,
    ) -> Result<Vec<F>, Error>;

    /// generates the constraints for the step of F for the given z_i
    fn generate_step_constraints(
        // this method uses self, so that each FCircuit implementation (and different frontends)
        // can hold a state if needed to store data to generate the constraints.
        self,
        cs: ConstraintSystemRef<F>,
        z_i: Vec<FpVar<F>>,
    ) -> Result<Vec<FpVar<F>>, SynthesisError>;
}

/// Define CircomFCircuit
#[derive(Clone, Debug)]
pub struct CircomtoFCircuit<F: PrimeField> {
    circom_wrapper: CircomWrapper<F>,
}

impl<F: PrimeField> FCircuit<F> for CircomtoFCircuit<F> {
    type Params = (PathBuf, PathBuf);

    fn new(params: Self::Params) -> Self {
        let (r1cs_path, wasm_path) = params;
        let circom_wrapper = CircomWrapper::new(r1cs_path, wasm_path);
        Self { circom_wrapper}
    }

    fn step_native(self, z_i: Vec<F>) -> Result<Vec<F>, Error> {
        // Convert from PrimeField::Bigint to num_bigint::BigInt
        let input_num_bigint = z_i.iter().map(|val| {
            self.circom_wrapper.ark_bigint_to_num_bigint(*val)
        }).collect::<Vec<BigInt>>();

        // Compute witness
        let (_, witness) = self.circom_wrapper.extract_r1cs_and_witness(&[
            ("ivc_input".to_string(), input_num_bigint)
        ]).map_err(|e| Error::Other(format!("Circom computation failed: {}", e)))?;  
        
        // [To Do: extract the z_i1(next public output) in Z(R1CS vector)]
        match witness {
            Some(new_z_i) => Ok(new_z_i),
            None => Err(Error::Other("Witness was not found".to_string())),
        }
    }

    fn generate_step_constraints(
        self,
        cs: ConstraintSystemRef<F>,
        z_i: Vec<FpVar<F>>,
    ) -> Result<Vec<FpVar<F>>, SynthesisError> {
        let mut input_values = Vec::new();
        // Convert each FpVar to BigInt and add it to the input_values vector
        for fp_var in z_i.iter() {
            // Convert from FpVar to PrimeField::Bigint
            let prime_bigint = fp_var.value()?;
            // Convert from PrimeField::Bigint to num_bigint::BigInt
            let num_bigint = self.circom_wrapper.ark_bigint_to_num_bigint(prime_bigint);
            input_values.push(num_bigint);
        }
    
        // Temporarily
        let big_int_inputs = vec![("ivc_input".to_string(), input_values)];
        // let big_int_inputs = vec![("ivc_input".to_string(), vec![BigInt::from(5)])];

        let (r1cs, witness) = self.circom_wrapper.extract_r1cs_and_witness(&big_int_inputs)
            .map_err(|_| SynthesisError::AssignmentMissing)?;
        println!("Extracted R1CS and witness");
        println!("r1cs: {:?}", r1cs);
        println!("witness: {:?}", witness);

        // CircomCircuit constraints
        let circom_circuit = CircomCircuit { r1cs, witness };

        circom_circuit.generate_constraints(cs.clone())
            .map_err(|_| SynthesisError::AssignmentMissing)?;
        println!("Generated constraints");

        // [ToDo: error: Constraint trace requires enabling `ConstraintLayer`]
    
        // satisfication check
        if !cs.is_satisfied().unwrap() {
            println!("Constraint is not satisfied");
            return Err(SynthesisError::AssignmentMissing);
        }
        println!("Constraint is satisfied");
        
        // [To Do: extract the z_i1(next public output) in Z(R1CS vector)]
        //let new_z_i = witness.iter().map(|w| {
        //    FpVar::<F>::new_witness(cs.clone(), || Ok(*w))
        //}).collect::<Result<Vec<FpVar<F>>, SynthesisError>>()?;
    
        //Ok(new_z_i)
        Ok(z_i)
    } 
       
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use ark_bn254::Fr;
    use ark_r1cs_std::{alloc::AllocVar, eq::EqGadget};
    use ark_relations::r1cs::{
        ConstraintSynthesizer, ConstraintSystem, ConstraintSystemRef, SynthesisError,
    };
    use core::marker::PhantomData;

    /// CubicFCircuit is a struct that implements the FCircuit trait, for the R1CS example circuit
    /// from https://www.vitalik.ca/general/2016/12/10/qap.html, which checks `x^3 + x + 5 = y`. It
    /// has 2 public inputs which are used as the state. `z_i` is used as `x`, and `z_{i+1}` is
    /// used as `y`, and at the next step, `z_{i+1}` will be assigned to `z_i`, and a new `z+{i+1}`
    /// will be computted.
    #[derive(Clone, Copy, Debug)]
    pub struct CubicFCircuit<F: PrimeField> {
        _f: PhantomData<F>,
    }
    impl<F: PrimeField> FCircuit<F> for CubicFCircuit<F> {
        type Params = ();
        fn new(_params: Self::Params) -> Self {
            Self { _f: PhantomData }
        }
        fn state_len(self) -> usize {
            1
        }
        fn step_native(self, z_i: Vec<F>) -> Result<Vec<F>, Error> {
            Ok(vec![z_i[0] * z_i[0] * z_i[0] + z_i[0] + F::from(5_u32)])
        }
        fn generate_step_constraints(
            self,
            cs: ConstraintSystemRef<F>,
            z_i: Vec<FpVar<F>>,
        ) -> Result<Vec<FpVar<F>>, SynthesisError> {
            let five = FpVar::<F>::new_constant(cs.clone(), F::from(5u32))?;
            let z_i = z_i[0].clone();

            Ok(vec![&z_i * &z_i * &z_i + &z_i + &five])
        }
    }

    /// CustomFCircuit is a circuit that has the number of constraints specified in the
    /// `n_constraints` parameter. Note that the generated circuit will have very sparse matrices.
    #[derive(Clone, Copy, Debug)]
    pub struct CustomFCircuit<F: PrimeField> {
        _f: PhantomData<F>,
        pub n_constraints: usize,
    }
    impl<F: PrimeField> FCircuit<F> for CustomFCircuit<F> {
        type Params = usize;

        fn new(params: Self::Params) -> Self {
            Self {
                _f: PhantomData,
                n_constraints: params,
            }
        }
        fn state_len(self) -> usize {
            1
        }
        fn step_native(self, z_i: Vec<F>) -> Result<Vec<F>, Error> {
            let mut z_i1 = F::one();
            for _ in 0..self.n_constraints - 1 {
                z_i1 *= z_i[0];
            }
            Ok(vec![z_i1])
        }
        fn generate_step_constraints(
            self,
            cs: ConstraintSystemRef<F>,
            z_i: Vec<FpVar<F>>,
        ) -> Result<Vec<FpVar<F>>, SynthesisError> {
            let mut z_i1 = FpVar::<F>::new_witness(cs.clone(), || Ok(F::one()))?;
            for _ in 0..self.n_constraints - 1 {
                z_i1 *= z_i[0].clone();
            }

            Ok(vec![z_i1])
        }
    }

    /// WrapperCircuit is a circuit that wraps any circuit that implements the FCircuit trait. This
    /// is used to test the `FCircuit.generate_step_constraints` method. This is a similar wrapping
    /// than the one done in the `AugmentedFCircuit`, but without adding all the extra constraints
    /// of the AugmentedF circuit logic, in order to run lighter tests when we're not interested in
    /// the the AugmentedF logic but in the wrapping of the circuits.
    pub struct WrapperCircuit<F: PrimeField, FC: FCircuit<F>> {
        pub FC: FC, // F circuit
        pub z_i: Option<Vec<F>>,
        pub z_i1: Option<Vec<F>>,
    }
    impl<F, FC> ConstraintSynthesizer<F> for WrapperCircuit<F, FC>
    where
        F: PrimeField,
        FC: FCircuit<F>,
    {
        fn generate_constraints(self, cs: ConstraintSystemRef<F>) -> Result<(), SynthesisError> {
            let z_i = Vec::<FpVar<F>>::new_witness(cs.clone(), || {
                Ok(self.z_i.unwrap_or(vec![F::zero()]))
            })?;
            let z_i1 = Vec::<FpVar<F>>::new_input(cs.clone(), || {
                Ok(self.z_i1.unwrap_or(vec![F::zero()]))
            })?;
            let computed_z_i1 = self.FC.generate_step_constraints(cs.clone(), z_i.clone())?;

            computed_z_i1.enforce_equal(&z_i1)?;
            Ok(())
        }
    }

    #[test]
    fn test_testfcircuit() {
        let cs = ConstraintSystem::<Fr>::new_ref();
        let F_circuit = CubicFCircuit::<Fr>::new(());

        let wrapper_circuit = WrapperCircuit::<Fr, CubicFCircuit<Fr>> {
            FC: F_circuit,
            z_i: Some(vec![Fr::from(3_u32)]),
            z_i1: Some(vec![Fr::from(35_u32)]),
        };
        wrapper_circuit.generate_constraints(cs.clone()).unwrap();
        assert_eq!(cs.num_constraints(), 3);
    }

    #[test]
    fn test_customtestfcircuit() {
        let cs = ConstraintSystem::<Fr>::new_ref();
        let n_constraints = 1000;
        let custom_circuit = CustomFCircuit::<Fr>::new(n_constraints);
        let z_i = vec![Fr::from(5_u32)];
        let wrapper_circuit = WrapperCircuit::<Fr, CustomFCircuit<Fr>> {
            FC: custom_circuit,
            z_i: Some(z_i.clone()),
            z_i1: Some(custom_circuit.step_native(z_i).unwrap()),
        };
        wrapper_circuit.generate_constraints(cs.clone()).unwrap();
        assert_eq!(cs.num_constraints(), n_constraints);
    }

    #[test]
    fn test_circom_step_constraints() -> Result<(), Box<dyn std::error::Error>> {
        let r1cs_path = PathBuf::from("./src/frontend/circom/test_folder/cubic_circuit.r1cs");
        let wasm_path = PathBuf::from("./src/frontend/circom/test_folder/cubic_circuit_js/cubic_circuit.wasm");

        let circom_fcircuit = CircomtoFCircuit::<Fr>::new((r1cs_path, wasm_path));

        let cs = ConstraintSystem::<Fr>::new_ref();

        let z_i_values = vec![Fr::from(3u32)];

        let z_i_vars = z_i_values.into_iter().map(|val| {
            FpVar::<Fr>::new_witness(cs.clone(), || Ok(val))
                .expect("Failed to create FpVar")
        }).collect::<Vec<FpVar<Fr>>>();

        circom_fcircuit.generate_step_constraints(cs.clone(), z_i_vars)?;

        Ok(())
    }

    #[test]
    fn test_circom_step_native() -> Result<(), Box<dyn std::error::Error>> {
        let r1cs_path = PathBuf::from("./src/frontend/circom/test_folder/cubic_circuit.r1cs");
        let wasm_path = PathBuf::from("./src/frontend/circom/test_folder/cubic_circuit_js/cubic_circuit.wasm");

        let circom_fcircuit = CircomtoFCircuit::<Fr>::new((r1cs_path, wasm_path));

        let z_i = vec![Fr::from(3u32)];
        match circom_fcircuit.step_native(z_i) {
            Ok(witness) => {
                assert!(!witness.is_empty(), "Witness should not be empty");
                println!("Test passed with witness: {:?}", witness);
            },
            Err(e) => return Err(Box::new(e)),
        }
        Ok(())
    }

    // [To Do extract the z_i1]
    // Absolutely fails because all elements of Z(R1CS) are passed to z_i1
    #[test]
    fn test_wrapper_circomtofcircuit() {
        let r1cs_path = PathBuf::from("./src/frontend/circom/test_folder/cubic_circuit.r1cs");
        let wasm_path = PathBuf::from("./src/frontend/circom/test_folder/cubic_circuit_js/cubic_circuit.wasm");
        
        let z_i = vec![Fr::from(3u32)];
        let circom_fcircuit = CircomtoFCircuit::<Fr>::new((r1cs_path, wasm_path));

        let wrapper_circuit = WrapperCircuit {
            FC: circom_fcircuit,
            z_i: Some(z_i.clone()),
            z_i1: Some(vec![Fr::from(35u32)]),
        };

        let cs = ConstraintSystem::<Fr>::new_ref();

        wrapper_circuit.generate_constraints(cs.clone()).unwrap();
        assert!(cs.is_satisfied().unwrap(), "Constraint system is not satisfied");
    }
}