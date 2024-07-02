use ark_circom::{
    circom::{r1cs_reader, R1CS},
    WitnessCalculator,
};
use ark_ff::{BigInteger, PrimeField};
use color_eyre::Result;
use num_bigint::{BigInt, Sign};
use std::{fs::File, io::BufReader, marker::PhantomData, path::PathBuf};

use crate::Error;

// A struct that wraps Circom functionalities, allowing for extraction of R1CS and witnesses
// based on file paths to Circom's .r1cs and .wasm.
#[derive(Clone, Debug)]
pub struct CircomWrapper<F: PrimeField> {
    r1cs_filepath: PathBuf,
    wasm_filepath: PathBuf,
    _marker: PhantomData<F>,
}

impl<F: PrimeField> CircomWrapper<F> {
    // Creates a new instance of the CircomWrapper with the file paths.
    pub fn new(r1cs_filepath: PathBuf, wasm_filepath: PathBuf) -> Self {
        CircomWrapper {
            r1cs_filepath,
            wasm_filepath,
            _marker: PhantomData,
        }
    }

    // Aggregated function to obtain R1CS and witness from Circom.
    pub fn extract_r1cs_and_witness(
        &self,
        inputs: &[(String, Vec<BigInt>)],
    ) -> Result<(R1CS<F>, Option<Vec<F>>), Error> {
        // Extracts the R1CS
        let file = File::open(&self.r1cs_filepath)?;
        let reader = BufReader::new(file);
        let r1cs_file = r1cs_reader::R1CSFile::<F>::new(reader)?;
        let r1cs = r1cs_reader::R1CS::<F>::from(r1cs_file);

        // Extracts the witness vector
        let witness_vec = self.extract_witness(inputs)?;

        Ok((r1cs, Some(witness_vec)))
    }

    pub fn extract_r1cs(&self) -> Result<R1CS<F>, Error> {
        let file = File::open(&self.r1cs_filepath)?;
        let reader = BufReader::new(file);
        let r1cs_file = r1cs_reader::R1CSFile::<F>::new(reader)?;
        let mut r1cs = r1cs_reader::R1CS::<F>::from(r1cs_file);
        r1cs.wire_mapping = None;
        Ok(r1cs)
    }

    // Extracts the witness vector as a vector of PrimeField elements.
    pub fn extract_witness(&self, inputs: &[(String, Vec<BigInt>)]) -> Result<Vec<F>, Error> {
        let witness_bigint = self.calculate_witness(inputs)?;

        witness_bigint
            .iter()
            .map(|big_int| {
                self.num_bigint_to_ark_bigint(big_int)
                    .and_then(|ark_big_int| {
                        F::from_bigint(ark_big_int)
                            .ok_or_else(|| Error::Other("could not get F from bigint".to_string()))
                    })
            })
            .collect()
    }

    // Calculates the witness given the Wasm filepath and inputs.
    pub fn calculate_witness(
        &self,
        inputs: &[(String, Vec<BigInt>)],
    ) -> Result<Vec<BigInt>, Error> {
        let mut calculator = WitnessCalculator::new(&self.wasm_filepath).map_err(|e| {
            Error::WitnessCalculationError(format!("Failed to create WitnessCalculator: {}", e))
        })?;
        calculator
            .calculate_witness(inputs.iter().cloned(), true)
            .map_err(|e| {
                Error::WitnessCalculationError(format!("Failed to calculate witness: {}", e))
            })
    }

    // Converts a num_bigint::BigInt to a PrimeField::BigInt.
    pub fn num_bigint_to_ark_bigint(&self, value: &BigInt) -> Result<F::BigInt, Error> {
        let big_uint = value
            .to_biguint()
            .ok_or_else(|| Error::BigIntConversionError("BigInt is negative".to_string()))?;
        F::BigInt::try_from(big_uint).map_err(|_| {
            Error::BigIntConversionError("Failed to convert to PrimeField::BigInt".to_string())
        })
    }

    // Converts a PrimeField element to a num_bigint::BigInt representation.
    pub fn ark_primefield_to_num_bigint(&self, value: F) -> BigInt {
        let primefield_bigint: F::BigInt = value.into_bigint();
        let bytes = primefield_bigint.to_bytes_be();
        BigInt::from_bytes_be(Sign::Plus, &bytes)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_bn254::Fr;
    use ark_circom::circom::{CircomBuilder, CircomConfig};
    use ark_circom::CircomCircuit;
    use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystem};

    //To generate .r1cs and .wasm files, run the below command in the terminal.
    //bash ./folding-schemes/src/frontend/circom/test_folder/compile.sh

    // Test the satisfication by using the CircomBuilder of circom-compat
    #[test]
    fn test_circombuilder_satisfied() {
        let cfg = CircomConfig::<Fr>::new(
            "./src/frontend/circom/test_folder/cubic_circuit_js/cubic_circuit.wasm",
            "./src/frontend/circom/test_folder/cubic_circuit.r1cs",
        )
        .unwrap();
        let mut builder = CircomBuilder::new(cfg);
        builder.push_input("ivc_input", 3);

        let circom = builder.build().unwrap();
        let cs = ConstraintSystem::<Fr>::new_ref();
        circom.generate_constraints(cs.clone()).unwrap();
        assert!(cs.is_satisfied().unwrap());
    }

    // Test the satisfication by using the CircomWrapper
    #[test]
    fn test_extract_r1cs_and_witness() {
        let r1cs_path = PathBuf::from("./src/frontend/circom/test_folder/cubic_circuit.r1cs");
        let wasm_path =
            PathBuf::from("./src/frontend/circom/test_folder/cubic_circuit_js/cubic_circuit.wasm");

        let inputs = vec![("ivc_input".to_string(), vec![BigInt::from(3)])];
        let wrapper = CircomWrapper::<Fr>::new(r1cs_path, wasm_path);

        let (r1cs, witness) = wrapper.extract_r1cs_and_witness(&inputs).unwrap();

        let cs = ConstraintSystem::<Fr>::new_ref();

        let circom_circuit = CircomCircuit {
            r1cs,
            witness,
            public_inputs_indexes: vec![],
            allocate_inputs_as_witnesses: false,
        };

        circom_circuit.generate_constraints(cs.clone()).unwrap();
        assert!(cs.is_satisfied().unwrap());
    }
}
