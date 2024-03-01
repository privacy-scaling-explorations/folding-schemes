use std::{error::Error, fs::File, io::BufReader, marker::PhantomData, path::PathBuf};

use color_eyre::Result;
use num_bigint::{BigInt, Sign};

use ark_circom::{circom::{r1cs_reader, R1CS}, WitnessCalculator};
use ark_ff::{BigInteger, PrimeField};

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

    // Aggregated funtion to obtain R1CS and witness from Circom.
    pub fn extract_r1cs_and_witness(
        &self,
        inputs: &[(String, Vec<BigInt>)],
    ) -> Result<(R1CS<F>, Option<Vec<F>>), Box<dyn Error>> {
        // extracts the R1CS data from the file.
        let file = File::open(&self.r1cs_filepath)?;
        let reader = BufReader::new(file);
        let r1cs_file = r1cs_reader::R1CSFile::<F>::new(reader)?;
        let r1cs = r1cs_reader::R1CS::<F>::from(r1cs_file);
    
        // Calcultes the witness
        let witness = self.calculate_witness(inputs)?;
    
        let witness_vec: Result<Vec<F>, _> = witness.iter().map(|big_int| {
            let ark_big_int = self.num_bigint_to_ark_bigint(big_int)
                .map_err(|_| Box::new(std::fmt::Error) as Box<dyn Error>)?;
            F::from_bigint(ark_big_int).ok_or_else(|| {
                Box::new(std::fmt::Error) as Box<dyn Error> 
            })
        }).collect();
          
    
        Ok((r1cs, witness_vec.ok()))
    }

    // Calculates the witness given the Wasm filepath and inputs.
    pub fn calculate_witness(&self, inputs: &[(String, Vec<BigInt>)]) -> Result<Vec<BigInt>> {
        let mut calculator = WitnessCalculator::new(&self.wasm_filepath)?;
        calculator.calculate_witness(inputs.iter().cloned(), true)
    }

    // Converts a num_bigint::Bigint to PrimeField::BigInt.
    pub fn num_bigint_to_ark_bigint(
        &self,
        value: &BigInt,
    ) -> Result<F::BigInt, Box<dyn Error>> {
        let big_uint = value
            .to_biguint()
            .ok_or_else(|| "BigInt is negative".to_string())?;
        F::BigInt::try_from(big_uint).map_err(|_| "BigInt conversion failed".to_string().into())
    }

    // Converts a PrimeField::BigInt to num_bigint::BigInt.
    pub fn ark_bigint_to_num_bigint(&self, value: F) -> BigInt {
        let bigint_repr: F::BigInt = value.into_bigint();  
        let bytes = bigint_repr.to_bytes_be();
        BigInt::from_bytes_be(Sign::Plus, &bytes)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_bn254::Fr;
    use std::path::PathBuf;
    use ark_relations::r1cs::{ConstraintSystem, ConstraintSynthesizer};
    use ark_circom::CircomCircuit;
    use ark_circom::circom::{CircomBuilder, CircomConfig};

    // satisfied function that uses the circom builder
    #[test]
    fn satisfied() {
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

    // test CircomWrapper function
    #[test]
    fn test_extract_r1cs_and_witness() -> Result<(), Box<dyn Error>> {
        let r1cs_path = PathBuf::from("./src/frontend/circom/test_folder/cubic_circuit.r1cs");
        let wasm_path = PathBuf::from("./src/frontend/circom/test_folder/cubic_circuit_js/cubic_circuit.wasm");

        let inputs = vec![("ivc_input".to_string(), vec![BigInt::from(3)])];
        let wrapper = CircomWrapper::<Fr>::new(r1cs_path, wasm_path);

        let (r1cs, witness) = wrapper.extract_r1cs_and_witness(&inputs)?;
        println!("Test passed with r1cs: {:?}", r1cs);
        println!("Test passed with witness: {:?}", witness);

        let cs = ConstraintSystem::<Fr>::new_ref();

        let circom_circuit = CircomCircuit { r1cs, witness };

        circom_circuit.generate_constraints(cs.clone())?;
        assert!(cs.is_satisfied().unwrap());

        Ok(())
    }
}