use std::{error::Error, fs::File, io::BufReader, path::PathBuf};

use color_eyre::Result;
use num_bigint::BigInt;

use ark_circom::{circom::r1cs_reader, WitnessCalculator};
use ark_ec::pairing::Pairing;
use ark_ff::PrimeField;

use crate::ccs::r1cs::R1CS;
use crate::utils::vec::SparseMatrix;

// Define the sparse matrices on PrimeFiled
pub type Constraints<F> = (ConstraintVec<F>, ConstraintVec<F>, ConstraintVec<F>);
pub type ConstraintVec<F> = Vec<(usize, F)>;

// Convert the generic type of constraints from Pairing's ScalarField to PrimeField.
pub fn convert_constraints_bigint_to_scalar<E, F>(
    constraints: Constraints<E::ScalarField>,
) -> Constraints<F>
where
    E: Pairing,
    F: PrimeField,
{
    let convert_vec = |vec: ConstraintVec<E::ScalarField>| -> ConstraintVec<F> {
        vec.into_iter()
            .filter_map(|(index, element)| {
                // Convert element into BigInt, then to BigUint, then to the destination PrimeField
                let bigint_e: <<E as Pairing>::ScalarField as PrimeField>::BigInt =
                    element.into_bigint();
                let generic_biguint: num_bigint::BigUint = bigint_e.into();
                let f_element: F = F::from(generic_biguint);
                Some((index, f_element))
            })
            .collect()
    };

    (
        convert_vec(constraints.0),
        convert_vec(constraints.1),
        convert_vec(constraints.2),
    )
}

// Extract constraints on Pairing's ScalarField from an .r1cs file
// and convert them into constraints on PrimeField
pub fn extract_constraints_from_r1cs<E, F>(
    r1cs_filepath: &PathBuf,
) -> Result<(Vec<Constraints<F>>, usize), Box<dyn Error>>
where
    E: Pairing,
    F: PrimeField,
{
    // Open the .r1cs file and create a reader
    let file = File::open(r1cs_filepath)?;
    let reader = BufReader::new(file);

    // Read the R1CS file, extract the constraints, and then convert them into new constraints on PrimeField
    let r1cs_file = r1cs_reader::R1CSFile::<E>::new(reader)?;
    let pub_io_len = (r1cs_file.header.n_pub_in + r1cs_file.header.n_pub_out) as usize;
    let r1cs = r1cs_reader::R1CS::<E>::from(r1cs_file);
    let converted_constraints: Vec<Constraints<F>> = r1cs
        .constraints
        .into_iter()
        .map(|c| convert_constraints_bigint_to_scalar::<E, F>(c))
        .collect();

    Ok((converted_constraints, pub_io_len))
}

// Convert a set of constraints from ark-circom into R1CS format of folding_schemes
pub fn convert_to_folding_schemes_r1cs<F>(
    constraints: Vec<Constraints<F>>,
    pub_io_len: usize,
) -> R1CS<F>
where
    F: PrimeField,
{
    let mut a_matrix: Vec<Vec<(F, usize)>> = Vec::new();
    let mut b_matrix: Vec<Vec<(F, usize)>> = Vec::new();
    let mut c_matrix: Vec<Vec<(F, usize)>> = Vec::new();

    let n_rows = constraints.len();

    for (ai, bi, ci) in constraints {
        a_matrix.push(
            ai.into_iter()
                .map(|(index, scalar)| (scalar, index))
                .collect(),
        );
        b_matrix.push(
            bi.into_iter()
                .map(|(index, scalar)| (scalar, index))
                .collect(),
        );
        c_matrix.push(
            ci.into_iter()
                .map(|(index, scalar)| (scalar, index))
                .collect(),
        );
    }

    let l = pub_io_len;
    let n_cols = a_matrix.first().map(|vec| vec.len()).unwrap_or(0);

    let A = SparseMatrix {
        n_rows,
        n_cols,
        coeffs: a_matrix,
    };
    let B = SparseMatrix {
        n_rows,
        n_cols,
        coeffs: b_matrix,
    };
    let C = SparseMatrix {
        n_rows,
        n_cols,
        coeffs: c_matrix,
    };

    R1CS::<F> { l, A, B, C }
}

// Calculate the witness given the WASM filepath and inputs.
pub fn calculate_witness<I: IntoIterator<Item = (String, Vec<BigInt>)>>(
    wasm_filepath: &PathBuf,
    inputs: I,
) -> Result<Vec<BigInt>> {
    let mut calculator = WitnessCalculator::new(wasm_filepath.clone())?;
    calculator.calculate_witness(inputs, true)
}

// Convert a num_bigint's BigInt to PrimeField's BigInt
fn num_bigint_to_ark_bigint<F: PrimeField>(value: &BigInt) -> Result<F::BigInt, Box<dyn Error>> {
    let big_uint = value
        .to_biguint()
        .ok_or_else(|| "BigInt is negative".to_string())?;
    F::BigInt::try_from(big_uint).map_err(|_| "BigInt conversion failed".to_string().into())
}

// Convert R1CS constraints and witness from ark-circom format
// into folding-schemes R1CS and z format.
pub fn circom_to_folding_schemes_r1cs_and_z<F>(
    constraints: Vec<Constraints<F>>,
    witness: &Vec<BigInt>,
    pub_io_len: usize,
) -> Result<(R1CS<F>, Vec<F>), Box<dyn Error>>
where
    F: PrimeField,
{
    let folding_schemes_r1cs = convert_to_folding_schemes_r1cs(constraints, pub_io_len);

    let z: Result<Vec<F>, _> = witness
        .iter()
        .map(|big_int| {
            let ark_big_int = num_bigint_to_ark_bigint::<F>(big_int)?;
            F::from_bigint(ark_big_int).ok_or_else(|| {
                "Failed to convert bigint to field element"
                    .to_string()
                    .into()
            })
        })
        .collect();

    z.map(|z| (folding_schemes_r1cs, z))
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_bn254::{Bn254, Fr};
    use num_bigint::BigInt;
    use std::env;

    /*
    test_circuit represents 35 = x^3 + x + 5 in test_folder/test_circuit.circom.
    In the test_circom_conversion_success function, x is assigned the value 3, which satisfies the R1CS correctly.
    In the test_circom_conversion_failure function, x is assigned the value 6, which doesn't satisfy the R1CS.
    */

    fn test_circom_conversion_logic(expect_success: bool, inputs: Vec<(String, Vec<BigInt>)>) {
        let current_dir = env::current_dir().unwrap();
        let base_path = current_dir.join("src/frontend/circom/test_folder");
        let r1cs_filepath = base_path.join("test_circuit.r1cs");
        let wasm_filepath = base_path.join("test_circuit.wasm");

        assert!(r1cs_filepath.exists());
        assert!(wasm_filepath.exists());

        let (constraints, pub_io_len) = extract_constraints_from_r1cs::<Bn254, Fr>(&r1cs_filepath)
            .expect("Error extracting constraints");
        assert!(!constraints.is_empty());

        let converted_constraints: Vec<Constraints<Fr>> = constraints
            .iter()
            .map(|constraint| convert_constraints_bigint_to_scalar::<Bn254, Fr>(constraint.clone()))
            .collect();
        assert_eq!(constraints.len(), converted_constraints.len());

        let witness = calculate_witness(&wasm_filepath, inputs).expect("Error calculating witness");
        assert!(!witness.is_empty());

        let (r1cs, z) =
            circom_to_folding_schemes_r1cs_and_z(converted_constraints, &witness, pub_io_len)
                .expect("Error converting to folding schemes");
        assert!(!z.is_empty());

        let check_result = std::panic::catch_unwind(|| {
            r1cs.check_relation(&z).unwrap();
        });

        match (expect_success, check_result) {
            (true, Ok(_)) => {}
            (false, Err(_)) => {}
            (true, Err(_)) => panic!("Expected success but got a failure."),
            (false, Ok(_)) => panic!("Expected a failure but got success."),
        }
    }

    #[test]
    fn test_circom_conversion() {
        // expect it to pass for correct inputs
        test_circom_conversion_logic(true, vec![("step_in".to_string(), vec![BigInt::from(3)])]);

        // expect it to fail for incorrect inputs
        test_circom_conversion_logic(false, vec![("step_in".to_string(), vec![BigInt::from(4)])]);
    }
}
