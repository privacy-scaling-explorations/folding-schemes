use crate::ccs::{r1cs::R1CS, CCS};
use crate::frontend::arkworks::extract_r1cs_and_z;
use crate::frontend::circom::CircomWrapper;

use ark_ec::pairing::Pairing;
use ark_ec::CurveGroup;
use ark_ff::PrimeField;
use ark_relations::r1cs::ConstraintSystem;
use num_bigint::BigInt;
use std::{error::Error, vec::Vec};

// Define a Frontend trait
#[allow(clippy::type_complexity)]
pub trait Frontend<C: CurveGroup, F: PrimeField> {
    fn extract_r1cs_and_z(
        &self,
        inputs: &[(String, Vec<BigInt>)],
    ) -> Result<(R1CS<C::ScalarField>, Vec<C::ScalarField>), Box<dyn Error>>;

    fn extract_ccs_and_z(
        &self,
        inputs: &[(String, Vec<BigInt>)],
    ) -> Result<(CCS<C>, Vec<C::ScalarField>), Box<dyn Error>>;
}

// Implement Frontend trait for Arkworks
impl<C: CurveGroup<ScalarField = F>, F: PrimeField> Frontend<C, F> for ConstraintSystem<F>
where
    C::ScalarField: PrimeField,
{
    fn extract_r1cs_and_z(
        &self,
        _inputs: &[(String, Vec<BigInt>)],
    ) -> Result<(R1CS<C::ScalarField>, Vec<C::ScalarField>), Box<dyn Error>> {
        Ok(extract_r1cs_and_z(self))
    }

    fn extract_ccs_and_z(
        &self,
        _inputs: &[(String, Vec<BigInt>)],
    ) -> Result<(CCS<C>, Vec<C::ScalarField>), Box<dyn Error>> {
        let (r1cs, z) = extract_r1cs_and_z(self);
        let ccs = CCS::from_r1cs(r1cs);
        Ok((ccs, z))
    }
}

// Implement Frontend trait for Circom
impl<E: Pairing, F: PrimeField> Frontend<E::G1, F> for CircomWrapper<E> {
    fn extract_r1cs_and_z(
        &self,
        inputs: &[(String, Vec<BigInt>)],
    ) -> Result<(R1CS<E::ScalarField>, Vec<E::ScalarField>), Box<dyn Error>> {
        self.extract_r1cs_and_z(inputs)
    }

    fn extract_ccs_and_z(
        &self,
        inputs: &[(String, Vec<BigInt>)],
    ) -> Result<(CCS<E::G1>, Vec<E::ScalarField>), Box<dyn Error>> {
        let (r1cs, z) = self.extract_r1cs_and_z(inputs)?;
        let ccs = CCS::from_r1cs(r1cs);
        Ok((ccs, z))
    }
}

#[cfg(test)]
mod frontend_tests {
    use super::*;
    use crate::frontend::arkworks::tests::TestCircuit;
    use ark_bn254::Bn254;
    use ark_pallas::{Fr, Projective};
    use ark_relations::r1cs::ConstraintSynthesizer;
    use std::env;

    // arkworks
    #[test]
    fn test_frontend_trait_for_arkworks() {
        let cs_ref = ConstraintSystem::<Fr>::new_ref();
        let x = Fr::from(3_u32);
        let y = x * x * x + x + Fr::from(5_u32);
        let test_circuit = TestCircuit::<Fr> { x, y };
        test_circuit.generate_constraints(cs_ref.clone()).unwrap();
        cs_ref.finalize();
        assert!(cs_ref.is_satisfied().unwrap());

        let cs = cs_ref.into_inner().unwrap();

        let frontend: &dyn Frontend<Projective, Fr> = &cs;

        // R1CS
        let (r1cs, z_r1cs) = frontend
            .extract_r1cs_and_z([].as_slice())
            .expect("Frontend: Failed to extract R1CS and Z");
        r1cs.check_relation(&z_r1cs)
            .expect("Relation Check: Failure in R1CS");

        // CCS
        let (ccs, z_ccs) = frontend
            .extract_ccs_and_z([].as_slice())
            .expect("Frontend: Failed to extract CCS and Z");
        ccs.check_relation(&z_ccs[..])
            .expect("Relation Check: Failure in CCS");
    }

    // Circom
    fn load_circom_wrapper_as_frontend<F: PrimeField>(
    ) -> Box<dyn Frontend<<Bn254 as Pairing>::G1, F>> {
        let current_dir = env::current_dir().unwrap();
        let base_path = current_dir.join("src/frontend/circom/test_folder");
        let r1cs_filepath = base_path.join("test_circuit.r1cs");
        let wasm_filepath = base_path.join("test_circuit_js/test_circuit.wasm");

        assert!(r1cs_filepath.exists());
        assert!(wasm_filepath.exists());

        Box::new(CircomWrapper::<Bn254>::new(r1cs_filepath, wasm_filepath))
    }

    fn test_frontend_trait_logic<C: CurveGroup, F: PrimeField>(
        frontend: &dyn Frontend<C, F>,
        expect_success: bool,
        inputs: Vec<(String, Vec<BigInt>)>,
    ) {
        // R1CS
        let (r1cs, z_r1cs) = frontend
            .extract_r1cs_and_z(&inputs)
            .expect("Frontend: Failed to extract R1CS and Z");
        let r1cs_check_result = r1cs.check_relation(&z_r1cs);

        // CCS
        let (ccs, z_ccs) = frontend
            .extract_ccs_and_z(&inputs)
            .expect("Frontend: Failed to extract CCS and Z");
        let ccs_check_result = ccs.check_relation(&z_ccs);

        if expect_success {
            if r1cs_check_result.is_err() {
                panic!("Relation Check: Failure in R1CS");
            }
            if ccs_check_result.is_err() {
                panic!("Relation Check: Failure in CCS");
            }
        } else if r1cs_check_result.is_ok() && ccs_check_result.is_ok() {
            panic!("Relation Check: Unexpected success in both R1CS and CCS");
        }
    }

    #[test]
    fn test_frontend_trait_for_circom() {
        let frontend: Box<dyn Frontend<<Bn254 as Pairing>::G1, Fr>> =
            load_circom_wrapper_as_frontend();

        // expect it to pass for correct inputs.
        test_frontend_trait_logic(
            &*frontend,
            true,
            vec![("step_in".to_string(), vec![BigInt::from(3)])],
        );
        // expect it to pass for incorrect inputs.
        test_frontend_trait_logic(
            &*frontend,
            false,
            vec![("step_in".to_string(), vec![BigInt::from(7)])],
        );
    }
}
