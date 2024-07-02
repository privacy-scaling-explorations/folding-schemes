use crate::Error;
use ark_ff::PrimeField;
use ark_r1cs_std::fields::fp::FpVar;
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};
use ark_std::fmt::Debug;

pub mod circom;

/// FCircuit defines the trait of the circuit of the F function, which is the one being folded (ie.
/// inside the agmented F' function).
/// The parameter z_i denotes the current state, and z_{i+1} denotes the next state after applying
/// the step.
pub trait FCircuit<F: PrimeField>: Clone + Debug {
    type Params: Debug;

    /// returns a new FCircuit instance
    fn new(params: Self::Params) -> Result<Self, Error>;

    /// returns the number of elements in the state of the FCircuit, which corresponds to the
    /// FCircuit inputs.
    fn state_len(&self) -> usize;

    /// returns the number of elements in the external inputs used by the FCircuit. External inputs
    /// are optional, and in case no external inputs are used, this method should return 0.
    fn external_inputs_len(&self) -> usize;

    /// computes the next state values in place, assigning z_{i+1} into z_i, and computing the new
    /// z_{i+1}
    fn step_native(
        // this method uses self, so that each FCircuit implementation (and different frontends)
        // can hold a state if needed to store data to compute the next state.
        &self,
        i: usize,
        z_i: Vec<F>,
        external_inputs: Vec<F>, // inputs that are not part of the state
    ) -> Result<Vec<F>, Error>;

    /// generates the constraints for the step of F for the given z_i
    fn generate_step_constraints(
        // this method uses self, so that each FCircuit implementation (and different frontends)
        // can hold a state if needed to store data to generate the constraints.
        &self,
        cs: ConstraintSystemRef<F>,
        i: usize,
        z_i: Vec<FpVar<F>>,
        external_inputs: Vec<FpVar<F>>, // inputs that are not part of the state
    ) -> Result<Vec<FpVar<F>>, SynthesisError>;
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use ark_bn254::Fr;
    use ark_r1cs_std::{alloc::AllocVar, eq::EqGadget};
    use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystem};
    use core::marker::PhantomData;

    /// CubicFCircuit is a struct that implements the FCircuit trait, for the R1CS example circuit
    /// from https://www.vitalik.ca/general/2016/12/10/qap.html, which checks `x^3 + x + 5 = y`.
    /// `z_i` is used as `x`, and `z_{i+1}` is used as `y`, and at the next step, `z_{i+1}` will be
    /// assigned to `z_i`, and a new `z+{i+1}` will be computted.
    #[derive(Clone, Copy, Debug)]
    pub struct CubicFCircuit<F: PrimeField> {
        _f: PhantomData<F>,
    }
    impl<F: PrimeField> FCircuit<F> for CubicFCircuit<F> {
        type Params = ();
        fn new(_params: Self::Params) -> Result<Self, Error> {
            Ok(Self { _f: PhantomData })
        }
        fn state_len(&self) -> usize {
            1
        }
        fn external_inputs_len(&self) -> usize {
            0
        }
        fn step_native(
            &self,
            _i: usize,
            z_i: Vec<F>,
            _external_inputs: Vec<F>,
        ) -> Result<Vec<F>, Error> {
            Ok(vec![z_i[0] * z_i[0] * z_i[0] + z_i[0] + F::from(5_u32)])
        }
        fn generate_step_constraints(
            &self,
            cs: ConstraintSystemRef<F>,
            _i: usize,
            z_i: Vec<FpVar<F>>,
            _external_inputs: Vec<FpVar<F>>,
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

        fn new(params: Self::Params) -> Result<Self, Error> {
            Ok(Self {
                _f: PhantomData,
                n_constraints: params,
            })
        }
        fn state_len(&self) -> usize {
            1
        }
        fn external_inputs_len(&self) -> usize {
            0
        }
        fn step_native(
            &self,
            _i: usize,
            z_i: Vec<F>,
            _external_inputs: Vec<F>,
        ) -> Result<Vec<F>, Error> {
            let mut z_i1 = F::one();
            for _ in 0..self.n_constraints - 1 {
                z_i1 *= z_i[0];
            }
            Ok(vec![z_i1])
        }
        fn generate_step_constraints(
            &self,
            cs: ConstraintSystemRef<F>,
            _i: usize,
            z_i: Vec<FpVar<F>>,
            _external_inputs: Vec<FpVar<F>>,
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
            let computed_z_i1 =
                self.FC
                    .generate_step_constraints(cs.clone(), 0, z_i.clone(), vec![])?;

            computed_z_i1.enforce_equal(&z_i1)?;
            Ok(())
        }
    }

    #[test]
    fn test_testfcircuit() {
        let cs = ConstraintSystem::<Fr>::new_ref();
        let F_circuit = CubicFCircuit::<Fr>::new(()).unwrap();

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
        let custom_circuit = CustomFCircuit::<Fr>::new(n_constraints).unwrap();
        let z_i = vec![Fr::from(5_u32)];
        let wrapper_circuit = WrapperCircuit::<Fr, CustomFCircuit<Fr>> {
            FC: custom_circuit,
            z_i: Some(z_i.clone()),
            z_i1: Some(custom_circuit.step_native(0, z_i, vec![]).unwrap()),
        };
        wrapper_circuit.generate_constraints(cs.clone()).unwrap();
        assert_eq!(cs.num_constraints(), n_constraints);
    }
}
