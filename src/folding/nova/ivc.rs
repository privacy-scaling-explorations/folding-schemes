use ark_crypto_primitives::sponge::{poseidon::PoseidonConfig, Absorb};
use ark_ec::{AffineRepr, CurveGroup, Group};
use ark_ff::{BigInteger, PrimeField};
use ark_r1cs_std::{groups::GroupOpsBounds, prelude::CurveVar};
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystem};
use ark_std::rand::Rng;
use ark_std::{One, Zero};
use core::marker::PhantomData;

use super::{
    circuits::{AugmentedFCircuit, ChallengeGadget, FCircuit, CF2},
    cyclefold::{CycleFoldChallengeGadget, CycleFoldCircuit},
};
use super::{nifs::NIFS, traits::NovaR1CS, CommittedInstance, Witness};
use crate::ccs::r1cs::R1CS;
use crate::frontend::arkworks::{extract_r1cs, extract_w_x}; // TODO once Frontend trait is ready, use that
use crate::pedersen::{Params as PedersenParams, Pedersen};
use crate::Error;

#[cfg(test)]
use super::cyclefold::CF_IO_LEN;

/// Implements the Incremental Verifiable Computation described in sections 1.2 and 5 of
/// [Nova](https://eprint.iacr.org/2021/370.pdf)
pub struct IVC<C1, GC1, C2, GC2, FC>
where
    C1: CurveGroup,
    GC1: CurveVar<C1, CF2<C1>>,
    C2: CurveGroup,
    GC2: CurveVar<C2, CF2<C2>>,
    FC: FCircuit<C1::ScalarField>,
{
    _gc1: PhantomData<GC1>,
    _c2: PhantomData<C2>,
    _gc2: PhantomData<GC2>,
    /// R1CS of the Augmented Function circuit
    pub r1cs: R1CS<C1::ScalarField>,
    /// R1CS of the CycleFold circuit
    pub cf_r1cs: R1CS<C2::ScalarField>,
    pub poseidon_config: PoseidonConfig<C1::ScalarField>,
    /// PedersenParams over C1
    pub pedersen_params: PedersenParams<C1>,
    /// CycleFold PedersenParams, over C2
    pub cf_pedersen_params: PedersenParams<C2>,
    /// F circuit, the circuit that is being folded
    pub F: FC,
    pub i: C1::ScalarField,
    /// initial state
    pub z_0: Vec<C1::ScalarField>,
    /// current i-th state
    pub z_i: Vec<C1::ScalarField>,
    /// Nova instances
    pub w_i: Witness<C1>,
    pub u_i: CommittedInstance<C1>,
    pub W_i: Witness<C1>,
    pub U_i: CommittedInstance<C1>,

    /// CycleFold running instance
    pub cf_W_i: Witness<C2>,
    pub cf_U_i: CommittedInstance<C2>,
}

impl<C1, GC1, C2, GC2, FC> IVC<C1, GC1, C2, GC2, FC>
where
    C1: CurveGroup,
    GC1: CurveVar<C1, CF2<C1>>,
    C2: CurveGroup,
    GC2: CurveVar<C2, CF2<C2>>,
    FC: FCircuit<C1::ScalarField>,
    <C1 as CurveGroup>::BaseField: PrimeField,
    <C2 as CurveGroup>::BaseField: PrimeField,
    <C1 as Group>::ScalarField: Absorb,
    <C2 as Group>::ScalarField: Absorb,
    C1: CurveGroup<BaseField = C2::ScalarField, ScalarField = C2::BaseField>,
    for<'a> &'a GC1: GroupOpsBounds<'a, C1, GC1>,
    for<'a> &'a GC2: GroupOpsBounds<'a, C2, GC2>,
{
    /// Initializes the IVC for the given parameters and initial state `z_0`.
    pub fn new<R: Rng>(
        rng: &mut R,
        poseidon_config: PoseidonConfig<C1::ScalarField>,
        F: FC,
        z_0: Vec<C1::ScalarField>,
    ) -> Result<Self, Error> {
        // prepare the circuit to obtain its R1CS
        let cs = ConstraintSystem::<C1::ScalarField>::new_ref();
        let cs2 = ConstraintSystem::<C1::BaseField>::new_ref();

        let augmented_F_circuit = AugmentedFCircuit::<C1, C2, GC2, FC>::empty(&poseidon_config, F);
        let cf_circuit = CycleFoldCircuit::<C1, GC1>::empty();

        augmented_F_circuit.generate_constraints(cs.clone())?;
        cs.finalize();
        let cs = cs.into_inner().ok_or(Error::NoInnerConstraintSystem)?;
        let r1cs = extract_r1cs::<C1::ScalarField>(&cs);

        cf_circuit.generate_constraints(cs2.clone())?;
        cs2.finalize();
        let cs2 = cs2.into_inner().ok_or(Error::NoInnerConstraintSystem)?;
        let cf_r1cs = extract_r1cs::<C1::BaseField>(&cs2);

        // this will not be randomly generated in this method, and will come from above levels, so
        // the same params can be loaded on multiple instances
        let pedersen_params = Pedersen::<C1>::new_params(rng, r1cs.A.n_rows);
        let cf_pedersen_params = Pedersen::<C2>::new_params(rng, cf_r1cs.A.n_rows);

        // setup the dummy instances
        let (w_dummy, u_dummy) = r1cs.dummy_instance();
        let (cf_w_dummy, cf_u_dummy) = cf_r1cs.dummy_instance();

        // W_dummy=W_0 is a 'dummy witness', all zeroes, but with the size corresponding to the
        // R1CS that we're working with.
        Ok(Self {
            _gc1: PhantomData,
            _c2: PhantomData,
            _gc2: PhantomData,
            r1cs,
            cf_r1cs,
            poseidon_config,
            pedersen_params,
            cf_pedersen_params,
            F,
            i: C1::ScalarField::zero(),
            z_0: z_0.clone(),
            z_i: z_0,
            w_i: w_dummy.clone(),
            u_i: u_dummy.clone(),
            W_i: w_dummy,
            U_i: u_dummy,
            // cyclefold running instance
            cf_W_i: cf_w_dummy.clone(),
            cf_U_i: cf_u_dummy.clone(),
        })
    }

    /// Implements IVC.P
    pub fn prove_step(&mut self) -> Result<(), Error> {
        let augmented_F_circuit: AugmentedFCircuit<C1, C2, GC2, FC>;
        let cf_circuit: CycleFoldCircuit<C1, GC1>;

        let z_i1 = self.F.step_native(self.z_i.clone());

        // compute T and cmT for AugmentedFCircuit
        let (T, cmT) = self.compute_cmT()?;

        let r_bits = ChallengeGadget::<C1>::get_challenge_native(
            &self.poseidon_config,
            self.u_i.clone(),
            self.U_i.clone(),
            cmT,
        )?;
        let r_Fr = C1::ScalarField::from_bigint(BigInteger::from_bits_le(&r_bits))
            .ok_or(Error::OutOfBounds)?;

        // fold Nova instances
        let (W_i1, U_i1): (Witness<C1>, CommittedInstance<C1>) =
            NIFS::<C1>::fold_instances(r_Fr, &self.w_i, &self.u_i, &self.W_i, &self.U_i, &T, cmT)?;

        // folded instance output (public input, x)
        // u_{i+1}.x = H(i+1, z_0, z_{i+1}, U_{i+1})
        let u_i1_x = U_i1.hash(
            &self.poseidon_config,
            self.i + C1::ScalarField::one(),
            self.z_0.clone(),
            z_i1.clone(),
        )?;

        if self.i == C1::ScalarField::zero() {
            // base case
            augmented_F_circuit = AugmentedFCircuit::<C1, C2, GC2, FC> {
                _gc2: PhantomData,
                poseidon_config: self.poseidon_config.clone(),
                i: Some(C1::ScalarField::zero()), // = i=0
                z_0: Some(self.z_0.clone()),      // = z_i
                z_i: Some(self.z_i.clone()),
                u_i: Some(self.u_i.clone()), // = dummy
                U_i: Some(self.U_i.clone()), // = dummy
                U_i1: Some(U_i1.clone()),
                cmT: Some(cmT),
                F: self.F,
                x: Some(u_i1_x),
                cf_u_i: None,
                cf_U_i: None,
                cf_U_i1: None,
                cf_cmT: None,
                cf_r_nonnat: None,
            };

            #[cfg(test)]
            NIFS::verify_folded_instance(r_Fr, &self.u_i, &self.U_i, &U_i1, &cmT)?;
        } else {
            // CycleFold part:
            // get the vector used as public inputs 'x' in the CycleFold circuit
            let cf_u_i_x = [
                get_committed_instance_coordinates(&self.u_i),
                get_committed_instance_coordinates(&self.U_i),
                get_committed_instance_coordinates(&U_i1),
            ]
            .concat();

            cf_circuit = CycleFoldCircuit::<C1, GC1> {
                _gc: PhantomData,
                r_bits: Some(r_bits.clone()),
                cmT: Some(cmT),
                u_i: Some(self.u_i.clone()),
                U_i: Some(self.U_i.clone()),
                U_i1: Some(U_i1.clone()),
                x: Some(cf_u_i_x.clone()),
            };

            let cs2 = ConstraintSystem::<C1::BaseField>::new_ref();
            cf_circuit.generate_constraints(cs2.clone())?;

            let cs2 = cs2.into_inner().ok_or(Error::NoInnerConstraintSystem)?;
            let (cf_w_i, cf_x_i) = extract_w_x::<C1::BaseField>(&cs2);
            if cf_x_i != cf_u_i_x {
                return Err(Error::NotEqual);
            }

            #[cfg(test)]
            if cf_x_i.len() != CF_IO_LEN {
                return Err(Error::NotExpectedLength(cf_x_i.len(), CF_IO_LEN));
            }

            // fold cyclefold instances
            let cf_w_i = Witness::<C2>::new(cf_w_i.clone(), self.cf_r1cs.A.n_rows);
            let cf_u_i: CommittedInstance<C2> =
                cf_w_i.commit(&self.cf_pedersen_params, cf_x_i.clone())?;

            // compute T* and cmT* for CycleFoldCircuit
            let (cf_T, cf_cmT) = self.compute_cf_cmT(&cf_w_i, &cf_u_i)?;

            let cf_r_bits = CycleFoldChallengeGadget::<C2, GC2>::get_challenge_native(
                &self.poseidon_config,
                cf_u_i.clone(),
                self.cf_U_i.clone(),
                cf_cmT,
            )?;
            let cf_r_Fq = C1::BaseField::from_bigint(BigInteger::from_bits_le(&cf_r_bits))
                .ok_or(Error::OutOfBounds)?;

            let (cf_W_i1, cf_U_i1) = NIFS::<C2>::fold_instances(
                cf_r_Fq,
                &self.cf_W_i,
                &self.cf_U_i,
                &cf_w_i,
                &cf_u_i,
                &cf_T,
                cf_cmT,
            )?;

            augmented_F_circuit = AugmentedFCircuit::<C1, C2, GC2, FC> {
                _gc2: PhantomData,
                poseidon_config: self.poseidon_config.clone(),
                i: Some(self.i),
                z_0: Some(self.z_0.clone()),
                z_i: Some(self.z_i.clone()),
                u_i: Some(self.u_i.clone()),
                U_i: Some(self.U_i.clone()),
                U_i1: Some(U_i1.clone()),
                cmT: Some(cmT),
                F: self.F,
                x: Some(u_i1_x),
                // cyclefold values
                cf_u_i: Some(cf_u_i.clone()),
                cf_U_i: Some(self.cf_U_i.clone()),
                cf_U_i1: Some(cf_U_i1.clone()),
                cf_cmT: Some(cf_cmT),
                cf_r_nonnat: Some(cf_r_Fq),
            };

            self.cf_W_i = cf_W_i1.clone();
            self.cf_U_i = cf_U_i1.clone();

            #[cfg(test)]
            {
                self.cf_r1cs.check_instance_relation(&cf_w_i, &cf_u_i)?;
                self.cf_r1cs
                    .check_relaxed_instance_relation(&self.cf_W_i, &self.cf_U_i)?;
            }
        }

        let cs = ConstraintSystem::<C1::ScalarField>::new_ref();

        augmented_F_circuit.generate_constraints(cs.clone())?;

        let cs = cs.into_inner().ok_or(Error::NoInnerConstraintSystem)?;
        let (w_i1, x_i1) = extract_w_x::<C1::ScalarField>(&cs);
        if x_i1[0] != u_i1_x {
            return Err(Error::NotEqual);
        }

        #[cfg(test)]
        if x_i1.len() != 1 {
            return Err(Error::NotExpectedLength(x_i1.len(), 1));
        }

        // set values for next iteration
        self.i += C1::ScalarField::one();
        self.z_i = z_i1.clone();
        self.w_i = Witness::<C1>::new(w_i1, self.r1cs.A.n_rows);
        self.u_i = self.w_i.commit(&self.pedersen_params, vec![u_i1_x])?;
        self.W_i = W_i1.clone();
        self.U_i = U_i1.clone();

        #[cfg(test)]
        {
            self.r1cs.check_instance_relation(&self.w_i, &self.u_i)?;
            self.r1cs
                .check_relaxed_instance_relation(&self.W_i, &self.U_i)?;
        }

        Ok(())
    }

    /// Implements IVC.V
    pub fn verify(&mut self, z_0: Vec<C1::ScalarField>, num_steps: u32) -> Result<(), Error> {
        if self.i != C1::ScalarField::from(num_steps) {
            return Err(Error::IVCVerificationFail);
        }

        if self.u_i.x.len() != 1 || self.U_i.x.len() != 1 {
            return Err(Error::IVCVerificationFail);
        }

        // check that u_i's output points to the running instance
        // u_i.X == H(i, z_0, z_i, U_i)
        let expected_u_i_x = self
            .U_i
            .hash(&self.poseidon_config, self.i, z_0, self.z_i.clone())?;
        if expected_u_i_x != self.u_i.x[0] {
            return Err(Error::IVCVerificationFail);
        }

        // check u_i.cmE==0, u_i.u==1 (=u_i is a un-relaxed instance)
        if !self.u_i.cmE.is_zero() || !self.u_i.u.is_one() {
            return Err(Error::IVCVerificationFail);
        }

        // check R1CS satisfiability
        self.r1cs.check_instance_relation(&self.w_i, &self.u_i)?;
        // check RelaxedR1CS satisfiability
        self.r1cs
            .check_relaxed_instance_relation(&self.W_i, &self.U_i)?;

        // check CycleFold RelaxedR1CS satisfiability
        self.cf_r1cs
            .check_relaxed_instance_relation(&self.cf_W_i, &self.cf_U_i)?;

        Ok(())
    }

    // computes T and cmT for the AugmentedFCircuit
    fn compute_cmT(&self) -> Result<(Vec<C1::ScalarField>, C1), Error> {
        NIFS::<C1>::compute_cmT(
            &self.pedersen_params,
            &self.r1cs,
            &self.w_i,
            &self.u_i,
            &self.W_i,
            &self.U_i,
        )
    }
    // computes T* and cmT* for the CycleFoldCircuit
    fn compute_cf_cmT(
        &self,
        cf_w_i: &Witness<C2>,
        cf_u_i: &CommittedInstance<C2>,
    ) -> Result<(Vec<C2::ScalarField>, C2), Error> {
        NIFS::<C2>::compute_cyclefold_cmT(
            &self.cf_pedersen_params,
            &self.cf_r1cs,
            cf_w_i,
            cf_u_i,
            &self.cf_W_i,
            &self.cf_U_i,
        )
    }
}

pub(crate) fn get_committed_instance_coordinates<C: CurveGroup>(
    u: &CommittedInstance<C>,
) -> Vec<C::BaseField> {
    let zero = (&C::BaseField::zero(), &C::BaseField::one());

    let cmE = u.cmE.into_affine();
    let (cmE_x, cmE_y) = cmE.xy().unwrap_or(zero);

    let cmW = u.cmW.into_affine();
    let (cmW_x, cmW_y) = cmW.xy().unwrap_or(zero);
    vec![*cmE_x, *cmE_y, *cmW_x, *cmW_y]
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_pallas::{constraints::GVar, Fr, Projective};
    use ark_vesta::{constraints::GVar as GVar2, Projective as Projective2};

    use crate::folding::nova::circuits::tests::TestFCircuit;
    use crate::transcript::poseidon::tests::poseidon_test_config;

    #[test]
    fn test_ivc() {
        let mut rng = ark_std::test_rng();
        let poseidon_config = poseidon_test_config::<Fr>();

        let F_circuit = TestFCircuit::<Fr>::new();
        let z_0 = vec![Fr::from(3_u32)];

        let mut ivc = IVC::<Projective, GVar, Projective2, GVar2, TestFCircuit<Fr>>::new(
            &mut rng,
            poseidon_config,
            F_circuit,
            z_0.clone(),
        )
        .unwrap();

        let num_steps: usize = 3;
        for _ in 0..num_steps {
            ivc.prove_step().unwrap();
        }

        ivc.verify(z_0, num_steps as u32).unwrap();
    }
}
