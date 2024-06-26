/// Implements the scheme described in [HyperNova](https://eprint.iacr.org/2023/573.pdf)
use ark_crypto_primitives::sponge::{poseidon::PoseidonConfig, Absorb};
use ark_ec::{CurveGroup, Group};
use ark_ff::{BigInteger, PrimeField};
use ark_r1cs_std::{groups::GroupOpsBounds, prelude::CurveVar, ToConstraintFieldGadget};
use ark_std::rand::RngCore;
use ark_std::{One, Zero};
use core::marker::PhantomData;
use std::fmt::Debug;

pub mod cccs;
pub mod circuits;
use circuits::AugmentedFCircuit;
pub mod lcccs;
pub mod nimfs;
pub mod utils;
use cccs::CCCS;
use lcccs::LCCCS;
use nimfs::NIMFS;

use crate::commitment::CommitmentScheme;
use crate::folding::circuits::{
    cyclefold::{fold_cyclefold_circuit, CycleFoldCircuit},
    CF2,
};
use crate::folding::nova::{
    get_r1cs_from_cs, traits::NovaR1CS, CommittedInstance, PreprocessorParam,
    Witness as NovaWitness,
};
use crate::frontend::FCircuit;
use crate::utils::{get_cm_coordinates, pp_hash};
use crate::Error;
use crate::FoldingScheme;
use crate::{
    arith::{
        ccs::CCS,
        r1cs::{extract_w_x, R1CS},
    },
    transcript::{poseidon::PoseidonTranscript, Transcript},
};

/// Witness for the LCCCS & CCCS, containing the w vector, and the r_w used as randomness in the Pedersen commitment.
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Witness<F: PrimeField> {
    pub w: Vec<F>,
    pub r_w: F,
}

impl<F: PrimeField> Witness<F> {
    pub fn new(w: Vec<F>) -> Self {
        // note: at the current version, we don't use the blinding factors and we set them to 0
        // always.
        Self { w, r_w: F::zero() }
    }
    pub fn dummy(ccs: &CCS<F>) -> Self {
        Witness::<F>::new(vec![F::zero(); ccs.n - ccs.l - 1])
    }
}

#[derive(Debug, Clone)]
pub struct ProverParams<C1, C2, CS1, CS2>
where
    C1: CurveGroup,
    C2: CurveGroup,
    CS1: CommitmentScheme<C1>,
    CS2: CommitmentScheme<C2>,
{
    pub poseidon_config: PoseidonConfig<C1::ScalarField>,
    pub cs_params: CS1::ProverParams,
    pub cf_cs_params: CS2::ProverParams,
    // if ccs is set, it will be used, if not, it will be computed at runtime
    pub ccs: Option<CCS<C1::ScalarField>>,
}

#[derive(Debug, Clone)]
pub struct VerifierParams<
    C1: CurveGroup,
    C2: CurveGroup,
    CS1: CommitmentScheme<C1>,
    CS2: CommitmentScheme<C2>,
> {
    pub poseidon_config: PoseidonConfig<C1::ScalarField>,
    pub ccs: CCS<C1::ScalarField>,
    pub cf_r1cs: R1CS<C2::ScalarField>,
    pub cs_vp: CS1::VerifierParams,
    pub cf_cs_vp: CS2::VerifierParams,
}

impl<C1, C2, CS1, CS2> VerifierParams<C1, C2, CS1, CS2>
where
    C1: CurveGroup,
    C2: CurveGroup,
    CS1: CommitmentScheme<C1>,
    CS2: CommitmentScheme<C2>,
{
    /// returns the hash of the public parameters of HyperNova
    pub fn pp_hash(&self) -> Result<C1::ScalarField, Error> {
        pp_hash::<C1, C2, CS1, CS2>(
            &self.ccs,
            &self.cf_r1cs,
            &self.cs_vp,
            &self.cf_cs_vp,
            &self.poseidon_config,
        )
    }
}

/// Implements HyperNova+CycleFold's IVC, described in
/// [HyperNova](https://eprint.iacr.org/2023/573.pdf) and
/// [CycleFold](https://eprint.iacr.org/2023/1192.pdf), following the FoldingScheme trait
#[derive(Clone, Debug)]
pub struct HyperNova<C1, GC1, C2, GC2, FC, CS1, CS2>
where
    C1: CurveGroup,
    GC1: CurveVar<C1, CF2<C1>> + ToConstraintFieldGadget<CF2<C1>>,
    C2: CurveGroup,
    GC2: CurveVar<C2, CF2<C2>>,
    FC: FCircuit<C1::ScalarField>,
    CS1: CommitmentScheme<C1>,
    CS2: CommitmentScheme<C2>,
{
    _gc1: PhantomData<GC1>,
    _c2: PhantomData<C2>,
    _gc2: PhantomData<GC2>,

    /// CCS of the Augmented Function circuit
    pub ccs: CCS<C1::ScalarField>,
    /// R1CS of the CycleFold circuit
    pub cf_r1cs: R1CS<C2::ScalarField>,
    pub poseidon_config: PoseidonConfig<C1::ScalarField>,
    /// CommitmentScheme::ProverParams over C1
    pub cs_params: CS1::ProverParams,
    /// CycleFold CommitmentScheme::ProverParams, over C2
    pub cf_cs_params: CS2::ProverParams,
    /// F circuit, the circuit that is being folded
    pub F: FC,
    /// public params hash
    pub pp_hash: C1::ScalarField,
    pub i: C1::ScalarField,
    /// initial state
    pub z_0: Vec<C1::ScalarField>,
    /// current i-th state
    pub z_i: Vec<C1::ScalarField>,
    /// HyperNova instances
    pub W_i: Witness<C1::ScalarField>,
    pub U_i: LCCCS<C1>,
    pub w_i: Witness<C1::ScalarField>,
    pub u_i: CCCS<C1>,

    /// CycleFold running instance
    pub cf_W_i: NovaWitness<C2>,
    pub cf_U_i: CommittedInstance<C2>,
}

impl<C1, GC1, C2, GC2, FC, CS1, CS2> FoldingScheme<C1, C2, FC>
    for HyperNova<C1, GC1, C2, GC2, FC, CS1, CS2>
where
    C1: CurveGroup,
    GC1: CurveVar<C1, CF2<C1>> + ToConstraintFieldGadget<CF2<C1>>,
    C2: CurveGroup,
    GC2: CurveVar<C2, CF2<C2>> + ToConstraintFieldGadget<CF2<C2>>,
    FC: FCircuit<C1::ScalarField>,
    CS1: CommitmentScheme<C1>,
    CS2: CommitmentScheme<C2>,
    <C1 as CurveGroup>::BaseField: PrimeField,
    <C2 as CurveGroup>::BaseField: PrimeField,
    <C1 as Group>::ScalarField: Absorb,
    <C2 as Group>::ScalarField: Absorb,
    C1: CurveGroup<BaseField = C2::ScalarField, ScalarField = C2::BaseField>,
    for<'a> &'a GC1: GroupOpsBounds<'a, C1, GC1>,
    for<'a> &'a GC2: GroupOpsBounds<'a, C2, GC2>,
{
    type PreprocessorParam = PreprocessorParam<C1, C2, FC, CS1, CS2>;
    type ProverParam = ProverParams<C1, C2, CS1, CS2>;
    type VerifierParam = VerifierParams<C1, C2, CS1, CS2>;
    type RunningCommittedInstanceWithWitness = (LCCCS<C1>, Witness<C1::ScalarField>);
    type IncomingCommittedInstanceWithWitness = (CCCS<C1>, Witness<C1::ScalarField>);
    type CFCommittedInstanceWithWitness = (CommittedInstance<C2>, NovaWitness<C2>);

    fn preprocess(
        mut rng: impl RngCore,
        prep_param: &Self::PreprocessorParam,
    ) -> Result<(Self::ProverParam, Self::VerifierParam), Error> {
        let augmented_f_circuit = AugmentedFCircuit::<C1, C2, GC2, FC>::empty(
            &prep_param.poseidon_config,
            prep_param.F.clone(),
            None,
        )?;
        let ccs = augmented_f_circuit.ccs.clone();

        let cf_circuit = CycleFoldCircuit::<C1, GC1>::empty();
        let cf_r1cs = get_r1cs_from_cs::<C2::ScalarField>(cf_circuit)?;

        // if cs params exist, use them, if not, generate new ones
        let cs_pp: CS1::ProverParams;
        let cs_vp: CS1::VerifierParams;
        let cf_cs_pp: CS2::ProverParams;
        let cf_cs_vp: CS2::VerifierParams;
        if prep_param.cs_pp.is_some()
            && prep_param.cf_cs_pp.is_some()
            && prep_param.cs_vp.is_some()
            && prep_param.cf_cs_vp.is_some()
        {
            cs_pp = prep_param.clone().cs_pp.unwrap();
            cs_vp = prep_param.clone().cs_vp.unwrap();
            cf_cs_pp = prep_param.clone().cf_cs_pp.unwrap();
            cf_cs_vp = prep_param.clone().cf_cs_vp.unwrap();
        } else {
            (cs_pp, cs_vp) = CS1::setup(&mut rng, ccs.n - ccs.l - 1)?;
            (cf_cs_pp, cf_cs_vp) = CS2::setup(&mut rng, cf_r1cs.A.n_cols - cf_r1cs.l - 1)?;
        }

        let pp = ProverParams::<C1, C2, CS1, CS2> {
            poseidon_config: prep_param.poseidon_config.clone(),
            cs_params: cs_pp.clone(),
            cf_cs_params: cf_cs_pp.clone(),
            ccs: Some(ccs.clone()),
        };
        let vp = VerifierParams::<C1, C2, CS1, CS2> {
            poseidon_config: prep_param.poseidon_config.clone(),
            ccs,
            cf_r1cs,
            cs_vp: cs_vp.clone(),
            cf_cs_vp: cf_cs_vp.clone(),
        };
        Ok((pp, vp))
    }

    /// Initializes the HyperNova+CycleFold's IVC for the given parameters and initial state `z_0`.
    fn init(
        params: (Self::ProverParam, Self::VerifierParam),
        F: FC,
        z_0: Vec<C1::ScalarField>,
    ) -> Result<Self, Error> {
        let (pp, vp) = params;

        // prepare the HyperNova's AugmentedFCircuit and CycleFOld's circuits and obtain its CCS
        // and R1CS respectively
        let augmented_f_circuit = AugmentedFCircuit::<C1, C2, GC2, FC>::empty(
            &pp.poseidon_config,
            F.clone(),
            pp.ccs.clone(),
        )?;
        let ccs = augmented_f_circuit.ccs.clone();

        let cf_circuit = CycleFoldCircuit::<C1, GC1>::empty();
        let cf_r1cs = get_r1cs_from_cs::<C2::ScalarField>(cf_circuit)?;

        // compute the public params hash
        let pp_hash = vp.pp_hash()?;

        // setup the dummy instances
        let W_dummy = Witness::<C1::ScalarField>::dummy(&ccs);
        let U_dummy = LCCCS::<C1>::dummy(ccs.l, ccs.t, ccs.s);
        let w_dummy = W_dummy.clone();
        let mut u_dummy = CCCS::<C1>::dummy(ccs.l);
        let (cf_W_dummy, cf_U_dummy): (NovaWitness<C2>, CommittedInstance<C2>) =
            cf_r1cs.dummy_instance();
        u_dummy.x = vec![
            U_dummy.hash(
                &pp.poseidon_config,
                pp_hash,
                C1::ScalarField::zero(),
                z_0.clone(),
                z_0.clone(),
            )?,
            cf_U_dummy.hash_cyclefold(&pp.poseidon_config, pp_hash)?,
        ];

        // W_dummy=W_0 is a 'dummy witness', all zeroes, but with the size corresponding to the
        // R1CS that we're working with.
        Ok(Self {
            _gc1: PhantomData,
            _c2: PhantomData,
            _gc2: PhantomData,
            ccs,
            cf_r1cs,
            poseidon_config: pp.poseidon_config.clone(),
            cs_params: pp.cs_params.clone(),
            cf_cs_params: pp.cf_cs_params.clone(),
            F,
            pp_hash,
            i: C1::ScalarField::zero(),
            z_0: z_0.clone(),
            z_i: z_0,
            W_i: W_dummy,
            U_i: U_dummy,
            w_i: w_dummy,
            u_i: u_dummy,
            // cyclefold running instance
            cf_W_i: cf_W_dummy,
            cf_U_i: cf_U_dummy,
        })
    }

    /// Implements IVC.P of HyperNova+CycleFold
    fn prove_step(
        &mut self,
        mut rng: impl RngCore,
        external_inputs: Vec<C1::ScalarField>,
    ) -> Result<(), Error> {
        let augmented_f_circuit: AugmentedFCircuit<C1, C2, GC2, FC>;

        if self.z_i.len() != self.F.state_len() {
            return Err(Error::NotSameLength(
                "z_i.len()".to_string(),
                self.z_i.len(),
                "F.state_len()".to_string(),
                self.F.state_len(),
            ));
        }
        if external_inputs.len() != self.F.external_inputs_len() {
            return Err(Error::NotSameLength(
                "F.external_inputs_len()".to_string(),
                self.F.external_inputs_len(),
                "external_inputs.len()".to_string(),
                external_inputs.len(),
            ));
        }

        if self.i > C1::ScalarField::from_le_bytes_mod_order(&usize::MAX.to_le_bytes()) {
            return Err(Error::MaxStep);
        }

        let mut transcript_p: PoseidonTranscript<C1> =
            PoseidonTranscript::<C1>::new(&self.poseidon_config.clone());
        let (nimfs_proof, U_i1, W_i1, rho_bits) = NIMFS::<C1, PoseidonTranscript<C1>>::prove(
            &mut transcript_p,
            &self.ccs,
            &[self.U_i.clone()],
            &[self.u_i.clone()],
            &[self.W_i.clone()],
            &[self.w_i.clone()],
        )?;

        // sanity check: check the folded instance relation
        #[cfg(test)]
        U_i1.check_relation(&self.ccs, &W_i1)?;

        let mut i_bytes: [u8; 8] = [0; 8];
        i_bytes.copy_from_slice(&self.i.into_bigint().to_bytes_le()[..8]);
        let i_usize: usize = usize::from_le_bytes(i_bytes);

        let z_i1 = self
            .F
            .step_native(i_usize, self.z_i.clone(), external_inputs.clone())?;

        let u_i1_x = U_i1.hash(
            &self.poseidon_config,
            self.pp_hash,
            self.i + C1::ScalarField::one(),
            self.z_0.clone(),
            z_i1.clone(),
        )?;

        // u_{i+1}.x[1] = H(cf_U_{i+1})
        let cf_u_i1_x: C1::ScalarField;

        if self.i == C1::ScalarField::zero() {
            cf_u_i1_x = self
                .cf_U_i
                .hash_cyclefold(&self.poseidon_config, self.pp_hash)?;

            augmented_f_circuit = AugmentedFCircuit::<C1, C2, GC2, FC> {
                _c2: PhantomData,
                _gc2: PhantomData,
                poseidon_config: self.poseidon_config.clone(),
                ccs: self.ccs.clone(),
                pp_hash: Some(self.pp_hash),
                i: Some(C1::ScalarField::zero()),
                i_usize: Some(0),
                z_0: Some(self.z_0.clone()),
                z_i: Some(self.z_i.clone()),
                external_inputs: Some(external_inputs.clone()),
                u_i_C: Some(self.u_i.C),
                U_i: Some(self.U_i.clone()),
                U_i1_C: Some(U_i1.C),
                F: self.F.clone(),
                x: Some(u_i1_x),
                nimfs_proof: Some(nimfs_proof),

                // cyclefold values
                cf_u_i_cmW: None,
                cf_U_i: None,
                cf_x: Some(cf_u_i1_x),
                cf_cmT: None,
            };
        } else {
            let rho_Fq = C2::ScalarField::from_bigint(BigInteger::from_bits_le(&rho_bits))
                .ok_or(Error::OutOfBounds)?;
            // CycleFold part:
            // get the vector used as public inputs 'x' in the CycleFold circuit
            // cyclefold circuit for cmW
            let cf_u_i_x = [
                vec![rho_Fq],
                get_cm_coordinates(&self.U_i.C),
                get_cm_coordinates(&self.u_i.C),
                get_cm_coordinates(&U_i1.C),
            ]
            .concat();

            let cf_circuit = CycleFoldCircuit::<C1, GC1> {
                _gc: PhantomData,
                r_bits: Some(rho_bits.clone()),
                p1: Some(self.U_i.clone().C),
                p2: Some(self.u_i.clone().C),
                x: Some(cf_u_i_x.clone()),
            };

            let (_cf_w_i, cf_u_i, cf_W_i1, cf_U_i1, cf_cmT, _) =
                fold_cyclefold_circuit::<C1, GC1, C2, GC2, FC, CS1, CS2>(
                    &self.poseidon_config,
                    self.cf_r1cs.clone(),
                    self.cf_cs_params.clone(),
                    self.pp_hash,
                    self.cf_W_i.clone(), // CycleFold running instance witness
                    self.cf_U_i.clone(), // CycleFold running instance
                    cf_u_i_x,
                    cf_circuit,
                )?;

            cf_u_i1_x = cf_U_i1.hash_cyclefold(&self.poseidon_config, self.pp_hash)?;

            augmented_f_circuit = AugmentedFCircuit::<C1, C2, GC2, FC> {
                _c2: PhantomData,
                _gc2: PhantomData,
                poseidon_config: self.poseidon_config.clone(),
                ccs: self.ccs.clone(),
                pp_hash: Some(self.pp_hash),
                i: Some(self.i),
                i_usize: Some(i_usize),
                z_0: Some(self.z_0.clone()),
                z_i: Some(self.z_i.clone()),
                external_inputs: Some(external_inputs),
                u_i_C: Some(self.u_i.C),
                U_i: Some(self.U_i.clone()),
                U_i1_C: Some(U_i1.C),
                F: self.F.clone(),
                x: Some(u_i1_x),
                nimfs_proof: Some(nimfs_proof),

                // cyclefold values
                cf_u_i_cmW: Some(cf_u_i.cmW),
                cf_U_i: Some(self.cf_U_i.clone()),
                cf_x: Some(cf_u_i1_x),
                cf_cmT: Some(cf_cmT),
            };

            // assign the next round instances
            self.cf_W_i = cf_W_i1;
            self.cf_U_i = cf_U_i1;
        }

        let (cs, _) = augmented_f_circuit.compute_cs_ccs()?;

        #[cfg(test)]
        assert!(cs.is_satisfied()?);

        let (r1cs_w_i1, r1cs_x_i1) = extract_w_x::<C1::ScalarField>(&cs); // includes 1 and public inputs

        let r1cs_z = [
            vec![C1::ScalarField::one()],
            r1cs_x_i1.clone(),
            r1cs_w_i1.clone(),
        ]
        .concat();
        // compute committed instances, w_{i+1}, u_{i+1}, which will be used as w_i, u_i, so we
        // assign them directly to w_i, u_i.
        let (u_i, w_i) = self
            .ccs
            .to_cccs::<_, C1, CS1>(&mut rng, &self.cs_params, &r1cs_z)?;
        self.u_i = u_i.clone();
        self.w_i = w_i.clone();

        // set values for next iteration
        self.i += C1::ScalarField::one();
        // assign z_{i+1} into z_i
        self.z_i = z_i1.clone();
        self.U_i = U_i1.clone();
        self.W_i = W_i1.clone();

        #[cfg(test)]
        {
            // check the new LCCCS instance relation
            self.U_i.check_relation(&self.ccs, &self.W_i)?;
            // check the new CCCS instance relation
            self.u_i.check_relation(&self.ccs, &self.w_i)?;
        }

        Ok(())
    }
    fn state(&self) -> Vec<C1::ScalarField> {
        self.z_i.clone()
    }
    fn instances(
        &self,
    ) -> (
        Self::RunningCommittedInstanceWithWitness,
        Self::IncomingCommittedInstanceWithWitness,
        Self::CFCommittedInstanceWithWitness,
    ) {
        (
            (self.U_i.clone(), self.W_i.clone()),
            (self.u_i.clone(), self.w_i.clone()),
            (self.cf_U_i.clone(), self.cf_W_i.clone()),
        )
    }

    /// Implements IVC.V of HyperNova+CycleFold
    fn verify(
        vp: Self::VerifierParam,
        z_0: Vec<C1::ScalarField>, // initial state
        z_i: Vec<C1::ScalarField>, // last state
        num_steps: C1::ScalarField,
        running_instance: Self::RunningCommittedInstanceWithWitness,
        incoming_instance: Self::IncomingCommittedInstanceWithWitness,
        cyclefold_instance: Self::CFCommittedInstanceWithWitness,
    ) -> Result<(), Error> {
        let (U_i, W_i) = running_instance;
        let (u_i, w_i) = incoming_instance;
        let (cf_U_i, cf_W_i) = cyclefold_instance;
        if u_i.x.len() != 2 || U_i.x.len() != 2 {
            return Err(Error::IVCVerificationFail);
        }

        let pp_hash = vp.pp_hash()?;

        // check that u_i's output points to the running instance
        // u_i.X[0] == H(i, z_0, z_i, U_i)
        let expected_u_i_x = U_i.hash(&vp.poseidon_config, pp_hash, num_steps, z_0, z_i.clone())?;
        if expected_u_i_x != u_i.x[0] {
            return Err(Error::IVCVerificationFail);
        }
        // u_i.X[1] == H(cf_U_i)
        let expected_cf_u_i_x = cf_U_i.hash_cyclefold(&vp.poseidon_config, pp_hash)?;
        if expected_cf_u_i_x != u_i.x[1] {
            return Err(Error::IVCVerificationFail);
        }

        // check LCCCS satisfiability
        U_i.check_relation(&vp.ccs, &W_i)?;
        // check CCCS satisfiability
        u_i.check_relation(&vp.ccs, &w_i)?;

        // check CycleFold's RelaxedR1CS satisfiability
        vp.cf_r1cs
            .check_relaxed_instance_relation(&cf_W_i, &cf_U_i)?;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::commitment::kzg::KZG;
    use ark_bn254::{constraints::GVar, Bn254, Fr, G1Projective as Projective};
    use ark_grumpkin::{constraints::GVar as GVar2, Projective as Projective2};

    use super::*;
    use crate::commitment::pedersen::Pedersen;
    use crate::frontend::tests::CubicFCircuit;
    use crate::transcript::poseidon::poseidon_canonical_config;

    #[test]
    pub fn test_ivc() {
        let poseidon_config = poseidon_canonical_config::<Fr>();

        let F_circuit = CubicFCircuit::<Fr>::new(()).unwrap();

        // run the test using Pedersen commitments on both sides of the curve cycle
        test_ivc_opt::<Pedersen<Projective>, Pedersen<Projective2>>(
            poseidon_config.clone(),
            F_circuit,
        );
        // run the test using KZG for the commitments on the main curve, and Pedersen for the
        // commitments on the secondary curve
        test_ivc_opt::<KZG<Bn254>, Pedersen<Projective2>>(poseidon_config, F_circuit);
    }

    // test_ivc allowing to choose the CommitmentSchemes
    fn test_ivc_opt<CS1: CommitmentScheme<Projective>, CS2: CommitmentScheme<Projective2>>(
        poseidon_config: PoseidonConfig<Fr>,
        F_circuit: CubicFCircuit<Fr>,
    ) {
        let mut rng = ark_std::test_rng();

        type HN<CS1, CS2> =
            HyperNova<Projective, GVar, Projective2, GVar2, CubicFCircuit<Fr>, CS1, CS2>;

        let prep_param =
            PreprocessorParam::<Projective, Projective2, CubicFCircuit<Fr>, CS1, CS2>::new(
                poseidon_config.clone(),
                F_circuit,
            );
        let (prover_params, verifier_params) = HN::preprocess(&mut rng, &prep_param).unwrap();

        let z_0 = vec![Fr::from(3_u32)];
        let mut hypernova = HN::init(
            (prover_params, verifier_params.clone()),
            F_circuit,
            z_0.clone(),
        )
        .unwrap();

        let num_steps: usize = 3;
        for _ in 0..num_steps {
            hypernova.prove_step(&mut rng, vec![]).unwrap();
        }
        assert_eq!(Fr::from(num_steps as u32), hypernova.i);

        let (running_instance, incoming_instance, cyclefold_instance) = hypernova.instances();
        HN::verify(
            verifier_params,
            z_0,
            hypernova.z_i,
            hypernova.i,
            running_instance,
            incoming_instance,
            cyclefold_instance,
        )
        .unwrap();
    }
}
