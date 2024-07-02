/// Implementation of [HyperNova](https://eprint.iacr.org/2023/573.pdf) circuits
use ark_crypto_primitives::crh::{
    poseidon::constraints::{CRHGadget, CRHParametersVar},
    CRHSchemeGadget,
};
use ark_crypto_primitives::sponge::{poseidon::PoseidonConfig, Absorb};
use ark_ec::{CurveGroup, Group};
use ark_ff::PrimeField;
use ark_r1cs_std::{
    alloc::{AllocVar, AllocationMode},
    boolean::Boolean,
    eq::EqGadget,
    fields::{fp::FpVar, FieldVar},
    groups::GroupOpsBounds,
    prelude::CurveVar,
    R1CSVar, ToConstraintFieldGadget,
};
use ark_relations::r1cs::{
    ConstraintSynthesizer, ConstraintSystem, ConstraintSystemRef, Namespace, SynthesisError,
};
use ark_std::{fmt::Debug, ops::Neg, One, Zero};
use core::{borrow::Borrow, marker::PhantomData};

use super::{
    cccs::CCCS,
    lcccs::LCCCS,
    nimfs::{NIMFSProof, NIMFS},
    Witness,
};
use crate::constants::N_BITS_RO;
use crate::folding::{
    circuits::cyclefold::{
        CycleFoldChallengeGadget, CycleFoldCommittedInstanceVar, NIFSFullGadget, CF_IO_LEN,
    },
    circuits::{
        nonnative::{affine::NonNativeAffineVar, uint::NonNativeUintVar},
        sum_check::{IOPProofVar, SumCheckVerifierGadget, VPAuxInfoVar},
        utils::EqEvalGadget,
        CF1, CF2,
    },
    nova::{get_r1cs_from_cs, CommittedInstance},
};
use crate::frontend::FCircuit;
use crate::utils::virtual_polynomial::VPAuxInfo;
use crate::Error;
use crate::{
    ccs::{r1cs::extract_r1cs, CCS},
    transcript::{
        poseidon::{PoseidonTranscript, PoseidonTranscriptVar},
        Transcript, TranscriptVar,
    },
};

/// Committed CCS instance
#[derive(Debug, Clone)]
pub struct CCCSVar<C: CurveGroup>
where
    <C as CurveGroup>::BaseField: PrimeField,
{
    // Commitment to witness
    pub C: NonNativeAffineVar<C>,
    // Public io
    pub x: Vec<FpVar<CF1<C>>>,
}
impl<C> AllocVar<CCCS<C>, CF1<C>> for CCCSVar<C>
where
    C: CurveGroup,
    <C as ark_ec::CurveGroup>::BaseField: PrimeField,
{
    fn new_variable<T: Borrow<CCCS<C>>>(
        cs: impl Into<Namespace<CF1<C>>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        f().and_then(|val| {
            let cs = cs.into();

            let C = NonNativeAffineVar::<C>::new_variable(cs.clone(), || Ok(val.borrow().C), mode)?;
            let x: Vec<FpVar<C::ScalarField>> =
                Vec::new_variable(cs.clone(), || Ok(val.borrow().x.clone()), mode)?;

            Ok(Self { C, x })
        })
    }
}

/// Linearized Committed CCS instance
#[derive(Debug, Clone)]
pub struct LCCCSVar<C: CurveGroup>
where
    <C as CurveGroup>::BaseField: PrimeField,
{
    // Commitment to witness
    pub C: NonNativeAffineVar<C>,
    // Relaxation factor of z for folded LCCCS
    pub u: FpVar<CF1<C>>,
    // Public io
    pub x: Vec<FpVar<CF1<C>>>,
    // Random evaluation point for the v_i
    pub r_x: Vec<FpVar<CF1<C>>>,
    // Vector of v_i
    pub v: Vec<FpVar<CF1<C>>>,
}
impl<C> AllocVar<LCCCS<C>, CF1<C>> for LCCCSVar<C>
where
    C: CurveGroup,
    <C as ark_ec::CurveGroup>::BaseField: PrimeField,
{
    fn new_variable<T: Borrow<LCCCS<C>>>(
        cs: impl Into<Namespace<CF1<C>>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        f().and_then(|val| {
            let cs = cs.into();

            let C = NonNativeAffineVar::<C>::new_variable(cs.clone(), || Ok(val.borrow().C), mode)?;
            let u = FpVar::<C::ScalarField>::new_variable(cs.clone(), || Ok(val.borrow().u), mode)?;
            let x: Vec<FpVar<C::ScalarField>> =
                Vec::new_variable(cs.clone(), || Ok(val.borrow().x.clone()), mode)?;
            let r_x: Vec<FpVar<C::ScalarField>> =
                Vec::new_variable(cs.clone(), || Ok(val.borrow().r_x.clone()), mode)?;
            let v: Vec<FpVar<C::ScalarField>> =
                Vec::new_variable(cs.clone(), || Ok(val.borrow().v.clone()), mode)?;

            Ok(Self { C, u, x, r_x, v })
        })
    }
}

impl<C> LCCCSVar<C>
where
    C: CurveGroup,
    <C as Group>::ScalarField: Absorb,
    <C as ark_ec::CurveGroup>::BaseField: ark_ff::PrimeField,
{
    /// [`LCCCSVar`].hash implements the LCCCS instance hash compatible with the native
    /// implementation from LCCCS.hash.
    /// Returns `H(i, z_0, z_i, U_i)`, where `i` can be `i` but also `i+1`, and `U` is the LCCCS.
    /// Additionally it returns the vector of the field elements from the self parameters, so they
    /// can be reused in other gadgets avoiding recalculating (reconstraining) them.
    #[allow(clippy::type_complexity)]
    pub fn hash(
        self,
        crh_params: &CRHParametersVar<CF1<C>>,
        i: FpVar<CF1<C>>,
        z_0: Vec<FpVar<CF1<C>>>,
        z_i: Vec<FpVar<CF1<C>>>,
    ) -> Result<(FpVar<CF1<C>>, Vec<FpVar<CF1<C>>>), SynthesisError> {
        let U_vec = [
            self.C.to_constraint_field()?,
            vec![self.u],
            self.x,
            self.r_x,
            self.v,
        ]
        .concat();
        let input = [vec![i], z_0, z_i, U_vec.clone()].concat();
        Ok((
            CRHGadget::<C::ScalarField>::evaluate(crh_params, &input)?,
            U_vec,
        ))
    }
}

/// ProofVar defines a multifolding proof
#[derive(Debug)]
pub struct ProofVar<C: CurveGroup> {
    pub sc_proof: IOPProofVar<C>,
    #[allow(clippy::type_complexity)]
    pub sigmas_thetas: (Vec<Vec<FpVar<CF1<C>>>>, Vec<Vec<FpVar<CF1<C>>>>),
}
impl<C> AllocVar<NIMFSProof<C>, CF1<C>> for ProofVar<C>
where
    C: CurveGroup,
    <C as ark_ec::CurveGroup>::BaseField: PrimeField,
    <C as Group>::ScalarField: Absorb,
{
    fn new_variable<T: Borrow<NIMFSProof<C>>>(
        cs: impl Into<Namespace<CF1<C>>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        f().and_then(|val| {
            let cs = cs.into();

            let sc_proof = IOPProofVar::<C>::new_variable(
                cs.clone(),
                || Ok(val.borrow().sc_proof.clone()),
                mode,
            )?;
            let sigmas: Vec<Vec<FpVar<CF1<C>>>> = val
                .borrow()
                .sigmas_thetas
                .0
                .iter()
                .map(|sigmas_i| Vec::new_variable(cs.clone(), || Ok(sigmas_i.clone()), mode))
                .collect::<Result<Vec<Vec<FpVar<CF1<C>>>>, SynthesisError>>()?;
            let thetas: Vec<Vec<FpVar<CF1<C>>>> = val
                .borrow()
                .sigmas_thetas
                .1
                .iter()
                .map(|thetas_i| Vec::new_variable(cs.clone(), || Ok(thetas_i.clone()), mode))
                .collect::<Result<Vec<Vec<FpVar<CF1<C>>>>, SynthesisError>>()?;

            Ok(Self {
                sc_proof,
                sigmas_thetas: (sigmas.clone(), thetas.clone()),
            })
        })
    }
}

pub struct NIMFSGadget<C: CurveGroup> {
    _c: PhantomData<C>,
}
impl<C: CurveGroup> NIMFSGadget<C>
where
    <C as CurveGroup>::BaseField: PrimeField,
{
    /// Runs (in-circuit) the NIMFS.V, which outputs the new folded LCCCS instance together with
    /// the rho_bits, which will be used in other parts of the AugmentedFCircuit
    #[allow(clippy::type_complexity)]
    pub fn verify(
        cs: ConstraintSystemRef<CF1<C>>,
        // only used the CCS params, not the matrices
        ccs: &CCS<C::ScalarField>,
        mut transcript: impl TranscriptVar<C::ScalarField>,

        running_instances: &[LCCCSVar<C>],
        new_instances: &[CCCSVar<C>],
        proof: ProofVar<C>,
        enabled: Boolean<C::ScalarField>,
    ) -> Result<(LCCCSVar<C>, Vec<Boolean<CF1<C>>>), SynthesisError> {
        // absorb instances to transcript
        for U_i in running_instances {
            let v = [
                U_i.C.to_constraint_field()?,
                vec![U_i.u.clone()],
                U_i.x.clone(),
                U_i.r_x.clone(),
                U_i.v.clone(),
            ]
            .concat();
            transcript.absorb_vec(&v)?;
        }
        for u_i in new_instances {
            let v = [u_i.C.to_constraint_field()?, u_i.x.clone()].concat();
            transcript.absorb_vec(&v)?;
        }

        // get the challenges
        let gamma_scalar_raw = C::ScalarField::from_le_bytes_mod_order(b"gamma");
        let gamma_scalar: FpVar<CF1<C>> =
            FpVar::<CF1<C>>::new_constant(cs.clone(), gamma_scalar_raw)?;
        transcript.absorb(gamma_scalar)?;
        let gamma: FpVar<CF1<C>> = transcript.get_challenge()?;

        let beta_scalar_raw = C::ScalarField::from_le_bytes_mod_order(b"beta");
        let beta_scalar: FpVar<CF1<C>> =
            FpVar::<CF1<C>>::new_constant(cs.clone(), beta_scalar_raw)?;
        transcript.absorb(beta_scalar)?;
        let beta: Vec<FpVar<CF1<C>>> = transcript.get_challenges(ccs.s)?;

        let vp_aux_info_raw = VPAuxInfo::<C::ScalarField> {
            max_degree: ccs.d + 1,
            num_variables: ccs.s,
            phantom: PhantomData::<C::ScalarField>,
        };
        let vp_aux_info = VPAuxInfoVar::<CF1<C>>::new_witness(cs.clone(), || Ok(vp_aux_info_raw))?;

        // sumcheck
        // first, compute the expected sumcheck sum: \sum gamma^j v_j
        let mut sum_v_j_gamma = FpVar::<CF1<C>>::zero();
        let mut gamma_j = FpVar::<C::ScalarField>::one();
        for running_instance in running_instances.iter() {
            for j in 0..running_instance.v.len() {
                gamma_j *= gamma.clone();
                sum_v_j_gamma += running_instance.v[j].clone() * gamma_j.clone();
            }
        }

        // verify the interactive part of the sumcheck
        let (e_vars, r_vars) = SumCheckVerifierGadget::<C>::verify(
            &proof.sc_proof,
            &vp_aux_info,
            &mut transcript,
            enabled.clone(),
        )?;

        // extract the randomness from the sumcheck
        let r_x_prime = r_vars.clone();

        // verify the claim c
        let computed_c = compute_c_gadget(
            cs.clone(),
            ccs,
            proof.sigmas_thetas.0.clone(), // sigmas
            proof.sigmas_thetas.1.clone(), // thetas
            gamma,
            beta,
            running_instances
                .iter()
                .map(|lcccs| lcccs.r_x.clone())
                .collect(),
            r_x_prime.clone(),
        )?;
        computed_c.conditional_enforce_equal(&e_vars[e_vars.len() - 1], &enabled)?;

        // get the folding challenge
        let rho_scalar_raw = C::ScalarField::from_le_bytes_mod_order(b"rho");
        let rho_scalar: FpVar<CF1<C>> = FpVar::<CF1<C>>::new_constant(cs.clone(), rho_scalar_raw)?;
        transcript.absorb(rho_scalar)?;
        let rho_bits: Vec<Boolean<CF1<C>>> = transcript.get_challenge_nbits(N_BITS_RO)?;
        let rho = Boolean::le_bits_to_fp_var(&rho_bits)?;

        // return the folded instance, together with the rho_bits so they can be used in other
        // parts of the AugmentedFCircuit
        Ok((
            Self::fold(
                running_instances,
                new_instances,
                proof.sigmas_thetas,
                r_x_prime,
                rho,
            )?,
            rho_bits,
        ))
    }

    /// Runs (in-circuit) the verifier side of the fold, computing the new folded LCCCS instance
    #[allow(clippy::type_complexity)]
    fn fold(
        lcccs: &[LCCCSVar<C>],
        cccs: &[CCCSVar<C>],
        sigmas_thetas: (Vec<Vec<FpVar<CF1<C>>>>, Vec<Vec<FpVar<CF1<C>>>>),
        r_x_prime: Vec<FpVar<CF1<C>>>,
        rho: FpVar<CF1<C>>,
    ) -> Result<LCCCSVar<C>, SynthesisError> {
        let (sigmas, thetas) = (sigmas_thetas.0.clone(), sigmas_thetas.1.clone());
        let mut u_folded: FpVar<CF1<C>> = FpVar::zero();
        let mut x_folded: Vec<FpVar<CF1<C>>> = vec![FpVar::zero(); lcccs[0].x.len()];
        let mut v_folded: Vec<FpVar<CF1<C>>> = vec![FpVar::zero(); sigmas[0].len()];

        let mut rho_i = FpVar::one();
        for i in 0..(lcccs.len() + cccs.len()) {
            let u: FpVar<CF1<C>>;
            let x: Vec<FpVar<CF1<C>>>;
            let v: Vec<FpVar<CF1<C>>>;
            if i < lcccs.len() {
                u = lcccs[i].u.clone();
                x = lcccs[i].x.clone();
                v = sigmas[i].clone();
            } else {
                u = FpVar::one();
                x = cccs[i - lcccs.len()].x.clone();
                v = thetas[i - lcccs.len()].clone();
            }

            u_folded += rho_i.clone() * u;
            x_folded = x_folded
                .iter()
                .zip(
                    x.iter()
                        .map(|x_i| x_i * rho_i.clone())
                        .collect::<Vec<FpVar<CF1<C>>>>(),
                )
                .map(|(a_i, b_i)| a_i + b_i)
                .collect();

            v_folded = v_folded
                .iter()
                .zip(
                    v.iter()
                        .map(|x_i| x_i * rho_i.clone())
                        .collect::<Vec<FpVar<CF1<C>>>>(),
                )
                .map(|(a_i, b_i)| a_i + b_i)
                .collect();

            rho_i *= rho.clone();
        }

        Ok(LCCCSVar::<C> {
            C: lcccs[0].C.clone(), // WIP this will come from the cyclefold circuit
            u: u_folded,
            x: x_folded,
            r_x: r_x_prime,
            v: v_folded,
        })
    }
}

/// Computes c from the step 5 in section 5 of HyperNova, adapted to multiple LCCCS & CCCS
/// instances:
/// $$
/// c = \sum_{i \in [\mu]} \left(\sum_{j \in [t]} \gamma^{i \cdot t + j} \cdot e_i \cdot \sigma_{i,j} \right)
/// + \sum_{k \in [\nu]} \gamma^{\mu \cdot t+k} \cdot e_k \cdot \left( \sum_{i=1}^q c_i \cdot \prod_{j \in S_i}
/// \theta_{k,j} \right)
/// $$
#[allow(clippy::too_many_arguments)]
fn compute_c_gadget<F: PrimeField>(
    cs: ConstraintSystemRef<F>,
    ccs: &CCS<F>,
    vec_sigmas: Vec<Vec<FpVar<F>>>,
    vec_thetas: Vec<Vec<FpVar<F>>>,
    gamma: FpVar<F>,
    beta: Vec<FpVar<F>>,
    vec_r_x: Vec<Vec<FpVar<F>>>,
    vec_r_x_prime: Vec<FpVar<F>>,
) -> Result<FpVar<F>, SynthesisError> {
    let mut e_lcccs = Vec::new();
    for r_x in vec_r_x.iter() {
        e_lcccs.push(EqEvalGadget::eq_eval(r_x, &vec_r_x_prime)?);
    }

    let mut c = FpVar::<F>::zero();
    let mut current_gamma = FpVar::<F>::one();
    for i in 0..vec_sigmas.len() {
        for j in 0..ccs.t {
            c += current_gamma.clone() * e_lcccs[i].clone() * vec_sigmas[i][j].clone();
            current_gamma *= gamma.clone();
        }
    }

    let ccs_c = Vec::<FpVar<F>>::new_constant(cs.clone(), ccs.c.clone())?;
    let e_k = EqEvalGadget::eq_eval(&beta, &vec_r_x_prime)?;
    #[allow(clippy::needless_range_loop)]
    for k in 0..vec_thetas.len() {
        let mut sum = FpVar::<F>::zero();
        for i in 0..ccs.q {
            let mut prod = FpVar::<F>::one();
            for j in ccs.S[i].clone() {
                prod *= vec_thetas[k][j].clone();
            }
            sum += ccs_c[i].clone() * prod;
        }
        c += current_gamma.clone() * e_k.clone() * sum;
        current_gamma *= gamma.clone();
    }
    Ok(c)
}

#[derive(Debug, Clone)]
pub struct AugmentedFCircuit<
    C1: CurveGroup,
    C2: CurveGroup,
    GC2: CurveVar<C2, CF2<C2>>,
    FC: FCircuit<CF1<C1>>,
> where
    for<'a> &'a GC2: GroupOpsBounds<'a, C2, GC2>,
{
    pub _c2: PhantomData<C2>,
    pub _gc2: PhantomData<GC2>,
    pub poseidon_config: PoseidonConfig<CF1<C1>>,
    pub ccs: CCS<C1::ScalarField>, // CCS of the AugmentedFCircuit
    pub i: Option<CF1<C1>>,
    pub i_usize: Option<usize>,
    pub z_0: Option<Vec<C1::ScalarField>>,
    pub z_i: Option<Vec<C1::ScalarField>>,
    pub external_inputs: Option<Vec<C1::ScalarField>>,
    pub u_i_C: Option<C1>, // u_i.C
    pub U_i: Option<LCCCS<C1>>,
    pub U_i1_C: Option<C1>, // U_{i+1}.C
    pub F: FC,              // F circuit
    pub x: Option<CF1<C1>>, // public input (u_{i+1}.x[0])
    pub nimfs_proof: Option<NIMFSProof<C1>>,

    // cyclefold verifier on C1
    pub cf_u_i_cmW: Option<C2>,                // input, cf_u_i.cmW
    pub cf_U_i: Option<CommittedInstance<C2>>, // input, RelaxedR1CS CycleFold instance
    pub cf_x: Option<CF1<C1>>,                 // public input (cf_u_{i+1}.x[1])
    pub cf_cmT: Option<C2>,
}

impl<C1, C2, GC2, FC> AugmentedFCircuit<C1, C2, GC2, FC>
where
    C1: CurveGroup,
    C2: CurveGroup,
    GC2: CurveVar<C2, CF2<C2>> + ToConstraintFieldGadget<CF2<C2>>,
    FC: FCircuit<CF1<C1>>,
    <C1 as CurveGroup>::BaseField: PrimeField,
    <C2 as CurveGroup>::BaseField: PrimeField,
    <C1 as Group>::ScalarField: Absorb,
    <C2 as Group>::ScalarField: Absorb,
    C1: CurveGroup<BaseField = C2::ScalarField, ScalarField = C2::BaseField>,
    for<'a> &'a GC2: GroupOpsBounds<'a, C2, GC2>,
{
    pub fn default(
        poseidon_config: &PoseidonConfig<CF1<C1>>,
        F_circuit: FC,
        ccs: CCS<C1::ScalarField>,
    ) -> Self {
        Self {
            _c2: PhantomData,
            _gc2: PhantomData,
            poseidon_config: poseidon_config.clone(),
            ccs,
            i: None,
            i_usize: None,
            z_0: None,
            z_i: None,
            external_inputs: None,
            u_i_C: None,
            U_i: None,
            U_i1_C: None,
            F: F_circuit,
            x: None,
            nimfs_proof: None,
            cf_u_i_cmW: None,
            cf_U_i: None,
            cf_x: None,
            cf_cmT: None,
        }
    }

    pub fn empty(
        poseidon_config: &PoseidonConfig<CF1<C1>>,
        F_circuit: FC,
        ccs: Option<CCS<C1::ScalarField>>,
    ) -> Result<Self, Error> {
        let initial_ccs = CCS {
            // m, n, s, s_prime and M will be overwritten by the `upper_bound_ccs' method
            m: 0,
            n: 0,
            l: 2, // io_len
            s: 1,
            s_prime: 1,
            t: 3, // note: this is only supports R1CS for the moment
            q: 2,
            d: 2,
            S: vec![vec![0, 1], vec![2]],
            c: vec![C1::ScalarField::one(), C1::ScalarField::one().neg()],
            M: vec![],
        };
        let mut augmented_f_circuit = Self::default(poseidon_config, F_circuit, initial_ccs);
        if ccs.is_some() {
            augmented_f_circuit.ccs = ccs.unwrap();
        } else {
            augmented_f_circuit.ccs = augmented_f_circuit.upper_bound_ccs()?;
        }
        Ok(augmented_f_circuit)
    }

    /// This method computes the CCS parameters. This is used because there is a circular
    /// dependency between the AugmentedFCircuit CCS and the CCS parameters m & n & s & s'.
    /// For a stable FCircuit circuit, the CCS parameters can be computed in advance and can be
    /// feed in as parameter for the AugmentedFCircuit::empty method to avoid computing them there.
    pub fn upper_bound_ccs(&self) -> Result<CCS<C1::ScalarField>, Error> {
        let r1cs = get_r1cs_from_cs::<CF1<C1>>(self.clone()).unwrap();
        let ccs = CCS::from_r1cs(r1cs.clone());

        let z_0 = vec![C1::ScalarField::zero(); self.F.state_len()];
        let W_i = Witness::<C1::ScalarField>::dummy(&ccs);
        let U_i = LCCCS::<C1>::dummy(ccs.l, ccs.t, ccs.s);
        let w_i = W_i.clone();
        let u_i = CCCS::<C1>::dummy(ccs.l);

        let mut transcript_p: PoseidonTranscript<C1> =
            PoseidonTranscript::<C1>::new(&self.poseidon_config.clone());
        let (nimfs_proof, U_i1, _, _) = NIMFS::<C1, PoseidonTranscript<C1>>::prove(
            &mut transcript_p,
            &ccs,
            &[U_i.clone()],
            &[u_i.clone()],
            &[W_i.clone()],
            &[w_i.clone()],
        )?;

        let augmented_f_circuit = Self {
            _c2: PhantomData,
            _gc2: PhantomData,
            poseidon_config: self.poseidon_config.clone(),
            ccs: ccs.clone(),
            i: Some(C1::ScalarField::zero()),
            i_usize: Some(0),
            z_0: Some(z_0.clone()),
            z_i: Some(z_0.clone()),
            external_inputs: Some(vec![]),
            u_i_C: Some(u_i.C),
            U_i: Some(U_i.clone()),
            U_i1_C: Some(U_i1.C),
            F: self.F.clone(),
            x: Some(C1::ScalarField::zero()),
            nimfs_proof: Some(nimfs_proof),
            // cyclefold values
            cf_u_i_cmW: None,
            cf_U_i: None,
            cf_x: None,
            cf_cmT: None,
        };

        Ok(augmented_f_circuit.compute_cs_ccs()?.1)
    }

    /// Returns the cs (ConstraintSystem) and the CCS out of the AugmentedFCircuit
    #[allow(clippy::type_complexity)]
    pub fn compute_cs_ccs(
        &self,
    ) -> Result<(ConstraintSystem<C1::ScalarField>, CCS<C1::ScalarField>), Error> {
        let cs = ConstraintSystem::<C1::ScalarField>::new_ref();
        self.clone().generate_constraints(cs.clone())?;
        cs.finalize();
        let cs = cs.into_inner().ok_or(Error::NoInnerConstraintSystem)?;
        let r1cs = extract_r1cs::<C1::ScalarField>(&cs);
        let ccs = CCS::from_r1cs(r1cs.clone());

        Ok((cs, ccs))
    }
}

impl<C1, C2, GC2, FC> ConstraintSynthesizer<CF1<C1>> for AugmentedFCircuit<C1, C2, GC2, FC>
where
    C1: CurveGroup,
    C2: CurveGroup,
    GC2: CurveVar<C2, CF2<C2>> + ToConstraintFieldGadget<CF2<C2>>,
    FC: FCircuit<CF1<C1>>,
    <C1 as CurveGroup>::BaseField: PrimeField,
    <C2 as CurveGroup>::BaseField: PrimeField,
    <C1 as Group>::ScalarField: Absorb,
    <C2 as Group>::ScalarField: Absorb,
    C1: CurveGroup<BaseField = C2::ScalarField, ScalarField = C2::BaseField>,
    for<'a> &'a GC2: GroupOpsBounds<'a, C2, GC2>,
{
    fn generate_constraints(self, cs: ConstraintSystemRef<CF1<C1>>) -> Result<(), SynthesisError> {
        let i = FpVar::<CF1<C1>>::new_witness(cs.clone(), || {
            Ok(self.i.unwrap_or_else(CF1::<C1>::zero))
        })?;
        let z_0 = Vec::<FpVar<CF1<C1>>>::new_witness(cs.clone(), || {
            Ok(self
                .z_0
                .unwrap_or(vec![CF1::<C1>::zero(); self.F.state_len()]))
        })?;
        let z_i = Vec::<FpVar<CF1<C1>>>::new_witness(cs.clone(), || {
            Ok(self
                .z_i
                .unwrap_or(vec![CF1::<C1>::zero(); self.F.state_len()]))
        })?;
        let external_inputs = Vec::<FpVar<CF1<C1>>>::new_witness(cs.clone(), || {
            Ok(self
                .external_inputs
                .unwrap_or(vec![CF1::<C1>::zero(); self.F.external_inputs_len()]))
        })?;

        let U_dummy = LCCCS::<C1>::dummy(self.ccs.l, self.ccs.t, self.ccs.s);

        let U_i =
            LCCCSVar::<C1>::new_witness(cs.clone(), || Ok(self.U_i.unwrap_or(U_dummy.clone())))?;
        let U_i1_C = NonNativeAffineVar::new_witness(cs.clone(), || {
            Ok(self.U_i1_C.unwrap_or_else(C1::zero))
        })?;
        let mu = 1; // Note: at this commit, only 2-to-1 instance fold is supported
        let nu = 1;
        let nimfs_proof_dummy = NIMFSProof::<C1>::dummy(&self.ccs, mu, nu);
        let nimfs_proof = ProofVar::<C1>::new_witness(cs.clone(), || {
            Ok(self.nimfs_proof.unwrap_or(nimfs_proof_dummy))
        })?;

        let cf_u_dummy = CommittedInstance::dummy(CF_IO_LEN);
        let cf_U_i = CycleFoldCommittedInstanceVar::<C2, GC2>::new_witness(cs.clone(), || {
            Ok(self.cf_U_i.unwrap_or(cf_u_dummy.clone()))
        })?;
        let cf_cmT = GC2::new_witness(cs.clone(), || Ok(self.cf_cmT.unwrap_or_else(C2::zero)))?;

        let crh_params = CRHParametersVar::<C1::ScalarField>::new_constant(
            cs.clone(),
            self.poseidon_config.clone(),
        )?;

        // get z_{i+1} from the F circuit
        let i_usize = self.i_usize.unwrap_or(0);
        let z_i1 =
            self.F
                .generate_step_constraints(cs.clone(), i_usize, z_i.clone(), external_inputs)?;

        let is_basecase = i.is_zero()?;
        let is_not_basecase = is_basecase.not();

        // Primary Part
        // P.1. Compute u_i.x
        // u_i.x[0] = H(i, z_0, z_i, U_i)
        let (u_i_x, _) = U_i
            .clone()
            .hash(&crh_params, i.clone(), z_0.clone(), z_i.clone())?;
        // u_i.x[1] = H(cf_U_i)
        let (cf_u_i_x, cf_U_i_vec) = cf_U_i.clone().hash(&crh_params)?;

        // P.2. Construct u_i
        let u_i = CCCSVar::<C1> {
            // u_i.C is provided by the prover as witness
            C: NonNativeAffineVar::<C1>::new_witness(cs.clone(), || {
                Ok(self.u_i_C.unwrap_or(C1::zero()))
            })?,
            // u_i.x is computed in step 1
            x: vec![u_i_x, cf_u_i_x],
        };

        // P.3. NIMFS.verify, obtains U_{i+1} by folding [U_i] & [u_i].
        // Notice that NIMFSGadget::fold_committed_instance does not fold C. We set `U_i1.C` to
        // unconstrained witnesses `U_i1_C` respectively. Its correctness will be checked on the
        // other curve.
        let transcript =
            PoseidonTranscriptVar::<C1::ScalarField>::new(cs.clone(), &self.poseidon_config);
        let (mut U_i1, rho_bits) = NIMFSGadget::<C1>::verify(
            cs.clone(),
            &self.ccs.clone(),
            transcript,
            &[U_i.clone()],
            &[u_i.clone()],
            nimfs_proof,
            is_not_basecase.clone(),
        )?;
        U_i1.C = U_i1_C;

        // P.4.a compute and check the first output of F'
        let (u_i1_x, _) = U_i1.clone().hash(
            &crh_params,
            i + FpVar::<CF1<C1>>::one(),
            z_0.clone(),
            z_i1.clone(),
        )?;
        let x = FpVar::new_input(cs.clone(), || Ok(self.x.unwrap_or(C1::ScalarField::zero())))?;
        x.enforce_equal(&u_i1_x)?;

        // convert rho_bits to a `NonNativeFieldVar`
        let rho_nonnat = {
            let mut bits = rho_bits;
            bits.resize(C1::BaseField::MODULUS_BIT_SIZE as usize, Boolean::FALSE);
            NonNativeUintVar::from(&bits)
        };

        // CycleFold part
        // C.1. Compute cf1_u_i.x and cf2_u_i.x
        let cf_x = vec![
            rho_nonnat, U_i.C.x, U_i.C.y, u_i.C.x, u_i.C.y, U_i1.C.x, U_i1.C.y,
        ];

        // ensure that cf_u has as public inputs the C from main instances U_i, u_i, U_i+1
        // coordinates of the commitments.
        // C.2. Construct `cf_u_i`
        let cf_u_i = CycleFoldCommittedInstanceVar {
            // cf1_u_i.cmE = 0. Notice that we enforce cmE to be equal to 0 since it is allocated
            // as 0.
            cmE: GC2::zero(),
            // cf1_u_i.u = 1
            u: NonNativeUintVar::new_constant(cs.clone(), C1::BaseField::one())?,
            // cf_u_i.cmW is provided by the prover as witness
            cmW: GC2::new_witness(cs.clone(), || Ok(self.cf_u_i_cmW.unwrap_or(C2::zero())))?,
            // cf_u_i.x is computed in step 1
            x: cf_x,
        };

        // C.3. nifs.verify (fold_committed_instance), obtains cf_U_{i+1} by folding cf_u_i & cf_U_i.
        // compute cf_r = H(cf_u_i, cf_U_i, cf_cmT)
        // cf_r_bits is denoted by rho* in the paper.
        let cf_r_bits = CycleFoldChallengeGadget::<C2, GC2>::get_challenge_gadget(
            cs.clone(),
            &self.poseidon_config,
            cf_U_i_vec,
            cf_u_i.clone(),
            cf_cmT.clone(),
        )?;
        // Convert cf_r_bits to a `NonNativeFieldVar`
        let cf_r_nonnat = {
            let mut bits = cf_r_bits.clone();
            bits.resize(C1::BaseField::MODULUS_BIT_SIZE as usize, Boolean::FALSE);
            NonNativeUintVar::from(&bits)
        };
        // Fold cf1_u_i & cf_U_i into cf1_U_{i+1}
        let cf_U_i1 = NIFSFullGadget::<C2, GC2>::fold_committed_instance(
            cf_r_bits,
            cf_r_nonnat,
            cf_cmT,
            cf_U_i,
            cf_u_i,
        )?;

        // Back to Primary Part
        // P.4.b compute and check the second output of F'
        // Base case: u_{i+1}.x[1] == H(cf_U_{\bot})
        // Non-base case: u_{i+1}.x[1] == H(cf_U_{i+1})
        let (cf_u_i1_x, _) = cf_U_i1.clone().hash(&crh_params)?;
        let (cf_u_i1_x_base, _) =
            CycleFoldCommittedInstanceVar::new_constant(cs.clone(), cf_u_dummy)?
                .hash(&crh_params)?;
        let cf_x = FpVar::new_input(cs.clone(), || {
            Ok(self.cf_x.unwrap_or(cf_u_i1_x_base.value()?))
        })?;
        cf_x.enforce_equal(&is_basecase.select(&cf_u_i1_x_base, &cf_u_i1_x)?)?;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use ark_bn254::{constraints::GVar, Fq, Fr, G1Projective as Projective};
    use ark_ff::BigInteger;
    use ark_grumpkin::{constraints::GVar as GVar2, Projective as Projective2};
    use ark_r1cs_std::{alloc::AllocVar, fields::fp::FpVar, R1CSVar};
    use ark_std::{test_rng, UniformRand};
    use std::time::Instant;

    use super::*;
    use crate::{
        ccs::{
            r1cs::extract_w_x,
            tests::{get_test_ccs, get_test_z},
            CCS,
        },
        commitment::{pedersen::Pedersen, CommitmentScheme},
        folding::{
            circuits::cyclefold::{fold_cyclefold_circuit, CycleFoldCircuit},
            hypernova::{
                nimfs::NIMFS,
                utils::{compute_c, compute_sigmas_thetas},
                Witness,
            },
            nova::{traits::NovaR1CS, CommittedInstance, Witness as NovaWitness},
        },
        frontend::tests::CubicFCircuit,
        transcript::{
            poseidon::{poseidon_canonical_config, PoseidonTranscript, PoseidonTranscriptVar},
            Transcript,
        },
        utils::get_cm_coordinates,
    };

    #[test]
    pub fn test_compute_c_gadget() {
        // number of LCCCS & CCCS instances to fold in a single step
        let mu = 32;
        let nu = 42;

        let mut z_lcccs = Vec::new();
        for i in 0..mu {
            let z = get_test_z(i + 3);
            z_lcccs.push(z);
        }
        let mut z_cccs = Vec::new();
        for i in 0..nu {
            let z = get_test_z(i + 3);
            z_cccs.push(z);
        }

        let ccs: CCS<Fr> = get_test_ccs();

        let mut rng = test_rng();
        let gamma: Fr = Fr::rand(&mut rng);
        let beta: Vec<Fr> = (0..ccs.s).map(|_| Fr::rand(&mut rng)).collect();
        let r_x_prime: Vec<Fr> = (0..ccs.s).map(|_| Fr::rand(&mut rng)).collect();

        let (pedersen_params, _) =
            Pedersen::<Projective>::setup(&mut rng, ccs.n - ccs.l - 1).unwrap();

        // Create the LCCCS instances out of z_lcccs
        let mut lcccs_instances = Vec::new();
        for z_i in z_lcccs.iter() {
            let (inst, _) = ccs
                .to_lcccs::<_, _, Pedersen<Projective>>(&mut rng, &pedersen_params, z_i)
                .unwrap();
            lcccs_instances.push(inst);
        }
        // Create the CCCS instance out of z_cccs
        let mut cccs_instances = Vec::new();
        for z_i in z_cccs.iter() {
            let (inst, _) = ccs
                .to_cccs::<_, _, Pedersen<Projective>>(&mut rng, &pedersen_params, z_i)
                .unwrap();
            cccs_instances.push(inst);
        }

        let sigmas_thetas = compute_sigmas_thetas(&ccs, &z_lcccs, &z_cccs, &r_x_prime).unwrap();

        let expected_c = compute_c(
            &ccs,
            &sigmas_thetas,
            gamma,
            &beta,
            &lcccs_instances
                .iter()
                .map(|lcccs| lcccs.r_x.clone())
                .collect(),
            &r_x_prime,
        )
        .unwrap();

        let cs = ConstraintSystem::<Fr>::new_ref();
        let mut vec_sigmas = Vec::new();
        let mut vec_thetas = Vec::new();
        for sigmas in sigmas_thetas.0 {
            vec_sigmas
                .push(Vec::<FpVar<Fr>>::new_witness(cs.clone(), || Ok(sigmas.clone())).unwrap());
        }
        for thetas in sigmas_thetas.1 {
            vec_thetas
                .push(Vec::<FpVar<Fr>>::new_witness(cs.clone(), || Ok(thetas.clone())).unwrap());
        }
        let vec_r_x: Vec<Vec<FpVar<Fr>>> = lcccs_instances
            .iter()
            .map(|lcccs| {
                Vec::<FpVar<Fr>>::new_witness(cs.clone(), || Ok(lcccs.r_x.clone())).unwrap()
            })
            .collect();
        let vec_r_x_prime =
            Vec::<FpVar<Fr>>::new_witness(cs.clone(), || Ok(r_x_prime.clone())).unwrap();
        let gamma_var = FpVar::<Fr>::new_witness(cs.clone(), || Ok(gamma)).unwrap();
        let beta_var = Vec::<FpVar<Fr>>::new_witness(cs.clone(), || Ok(beta.clone())).unwrap();

        let computed_c = compute_c_gadget(
            cs.clone(),
            &ccs,
            vec_sigmas,
            vec_thetas,
            gamma_var,
            beta_var,
            vec_r_x,
            vec_r_x_prime,
        )
        .unwrap();

        assert_eq!(expected_c, computed_c.value().unwrap());
    }

    /// Test that generates mu>1 and nu>1 instances, and folds them in a single multifolding step,
    /// to verify the folding in the NIMFSGadget circuit
    #[test]
    pub fn test_nimfs_gadget_verify() {
        let mut rng = test_rng();

        // Create a basic CCS circuit
        let ccs = get_test_ccs::<Fr>();
        let (pedersen_params, _) =
            Pedersen::<Projective>::setup(&mut rng, ccs.n - ccs.l - 1).unwrap();

        let mu = 32;
        let nu = 42;

        // Generate a mu LCCCS & nu CCCS satisfying witness
        let mut z_lcccs = Vec::new();
        for i in 0..mu {
            let z = get_test_z(i + 3);
            z_lcccs.push(z);
        }
        let mut z_cccs = Vec::new();
        for i in 0..nu {
            let z = get_test_z(nu + i + 3);
            z_cccs.push(z);
        }

        // Create the LCCCS instances out of z_lcccs
        let mut lcccs_instances = Vec::new();
        let mut w_lcccs = Vec::new();
        for z_i in z_lcccs.iter() {
            let (running_instance, w) = ccs
                .to_lcccs::<_, _, Pedersen<Projective>>(&mut rng, &pedersen_params, z_i)
                .unwrap();
            lcccs_instances.push(running_instance);
            w_lcccs.push(w);
        }
        // Create the CCCS instance out of z_cccs
        let mut cccs_instances = Vec::new();
        let mut w_cccs = Vec::new();
        for z_i in z_cccs.iter() {
            let (new_instance, w) = ccs
                .to_cccs::<_, _, Pedersen<Projective>>(&mut rng, &pedersen_params, z_i)
                .unwrap();
            cccs_instances.push(new_instance);
            w_cccs.push(w);
        }

        // Prover's transcript
        let poseidon_config = poseidon_canonical_config::<Fr>();
        let mut transcript_p: PoseidonTranscript<Projective> =
            PoseidonTranscript::<Projective>::new(&poseidon_config);

        // Run the prover side of the multifolding
        let (proof, folded_lcccs, folded_witness, _) =
            NIMFS::<Projective, PoseidonTranscript<Projective>>::prove(
                &mut transcript_p,
                &ccs,
                &lcccs_instances,
                &cccs_instances,
                &w_lcccs,
                &w_cccs,
            )
            .unwrap();

        // Verifier's transcript
        let mut transcript_v: PoseidonTranscript<Projective> =
            PoseidonTranscript::<Projective>::new(&poseidon_config);

        // Run the verifier side of the multifolding
        let folded_lcccs_v = NIMFS::<Projective, PoseidonTranscript<Projective>>::verify(
            &mut transcript_v,
            &ccs,
            &lcccs_instances,
            &cccs_instances,
            proof.clone(),
        )
        .unwrap();
        assert_eq!(folded_lcccs, folded_lcccs_v);

        // Check that the folded LCCCS instance is a valid instance with respect to the folded witness
        folded_lcccs.check_relation(&ccs, &folded_witness).unwrap();

        // allocate circuit inputs
        let cs = ConstraintSystem::<Fr>::new_ref();
        let lcccs_instancesVar =
            Vec::<LCCCSVar<Projective>>::new_witness(cs.clone(), || Ok(lcccs_instances.clone()))
                .unwrap();
        let cccs_instancesVar =
            Vec::<CCCSVar<Projective>>::new_witness(cs.clone(), || Ok(cccs_instances.clone()))
                .unwrap();
        let proofVar =
            ProofVar::<Projective>::new_witness(cs.clone(), || Ok(proof.clone())).unwrap();
        let transcriptVar = PoseidonTranscriptVar::<Fr>::new(cs.clone(), &poseidon_config);

        let enabled = Boolean::<Fr>::new_witness(cs.clone(), || Ok(true)).unwrap();
        let (folded_lcccsVar, _) = NIMFSGadget::<Projective>::verify(
            cs.clone(),
            &ccs,
            transcriptVar,
            &lcccs_instancesVar,
            &cccs_instancesVar,
            proofVar,
            enabled,
        )
        .unwrap();
        assert!(cs.is_satisfied().unwrap());
        assert_eq!(folded_lcccsVar.u.value().unwrap(), folded_lcccs.u);
    }

    /// test that checks the native LCCCS.hash vs the R1CS constraints version
    #[test]
    pub fn test_lcccs_hash() {
        let mut rng = test_rng();
        let poseidon_config = poseidon_canonical_config::<Fr>();

        let ccs = get_test_ccs();
        let z1 = get_test_z::<Fr>(3);

        let (pedersen_params, _) =
            Pedersen::<Projective>::setup(&mut rng, ccs.n - ccs.l - 1).unwrap();

        let i = Fr::from(3_u32);
        let z_0 = vec![Fr::from(3_u32)];
        let z_i = vec![Fr::from(3_u32)];
        let (lcccs, _) = ccs
            .to_lcccs::<_, _, Pedersen<Projective>>(&mut rng, &pedersen_params, &z1)
            .unwrap();
        let h = lcccs
            .clone()
            .hash(&poseidon_config, i, z_0.clone(), z_i.clone())
            .unwrap();

        let cs = ConstraintSystem::<Fr>::new_ref();

        let crh_params = CRHParametersVar::<Fr>::new_constant(cs.clone(), poseidon_config).unwrap();
        let iVar = FpVar::<Fr>::new_witness(cs.clone(), || Ok(i)).unwrap();
        let z_0Var = Vec::<FpVar<Fr>>::new_witness(cs.clone(), || Ok(z_0.clone())).unwrap();
        let z_iVar = Vec::<FpVar<Fr>>::new_witness(cs.clone(), || Ok(z_i.clone())).unwrap();
        let lcccsVar = LCCCSVar::<Projective>::new_witness(cs.clone(), || Ok(lcccs)).unwrap();
        let (hVar, _) = lcccsVar
            .clone()
            .hash(&crh_params, iVar.clone(), z_0Var.clone(), z_iVar.clone())
            .unwrap();
        assert!(cs.is_satisfied().unwrap());

        // check that the natively computed and in-circuit computed hashes match
        assert_eq!(hVar.value().unwrap(), h);
    }

    #[test]
    pub fn test_augmented_f_circuit() {
        let mut rng = test_rng();
        let poseidon_config = poseidon_canonical_config::<Fr>();

        let start = Instant::now();
        let F_circuit = CubicFCircuit::<Fr>::new(()).unwrap();
        let mut augmented_f_circuit = AugmentedFCircuit::<
            Projective,
            Projective2,
            GVar2,
            CubicFCircuit<Fr>,
        >::empty(&poseidon_config, F_circuit, None)
        .unwrap();
        let ccs = augmented_f_circuit.ccs.clone();
        println!("AugmentedFCircuit & CCS generation: {:?}", start.elapsed());
        println!("CCS m x n: {} x {}", ccs.m, ccs.n);

        // CycleFold circuit
        let cs2 = ConstraintSystem::<Fq>::new_ref();
        let cf_circuit = CycleFoldCircuit::<Projective, GVar>::empty();
        cf_circuit.generate_constraints(cs2.clone()).unwrap();
        cs2.finalize();
        let cs2 = cs2
            .into_inner()
            .ok_or(Error::NoInnerConstraintSystem)
            .unwrap();
        let cf_r1cs = extract_r1cs::<Fq>(&cs2);

        let (pedersen_params, _) =
            Pedersen::<Projective>::setup(&mut rng, ccs.n - ccs.l - 1).unwrap();
        let (cf_pedersen_params, _) =
            Pedersen::<Projective2>::setup(&mut rng, cf_r1cs.A.n_cols - cf_r1cs.l - 1).unwrap();

        // first step
        let z_0 = vec![Fr::from(3_u32)];
        let mut z_i = z_0.clone();

        // prepare the dummy instances
        let W_dummy = Witness::<Fr>::dummy(&ccs);
        let U_dummy = LCCCS::<Projective>::dummy(ccs.l, ccs.t, ccs.s);
        let w_dummy = W_dummy.clone();
        let u_dummy = CCCS::<Projective>::dummy(ccs.l);
        let (cf_W_dummy, cf_U_dummy): (NovaWitness<Projective2>, CommittedInstance<Projective2>) =
            cf_r1cs.dummy_instance();

        // set the initial dummy instances
        let mut W_i = W_dummy.clone();
        let mut U_i = U_dummy.clone();
        let mut w_i = w_dummy.clone();
        let mut u_i = u_dummy.clone();
        let mut cf_W_i = cf_W_dummy.clone();
        let mut cf_U_i = cf_U_dummy.clone();
        u_i.x = vec![
            U_i.hash(&poseidon_config, Fr::zero(), z_0.clone(), z_i.clone())
                .unwrap(),
            cf_U_i.hash_cyclefold(&poseidon_config).unwrap(),
        ];

        let n_steps: usize = 4;
        let mut iFr = Fr::zero();
        for i in 0..n_steps {
            let start = Instant::now();
            let mut transcript_p: PoseidonTranscript<Projective> =
                PoseidonTranscript::<Projective>::new(&poseidon_config.clone());
            let (nimfs_proof, U_i1, W_i1, rho_bits) =
                NIMFS::<Projective, PoseidonTranscript<Projective>>::prove(
                    &mut transcript_p,
                    &ccs,
                    &[U_i.clone()],
                    &[u_i.clone()],
                    &[W_i.clone()],
                    &[w_i.clone()],
                )
                .unwrap();

            // sanity check: check the folded instance relation
            U_i1.check_relation(&ccs, &W_i1).unwrap();

            let z_i1 = F_circuit.step_native(i, z_i.clone(), vec![]).unwrap();
            let u_i1_x = U_i1
                .hash(&poseidon_config, iFr + Fr::one(), z_0.clone(), z_i1.clone())
                .unwrap();

            if i == 0 {
                // hash the initial (dummy) CycleFold instance, which is used as the 2nd public
                // input in the AugmentedFCircuit
                let cf_u_i1_x = cf_U_i.hash_cyclefold(&poseidon_config).unwrap();

                augmented_f_circuit =
                    AugmentedFCircuit::<Projective, Projective2, GVar2, CubicFCircuit<Fr>> {
                        _c2: PhantomData,
                        _gc2: PhantomData,
                        poseidon_config: poseidon_config.clone(),
                        ccs: ccs.clone(),
                        i: Some(Fr::zero()),
                        i_usize: Some(0),
                        z_0: Some(z_0.clone()),
                        z_i: Some(z_i.clone()),
                        external_inputs: Some(vec![]),
                        u_i_C: Some(u_i.C),
                        U_i: Some(U_i.clone()),
                        U_i1_C: Some(U_i1.C),
                        F: F_circuit,
                        x: Some(u_i1_x),
                        nimfs_proof: Some(nimfs_proof),

                        // cyclefold values
                        cf_u_i_cmW: None,
                        cf_U_i: None,
                        cf_x: Some(cf_u_i1_x),
                        cf_cmT: None,
                    };
            } else {
                let rho_Fq = Fq::from_bigint(BigInteger::from_bits_le(&rho_bits)).unwrap();
                // CycleFold part:
                // get the vector used as public inputs 'x' in the CycleFold circuit
                // cyclefold circuit for cmW
                let cf_u_i_x = [
                    vec![rho_Fq],
                    get_cm_coordinates(&U_i.C),
                    get_cm_coordinates(&u_i.C),
                    get_cm_coordinates(&U_i1.C),
                ]
                .concat();

                let cf_circuit = CycleFoldCircuit::<Projective, GVar> {
                    _gc: PhantomData,
                    r_bits: Some(rho_bits.clone()),
                    p1: Some(U_i.clone().C),
                    p2: Some(u_i.clone().C),
                    x: Some(cf_u_i_x.clone()),
                };

                let (_cf_w_i, cf_u_i, cf_W_i1, cf_U_i1, cf_cmT, _) = fold_cyclefold_circuit::<
                    Projective,
                    GVar,
                    Projective2,
                    GVar2,
                    CubicFCircuit<Fr>,
                    Pedersen<Projective>,
                    Pedersen<Projective2>,
                >(
                    &poseidon_config,
                    cf_r1cs.clone(),
                    cf_pedersen_params.clone(),
                    cf_W_i.clone(), // CycleFold running instance witness
                    cf_U_i.clone(), // CycleFold running instance
                    cf_u_i_x,       // CycleFold incoming instance
                    cf_circuit,
                )
                .unwrap();

                // hash the CycleFold folded instance, which is used as the 2nd public input in the
                // AugmentedFCircuit
                let cf_u_i1_x = cf_U_i1.hash_cyclefold(&poseidon_config).unwrap();

                augmented_f_circuit =
                    AugmentedFCircuit::<Projective, Projective2, GVar2, CubicFCircuit<Fr>> {
                        _c2: PhantomData,
                        _gc2: PhantomData,
                        poseidon_config: poseidon_config.clone(),
                        ccs: ccs.clone(),
                        i: Some(iFr),
                        i_usize: Some(i),
                        z_0: Some(z_0.clone()),
                        z_i: Some(z_i.clone()),
                        external_inputs: Some(vec![]),
                        u_i_C: Some(u_i.C),
                        U_i: Some(U_i.clone()),
                        U_i1_C: Some(U_i1.C),
                        F: F_circuit,
                        x: Some(u_i1_x),
                        nimfs_proof: Some(nimfs_proof),

                        // cyclefold values
                        cf_u_i_cmW: Some(cf_u_i.cmW),
                        cf_U_i: Some(cf_U_i),
                        cf_x: Some(cf_u_i1_x),
                        cf_cmT: Some(cf_cmT),
                    };

                // assign the next round instances
                cf_W_i = cf_W_i1;
                cf_U_i = cf_U_i1;
            }

            let (cs, _) = augmented_f_circuit.compute_cs_ccs().unwrap();
            assert!(cs.is_satisfied().unwrap());

            let (r1cs_w_i1, r1cs_x_i1) = extract_w_x::<Fr>(&cs); // includes 1 and public inputs
            assert_eq!(r1cs_x_i1[0], augmented_f_circuit.x.unwrap());
            let r1cs_z = [vec![Fr::one()], r1cs_x_i1.clone(), r1cs_w_i1.clone()].concat();
            // compute committed instances, w_{i+1}, u_{i+1}, which will be used as w_i, u_i, so we
            // assign them directly to w_i, u_i.
            (u_i, w_i) = ccs
                .to_cccs::<_, _, Pedersen<Projective>>(&mut rng, &pedersen_params, &r1cs_z)
                .unwrap();
            u_i.check_relation(&ccs, &w_i).unwrap();

            // sanity checks
            assert_eq!(w_i.w, r1cs_w_i1);
            assert_eq!(u_i.x, r1cs_x_i1);
            assert_eq!(u_i.x[0], augmented_f_circuit.x.unwrap());
            assert_eq!(u_i.x[1], augmented_f_circuit.cf_x.unwrap());
            let expected_u_i1_x = U_i1
                .hash(&poseidon_config, iFr + Fr::one(), z_0.clone(), z_i1.clone())
                .unwrap();
            let expected_cf_U_i1_x = cf_U_i.hash_cyclefold(&poseidon_config).unwrap();
            // u_i is already u_i1 at this point, check that has the expected value at x[0]
            assert_eq!(u_i.x[0], expected_u_i1_x);
            assert_eq!(u_i.x[1], expected_cf_U_i1_x);

            // set values for next iteration
            iFr += Fr::one();
            // assign z_{i+1} into z_i
            z_i = z_i1.clone();
            U_i = U_i1.clone();
            W_i = W_i1.clone();

            // check the new LCCCS instance relation
            U_i.check_relation(&ccs, &W_i).unwrap();
            // check the new CCCS instance relation
            u_i.check_relation(&ccs, &w_i).unwrap();

            // check the CycleFold instance relation
            cf_r1cs
                .check_relaxed_instance_relation(&cf_W_i, &cf_U_i)
                .unwrap();

            println!("augmented_f_circuit step {}: {:?}", i, start.elapsed());
        }
    }
}
