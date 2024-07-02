use ark_crypto_primitives::sponge::Absorb;
use ark_ec::{CurveGroup, Group};
use ark_std::Zero;
use std::marker::PhantomData;

use super::{CommittedInstance, Witness};
use crate::arith::r1cs::R1CS;
use crate::commitment::CommitmentScheme;
use crate::transcript::Transcript;
use crate::utils::vec::{hadamard, mat_vec_mul, vec_add, vec_scalar_mul, vec_sub};
use crate::Error;

/// Implements the Non-Interactive Folding Scheme described in section 4 of
/// [Nova](https://eprint.iacr.org/2021/370.pdf)
pub struct NIFS<C: CurveGroup, CS: CommitmentScheme<C>> {
    _c: PhantomData<C>,
    _cp: PhantomData<CS>,
}

impl<C: CurveGroup, CS: CommitmentScheme<C>> NIFS<C, CS>
where
    <C as Group>::ScalarField: Absorb,
{
    // compute_T: compute cross-terms T
    pub fn compute_T(
        r1cs: &R1CS<C::ScalarField>,
        u1: C::ScalarField,
        u2: C::ScalarField,
        z1: &[C::ScalarField],
        z2: &[C::ScalarField],
    ) -> Result<Vec<C::ScalarField>, Error> {
        let (A, B, C) = (r1cs.A.clone(), r1cs.B.clone(), r1cs.C.clone());

        // this is parallelizable (for the future)
        let Az1 = mat_vec_mul(&A, z1)?;
        let Bz1 = mat_vec_mul(&B, z1)?;
        let Cz1 = mat_vec_mul(&C, z1)?;
        let Az2 = mat_vec_mul(&A, z2)?;
        let Bz2 = mat_vec_mul(&B, z2)?;
        let Cz2 = mat_vec_mul(&C, z2)?;

        let Az1_Bz2 = hadamard(&Az1, &Bz2)?;
        let Az2_Bz1 = hadamard(&Az2, &Bz1)?;
        let u1Cz2 = vec_scalar_mul(&Cz2, &u1);
        let u2Cz1 = vec_scalar_mul(&Cz1, &u2);

        vec_sub(&vec_sub(&vec_add(&Az1_Bz2, &Az2_Bz1)?, &u1Cz2)?, &u2Cz1)
    }

    pub fn fold_witness(
        r: C::ScalarField,
        w1: &Witness<C>,
        w2: &Witness<C>,
        T: &[C::ScalarField],
        rT: C::ScalarField,
    ) -> Result<Witness<C>, Error> {
        let r2 = r * r;
        let E: Vec<C::ScalarField> = vec_add(
            &vec_add(&w1.E, &vec_scalar_mul(T, &r))?,
            &vec_scalar_mul(&w2.E, &r2),
        )?;
        let rE = w1.rE + r * rT + r2 * w2.rE;
        let W: Vec<C::ScalarField> = w1.W.iter().zip(&w2.W).map(|(a, b)| *a + (r * b)).collect();

        let rW = w1.rW + r * w2.rW;
        Ok(Witness::<C> { E, rE, W, rW })
    }

    pub fn fold_committed_instance(
        r: C::ScalarField,
        ci1: &CommittedInstance<C>, // U_i
        ci2: &CommittedInstance<C>, // u_i
        cmT: &C,
    ) -> CommittedInstance<C> {
        let r2 = r * r;
        let cmE = ci1.cmE + cmT.mul(r) + ci2.cmE.mul(r2);
        let u = ci1.u + r * ci2.u;
        let cmW = ci1.cmW + ci2.cmW.mul(r);
        let x = ci1
            .x
            .iter()
            .zip(&ci2.x)
            .map(|(a, b)| *a + (r * b))
            .collect::<Vec<C::ScalarField>>();

        CommittedInstance::<C> { cmE, u, cmW, x }
    }

    /// NIFS.P is the consecutive combination of compute_cmT with fold_instances

    /// compute_cmT is part of the NIFS.P logic
    pub fn compute_cmT(
        cs_prover_params: &CS::ProverParams,
        r1cs: &R1CS<C::ScalarField>,
        w1: &Witness<C>,
        ci1: &CommittedInstance<C>,
        w2: &Witness<C>,
        ci2: &CommittedInstance<C>,
    ) -> Result<(Vec<C::ScalarField>, C), Error> {
        let z1: Vec<C::ScalarField> = [vec![ci1.u], ci1.x.to_vec(), w1.W.to_vec()].concat();
        let z2: Vec<C::ScalarField> = [vec![ci2.u], ci2.x.to_vec(), w2.W.to_vec()].concat();

        // compute cross terms
        let T = Self::compute_T(r1cs, ci1.u, ci2.u, &z1, &z2)?;
        // use r_T=0 since we don't need hiding property for cm(T)
        let cmT = CS::commit(cs_prover_params, &T, &C::ScalarField::zero())?;
        Ok((T, cmT))
    }
    pub fn compute_cyclefold_cmT(
        cs_prover_params: &CS::ProverParams,
        r1cs: &R1CS<C::ScalarField>, // R1CS over C2.Fr=C1.Fq (here C=C2)
        w1: &Witness<C>,
        ci1: &CommittedInstance<C>,
        w2: &Witness<C>,
        ci2: &CommittedInstance<C>,
    ) -> Result<(Vec<C::ScalarField>, C), Error>
    where
        <C as ark_ec::CurveGroup>::BaseField: ark_ff::PrimeField,
    {
        let z1: Vec<C::ScalarField> = [vec![ci1.u], ci1.x.to_vec(), w1.W.to_vec()].concat();
        let z2: Vec<C::ScalarField> = [vec![ci2.u], ci2.x.to_vec(), w2.W.to_vec()].concat();

        // compute cross terms
        let T = Self::compute_T(r1cs, ci1.u, ci2.u, &z1, &z2)?;
        // use r_T=0 since we don't need hiding property for cm(T)
        let cmT = CS::commit(cs_prover_params, &T, &C::ScalarField::zero())?;
        Ok((T, cmT))
    }

    /// fold_instances is part of the NIFS.P logic described in
    /// [Nova](https://eprint.iacr.org/2021/370.pdf)'s section 4. It returns the folded Committed
    /// Instances and the Witness.
    pub fn fold_instances(
        r: C::ScalarField,
        w1: &Witness<C>,
        ci1: &CommittedInstance<C>,
        w2: &Witness<C>,
        ci2: &CommittedInstance<C>,
        T: &[C::ScalarField],
        cmT: C,
    ) -> Result<(Witness<C>, CommittedInstance<C>), Error> {
        // fold witness
        // use r_T=0 since we don't need hiding property for cm(T)
        let w3 = NIFS::<C, CS>::fold_witness(r, w1, w2, T, C::ScalarField::zero())?;

        // fold committed instances
        let ci3 = NIFS::<C, CS>::fold_committed_instance(r, ci1, ci2, &cmT);

        Ok((w3, ci3))
    }

    /// verify implements NIFS.V logic described in [Nova](https://eprint.iacr.org/2021/370.pdf)'s
    /// section 4. It returns the folded Committed Instance
    pub fn verify(
        // r comes from the transcript, and is a n-bit (N_BITS_CHALLENGE) element
        r: C::ScalarField,
        ci1: &CommittedInstance<C>,
        ci2: &CommittedInstance<C>,
        cmT: &C,
    ) -> CommittedInstance<C> {
        NIFS::<C, CS>::fold_committed_instance(r, ci1, ci2, cmT)
    }

    /// Verify committed folded instance (ci) relations. Notice that this method does not open the
    /// commitments, but just checks that the given committed instances (ci1, ci2) when folded
    /// result in the folded committed instance (ci3) values.
    pub fn verify_folded_instance(
        r: C::ScalarField,
        ci1: &CommittedInstance<C>,
        ci2: &CommittedInstance<C>,
        ci3: &CommittedInstance<C>,
        cmT: &C,
    ) -> Result<(), Error> {
        let expected = Self::fold_committed_instance(r, ci1, ci2, cmT);
        if ci3.cmE != expected.cmE
            || ci3.u != expected.u
            || ci3.cmW != expected.cmW
            || ci3.x != expected.x
        {
            return Err(Error::NotSatisfied);
        }
        Ok(())
    }

    pub fn prove_commitments(
        tr: &mut impl Transcript<C>,
        cs_prover_params: &CS::ProverParams,
        w: &Witness<C>,
        ci: &CommittedInstance<C>,
        T: Vec<C::ScalarField>,
        cmT: &C,
    ) -> Result<[CS::Proof; 3], Error> {
        let cmE_proof = CS::prove(cs_prover_params, tr, &ci.cmE, &w.E, &w.rE, None)?;
        let cmW_proof = CS::prove(cs_prover_params, tr, &ci.cmW, &w.W, &w.rW, None)?;
        let cmT_proof = CS::prove(cs_prover_params, tr, cmT, &T, &C::ScalarField::zero(), None)?; // cm(T) is committed with rT=0
        Ok([cmE_proof, cmW_proof, cmT_proof])
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use ark_crypto_primitives::sponge::poseidon::PoseidonConfig;
    use ark_ff::{BigInteger, PrimeField};
    use ark_pallas::{Fr, Projective};
    use ark_std::{ops::Mul, UniformRand};

    use crate::arith::r1cs::tests::{get_test_r1cs, get_test_z};
    use crate::commitment::pedersen::{Params as PedersenParams, Pedersen};
    use crate::folding::nova::circuits::ChallengeGadget;
    use crate::folding::nova::traits::NovaR1CS;
    use crate::transcript::poseidon::{poseidon_canonical_config, PoseidonTranscript};

    #[allow(clippy::type_complexity)]
    pub(crate) fn prepare_simple_fold_inputs<C>() -> (
        PedersenParams<C>,
        PoseidonConfig<C::ScalarField>,
        R1CS<C::ScalarField>,
        Witness<C>,           // w1
        CommittedInstance<C>, // ci1
        Witness<C>,           // w2
        CommittedInstance<C>, // ci2
        Witness<C>,           // w3
        CommittedInstance<C>, // ci3
        Vec<C::ScalarField>,  // T
        C,                    // cmT
        Vec<bool>,            // r_bits
        C::ScalarField,       // r_Fr
    )
    where
        C: CurveGroup,
        <C as CurveGroup>::BaseField: PrimeField,
        C::ScalarField: Absorb,
    {
        let r1cs = get_test_r1cs();
        let z1 = get_test_z(3);
        let z2 = get_test_z(4);
        let (w1, x1) = r1cs.split_z(&z1);
        let (w2, x2) = r1cs.split_z(&z2);

        let w1 = Witness::<C>::new(w1.clone(), r1cs.A.n_rows);
        let w2 = Witness::<C>::new(w2.clone(), r1cs.A.n_rows);

        let mut rng = ark_std::test_rng();
        let (pedersen_params, _) = Pedersen::<C>::setup(&mut rng, r1cs.A.n_cols).unwrap();

        // compute committed instances
        let ci1 = w1
            .commit::<Pedersen<C>>(&pedersen_params, x1.clone())
            .unwrap();
        let ci2 = w2
            .commit::<Pedersen<C>>(&pedersen_params, x2.clone())
            .unwrap();

        // NIFS.P
        let (T, cmT) =
            NIFS::<C, Pedersen<C>>::compute_cmT(&pedersen_params, &r1cs, &w1, &ci1, &w2, &ci2)
                .unwrap();

        let poseidon_config = poseidon_canonical_config::<C::ScalarField>();

        let pp_hash = C::ScalarField::from(42u32); // only for test
        let r_bits = ChallengeGadget::<C>::get_challenge_native(
            &poseidon_config,
            pp_hash,
            ci1.clone(),
            ci2.clone(),
            cmT,
        )
        .unwrap();
        let r_Fr = C::ScalarField::from_bigint(BigInteger::from_bits_le(&r_bits)).unwrap();

        let (w3, ci3) =
            NIFS::<C, Pedersen<C>>::fold_instances(r_Fr, &w1, &ci1, &w2, &ci2, &T, cmT).unwrap();

        (
            pedersen_params,
            poseidon_config,
            r1cs,
            w1,
            ci1,
            w2,
            ci2,
            w3,
            ci3,
            T,
            cmT,
            r_bits,
            r_Fr,
        )
    }

    // fold 2 dummy instances and check that the folded instance holds the relaxed R1CS relation
    #[test]
    fn test_nifs_fold_dummy() {
        let r1cs = get_test_r1cs::<Fr>();
        let z1 = get_test_z(3);
        let (w1, x1) = r1cs.split_z(&z1);

        let mut rng = ark_std::test_rng();
        let (pedersen_params, _) = Pedersen::<Projective>::setup(&mut rng, r1cs.A.n_cols).unwrap();

        // dummy instance, witness and public inputs zeroes
        let w_dummy = Witness::<Projective>::new(vec![Fr::zero(); w1.len()], r1cs.A.n_rows);
        let mut u_dummy = w_dummy
            .commit::<Pedersen<Projective>>(&pedersen_params, vec![Fr::zero(); x1.len()])
            .unwrap();
        u_dummy.u = Fr::zero();

        let w_i = w_dummy.clone();
        let u_i = u_dummy.clone();
        let W_i = w_dummy.clone();
        let U_i = u_dummy.clone();
        r1cs.check_relaxed_instance_relation(&w_i, &u_i).unwrap();
        r1cs.check_relaxed_instance_relation(&W_i, &U_i).unwrap();

        let r_Fr = Fr::from(3_u32);

        let (T, cmT) = NIFS::<Projective, Pedersen<Projective>>::compute_cmT(
            &pedersen_params,
            &r1cs,
            &w_i,
            &u_i,
            &W_i,
            &U_i,
        )
        .unwrap();
        let (W_i1, U_i1) = NIFS::<Projective, Pedersen<Projective>>::fold_instances(
            r_Fr, &w_i, &u_i, &W_i, &U_i, &T, cmT,
        )
        .unwrap();
        r1cs.check_relaxed_instance_relation(&W_i1, &U_i1).unwrap();
    }

    // fold 2 instances into one
    #[test]
    fn test_nifs_one_fold() {
        let (pedersen_params, poseidon_config, r1cs, w1, ci1, w2, ci2, w3, ci3, T, cmT, _, r) =
            prepare_simple_fold_inputs();

        // NIFS.V
        let ci3_v = NIFS::<Projective, Pedersen<Projective>>::verify(r, &ci1, &ci2, &cmT);
        assert_eq!(ci3_v, ci3);

        // check that relations hold for the 2 inputted instances and the folded one
        r1cs.check_relaxed_instance_relation(&w1, &ci1).unwrap();
        r1cs.check_relaxed_instance_relation(&w2, &ci2).unwrap();
        r1cs.check_relaxed_instance_relation(&w3, &ci3).unwrap();

        // check that folded commitments from folded instance (ci) are equal to folding the
        // use folded rE, rW to commit w3
        let ci3_expected = w3
            .commit::<Pedersen<Projective>>(&pedersen_params, ci3.x.clone())
            .unwrap();
        assert_eq!(ci3_expected.cmE, ci3.cmE);
        assert_eq!(ci3_expected.cmW, ci3.cmW);

        // next equalities should hold since we started from two cmE of zero-vector E's
        assert_eq!(ci3.cmE, cmT.mul(r));
        assert_eq!(w3.E, vec_scalar_mul(&T, &r));

        // NIFS.Verify_Folded_Instance:
        NIFS::<Projective, Pedersen<Projective>>::verify_folded_instance(r, &ci1, &ci2, &ci3, &cmT)
            .unwrap();

        // init Prover's transcript
        let mut transcript_p = PoseidonTranscript::<Projective>::new(&poseidon_config);
        // init Verifier's transcript
        let mut transcript_v = PoseidonTranscript::<Projective>::new(&poseidon_config);

        // prove the ci3.cmE, ci3.cmW, cmT commitments
        let cm_proofs = NIFS::<Projective, Pedersen<Projective>>::prove_commitments(
            &mut transcript_p,
            &pedersen_params,
            &w3,
            &ci3,
            T,
            &cmT,
        )
        .unwrap();

        // verify the ci3.cmE, ci3.cmW, cmT commitments
        assert_eq!(cm_proofs.len(), 3);
        Pedersen::<Projective>::verify(
            &pedersen_params,
            &mut transcript_v,
            &ci3.cmE,
            &cm_proofs[0].clone(),
        )
        .unwrap();
        Pedersen::<Projective>::verify(
            &pedersen_params,
            &mut transcript_v,
            &ci3.cmW,
            &cm_proofs[1].clone(),
        )
        .unwrap();
        Pedersen::<Projective>::verify(
            &pedersen_params,
            &mut transcript_v,
            &cmT,
            &cm_proofs[2].clone(),
        )
        .unwrap();
    }

    #[test]
    fn test_nifs_fold_loop() {
        let r1cs = get_test_r1cs();
        let z = get_test_z(3);
        let (w, x) = r1cs.split_z(&z);

        let mut rng = ark_std::test_rng();
        let (pedersen_params, _) = Pedersen::<Projective>::setup(&mut rng, r1cs.A.n_cols).unwrap();

        // prepare the running instance
        let mut running_instance_w = Witness::<Projective>::new(w.clone(), r1cs.A.n_rows);
        let mut running_committed_instance = running_instance_w
            .commit::<Pedersen<Projective>>(&pedersen_params, x)
            .unwrap();

        r1cs.check_relaxed_instance_relation(&running_instance_w, &running_committed_instance)
            .unwrap();

        let num_iters = 10;
        for i in 0..num_iters {
            // prepare the incoming instance
            let incoming_instance_z = get_test_z(i + 4);
            let (w, x) = r1cs.split_z(&incoming_instance_z);
            let incoming_instance_w = Witness::<Projective>::new(w.clone(), r1cs.A.n_rows);
            let incoming_committed_instance = incoming_instance_w
                .commit::<Pedersen<Projective>>(&pedersen_params, x)
                .unwrap();
            r1cs.check_relaxed_instance_relation(
                &incoming_instance_w,
                &incoming_committed_instance,
            )
            .unwrap();

            let r = Fr::rand(&mut rng); // folding challenge would come from the RO

            // NIFS.P
            let (T, cmT) = NIFS::<Projective, Pedersen<Projective>>::compute_cmT(
                &pedersen_params,
                &r1cs,
                &running_instance_w,
                &running_committed_instance,
                &incoming_instance_w,
                &incoming_committed_instance,
            )
            .unwrap();
            let (folded_w, _) = NIFS::<Projective, Pedersen<Projective>>::fold_instances(
                r,
                &running_instance_w,
                &running_committed_instance,
                &incoming_instance_w,
                &incoming_committed_instance,
                &T,
                cmT,
            )
            .unwrap();

            // NIFS.V
            let folded_committed_instance = NIFS::<Projective, Pedersen<Projective>>::verify(
                r,
                &running_committed_instance,
                &incoming_committed_instance,
                &cmT,
            );

            r1cs.check_relaxed_instance_relation(&folded_w, &folded_committed_instance)
                .unwrap();

            // set running_instance for next loop iteration
            running_instance_w = folded_w;
            running_committed_instance = folded_committed_instance;
        }
    }
}
