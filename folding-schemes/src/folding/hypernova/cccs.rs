use ark_ec::CurveGroup;
use ark_ff::PrimeField;
use ark_std::One;
use ark_std::Zero;
use std::sync::Arc;

use ark_std::rand::Rng;

use super::Witness;
use crate::ccs::CCS;
use crate::commitment::CommitmentScheme;
use crate::utils::mle::dense_vec_to_dense_mle;
use crate::utils::vec::mat_vec_mul;
use crate::utils::virtual_polynomial::{build_eq_x_r_vec, VirtualPolynomial};
use crate::Error;

/// Committed CCS instance
#[derive(Debug, Clone)]
pub struct CCCS<C: CurveGroup> {
    // Commitment to witness
    pub C: C,
    // Public input/output
    pub x: Vec<C::ScalarField>,
}

impl<F: PrimeField> CCS<F> {
    pub fn to_cccs<R: Rng, C: CurveGroup, CS: CommitmentScheme<C>>(
        &self,
        rng: &mut R,
        cs_params: &CS::ProverParams,
        z: &[C::ScalarField],
    ) -> Result<(CCCS<C>, Witness<C::ScalarField>), Error>
    where
        // enforce that CCS's F is the C::ScalarField
        C: CurveGroup<ScalarField = F>,
    {
        let w: Vec<C::ScalarField> = z[(1 + self.l)..].to_vec();

        // if the commitment scheme is set to be hiding, set the random blinding parameter
        let r_w = if CS::is_hiding() {
            C::ScalarField::rand(rng)
        } else {
            C::ScalarField::zero()
        };
        let C = CS::commit(cs_params, &w, &r_w)?;

        Ok((
            CCCS::<C> {
                C,
                x: z[1..(1 + self.l)].to_vec(),
            },
            Witness::<C::ScalarField> { w, r_w },
        ))
    }

    /// Computes q(x) = \sum^q c_i * \prod_{j \in S_i} ( \sum_{y \in {0,1}^s'} M_j(x, y) * z(y) )
    /// polynomial over x
    pub fn compute_q(&self, z: &[F]) -> Result<VirtualPolynomial<F>, Error> {
        let mut q_x = VirtualPolynomial::<F>::new(self.s);
        for i in 0..self.q {
            let mut Q_k = vec![];
            for &j in self.S[i].iter() {
                Q_k.push(dense_vec_to_dense_mle(self.s, &mat_vec_mul(&self.M[j], z)?));
            }
            q_x.add_mle_list(Q_k.iter().map(|v| Arc::new(v.clone())), self.c[i])?;
        }
        Ok(q_x)
    }

    /// Computes Q(x) = eq(beta, x) * q(x)
    ///               = eq(beta, x) * \sum^q c_i * \prod_{j \in S_i} ( \sum_{y \in {0,1}^s'} M_j(x, y) * z(y) )
    /// polynomial over x
    pub fn compute_Q(&self, z: &[F], beta: &[F]) -> Result<VirtualPolynomial<F>, Error> {
        let eq_beta = build_eq_x_r_vec(beta)?;
        let eq_beta_mle = dense_vec_to_dense_mle(self.s, &eq_beta);

        let mut Q = VirtualPolynomial::<F>::new(self.s);
        for i in 0..self.q {
            let mut Q_k = vec![];
            for &j in self.S[i].iter() {
                Q_k.push(dense_vec_to_dense_mle(self.s, &mat_vec_mul(&self.M[j], z)?));
            }
            Q_k.push(eq_beta_mle.clone());
            Q.add_mle_list(Q_k.iter().map(|v| Arc::new(v.clone())), self.c[i])?;
        }
        Ok(Q)
    }
}

impl<C: CurveGroup> CCCS<C> {
    pub fn dummy(l: usize) -> CCCS<C>
    where
        C::ScalarField: PrimeField,
    {
        CCCS::<C> {
            C: C::zero(),
            x: vec![C::ScalarField::zero(); l],
        }
    }

    /// Perform the check of the CCCS instance described at section 4.1,
    /// notice that this method does not check the commitment correctness
    pub fn check_relation(
        &self,
        ccs: &CCS<C::ScalarField>,
        w: &Witness<C::ScalarField>,
    ) -> Result<(), Error> {
        // check CCCS relation
        let z: Vec<C::ScalarField> =
            [vec![C::ScalarField::one()], self.x.clone(), w.w.to_vec()].concat();

        // A CCCS relation is satisfied if the q(x) multivariate polynomial evaluates to zero in
        // the hypercube, evaluating over the whole boolean hypercube for a normal-sized instance
        // would take too much, this checks the CCS relation of the CCCS.
        ccs.check_relation(&z)?;

        Ok(())
    }
}

#[cfg(test)]
pub mod tests {
    use ark_pallas::Fr;
    use ark_std::test_rng;
    use ark_std::UniformRand;

    use super::*;
    use crate::ccs::tests::{get_test_ccs, get_test_z};
    use crate::utils::hypercube::BooleanHypercube;

    /// Do some sanity checks on q(x). It's a multivariable polynomial and it should evaluate to zero inside the
    /// hypercube, but to not-zero outside the hypercube.
    #[test]
    fn test_compute_q() {
        let mut rng = test_rng();

        let ccs = get_test_ccs::<Fr>();
        let z = get_test_z(3);

        let q = ccs.compute_q(&z).unwrap();

        // Evaluate inside the hypercube
        for x in BooleanHypercube::new(ccs.s) {
            assert_eq!(Fr::zero(), q.evaluate(&x).unwrap());
        }

        // Evaluate outside the hypercube
        let beta: Vec<Fr> = (0..ccs.s).map(|_| Fr::rand(&mut rng)).collect();
        assert_ne!(Fr::zero(), q.evaluate(&beta).unwrap());
    }

    /// Perform some sanity checks on Q(x).
    #[test]
    fn test_compute_Q() {
        let mut rng = test_rng();

        let ccs: CCS<Fr> = get_test_ccs();
        let z = get_test_z(3);
        ccs.check_relation(&z).unwrap();

        let beta: Vec<Fr> = (0..ccs.s).map(|_| Fr::rand(&mut rng)).collect();

        // Compute Q(x) = eq(beta, x) * q(x).
        let Q = ccs.compute_Q(&z, &beta).unwrap();

        // Let's consider the multilinear polynomial G(x) = \sum_{y \in {0, 1}^s} eq(x, y) q(y)
        // which interpolates the multivariate polynomial q(x) inside the hypercube.
        //
        // Observe that summing Q(x) inside the hypercube, directly computes G(\beta).
        //
        // Now, G(x) is multilinear and agrees with q(x) inside the hypercube. Since q(x) vanishes inside the
        // hypercube, this means that G(x) also vanishes in the hypercube. Since G(x) is multilinear and vanishes
        // inside the hypercube, this makes it the zero polynomial.
        //
        // Hence, evaluating G(x) at a random beta should give zero.

        // Now sum Q(x) evaluations in the hypercube and expect it to be 0
        let r = BooleanHypercube::new(ccs.s)
            .map(|x| Q.evaluate(&x).unwrap())
            .fold(Fr::zero(), |acc, result| acc + result);
        assert_eq!(r, Fr::zero());
    }

    /// The polynomial G(x) (see above) interpolates q(x) inside the hypercube.
    /// Summing Q(x) over the hypercube is equivalent to evaluating G(x) at some point.
    /// This test makes sure that G(x) agrees with q(x) inside the hypercube, but not outside
    #[test]
    fn test_Q_against_q() {
        let mut rng = test_rng();

        let ccs: CCS<Fr> = get_test_ccs();
        let z = get_test_z(3);
        ccs.check_relation(&z).unwrap();

        // Now test that if we create Q(x) with eq(d,y) where d is inside the hypercube, \sum Q(x) should be G(d) which
        // should be equal to q(d), since G(x) interpolates q(x) inside the hypercube
        let q = ccs.compute_q(&z).unwrap();
        for d in BooleanHypercube::new(ccs.s) {
            let Q_at_d = ccs.compute_Q(&z, &d).unwrap();

            // Get G(d) by summing over Q_d(x) over the hypercube
            let G_at_d = BooleanHypercube::new(ccs.s)
                .map(|x| Q_at_d.evaluate(&x).unwrap())
                .fold(Fr::zero(), |acc, result| acc + result);
            assert_eq!(G_at_d, q.evaluate(&d).unwrap());
        }

        // Now test that they should disagree outside of the hypercube
        let r: Vec<Fr> = (0..ccs.s).map(|_| Fr::rand(&mut rng)).collect();
        let Q_at_r = ccs.compute_Q(&z, &r).unwrap();

        // Get G(d) by summing over Q_d(x) over the hypercube
        let G_at_r = BooleanHypercube::new(ccs.s)
            .map(|x| Q_at_r.evaluate(&x).unwrap())
            .fold(Fr::zero(), |acc, result| acc + result);
        assert_ne!(G_at_r, q.evaluate(&r).unwrap());
    }
}
