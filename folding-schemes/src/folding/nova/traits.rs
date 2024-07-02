use ark_crypto_primitives::sponge::Absorb;
use ark_ec::{CurveGroup, Group};
use ark_std::{One, Zero};

use super::{CommittedInstance, Witness};
use crate::arith::{r1cs::R1CS, Arith};
use crate::Error;

/// NovaR1CS extends R1CS methods with Nova specific methods
pub trait NovaR1CS<C: CurveGroup> {
    /// returns a dummy instance (Witness and CommittedInstance) for the current R1CS structure
    fn dummy_instance(&self) -> (Witness<C>, CommittedInstance<C>);

    /// checks the R1CS relation (un-relaxed) for the given Witness and CommittedInstance.
    fn check_instance_relation(
        &self,
        W: &Witness<C>,
        U: &CommittedInstance<C>,
    ) -> Result<(), Error>;

    /// checks the Relaxed R1CS relation (corresponding to the current R1CS) for the given Witness
    /// and CommittedInstance.
    fn check_relaxed_instance_relation(
        &self,
        W: &Witness<C>,
        U: &CommittedInstance<C>,
    ) -> Result<(), Error>;
}

impl<C: CurveGroup> NovaR1CS<C> for R1CS<C::ScalarField>
where
    <C as Group>::ScalarField: Absorb,
    <C as ark_ec::CurveGroup>::BaseField: ark_ff::PrimeField,
{
    fn dummy_instance(&self) -> (Witness<C>, CommittedInstance<C>) {
        let w_len = self.A.n_cols - 1 - self.l;
        let w_dummy = Witness::<C>::new(vec![C::ScalarField::zero(); w_len], self.A.n_rows);
        let u_dummy = CommittedInstance::<C>::dummy(self.l);
        (w_dummy, u_dummy)
    }

    // notice that this method does not check the commitment correctness
    fn check_instance_relation(
        &self,
        W: &Witness<C>,
        U: &CommittedInstance<C>,
    ) -> Result<(), Error> {
        if U.cmE != C::zero() || U.u != C::ScalarField::one() {
            return Err(Error::R1CSUnrelaxedFail);
        }

        let Z: Vec<C::ScalarField> = [vec![U.u], U.x.to_vec(), W.W.to_vec()].concat();
        self.check_relation(&Z)
    }

    // notice that this method does not check the commitment correctness
    fn check_relaxed_instance_relation(
        &self,
        W: &Witness<C>,
        U: &CommittedInstance<C>,
    ) -> Result<(), Error> {
        let mut rel_r1cs = self.clone().relax();
        rel_r1cs.u = U.u;
        rel_r1cs.E = W.E.clone();

        let Z: Vec<C::ScalarField> = [vec![U.u], U.x.to_vec(), W.W.to_vec()].concat();
        rel_r1cs.check_relation(&Z)
    }
}
