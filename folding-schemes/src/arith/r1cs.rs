use ark_ff::PrimeField;
use ark_relations::r1cs::ConstraintSystem;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::rand::Rng;

use super::Arith;
use crate::utils::vec::{hadamard, mat_vec_mul, vec_add, vec_scalar_mul, SparseMatrix};
use crate::Error;

#[derive(Debug, Clone, Eq, PartialEq, CanonicalSerialize, CanonicalDeserialize)]
pub struct R1CS<F: PrimeField> {
    pub l: usize, // io len
    pub A: SparseMatrix<F>,
    pub B: SparseMatrix<F>,
    pub C: SparseMatrix<F>,
}

impl<F: PrimeField> Arith<F> for R1CS<F> {
    /// check that a R1CS structure is satisfied by a z vector. Only for testing.
    fn check_relation(&self, z: &[F]) -> Result<(), Error> {
        let Az = mat_vec_mul(&self.A, z)?;
        let Bz = mat_vec_mul(&self.B, z)?;
        let Cz = mat_vec_mul(&self.C, z)?;
        let AzBz = hadamard(&Az, &Bz)?;
        if AzBz != Cz {
            return Err(Error::NotSatisfied);
        }
        Ok(())
    }

    fn params_to_bytes(&self) -> Vec<u8> {
        [
            self.l.to_le_bytes(),
            self.A.n_rows.to_le_bytes(),
            self.A.n_cols.to_le_bytes(),
        ]
        .concat()
    }
}

impl<F: PrimeField> R1CS<F> {
    pub fn rand<R: Rng>(rng: &mut R, n_rows: usize, n_cols: usize) -> Self {
        Self {
            l: 1,
            A: SparseMatrix::rand(rng, n_rows, n_cols),
            B: SparseMatrix::rand(rng, n_rows, n_cols),
            C: SparseMatrix::rand(rng, n_rows, n_cols),
        }
    }

    /// returns a tuple containing (w, x) (witness and public inputs respectively)
    pub fn split_z(&self, z: &[F]) -> (Vec<F>, Vec<F>) {
        (z[self.l + 1..].to_vec(), z[1..self.l + 1].to_vec())
    }

    /// converts the R1CS instance into a RelaxedR1CS as described in
    /// [Nova](https://eprint.iacr.org/2021/370.pdf) section 4.1.
    pub fn relax(self) -> RelaxedR1CS<F> {
        RelaxedR1CS::<F> {
            l: self.l,
            E: vec![F::zero(); self.A.n_rows],
            A: self.A,
            B: self.B,
            C: self.C,
            u: F::one(),
        }
    }
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct RelaxedR1CS<F: PrimeField> {
    pub l: usize, // io len
    pub A: SparseMatrix<F>,
    pub B: SparseMatrix<F>,
    pub C: SparseMatrix<F>,
    pub u: F,
    pub E: Vec<F>,
}

impl<F: PrimeField> RelaxedR1CS<F> {
    /// check that a RelaxedR1CS structure is satisfied by a z vector. Only for testing.
    pub fn check_relation(&self, z: &[F]) -> Result<(), Error> {
        let Az = mat_vec_mul(&self.A, z)?;
        let Bz = mat_vec_mul(&self.B, z)?;
        let Cz = mat_vec_mul(&self.C, z)?;
        let uCz = vec_scalar_mul(&Cz, &self.u);
        let uCzE = vec_add(&uCz, &self.E)?;
        let AzBz = hadamard(&Az, &Bz)?;
        if AzBz != uCzE {
            return Err(Error::NotSatisfied);
        }

        Ok(())
    }
}

/// extracts arkworks ConstraintSystem matrices into crate::utils::vec::SparseMatrix format as R1CS
/// struct.
pub fn extract_r1cs<F: PrimeField>(cs: &ConstraintSystem<F>) -> R1CS<F> {
    let m = cs.to_matrices().unwrap();

    let n_rows = cs.num_constraints;
    let n_cols = cs.num_instance_variables + cs.num_witness_variables; // cs.num_instance_variables already counts the 1

    let A = SparseMatrix::<F> {
        n_rows,
        n_cols,
        coeffs: m.a,
    };
    let B = SparseMatrix::<F> {
        n_rows,
        n_cols,
        coeffs: m.b,
    };
    let C = SparseMatrix::<F> {
        n_rows,
        n_cols,
        coeffs: m.c,
    };

    R1CS::<F> {
        l: cs.num_instance_variables - 1, // -1 to subtract the first '1'
        A,
        B,
        C,
    }
}

/// extracts the witness and the public inputs from arkworks ConstraintSystem.
pub fn extract_w_x<F: PrimeField>(cs: &ConstraintSystem<F>) -> (Vec<F>, Vec<F>) {
    (
        cs.witness_assignment.clone(),
        // skip the first element which is '1'
        cs.instance_assignment[1..].to_vec(),
    )
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use crate::utils::vec::tests::{to_F_matrix, to_F_vec};

    use ark_ff::PrimeField;
    use ark_pallas::Fr;

    pub fn get_test_r1cs<F: PrimeField>() -> R1CS<F> {
        // R1CS for: x^3 + x + 5 = y (example from article
        // https://www.vitalik.ca/general/2016/12/10/qap.html )
        let A = to_F_matrix::<F>(vec![
            vec![0, 1, 0, 0, 0, 0],
            vec![0, 0, 0, 1, 0, 0],
            vec![0, 1, 0, 0, 1, 0],
            vec![5, 0, 0, 0, 0, 1],
        ]);
        let B = to_F_matrix::<F>(vec![
            vec![0, 1, 0, 0, 0, 0],
            vec![0, 1, 0, 0, 0, 0],
            vec![1, 0, 0, 0, 0, 0],
            vec![1, 0, 0, 0, 0, 0],
        ]);
        let C = to_F_matrix::<F>(vec![
            vec![0, 0, 0, 1, 0, 0],
            vec![0, 0, 0, 0, 1, 0],
            vec![0, 0, 0, 0, 0, 1],
            vec![0, 0, 1, 0, 0, 0],
        ]);

        R1CS::<F> { l: 1, A, B, C }
    }

    pub fn get_test_z<F: PrimeField>(input: usize) -> Vec<F> {
        // z = (1, io, w)
        to_F_vec(vec![
            1,
            input,                             // io
            input * input * input + input + 5, // x^3 + x + 5
            input * input,                     // x^2
            input * input * input,             // x^2 * x
            input * input * input + input,     // x^3 + x
        ])
    }

    #[test]
    fn test_check_relation() {
        let r1cs = get_test_r1cs::<Fr>();
        let z = get_test_z(5);
        r1cs.check_relation(&z).unwrap();
        r1cs.relax().check_relation(&z).unwrap();
    }
}
