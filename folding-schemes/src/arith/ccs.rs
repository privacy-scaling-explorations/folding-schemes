use ark_ff::PrimeField;
use ark_std::log2;

use crate::utils::vec::{hadamard, mat_vec_mul, vec_add, vec_scalar_mul, SparseMatrix};
use crate::Error;

use super::{r1cs::R1CS, Arith};

/// CCS represents the Customizable Constraint Systems structure defined in
/// the [CCS paper](https://eprint.iacr.org/2023/552)
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct CCS<F: PrimeField> {
    /// m: number of rows in M_i (such that M_i \in F^{m, n})
    pub m: usize,
    /// n = |z|, number of cols in M_i
    pub n: usize,
    /// l = |io|, size of public input/output
    pub l: usize,
    /// t = |M|, number of matrices
    pub t: usize,
    /// q = |c| = |S|, number of multisets
    pub q: usize,
    /// d: max degree in each variable
    pub d: usize,
    /// s = log(m), dimension of x
    pub s: usize,
    /// s_prime = log(n), dimension of y
    pub s_prime: usize,

    /// vector of matrices
    pub M: Vec<SparseMatrix<F>>,
    /// vector of multisets
    pub S: Vec<Vec<usize>>,
    /// vector of coefficients
    pub c: Vec<F>,
}

impl<F: PrimeField> Arith<F> for CCS<F> {
    /// check that a CCS structure is satisfied by a z vector. Only for testing.
    fn check_relation(&self, z: &[F]) -> Result<(), Error> {
        let mut result = vec![F::zero(); self.m];

        for i in 0..self.q {
            // extract the needed M_j matrices out of S_i
            let vec_M_j: Vec<&SparseMatrix<F>> = self.S[i].iter().map(|j| &self.M[*j]).collect();

            // complete the hadamard chain
            let mut hadamard_result = vec![F::one(); self.m];
            for M_j in vec_M_j.into_iter() {
                hadamard_result = hadamard(&hadamard_result, &mat_vec_mul(M_j, z)?)?;
            }

            // multiply by the coefficient of this step
            let c_M_j_z = vec_scalar_mul(&hadamard_result, &self.c[i]);

            // add it to the final vector
            result = vec_add(&result, &c_M_j_z)?;
        }

        // make sure the final vector is all zeroes
        for e in result {
            if !e.is_zero() {
                return Err(Error::NotSatisfied);
            }
        }

        Ok(())
    }

    fn params_to_bytes(&self) -> Vec<u8> {
        [
            self.l.to_le_bytes(),
            self.m.to_le_bytes(),
            self.n.to_le_bytes(),
            self.t.to_le_bytes(),
            self.q.to_le_bytes(),
            self.d.to_le_bytes(),
        ]
        .concat()
    }
}

impl<F: PrimeField> CCS<F> {
    pub fn from_r1cs(r1cs: R1CS<F>) -> Self {
        let m = r1cs.A.n_rows;
        let n = r1cs.A.n_cols;
        CCS {
            m,
            n,
            l: r1cs.l,
            s: log2(m) as usize,
            s_prime: log2(n) as usize,
            t: 3,
            q: 2,
            d: 2,

            S: vec![vec![0, 1], vec![2]],
            c: vec![F::one(), F::one().neg()],
            M: vec![r1cs.A, r1cs.B, r1cs.C],
        }
    }

    pub fn to_r1cs(self) -> R1CS<F> {
        R1CS::<F> {
            l: self.l,
            A: self.M[0].clone(),
            B: self.M[1].clone(),
            C: self.M[2].clone(),
        }
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use crate::arith::r1cs::tests::{get_test_r1cs, get_test_z as r1cs_get_test_z};
    use ark_ff::PrimeField;
    use ark_pallas::Fr;

    pub fn get_test_ccs<F: PrimeField>() -> CCS<F> {
        let r1cs = get_test_r1cs::<F>();
        CCS::<F>::from_r1cs(r1cs)
    }
    pub fn get_test_z<F: PrimeField>(input: usize) -> Vec<F> {
        r1cs_get_test_z(input)
    }

    /// Test that a basic CCS relation can be satisfied
    #[test]
    fn test_ccs_relation() {
        let ccs = get_test_ccs::<Fr>();
        let z = get_test_z(3);

        ccs.check_relation(&z).unwrap();
    }
}
