use ark_ff::PrimeField;
use ark_r1cs_std::{
    alloc::{AllocVar, AllocationMode},
    fields::FieldVar,
};
use ark_relations::r1cs::{Namespace, SynthesisError};
use core::{borrow::Borrow, marker::PhantomData};

use crate::utils::vec::SparseMatrix;

pub fn mat_vec_mul_sparse<F: PrimeField, CF: PrimeField, FV: FieldVar<F, CF>>(
    m: SparseMatrixVar<F, CF, FV>,
    v: Vec<FV>,
) -> Vec<FV> {
    let mut res = vec![FV::zero(); m.n_rows];
    for (row_i, row) in m.coeffs.iter().enumerate() {
        for (value, col_i) in row.iter() {
            res[row_i] += value.clone().mul(&v[*col_i].clone());
        }
    }
    res
}
pub fn vec_add<F: PrimeField, CF: PrimeField, FV: FieldVar<F, CF>>(
    a: &Vec<FV>,
    b: &Vec<FV>,
) -> Result<Vec<FV>, SynthesisError> {
    if a.len() != b.len() {
        return Err(SynthesisError::Unsatisfiable);
    }
    let mut r: Vec<FV> = vec![FV::zero(); a.len()];
    for i in 0..a.len() {
        r[i] = a[i].clone() + b[i].clone();
    }
    Ok(r)
}
pub fn vec_scalar_mul<F: PrimeField, CF: PrimeField, FV: FieldVar<F, CF>>(
    vec: &Vec<FV>,
    c: &FV,
) -> Vec<FV> {
    let mut result = vec![FV::zero(); vec.len()];
    for (i, a) in vec.iter().enumerate() {
        result[i] = a.clone() * c;
    }
    result
}
pub fn hadamard<F: PrimeField, CF: PrimeField, FV: FieldVar<F, CF>>(
    a: &Vec<FV>,
    b: &Vec<FV>,
) -> Result<Vec<FV>, SynthesisError> {
    if a.len() != b.len() {
        return Err(SynthesisError::Unsatisfiable);
    }
    let mut r: Vec<FV> = vec![FV::zero(); a.len()];
    for i in 0..a.len() {
        r[i] = a[i].clone() * b[i].clone();
    }
    Ok(r)
}

#[derive(Debug, Clone)]
pub struct SparseMatrixVar<F: PrimeField, CF: PrimeField, FV: FieldVar<F, CF>> {
    _f: PhantomData<F>,
    _cf: PhantomData<CF>,
    _fv: PhantomData<FV>,
    pub n_rows: usize,
    pub n_cols: usize,
    // same format as the native SparseMatrix (which follows ark_relations::r1cs::Matrix format
    pub coeffs: Vec<Vec<(FV, usize)>>,
}

impl<F, CF, FV> AllocVar<SparseMatrix<F>, CF> for SparseMatrixVar<F, CF, FV>
where
    F: PrimeField,
    CF: PrimeField,
    FV: FieldVar<F, CF>,
{
    fn new_variable<T: Borrow<SparseMatrix<F>>>(
        cs: impl Into<Namespace<CF>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        f().and_then(|val| {
            let cs = cs.into();

            let mut coeffs: Vec<Vec<(FV, usize)>> = Vec::new();
            for row in val.borrow().coeffs.iter() {
                let mut rowVar: Vec<(FV, usize)> = Vec::new();
                for &(value, col_i) in row.iter() {
                    let coeffVar = FV::new_variable(cs.clone(), || Ok(value), mode)?;
                    rowVar.push((coeffVar, col_i));
                }
                coeffs.push(rowVar);
            }

            Ok(Self {
                _f: PhantomData,
                _cf: PhantomData,
                _fv: PhantomData,
                n_rows: val.borrow().n_rows,
                n_cols: val.borrow().n_cols,
                coeffs,
            })
        })
    }
}
