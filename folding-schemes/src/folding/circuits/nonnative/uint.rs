use std::{
    borrow::Borrow,
    cmp::{max, min},
};

use ark_ff::{BigInteger, Field, One, PrimeField, Zero};
use ark_r1cs_std::{
    alloc::{AllocVar, AllocationMode},
    boolean::Boolean,
    fields::{fp::FpVar, FieldVar},
    prelude::EqGadget,
    select::CondSelectGadget,
    R1CSVar, ToBitsGadget, ToConstraintFieldGadget,
};
use ark_relations::r1cs::{ConstraintSystemRef, Namespace, SynthesisError};
use num_bigint::BigUint;
use num_integer::Integer;

use crate::utils::gadgets::{MatrixGadget, SparseMatrixVar, VectorGadget};

/// `LimbVar` represents a single limb of a non-native unsigned integer in the
/// circuit.
/// The limb value `v` should be small enough to fit into `FpVar`, and we also
/// store an upper bound `ub` for the limb value, which is treated as a constant
/// in the circuit and is used for efficient equality checks and some arithmetic
/// operations.
#[derive(Debug, Clone)]
pub struct LimbVar<F: PrimeField> {
    pub v: FpVar<F>,
    pub ub: BigUint,
}

impl<F: PrimeField, B: AsRef<[Boolean<F>]>> From<B> for LimbVar<F> {
    fn from(bits: B) -> Self {
        Self {
            v: Boolean::le_bits_to_fp_var(bits.as_ref()).unwrap(),
            ub: (BigUint::one() << bits.as_ref().len()) - BigUint::one(),
        }
    }
}

impl<F: PrimeField> Default for LimbVar<F> {
    fn default() -> Self {
        Self {
            v: FpVar::zero(),
            ub: BigUint::zero(),
        }
    }
}

impl<F: PrimeField> R1CSVar<F> for LimbVar<F> {
    type Value = F;

    fn cs(&self) -> ConstraintSystemRef<F> {
        self.v.cs()
    }

    fn value(&self) -> Result<Self::Value, SynthesisError> {
        self.v.value()
    }
}

impl<F: PrimeField> CondSelectGadget<F> for LimbVar<F> {
    fn conditionally_select(
        cond: &Boolean<F>,
        true_value: &Self,
        false_value: &Self,
    ) -> Result<Self, SynthesisError> {
        // We only allow selecting between two values with the same upper bound
        assert_eq!(true_value.ub, false_value.ub);
        Ok(Self {
            v: cond.select(&true_value.v, &false_value.v)?,
            ub: true_value.ub.clone(),
        })
    }
}

impl<F: PrimeField> LimbVar<F> {
    /// Add two `LimbVar`s.
    /// Returns `None` if the upper bound of the sum is too large, i.e.,
    /// greater than `F::MODULUS_MINUS_ONE_DIV_TWO`.
    /// Otherwise, returns the sum as a `LimbVar`.
    pub fn add(&self, other: &Self) -> Option<Self> {
        let ubound = &self.ub + &other.ub;
        if ubound < F::MODULUS_MINUS_ONE_DIV_TWO.into() {
            Some(Self {
                v: &self.v + &other.v,
                ub: ubound,
            })
        } else {
            None
        }
    }

    /// Add multiple `LimbVar`s.
    /// Returns `None` if the upper bound of the sum is too large, i.e.,
    /// greater than `F::MODULUS_MINUS_ONE_DIV_TWO`.
    /// Otherwise, returns the sum as a `LimbVar`.
    pub fn add_many(limbs: &[Self]) -> Option<Self> {
        let ubound = limbs.iter().map(|l| &l.ub).sum();
        if ubound < F::MODULUS_MINUS_ONE_DIV_TWO.into() {
            Some(Self {
                v: if limbs.is_constant() {
                    FpVar::constant(limbs.value().unwrap_or_default().into_iter().sum())
                } else {
                    limbs.iter().map(|l| &l.v).sum()
                },
                ub: ubound,
            })
        } else {
            None
        }
    }

    /// Multiply two `LimbVar`s.
    /// Returns `None` if the upper bound of the product is too large, i.e.,
    /// greater than `F::MODULUS_MINUS_ONE_DIV_TWO`.
    /// Otherwise, returns the product as a `LimbVar`.
    pub fn mul(&self, other: &Self) -> Option<Self> {
        let ubound = &self.ub * &other.ub;
        if ubound < F::MODULUS_MINUS_ONE_DIV_TWO.into() {
            Some(Self {
                v: &self.v * &other.v,
                ub: ubound,
            })
        } else {
            None
        }
    }

    pub fn zero() -> Self {
        Self::default()
    }

    pub fn constant(v: F) -> Self {
        Self {
            v: FpVar::constant(v),
            ub: v.into(),
        }
    }
}

impl<F: PrimeField> ToBitsGadget<F> for LimbVar<F> {
    fn to_bits_le(&self) -> Result<Vec<Boolean<F>>, SynthesisError> {
        let cs = self.cs();

        let bits = &self
            .v
            .value()
            .unwrap_or_default()
            .into_bigint()
            .to_bits_le()[..self.ub.bits() as usize];
        let bits = if cs.is_none() {
            Vec::new_constant(cs, bits)?
        } else {
            Vec::new_witness(cs, || Ok(bits))?
        };

        Boolean::le_bits_to_fp_var(&bits)?.enforce_equal(&self.v)?;

        Ok(bits)
    }
}

/// `NonNativeUintVar` represents a non-native unsigned integer (BigUint) in the
/// circuit.
/// We apply [xJsnark](https://akosba.github.io/papers/xjsnark.pdf)'s techniques
/// for efficient operations on `NonNativeUintVar`.
/// Note that `NonNativeUintVar` is different from arkworks' `NonNativeFieldVar`
/// in that the latter runs the expensive `reduce` (`align` + `modulo` in our
/// terminology) after each arithmetic operation, while the former only reduces
/// the integer when explicitly called.
#[derive(Debug, Clone)]
pub struct NonNativeUintVar<F: PrimeField>(pub Vec<LimbVar<F>>);

impl<F: PrimeField> NonNativeUintVar<F> {
    pub const fn bits_per_limb() -> usize {
        assert!(F::MODULUS_BIT_SIZE > 250);
        // For a `F` with order > 250 bits, 55 is chosen for optimizing the most
        // expensive part `Az∘Bz` when checking the R1CS relation for CycleFold.
        // Consider using `NonNativeUintVar` to represent the base field `Fq`.
        // Since 250 / 55 = 4.46, the `NonNativeUintVar` has 5 limbs.
        // Now, the multiplication of two `NonNativeUintVar`s has 9 limbs, and
        // each limb has at most 2^{55 * 2} * 5 = 112.3 bits.
        // For a 1400x1400 matrix `A`, the multiplication of `A`'s row and `z`
        // is the sum of 1400 `NonNativeUintVar`s, each with 9 limbs.
        // Thus, the maximum bit length of limbs of each element in `Az` is
        // 2^{55 * 2} * 5 * 1400 = 122.7 bits.
        // Finally, in the hadamard product of `Az` and `Bz`, every element has
        // 17 limbs, whose maximum bit length is (2^{55 * 2} * 5 * 1400)^2 * 9
        // = 248.7 bits and is less than the native field `Fr`.
        // Thus, 55 allows us to compute `Az∘Bz` without the expensive alignment
        // operation.
        //
        // TODO (@winderica): either make it a global const, or compute an
        // optimal value based on the modulus size
        55
    }
}

struct BoundedBigUint(BigUint, usize);

impl<F: PrimeField> AllocVar<BoundedBigUint, F> for NonNativeUintVar<F> {
    fn new_variable<T: Borrow<BoundedBigUint>>(
        cs: impl Into<Namespace<F>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        let cs = cs.into().cs();
        let v = f()?;
        let BoundedBigUint(x, l) = v.borrow();

        let mut limbs = vec![];
        for chunk in (0..*l)
            .map(|i| x.bit(i as u64))
            .collect::<Vec<_>>()
            .chunks(Self::bits_per_limb())
        {
            let limb = F::from_bigint(F::BigInt::from_bits_le(chunk)).unwrap();
            let limb = FpVar::new_variable(cs.clone(), || Ok(limb), mode)?;
            Self::enforce_bit_length(&limb, chunk.len())?;
            limbs.push(LimbVar {
                v: limb,
                ub: (BigUint::one() << chunk.len()) - BigUint::one(),
            });
        }

        Ok(Self(limbs))
    }
}

impl<F: PrimeField, G: Field> AllocVar<G, F> for NonNativeUintVar<F> {
    fn new_variable<T: Borrow<G>>(
        cs: impl Into<Namespace<F>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        let cs = cs.into().cs();
        let v = f()?;
        assert_eq!(G::extension_degree(), 1);
        let v = v.borrow().to_base_prime_field_elements().next().unwrap();

        let mut limbs = vec![];

        for chunk in v.into_bigint().to_bits_le().chunks(Self::bits_per_limb()) {
            let limb = F::from_bigint(F::BigInt::from_bits_le(chunk)).unwrap();
            let limb = FpVar::new_variable(cs.clone(), || Ok(limb), mode)?;
            Self::enforce_bit_length(&limb, chunk.len())?;
            limbs.push(LimbVar {
                v: limb,
                ub: (BigUint::one() << chunk.len()) - BigUint::one(),
            });
        }

        Ok(Self(limbs))
    }
}

impl<F: PrimeField> NonNativeUintVar<F> {
    pub fn inputize<T: Field>(x: T) -> Vec<F> {
        assert_eq!(T::extension_degree(), 1);
        x.to_base_prime_field_elements()
            .next()
            .unwrap()
            .into_bigint()
            .to_bits_le()
            .chunks(Self::bits_per_limb())
            .map(|chunk| F::from_bigint(F::BigInt::from_bits_le(chunk)).unwrap())
            .collect()
    }
}

impl<F: PrimeField> R1CSVar<F> for NonNativeUintVar<F> {
    type Value = BigUint;

    fn cs(&self) -> ConstraintSystemRef<F> {
        self.0.cs()
    }

    fn value(&self) -> Result<Self::Value, SynthesisError> {
        let mut r = BigUint::zero();

        for limb in self.0.value()?.into_iter().rev() {
            r <<= Self::bits_per_limb();
            r += Into::<BigUint>::into(limb);
        }

        Ok(r)
    }
}

impl<F: PrimeField> NonNativeUintVar<F> {
    /// Enforce `self` to be less than `other`, where `self` and `other` should
    /// be aligned.
    /// Adapted from https://github.com/akosba/jsnark/blob/0955389d0aae986ceb25affc72edf37a59109250/JsnarkCircuitBuilder/src/circuit/auxiliary/LongElement.java#L801-L872
    pub fn enforce_lt(&self, other: &Self) -> Result<(), SynthesisError> {
        let len = max(self.0.len(), other.0.len());
        let zero = LimbVar::zero();

        // Compute the difference between limbs of `other` and `self`.
        // Denote a positive limb by `+`, a negative limb by `-`, a zero limb by
        // `0`, and an unknown limb by `?`.
        // Then, for `self < other`, `delta` should look like:
        // ? ? ... ? ? + 0 0 ... 0 0
        let delta = (0..len)
            .map(|i| {
                let x = &self.0.get(i).unwrap_or(&zero).v;
                let y = &other.0.get(i).unwrap_or(&zero).v;
                y - x
            })
            .collect::<Vec<_>>();

        // `helper` is a vector of booleans that indicates if the corresponding
        // limb of `delta` is the first (searching from MSB) positive limb.
        // For example, if `delta` is:
        // - + ... + - + 0 0 ... 0 0
        // <---- search in this direction --------
        // Then `helper` should be:
        // F F ... F F T F F ... F F
        let helper = {
            let cs = self.cs().or(other.cs());
            let mut helper = vec![false; len];
            for i in (0..len).rev() {
                let delta = delta[i].value().unwrap_or_default().into_bigint();
                if !delta.is_zero() && delta < F::MODULUS_MINUS_ONE_DIV_TWO {
                    helper[i] = true;
                    break;
                }
            }
            if cs.is_none() {
                Vec::<Boolean<F>>::new_constant(cs, helper)?
            } else {
                Vec::new_witness(cs, || Ok(helper))?
            }
        };

        // `p` is the first positive limb in `delta`.
        let mut p = FpVar::<F>::zero();
        // `r` is the sum of all bits in `helper`, which should be 1 when `self`
        // is less than `other`, as there should be more than one positive limb
        // in `delta`, and thus exactly one true bit in `helper`.
        let mut r = FpVar::zero();
        for (b, d) in helper.into_iter().zip(delta) {
            // Choose the limb `d` only if `b` is true.
            p += b.select(&d, &FpVar::zero())?;
            // Either `r` or `d` should be zero.
            // Consider the same example as above:
            // - + ... + - + 0 0 ... 0 0
            // F F ... F F T F F ... F F
            // |-----------|
            // `r = 0` in this range (before/when we meet the first positive limb)
            //               |---------|
            //               `d = 0` in this range (after we meet the first positive limb)
            // This guarantees that for every bit after the true bit in `helper`,
            // the corresponding limb in `delta` is zero.
            (&r * &d).enforce_equal(&FpVar::zero())?;
            // Add the current bit to `r`.
            r += FpVar::from(b);
        }

        // Ensure that `r` is exactly 1. This guarantees that there is exactly
        // one true value in `helper`.
        r.enforce_equal(&FpVar::one())?;
        // Ensure that `p` is positive, i.e.,
        // `0 <= p - 1 < 2^bits_per_limb < F::MODULUS_MINUS_ONE_DIV_TWO`.
        // This guarantees that the true value in `helper` corresponds to a
        // positive limb in `delta`.
        Self::enforce_bit_length(&(p - FpVar::one()), Self::bits_per_limb())?;

        Ok(())
    }

    /// Enforce `self` to be equal to `other`, where `self` and `other` are not
    /// necessarily aligned.
    ///
    /// Adapted from https://github.com/akosba/jsnark/blob/0955389d0aae986ceb25affc72edf37a59109250/JsnarkCircuitBuilder/src/circuit/auxiliary/LongElement.java#L562-L798
    /// Similar implementations can also be found in https://github.com/alex-ozdemir/bellman-bignat/blob/0585b9d90154603a244cba0ac80b9aafe1d57470/src/mp/bignat.rs#L566-L661
    /// and https://github.com/arkworks-rs/r1cs-std/blob/4020fbc22625621baa8125ede87abaeac3c1ca26/src/fields/emulated_fp/reduce.rs#L201-L323
    pub fn enforce_equal_unaligned(&self, other: &Self) -> Result<(), SynthesisError> {
        let len = min(self.0.len(), other.0.len());

        // Group the limbs of `self` and `other` so that each group nearly
        // reaches the capacity `F::MODULUS_MINUS_ONE_DIV_TWO`.
        // By saying group, we mean the operation `Σ x_i 2^{i * W}`, where `W`
        // is the initial number of bits in a limb, just as what we do in grade
        // school arithmetic, e.g.,
        //         5   9
        // x       7   3
        // -------------
        //        15  27
        //    35  63
        // -------------  <- When grouping 35, 15 + 63, and 27, we are computing
        // 4   3   0   7     35 * 100 + (15 + 63) * 10 + 27 = 4307
        // Note that this is different from the concatenation `x_0 || x_1 ...`,
        // since the bit-length of each limb is not necessarily the initial size
        // `W`.
        let (steps, x, y, rest) = {
            // `steps` stores the size of each grouped limb.
            let mut steps = vec![];
            // `x_grouped` stores the grouped limbs of `self`.
            let mut x_grouped = vec![];
            // `y_grouped` stores the grouped limbs of `other`.
            let mut y_grouped = vec![];
            let mut i = 0;
            while i < len {
                let mut j = i;
                // The current grouped limbs of `self` and `other`.
                let mut xx = LimbVar::zero();
                let mut yy = LimbVar::zero();
                while j < len {
                    let shift = BigUint::one() << (Self::bits_per_limb() * (j - i));
                    assert!(shift < F::MODULUS_MINUS_ONE_DIV_TWO.into());
                    let shift = LimbVar::constant(shift.into());
                    match (
                        // Try to group `x` and `y` into `xx` and `yy`.
                        self.0[j].mul(&shift).and_then(|x| xx.add(&x)),
                        other.0[j].mul(&shift).and_then(|y| yy.add(&y)),
                    ) {
                        // Update the result if successful.
                        (Some(x), Some(y)) => (xx, yy) = (x, y),
                        // Break the loop if the upper bound of the result exceeds
                        // the maximum capacity.
                        _ => break,
                    }
                    j += 1;
                }
                // Store the grouped limbs and their size.
                steps.push((j - i) * Self::bits_per_limb());
                x_grouped.push(xx);
                y_grouped.push(yy);
                // Start the next group
                i = j;
            }
            let remaining_limbs = &(if i < self.0.len() { self } else { other }).0[i..];
            let rest = if remaining_limbs.is_empty() {
                FpVar::zero()
            } else {
                // If there is any remaining limb, the first one should be the
                // final carry (which will be checked later), and the following
                // ones should be zero.

                // Enforce the remaining limbs to be zero.
                // Instead of doing that one by one, we check if their sum is
                // zero using a single constraint.
                // This is sound, as the upper bounds of the limbs and their sum
                // are guaranteed to be less than `F::MODULUS_MINUS_ONE_DIV_TWO`
                // (i.e., all of them are "non-negative"), implying that all
                // limbs should be zero to make the sum zero.
                LimbVar::add_many(&remaining_limbs[1..])
                    .unwrap()
                    .v
                    .enforce_equal(&FpVar::zero())?;
                remaining_limbs[0].v.clone()
            };
            (steps, x_grouped, y_grouped, rest)
        };
        let n = steps.len();
        // `c` stores the current carry of `x_i - y_i`
        let mut c = FpVar::<F>::zero();
        // For each group, check the last `step_i` bits of `x_i` and `y_i` are
        // equal.
        // The intuition is to check `diff = x_i - y_i = 0 (mod 2^step_i)`.
        // However, this is only true for `i = 0`, and we need to consider carry
        // values `diff >> step_i` for `i > 0`.
        // Therefore, we actually check `diff = x_i - y_i + c = 0 (mod 2^step_i)`
        // and derive the next `c` by computing `diff >> step_i`.
        // To enforce `diff = 0 (mod 2^step_i)`, we compute `diff / 2^step_i`
        // and enforce it to be small (soundness holds because for `a` that does
        // not divide `b`, `b / a` in the field will be very large.
        for i in 0..n {
            let step = steps[i];
            c = (&x[i].v - &y[i].v + &c)
                .mul_by_inverse_unchecked(&FpVar::constant(F::from(BigUint::one() << step)))?;
            if i != n - 1 {
                // Unlike the code mentioned above which add some offset to the
                // diff `x_i - y_i + c` to make it always positive, we directly
                // check if the absolute value of the diff is small.
                Self::enforce_abs_bit_length(
                    &c,
                    (max(&x[i].ub, &y[i].ub).bits() as usize)
                        .checked_sub(step)
                        .unwrap_or_default(),
                )?;
            } else {
                // For the final carry, we need to ensure that it equals the
                // remaining limb `rest`.
                c.enforce_equal(&rest)?;
            }
        }

        Ok(())
    }
}

impl<F: PrimeField> ToBitsGadget<F> for NonNativeUintVar<F> {
    fn to_bits_le(&self) -> Result<Vec<Boolean<F>>, SynthesisError> {
        Ok(self
            .0
            .iter()
            .map(|limb| limb.to_bits_le())
            .collect::<Result<Vec<_>, _>>()?
            .concat())
    }
}

impl<F: PrimeField> ToConstraintFieldGadget<F> for NonNativeUintVar<F> {
    fn to_constraint_field(&self) -> Result<Vec<FpVar<F>>, SynthesisError> {
        let bits_per_limb = F::MODULUS_BIT_SIZE as usize - 1;

        let limbs = self
            .to_bits_le()?
            .chunks(bits_per_limb)
            .map(Boolean::le_bits_to_fp_var)
            .collect::<Result<Vec<_>, _>>()?;

        Ok(limbs)
    }
}

impl<F: PrimeField> CondSelectGadget<F> for NonNativeUintVar<F> {
    fn conditionally_select(
        cond: &Boolean<F>,
        true_value: &Self,
        false_value: &Self,
    ) -> Result<Self, SynthesisError> {
        assert_eq!(true_value.0.len(), false_value.0.len());
        let mut v = vec![];
        for i in 0..true_value.0.len() {
            v.push(cond.select(&true_value.0[i], &false_value.0[i])?);
        }
        Ok(Self(v))
    }
}

impl<F: PrimeField> NonNativeUintVar<F> {
    pub fn ubound(&self) -> BigUint {
        let mut r = BigUint::zero();

        for i in self.0.iter().rev() {
            r <<= Self::bits_per_limb();
            r += &i.ub;
        }

        r
    }

    fn enforce_bit_length(x: &FpVar<F>, length: usize) -> Result<Vec<Boolean<F>>, SynthesisError> {
        let cs = x.cs();

        let bits = &x.value().unwrap_or_default().into_bigint().to_bits_le()[..length];
        let bits = if cs.is_none() {
            Vec::new_constant(cs, bits)?
        } else {
            Vec::new_witness(cs, || Ok(bits))?
        };

        Boolean::le_bits_to_fp_var(&bits)?.enforce_equal(x)?;

        Ok(bits)
    }

    fn enforce_abs_bit_length(
        x: &FpVar<F>,
        length: usize,
    ) -> Result<Vec<Boolean<F>>, SynthesisError> {
        let cs = x.cs();
        let mode = if cs.is_none() {
            AllocationMode::Constant
        } else {
            AllocationMode::Witness
        };

        let is_neg = Boolean::new_variable(
            cs.clone(),
            || Ok(x.value().unwrap_or_default().into_bigint() > F::MODULUS_MINUS_ONE_DIV_TWO),
            mode,
        )?;
        let bits = Vec::new_variable(
            cs.clone(),
            || {
                Ok({
                    let x = x.value().unwrap_or_default();
                    let mut bits = if is_neg.value().unwrap_or_default() {
                        -x
                    } else {
                        x
                    }
                    .into_bigint()
                    .to_bits_le();
                    bits.resize(length, false);
                    bits
                })
            },
            mode,
        )?;

        // Below is equivalent to but more efficient than
        // `Boolean::le_bits_to_fp_var(&bits)?.enforce_equal(&is_neg.select(&x.negate()?, &x)?)?`
        // Note that this enforces:
        // 1. The claimed absolute value `is_neg.select(&x.negate()?, &x)?` has
        //    exactly `length` bits.
        // 2. `is_neg` is indeed the sign of `x`, i.e., `is_neg = false` when
        //    `0 <= x < (|F| - 1) / 2`, and `is_neg = true` when
        //    `(|F| - 1) / 2 <= x < F`, thus the claimed absolute value is
        //    correct.
        //    If `is_neg` is incorrect, then:
        //        a. `0 <= x < (|F| - 1) / 2`, but `is_neg = true`, then
        //           `is_neg.select(&x.negate()?, &x)?` returns `|F| - x`,
        //           which is greater than `(|F| - 1) / 2` and cannot fit in
        //           `length` bits (given that `length` is small).
        //        b. `(|F| - 1) / 2 <= x < F`, but `is_neg = false`, then
        //           `is_neg.select(&x.negate()?, &x)?` returns `x`, which is
        //           greater than `(|F| - 1) / 2` and cannot fit in `length`
        //           bits.
        FpVar::from(is_neg).mul_equals(&x.double()?, &(x - Boolean::le_bits_to_fp_var(&bits)?))?;

        Ok(bits)
    }

    /// Compute `self + other`, without aligning the limbs.
    pub fn add_no_align(&self, other: &Self) -> Self {
        let mut z = vec![LimbVar::zero(); max(self.0.len(), other.0.len())];
        for (i, v) in self.0.iter().enumerate() {
            z[i] = z[i].add(v).unwrap();
        }
        for (i, v) in other.0.iter().enumerate() {
            z[i] = z[i].add(v).unwrap();
        }
        Self(z)
    }

    /// Compute `self * other`, without aligning the limbs.
    /// Implements the O(n) approach described in xJsnark, Section IV.B.1)
    pub fn mul_no_align(&self, other: &Self) -> Result<Self, SynthesisError> {
        let len = self.0.len() + other.0.len() - 1;
        if self.is_constant() || other.is_constant() {
            // Use the naive approach for constant operands, which costs no
            // constraints.
            let z = (0..len)
                .map(|i| {
                    let start = max(i + 1, other.0.len()) - other.0.len();
                    let end = min(i + 1, self.0.len());
                    LimbVar::add_many(
                        &(start..end)
                            .map(|j| self.0[j].mul(&other.0[i - j]))
                            .collect::<Option<Vec<_>>>()?,
                    )
                })
                .collect::<Option<Vec<_>>>()
                .unwrap();
            return Ok(Self(z));
        }
        let cs = self.cs().or(other.cs());
        let mode = if cs.is_none() {
            AllocationMode::Constant
        } else {
            AllocationMode::Witness
        };

        // Compute the result `z` outside the circuit and provide it as hints.
        let z = {
            let mut z = vec![(F::zero(), BigUint::zero()); len];
            for i in 0..self.0.len() {
                for j in 0..other.0.len() {
                    z[i + j].0 += self.0[i].value().unwrap_or_default()
                        * other.0[j].value().unwrap_or_default();
                    z[i + j].1 += &self.0[i].ub * &other.0[j].ub;
                }
            }
            z.into_iter()
                .map(|(v, ub)| {
                    assert!(ub < F::MODULUS_MINUS_ONE_DIV_TWO.into());
                    Ok(LimbVar {
                        v: FpVar::new_variable(cs.clone(), || Ok(v), mode)?,
                        ub,
                    })
                })
                .collect::<Result<Vec<_>, _>>()?
        };
        for c in 1..=len {
            let c = F::from(c as u64);
            let mut t = F::one();
            let mut c_powers = vec![];
            for _ in 0..len {
                c_powers.push(t);
                t *= c;
            }
            // `l = Σ self[i] c^i`
            let l = self
                .0
                .iter()
                .zip(&c_powers)
                .map(|(v, t)| (&v.v * *t))
                .collect::<Vec<_>>()
                .iter()
                .sum::<FpVar<_>>();
            // `r = Σ other[i] c^i`
            let r = other
                .0
                .iter()
                .zip(&c_powers)
                .map(|(v, t)| (&v.v * *t))
                .collect::<Vec<_>>()
                .iter()
                .sum::<FpVar<_>>();
            // `o = Σ z[i] c^i`
            let o = z
                .iter()
                .zip(&c_powers)
                .map(|(v, t)| &v.v * *t)
                .collect::<Vec<_>>()
                .iter()
                .sum::<FpVar<_>>();
            // Enforce `o = l * r`
            l.mul_equals(&r, &o)?;
        }

        Ok(Self(z))
    }

    /// Convert `Self` to an element in `M`, i.e., compute `Self % M::MODULUS`.
    pub fn modulo<M: PrimeField>(&self) -> Result<Self, SynthesisError> {
        let cs = self.cs();
        let mode = if cs.is_none() {
            AllocationMode::Constant
        } else {
            AllocationMode::Witness
        };
        let m: BigUint = M::MODULUS.into();
        // Provide the quotient and remainder as hints
        let (q, r) = {
            let v = self.value().unwrap_or_default();
            let (q, r) = v.div_rem(&m);
            let q_ubound = self.ubound().div_ceil(&m);
            let r_ubound = &m;
            (
                Self::new_variable(
                    cs.clone(),
                    || Ok(BoundedBigUint(q, q_ubound.bits() as usize)),
                    mode,
                )?,
                Self::new_variable(
                    cs.clone(),
                    || Ok(BoundedBigUint(r, r_ubound.bits() as usize)),
                    mode,
                )?,
            )
        };

        let m = Self::new_constant(cs.clone(), BoundedBigUint(m, M::MODULUS_BIT_SIZE as usize))?;
        // Enforce `self = q * m + r`
        q.mul_no_align(&m)?
            .add_no_align(&r)
            .enforce_equal_unaligned(self)?;
        // Enforce `r < m` (and `r >= 0` already holds)
        r.enforce_lt(&m)?;

        Ok(r)
    }

    /// Enforce that `self` is congruent to `other` modulo `M::MODULUS`.
    pub fn enforce_congruent<M: PrimeField>(&self, other: &Self) -> Result<(), SynthesisError> {
        let cs = self.cs();
        let mode = if cs.is_none() {
            AllocationMode::Constant
        } else {
            AllocationMode::Witness
        };
        let m: BigUint = M::MODULUS.into();
        let bits = (max(self.ubound(), other.ubound()) / &m).bits() as usize;
        // Provide the quotient `|x - y| / m` and a boolean indicating if `x > y`
        // as hints.
        let (q, is_ge) = {
            let x = self.value().unwrap_or_default();
            let y = other.value().unwrap_or_default();
            let (d, b) = if x > y {
                ((x - y) / &m, true)
            } else {
                ((y - x) / &m, false)
            };
            (
                Self::new_variable(cs.clone(), || Ok(BoundedBigUint(d, bits)), mode)?,
                Boolean::new_variable(cs.clone(), || Ok(b), mode)?,
            )
        };

        let zero = Self::new_constant(cs.clone(), BoundedBigUint(BigUint::zero(), bits))?;
        let m = Self::new_constant(cs.clone(), BoundedBigUint(m, M::MODULUS_BIT_SIZE as usize))?;
        let l = self.add_no_align(&is_ge.select(&zero, &q)?.mul_no_align(&m)?);
        let r = other.add_no_align(&is_ge.select(&q, &zero)?.mul_no_align(&m)?);
        // If `self >= other`, enforce `self = other + q * m`
        // Otherwise, enforce `self + q * m = other`
        // Soundness holds because if `self` and `other` are not congruent, then
        // one can never find a `q` satisfying either equation above.
        l.enforce_equal_unaligned(&r)
    }
}

impl<F: PrimeField, B: AsRef<[Boolean<F>]>> From<B> for NonNativeUintVar<F> {
    fn from(bits: B) -> Self {
        Self(
            bits.as_ref()
                .chunks(Self::bits_per_limb())
                .map(LimbVar::from)
                .collect::<Vec<_>>(),
        )
    }
}

/// The out-circuit counterpart of `NonNativeUintVar::to_constraint_field`
pub fn nonnative_field_to_field_elements<TargetField: Field, BaseField: PrimeField>(
    f: &TargetField,
) -> Vec<BaseField> {
    assert_eq!(TargetField::extension_degree(), 1);
    let bits = f
        .to_base_prime_field_elements()
        .next()
        .unwrap()
        .into_bigint()
        .to_bits_le();

    let bits_per_limb = BaseField::MODULUS_BIT_SIZE as usize - 1;
    let num_limbs =
        (TargetField::BasePrimeField::MODULUS_BIT_SIZE as usize).div_ceil(bits_per_limb);

    let mut limbs = bits
        .chunks(bits_per_limb)
        .map(|chunk| {
            let mut limb = BaseField::zero();
            let mut w = BaseField::one();
            for &b in chunk.iter() {
                limb += BaseField::from(b) * w;
                w.double_in_place();
            }
            limb
        })
        .collect::<Vec<BaseField>>();
    limbs.resize(num_limbs, BaseField::zero());

    limbs
}

impl<F: PrimeField> VectorGadget<NonNativeUintVar<F>> for [NonNativeUintVar<F>] {
    fn add(&self, other: &Self) -> Result<Vec<NonNativeUintVar<F>>, SynthesisError> {
        Ok(self
            .iter()
            .zip(other.iter())
            .map(|(x, y)| x.add_no_align(y))
            .collect())
    }

    fn hadamard(&self, other: &Self) -> Result<Vec<NonNativeUintVar<F>>, SynthesisError> {
        self.iter()
            .zip(other.iter())
            .map(|(x, y)| x.mul_no_align(y))
            .collect()
    }

    fn mul_scalar(
        &self,
        other: &NonNativeUintVar<F>,
    ) -> Result<Vec<NonNativeUintVar<F>>, SynthesisError> {
        self.iter().map(|x| x.mul_no_align(other)).collect()
    }
}

impl<F: PrimeField, CF: PrimeField> MatrixGadget<NonNativeUintVar<CF>>
    for SparseMatrixVar<F, CF, NonNativeUintVar<CF>>
{
    fn mul_vector(
        &self,
        v: &[NonNativeUintVar<CF>],
    ) -> Result<Vec<NonNativeUintVar<CF>>, SynthesisError> {
        Ok(self
            .coeffs
            .iter()
            .map(|row| {
                let len = row
                    .iter()
                    .map(|(value, col_i)| value.0.len() + v[*col_i].0.len() - 1)
                    .max()
                    .unwrap_or(0);
                // This is a combination of `mul_no_align` and `add_no_align`
                // that results in more flattened `LinearCombination`s.
                // Consequently, `ConstraintSystem::inline_all_lcs` costs less
                // time, thus making trusted setup and proof generation faster.
                let limbs = (0..len)
                    .map(|i| {
                        LimbVar::add_many(
                            &row.iter()
                                .flat_map(|(value, col_i)| {
                                    let start = max(i + 1, v[*col_i].0.len()) - v[*col_i].0.len();
                                    let end = min(i + 1, value.0.len());
                                    (start..end).map(|j| value.0[j].mul(&v[*col_i].0[i - j]))
                                })
                                .collect::<Option<Vec<_>>>()?,
                        )
                    })
                    .collect::<Option<Vec<_>>>()
                    .unwrap();
                NonNativeUintVar(limbs)
            })
            .collect())
    }
}

#[cfg(test)]
mod tests {
    use std::error::Error;

    use super::*;
    use ark_pallas::{Fq, Fr};
    use ark_relations::r1cs::ConstraintSystem;
    use ark_std::{test_rng, UniformRand};
    use num_bigint::RandBigInt;

    #[test]
    fn test_mul_biguint() -> Result<(), Box<dyn Error>> {
        let cs = ConstraintSystem::<Fr>::new_ref();

        let size = 256;

        let rng = &mut test_rng();
        let a = rng.gen_biguint(size as u64);
        let b = rng.gen_biguint(size as u64);
        let ab = &a * &b;
        let aab = &a * &ab;
        let abb = &ab * &b;

        let a_var = NonNativeUintVar::new_witness(cs.clone(), || Ok(BoundedBigUint(a, size)))?;
        let b_var = NonNativeUintVar::new_witness(cs.clone(), || Ok(BoundedBigUint(b, size)))?;
        let ab_var =
            NonNativeUintVar::new_witness(cs.clone(), || Ok(BoundedBigUint(ab, size * 2)))?;
        let aab_var =
            NonNativeUintVar::new_witness(cs.clone(), || Ok(BoundedBigUint(aab, size * 3)))?;
        let abb_var =
            NonNativeUintVar::new_witness(cs.clone(), || Ok(BoundedBigUint(abb, size * 3)))?;

        a_var
            .mul_no_align(&b_var)?
            .enforce_equal_unaligned(&ab_var)?;
        a_var
            .mul_no_align(&ab_var)?
            .enforce_equal_unaligned(&aab_var)?;
        ab_var
            .mul_no_align(&b_var)?
            .enforce_equal_unaligned(&abb_var)?;

        assert!(cs.is_satisfied()?);
        Ok(())
    }

    #[test]
    fn test_mul_fq() -> Result<(), Box<dyn Error>> {
        let cs = ConstraintSystem::<Fr>::new_ref();

        let rng = &mut test_rng();
        let a = Fq::rand(rng);
        let b = Fq::rand(rng);
        let ab = a * b;
        let aab = a * ab;
        let abb = ab * b;

        let a_var = NonNativeUintVar::new_witness(cs.clone(), || Ok(a))?;
        let b_var = NonNativeUintVar::new_witness(cs.clone(), || Ok(b))?;
        let ab_var = NonNativeUintVar::new_witness(cs.clone(), || Ok(ab))?;
        let aab_var = NonNativeUintVar::new_witness(cs.clone(), || Ok(aab))?;
        let abb_var = NonNativeUintVar::new_witness(cs.clone(), || Ok(abb))?;

        a_var
            .mul_no_align(&b_var)?
            .enforce_congruent::<Fq>(&ab_var)?;
        a_var
            .mul_no_align(&ab_var)?
            .enforce_congruent::<Fq>(&aab_var)?;
        ab_var
            .mul_no_align(&b_var)?
            .enforce_congruent::<Fq>(&abb_var)?;

        assert!(cs.is_satisfied()?);
        Ok(())
    }

    #[test]
    fn test_pow() -> Result<(), Box<dyn Error>> {
        let cs = ConstraintSystem::<Fr>::new_ref();

        let rng = &mut test_rng();

        let a = Fq::rand(rng);

        let a_var = NonNativeUintVar::new_witness(cs.clone(), || Ok(a))?;

        let mut r_var = a_var.clone();
        for _ in 0..16 {
            r_var = r_var.mul_no_align(&r_var)?.modulo::<Fq>()?;
        }
        r_var = r_var.mul_no_align(&a_var)?.modulo::<Fq>()?;
        assert_eq!(a.pow([65537u64]), Fq::from(r_var.value()?));
        assert!(cs.is_satisfied()?);
        Ok(())
    }

    #[test]
    fn test_vec_vec_mul() -> Result<(), Box<dyn Error>> {
        let cs = ConstraintSystem::<Fr>::new_ref();

        let len = 1000;

        let rng = &mut test_rng();
        let a = (0..len).map(|_| Fq::rand(rng)).collect::<Vec<Fq>>();
        let b = (0..len).map(|_| Fq::rand(rng)).collect::<Vec<Fq>>();
        let c = a.iter().zip(b.iter()).map(|(a, b)| a * b).sum::<Fq>();

        let a_var = Vec::<NonNativeUintVar<Fr>>::new_witness(cs.clone(), || Ok(a))?;
        let b_var = Vec::<NonNativeUintVar<Fr>>::new_witness(cs.clone(), || Ok(b))?;
        let c_var = NonNativeUintVar::new_witness(cs.clone(), || Ok(c))?;

        let mut r_var =
            NonNativeUintVar::new_constant(cs.clone(), BoundedBigUint(BigUint::zero(), 0))?;
        for (a, b) in a_var.into_iter().zip(b_var.into_iter()) {
            r_var = r_var.add_no_align(&a.mul_no_align(&b)?);
        }
        r_var.enforce_congruent::<Fq>(&c_var)?;

        assert!(cs.is_satisfied()?);
        Ok(())
    }
}
