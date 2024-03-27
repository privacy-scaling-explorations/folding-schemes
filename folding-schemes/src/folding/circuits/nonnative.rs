use ark_ec::{AffineRepr, CurveGroup};
use ark_r1cs_std::{
    alloc::{AllocVar, AllocationMode},
    fields::nonnative::{params::OptimizationType, AllocatedNonNativeFieldVar, NonNativeFieldVar},
};
use ark_relations::r1cs::{Namespace, SynthesisError};
use ark_std::{One, Zero};
use core::borrow::Borrow;

/// NonNativeAffineVar represents an elliptic curve point in Affine representation in the non-native
/// field, over the constraint field. It is not intended to perform operations, but just to contain
/// the affine coordinates in order to perform hash operations of the point.
#[derive(Debug, Clone)]
pub struct NonNativeAffineVar<C: CurveGroup>
where
    <C as ark_ec::CurveGroup>::BaseField: ark_ff::PrimeField,
{
    pub x: NonNativeFieldVar<C::BaseField, C::ScalarField>,
    pub y: NonNativeFieldVar<C::BaseField, C::ScalarField>,
    pub infinity: NonNativeFieldVar<C::BaseField, C::ScalarField>,
}

impl<C> AllocVar<C, C::ScalarField> for NonNativeAffineVar<C>
where
    C: CurveGroup,
    <C as ark_ec::CurveGroup>::BaseField: ark_ff::PrimeField,
{
    fn new_variable<T: Borrow<C>>(
        cs: impl Into<Namespace<C::ScalarField>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        f().and_then(|val| {
            let cs = cs.into();

            let affine = val.borrow().into_affine();
            let zero_point = (&C::BaseField::zero(), &C::BaseField::one());
            let xy = affine.xy().unwrap_or(zero_point);

            let x = NonNativeFieldVar::<C::BaseField, C::ScalarField>::new_variable(
                cs.clone(),
                || Ok(xy.0),
                mode,
            )?;
            let y = NonNativeFieldVar::<C::BaseField, C::ScalarField>::new_variable(
                cs.clone(),
                || Ok(xy.1),
                mode,
            )?;

            let is_infinity = affine.is_zero();
            let inf: C::BaseField = if is_infinity {
                C::BaseField::one()
            } else {
                C::BaseField::zero()
            };
            let infinity = NonNativeFieldVar::<C::BaseField, C::ScalarField>::new_variable(
                cs.clone(),
                || Ok(inf),
                mode,
            )?;

            Ok(Self { x, y, infinity })
        })
    }
}

/// Wrapper on top of [`point_to_nonnative_limbs_custom_opt`] which always uses
/// [`OptimizationType::Weight`].
#[allow(clippy::type_complexity)]
pub fn point_to_nonnative_limbs<C: CurveGroup>(
    p: C,
) -> Result<
    (
        Vec<C::ScalarField>,
        Vec<C::ScalarField>,
        Vec<C::ScalarField>,
    ),
    SynthesisError,
>
where
    <C as ark_ec::CurveGroup>::BaseField: ark_ff::PrimeField,
{
    point_to_nonnative_limbs_custom_opt(p, OptimizationType::Weight)
}

/// Used to compute (outside the circuit) the limbs representation of a point that matches the one
/// used in-circuit, and in particular this method allows to specify which [`OptimizationType`] to
/// use.
#[allow(clippy::type_complexity)]
pub fn point_to_nonnative_limbs_custom_opt<C: CurveGroup>(
    p: C,
    optimization_type: OptimizationType,
) -> Result<
    (
        Vec<C::ScalarField>,
        Vec<C::ScalarField>,
        Vec<C::ScalarField>,
    ),
    SynthesisError,
>
where
    <C as ark_ec::CurveGroup>::BaseField: ark_ff::PrimeField,
{
    let affine = p.into_affine();
    if affine.is_zero() {
        let x =
            AllocatedNonNativeFieldVar::<C::BaseField, C::ScalarField>::get_limbs_representations(
                &C::BaseField::zero(),
                optimization_type,
            )?;
        let y =
            AllocatedNonNativeFieldVar::<C::BaseField, C::ScalarField>::get_limbs_representations(
                &C::BaseField::one(),
                optimization_type,
            )?;
        let infinity =
            AllocatedNonNativeFieldVar::<C::BaseField, C::ScalarField>::get_limbs_representations(
                &C::BaseField::one(),
                optimization_type,
            )?;
        return Ok((x, y, infinity));
    }

    let (x, y) = affine.xy().unwrap();
    let x = AllocatedNonNativeFieldVar::<C::BaseField, C::ScalarField>::get_limbs_representations(
        x,
        optimization_type,
    )?;
    let y = AllocatedNonNativeFieldVar::<C::BaseField, C::ScalarField>::get_limbs_representations(
        y,
        optimization_type,
    )?;
    let infinity =
        AllocatedNonNativeFieldVar::<C::BaseField, C::ScalarField>::get_limbs_representations(
            &C::BaseField::zero(),
            optimization_type,
        )?;
    Ok((x, y, infinity))
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_pallas::{Fr, Projective};
    use ark_r1cs_std::{alloc::AllocVar, R1CSVar, ToConstraintFieldGadget};
    use ark_relations::r1cs::ConstraintSystem;
    use ark_std::{UniformRand, Zero};

    #[test]
    fn test_alloc_nonnativeaffinevar() {
        let cs = ConstraintSystem::<Fr>::new_ref();

        // dealing with the 'zero' point should not panic when doing the unwrap
        let p = Projective::zero();
        NonNativeAffineVar::<Projective>::new_witness(cs.clone(), || Ok(p)).unwrap();

        // check that point_to_nonnative_limbs returns the expected values
        let mut rng = ark_std::test_rng();
        let p = Projective::rand(&mut rng);
        let pVar = NonNativeAffineVar::<Projective>::new_witness(cs.clone(), || Ok(p)).unwrap();
        let (x, y, inf) = point_to_nonnative_limbs(p).unwrap();
        assert_eq!(pVar.x.to_constraint_field().unwrap().value().unwrap(), x);
        assert_eq!(pVar.y.to_constraint_field().unwrap().value().unwrap(), y);
        assert_eq!(
            pVar.infinity
                .to_constraint_field()
                .unwrap()
                .value()
                .unwrap(),
            inf
        );
    }
}
