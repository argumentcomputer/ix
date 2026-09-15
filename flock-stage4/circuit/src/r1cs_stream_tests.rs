use super::*;
use std::{cell::RefCell, rc::Rc};

fn fixture(builder: &mut R1csBuilder, value: Fr) -> Result<(), R1csError> {
  let public = builder.alloc_public(value)?;
  let x = builder.alloc_private(value)?;
  let y = builder.alloc_private(value + Fr::ONE)?;
  let z = builder.alloc_private(value * (value + Fr::ONE))?;
  builder.enforce_boolean(ConstraintPhase::Statement, x);
  builder.enforce(
    ConstraintPhase::Pcs,
    LinearCombination::from_variable(x),
    LinearCombination::from_variable(y),
    LinearCombination::from_variable(z),
  );
  builder.enforce_zero(
    ConstraintPhase::Transcript,
    LinearCombination::from_variable(public)
      .minus(&LinearCombination::from_variable(x)),
  );
  builder.enforce_zero(
    ConstraintPhase::Pcs,
    LinearCombination::from_variable(y)
      .minus(&LinearCombination::from_variable(x))
      .minus(&LinearCombination::one()),
  );
  builder.enforce_zero(ConstraintPhase::Pcs, LinearCombination::zero());
  builder.check_status()
}

fn expected() -> R1csProjectionV1 {
  let mut builder = R1csBuilder::new_shape_projection();
  fixture(&mut builder, Fr::from(42u64)).unwrap();
  builder.finish_projection().unwrap()
}

fn materialized(value: Fr) -> (CanonicalR1csV1, Witness) {
  let mut builder = R1csBuilder::new();
  fixture(&mut builder, value).unwrap();
  builder.finish().unwrap()
}

#[test]
fn streamed_shape_and_checked_assignment_match_both_legacy_identities() {
  let expected = expected();
  let (r1cs, _) = materialized(Fr::ZERO);
  let seen = Rc::new(RefCell::new(Vec::new()));
  let observations = seen.clone();
  let mut shape = R1csBuilder::new_shape_streamed_observed(
    expected.clone(),
    move |constraint| {
      observations.borrow_mut().push(constraint.clone());
      Ok(())
    },
  )
  .unwrap();
  assert!(shape.is_shape_only());
  fixture(&mut shape, Fr::from(42u64)).unwrap();
  let shape = shape.finish_streamed_shape().unwrap();
  assert_eq!(shape.projection(), &expected);
  assert_eq!(shape.canonical_digest(), r1cs.digest());
  assert_eq!(&*seen.borrow(), r1cs.constraints());
  let mut stream = R1csShapeStreamV0::new(expected.clone()).unwrap();
  for constraint in r1cs.constraints() {
    stream.observe(constraint).unwrap();
  }
  assert_eq!(stream.finish().unwrap(), shape);
  for value in [Fr::ZERO, Fr::ONE] {
    let (materialized, witness) = materialized(value);
    let mut builder = R1csBuilder::new_checked_streamed_observed(
      expected.clone(),
      5 * 32,
      |_| Ok(()),
    )
    .unwrap();
    assert!(!builder.is_shape_only());
    let BuilderStorage::Streamed { state } = &builder.storage else {
      panic!("streamed mode");
    };
    assert_eq!(state.assignment.as_ref().unwrap().capacity(), 5);
    fixture(&mut builder, value).unwrap();
    let checked = builder.finish_checked_stream().unwrap();
    assert_eq!(checked.shape(), &shape);
    assert_eq!(checked.assignment(), witness.assignment());
    let (checked_shape, checked_witness) = checked.into_parts();
    assert_eq!(checked_shape.canonical_digest(), materialized.digest());
    assert_eq!(checked_witness, witness);
    materialized.check(&checked_witness).unwrap();
  }
}

#[test]
fn streamed_witness_checks_every_constraint_before_observing_and_fails_closed()
{
  let seen = Rc::new(RefCell::new(0usize));
  let observations = seen.clone();
  let mut builder =
    R1csBuilder::new_checked_streamed_observed(expected(), 160, move |_| {
      *observations.borrow_mut() += 1;
      Ok(())
    })
    .unwrap();
  let error = R1csError::Unsatisfied { constraint: 0 };
  assert_eq!(fixture(&mut builder, Fr::from(2u64)), Err(error.clone()));
  assert_eq!(*seen.borrow(), 0);
  assert_eq!(builder.alloc_private(Fr::ZERO), Err(error.clone()));
  builder.enforce_zero(ConstraintPhase::Pcs, LinearCombination::zero());
  assert_eq!(builder.finish_checked_stream(), Err(error));
  assert_eq!(*seen.borrow(), 0);

  // The first four rows pass; a false final constant row must also poison
  // the builder and cannot be ignored when the full size has been reached.
  let (r1cs, witness) = materialized(Fr::ONE);
  let mut builder =
    R1csBuilder::new_checked_streamed_observed(expected(), 160, |_| Ok(()))
      .unwrap();
  builder.alloc_public(witness.assignment()[1]).unwrap();
  for value in &witness.assignment()[2..] {
    builder.alloc_private(*value).unwrap();
  }
  for (index, row) in r1cs.constraints().iter().enumerate() {
    builder.enforce(
      row.phase,
      row.a.clone(),
      row.b.clone(),
      if index + 1 == r1cs.constraints().len() {
        LinearCombination::one()
      } else {
        row.c.clone()
      },
    );
  }
  assert_eq!(
    builder.finish_checked_stream(),
    Err(R1csError::Unsatisfied { constraint: 4 })
  );
}

#[test]
fn stream_digest_rejects_same_size_matrix_changes_order_and_prefixes() {
  let (r1cs, _) = materialized(Fr::ZERO);
  for changed in 0..5 {
    let mut rows = r1cs.constraints().to_vec();
    match changed {
      0 => rows[1].a = rows[1].a.clone().scale(Fr::from(2u64)),
      1 => rows[1].b = rows[1].b.clone().scale(Fr::from(2u64)),
      2 => rows[1].c = rows[1].c.clone().scale(Fr::from(2u64)),
      3 => rows.swap(1, 3),
      4 => {
        rows[1].a = LinearCombination::from_variable(Variable::from_index(4))
      },
      _ => unreachable!(),
    }
    let mut stream = R1csShapeStreamV0::new(expected()).unwrap();
    for row in &rows {
      stream.observe(row).unwrap();
    }
    assert_eq!(
      stream.finish(),
      Err(R1csError::StreamMismatch),
      "change={changed}"
    );
  }
  for prefix in 0..r1cs.constraints().len() {
    let mut stream = R1csShapeStreamV0::new(expected()).unwrap();
    for row in &r1cs.constraints()[..prefix] {
      stream.observe(row).unwrap();
    }
    assert_eq!(stream.finish(), Err(R1csError::StreamMismatch));
  }
  let mut stream = R1csShapeStreamV0::new(expected()).unwrap();
  for row in r1cs.constraints() {
    stream.observe(row).unwrap();
  }
  let error = stream.observe(&r1cs.constraints()[0]).unwrap_err();
  assert!(matches!(error, R1csError::ResourceLimit { .. }));
  assert_eq!(stream.observe(&r1cs.constraints()[0]), Err(error.clone()));
  assert_eq!(stream.finish(), Err(error));
}

#[test]
fn stream_checks_declared_wires_layout_and_allocation_limit_before_allocation()
{
  let expected = expected();
  for limit in [0, 159] {
    assert!(
      matches!(R1csBuilder::new_checked_streamed_observed(expected.clone(), limit, |_| Ok(())), Err(R1csError::ResourceLimit { resource: "streamed R1CS assignment bytes", limit: actual_limit, actual: 160 }) if actual_limit == limit)
    );
  }
  let unknown = Variable::from_index(expected.variables());
  let mut stream = R1csShapeStreamV0::new(expected.clone()).unwrap();
  assert_eq!(
    stream.observe(&Constraint {
      phase: ConstraintPhase::Pcs,
      a: LinearCombination::from_variable(unknown),
      b: LinearCombination::one(),
      c: LinearCombination::zero()
    }),
    Err(R1csError::UnknownVariable(unknown))
  );
  assert_eq!(stream.finish(), Err(R1csError::UnknownVariable(unknown)));
  for checked in [false, true] {
    let make = || {
      if checked {
        R1csBuilder::new_checked_streamed_observed(
          expected.clone(),
          160,
          |_| Ok(()),
        )
        .unwrap()
      } else {
        R1csBuilder::new_shape_streamed_observed(expected.clone(), |_| Ok(()))
          .unwrap()
      }
    };
    let mut builder = make();
    assert_eq!(builder.alloc_private(Fr::ZERO), Err(R1csError::StreamMismatch));
    assert_eq!(builder.check_status(), Err(R1csError::StreamMismatch));
    let mut builder = make();
    builder.alloc_public(Fr::ZERO).unwrap();
    assert_eq!(builder.alloc_public(Fr::ZERO), Err(R1csError::StreamMismatch));
    let mut builder = make();
    builder.alloc_public(Fr::ZERO).unwrap();
    for _ in 0..3 {
      builder.alloc_private(Fr::ZERO).unwrap();
    }
    assert_eq!(builder.alloc_private(Fr::ZERO), Err(R1csError::StreamMismatch));
    let mut builder = make();
    builder.alloc_public(Fr::ZERO).unwrap();
    builder.alloc_private(Fr::ZERO).unwrap();
    assert_eq!(
      builder.alloc_public(Fr::ZERO),
      Err(R1csError::PublicAfterPrivate)
    );
    // Streamed builders deliberately require allocation before use.
    let mut builder = make();
    let forward = Variable::from_index(1);
    builder.enforce_boolean(ConstraintPhase::Statement, forward);
    assert_eq!(
      builder.check_status(),
      Err(R1csError::UnknownVariable(forward))
    );
    assert_eq!(
      builder.finish_checked_stream(),
      Err(R1csError::UnknownVariable(forward))
    );
    let builder = make();
    assert_eq!(builder.finish_checked_stream(), Err(R1csError::StreamMismatch));
  }
}

#[test]
fn streamed_mode_and_observer_refusals_never_export_unchecked_state() {
  for shape_only in [false, true] {
    let make = || {
      if shape_only {
        R1csBuilder::new_shape_streamed_observed(expected(), |_| Ok(()))
          .unwrap()
      } else {
        R1csBuilder::new_checked_streamed_observed(expected(), 160, |_| Ok(()))
          .unwrap()
      }
    };
    let mut builder = make();
    fixture(&mut builder, Fr::ZERO).unwrap();
    assert_eq!(builder.finish(), Err(R1csError::WrongBuilderMode));
    let mut builder = make();
    fixture(&mut builder, Fr::ZERO).unwrap();
    assert_eq!(builder.finish_projection(), Err(R1csError::WrongBuilderMode));
    let mut builder = make();
    fixture(&mut builder, Fr::ZERO).unwrap();
    assert_eq!(builder.finish_shape(), Err(R1csError::WrongBuilderMode));
    let mut builder = make();
    fixture(&mut builder, Fr::ZERO).unwrap();
    if shape_only {
      assert_eq!(
        builder.finish_checked_stream(),
        Err(R1csError::WrongBuilderMode)
      );
    } else {
      assert_eq!(
        builder.finish_streamed_shape(),
        Err(R1csError::WrongBuilderMode)
      );
    }
  }
  for stop in [1, 5] {
    let error = R1csError::ObserverFailure(format!("row {stop}"));
    let fail = error.clone();
    let mut seen = 0;
    let mut builder =
      R1csBuilder::new_checked_streamed_observed(expected(), 160, move |_| {
        seen += 1;
        if seen == stop { Err(fail.clone()) } else { Ok(()) }
      })
      .unwrap();
    assert_eq!(fixture(&mut builder, Fr::ONE), Err(error.clone()));
    assert_eq!(builder.alloc_private(Fr::ONE), Err(error.clone()));
    assert_eq!(builder.finish_checked_stream(), Err(error));
  }
  assert_eq!(
    R1csBuilder::new().finish_checked_stream(),
    Err(R1csError::WrongBuilderMode)
  );
  assert_eq!(
    R1csBuilder::new_projection().finish_streamed_shape(),
    Err(R1csError::WrongBuilderMode)
  );
}

#[test]
fn empty_stream_and_malformed_expected_census_have_explicit_boundaries() {
  let expected =
    R1csBuilder::new_shape_projection().finish_projection().unwrap();
  let checked = R1csBuilder::new_checked_streamed_observed(
    expected.clone(),
    32,
    |_| Ok(()),
  )
  .unwrap()
  .finish_checked_stream()
  .unwrap();
  let (r1cs, witness) = R1csBuilder::new().finish().unwrap();
  assert_eq!(checked.assignment(), witness.assignment());
  assert_eq!(checked.shape().canonical_digest(), r1cs.digest());
  for bad in 0..4 {
    let mut expected = expected.clone();
    match bad {
      0 => expected.public_variables = u32::MAX,
      1 => expected.census.public_variables = 1,
      2 => expected.census.private_variables = 1,
      3 => expected
        .census
        .constraints_by_phase
        .insert(ConstraintPhase::Pcs, 1)
        .map_or((), |_| ()),
      _ => unreachable!(),
    }
    assert!(R1csShapeStreamV0::new(expected).is_err());
  }
}

#[test]
fn streamed_binary_field_products_preserve_default_and_selected_arithmetic() {
  use crate::{
    F128PreparedProductV1, alloc_f128_private, constrain_f128_multiply,
  };
  for encoding in [
    None,
    Some(F128PreparedProductV1::BooleanCarriesV0),
    Some(F128PreparedProductV1::PolynomialCarriesV1),
  ] {
    let emit = |builder: &mut R1csBuilder, value: u8| {
      if let Some(encoding) = encoding {
        builder
          .enable_f128_preparation_cache_with_product(2, encoding)
          .unwrap();
      }
      let a =
        alloc_f128_private(builder, [value; 16], ConstraintPhase::Pcs).unwrap();
      let b = alloc_f128_private(
        builder,
        [value.wrapping_add(1); 16],
        ConstraintPhase::Pcs,
      )
      .unwrap();
      constrain_f128_multiply(builder, &a, &b, ConstraintPhase::Pcs).unwrap();
    };
    let mut setup = R1csBuilder::new_shape_projection();
    emit(&mut setup, 0);
    let expected = setup.finish_projection().unwrap();
    for value in [0, 37, 255] {
      let mut builder = R1csBuilder::new();
      emit(&mut builder, value);
      let (r1cs, witness) = builder.finish().unwrap();
      let mut builder = R1csBuilder::new_checked_streamed_observed(
        expected.clone(),
        u64::from(expected.variables()) * 32,
        |_| Ok(()),
      )
      .unwrap();
      emit(&mut builder, value);
      let checked = builder.finish_checked_stream().unwrap();
      assert_eq!(checked.assignment(), witness.assignment());
      assert_eq!(checked.shape().canonical_digest(), r1cs.digest());
      assert_eq!(checked.shape().projection(), &expected);
      let mut builder =
        R1csBuilder::new_shape_streamed_observed(expected.clone(), |_| Ok(()))
          .unwrap();
      emit(&mut builder, 0);
      assert_eq!(builder.finish_streamed_shape().unwrap(), *checked.shape());
    }
  }
}
