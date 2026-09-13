use super::*;
use crate::{
  FflonkBlindingV1, KzgUniversalSrsV1, preprocess_fflonk,
  preprocess_fflonk_to_file, prove_fflonk, prove_fflonk_checked,
  prove_fflonk_checked_with_file_workspace, required_fflonk_srs_degree,
  verify_fflonk,
};
use ark_bls12_381::{G1Affine, G2Affine};
use ark_ec::{AffineRepr, CurveGroup};
use ix_terminal_circuit::R1csBuilder;
use std::io::Cursor;

fn fixture(builder: &mut R1csBuilder, seed: u64) -> Result<(), R1csError> {
  let value = Fr::from(seed);
  let public = builder.alloc_public(value)?;
  let inputs = (1..=4)
    .map(|i| builder.alloc_private(value + Fr::from(i)))
    .collect::<Result<Vec<_>, _>>()?;
  let product = builder.alloc_private(value * (value + Fr::ONE))?;
  let bit = builder.alloc_private(Fr::from(seed % 2))?;
  let sum = builder.alloc_private(value * Fr::from(5u64) + Fr::from(10u64))?;
  builder.enforce(
    ConstraintPhase::Statement,
    LinearCombination::from_variable(public),
    LinearCombination::from_variable(inputs[0]),
    LinearCombination::from_variable(product),
  );
  builder.enforce_boolean(ConstraintPhase::Transcript, bit);
  let mut wide = LinearCombination::from_variable(public)
    .minus(&LinearCombination::from_variable(sum));
  for (index, variable) in inputs.iter().copied().enumerate() {
    wide = wide.term(variable, Fr::ONE);
    builder.enforce_zero(
      ConstraintPhase::Pcs,
      LinearCombination::from_variable(variable)
        .minus(&LinearCombination::from_variable(public))
        .term(Variable::ONE, -Fr::from(index as u64 + 1)),
    );
  }
  builder.enforce_zero(ConstraintPhase::Zerocheck, wide);
  builder.check_status()
}

fn expected() -> (R1csProjectionV1, PlonkGateCensusV1) {
  let projection = PlonkGateProjectionV1::new();
  let mut builder =
    R1csBuilder::new_shape_projection_observed(projection.observer());
  fixture(&mut builder, 0).unwrap();
  let r1cs = builder.finish_projection().unwrap();
  let plonk = projection.finish(&r1cs).unwrap();
  (r1cs, plonk)
}

fn streamed_assignment(seed: u64) -> FflonkCheckedWitnessV1 {
  let (r1cs, _) = expected();
  let mut builder = R1csBuilder::new_checked_streamed_observed(
    r1cs.clone(),
    u64::from(r1cs.variables()) * 32,
    |_| Ok(()),
  )
  .unwrap();
  fixture(&mut builder, seed).unwrap();
  let checked = builder.finish_checked_stream().unwrap();
  let assignment_pointer = checked.assignment().as_ptr();
  let checked = FflonkCheckedWitnessV1::from_streamed(checked);
  assert_eq!(checked.assignment().as_ptr(), assignment_pointer);
  checked
}

#[test]
fn streamed_plonk_matches_every_gate_copy_target_and_checked_witness() {
  let (r1cs_expected, plonk_expected) = expected();
  let memory =
    plan_plonk_stream_memory(r1cs_expected.variables(), &plonk_expected)
      .unwrap();
  for seed in [0, 3, 41] {
    let mut builder = R1csBuilder::new();
    fixture(&mut builder, seed).unwrap();
    let (r1cs, witness) = builder.finish().unwrap();
    let original = arithmetize_r1cs(&r1cs).unwrap();
    for shape_only in [false, true] {
      let stream = PlonkArithmetizationStreamV0::new(
        r1cs_expected.clone(),
        plonk_expected.clone(),
        memory.peak_payload_bytes,
      )
      .unwrap();
      let n = usize::try_from(plonk_expected.domain_size).unwrap();
      assert_eq!(stream.state.borrow().sink.inner.gates.capacity(), n);
      let mut builder = if shape_only {
        R1csBuilder::new_shape_streamed_observed(
          r1cs_expected.clone(),
          stream.observer(),
        )
        .unwrap()
      } else {
        R1csBuilder::new_checked_streamed_observed(
          r1cs_expected.clone(),
          u64::from(r1cs_expected.variables()) * 32,
          stream.observer(),
        )
        .unwrap()
      };
      fixture(&mut builder, if shape_only { 0 } else { seed }).unwrap();
      assert_eq!(stream.state.borrow().sink.inner.gates.capacity(), n);
      if shape_only {
        assert_eq!(
          builder.finish_streamed_shape().unwrap().canonical_digest(),
          r1cs.digest()
        );
      } else {
        let checked = FflonkCheckedWitnessV1::from_streamed(
          builder.finish_checked_stream().unwrap(),
        );
        assert_eq!(
          checked,
          FflonkCheckedWitnessV1::new(&r1cs, witness.clone()).unwrap()
        );
      }
      let actual = stream.finish().unwrap();
      assert_eq!(actual, original);
      assert_eq!(actual.census(), &plonk_expected);
      assert_eq!(actual.gates.capacity(), n);
      assert!(actual.sigma.iter().all(|column| column.capacity() == n));
      let checked = streamed_assignment(seed);
      assert_eq!(
        lower_checked_plonk_witness(&actual, &checked).unwrap(),
        lower_plonk_witness(&original, &r1cs, &witness).unwrap()
      );
    }
  }
}

#[test]
fn stream_memory_admission_counts_all_dense_payloads_and_never_allocates_large_probe()
 {
  let (r1cs, plonk) = expected();
  let plan = plan_plonk_stream_memory(r1cs.variables(), &plonk).unwrap();
  assert_eq!(
    plan.gate_bytes,
    plonk.domain_size * size_of::<PlonkGateV1>() as u64
  );
  assert_eq!(
    plan.copy_target_bytes,
    plonk.domain_size * 3 * size_of::<PlonkCellV1>() as u64
  );
  assert_eq!(
    plan.copy_tail_bytes,
    (u64::from(r1cs.variables()) + plonk.auxiliary_wires) * 8
  );
  for limit in [0, plan.gate_bytes, plan.peak_payload_bytes - 1] {
    assert!(matches!(
      PlonkArithmetizationStreamV0::new(r1cs.clone(), plonk.clone(), limit),
      Err(PlonkArithmetizationError::R1cs(R1csError::ResourceLimit { .. }))
    ));
  }
  let n = crate::FFLONK_MAX_BASE_DOMAIN;
  let census =
    size_census(2, n - 4, 123, BTreeMap::from([(ConstraintPhase::Pcs, n - 4)]))
      .unwrap();
  let plan = plan_plonk_stream_memory(4096, &census).unwrap();
  assert_eq!(plan.gate_bytes, n * size_of::<PlonkGateV1>() as u64);
  assert_eq!(plan.copy_target_bytes, n * 3 * size_of::<PlonkCellV1>() as u64);
  assert_eq!(plan.copy_tail_bytes, (4096 + 123) * 8);
  assert_eq!(
    plan.peak_payload_bytes,
    plan.gate_bytes + plan.copy_target_bytes + plan.copy_tail_bytes
  );
  eprintln!(
    "streamed PLONK payload model at n=2^30: gate={} copy_targets={} tails={} bytes; no arrays allocated and NOT whole-pipeline RSS admission",
    plan.gate_bytes, plan.copy_target_bytes, plan.copy_tail_bytes
  );
  let too_large =
    size_census(2, n - 3, 0, BTreeMap::from([(ConstraintPhase::Pcs, n - 3)]))
      .unwrap();
  assert!(
    matches!(plan_plonk_stream_memory(4096, &too_large), Err(PlonkArithmetizationError::DomainTooLarge { maximum_domain, .. }) if maximum_domain == n)
  );
  let mut overflow = census.clone();
  overflow.auxiliary_wires = u64::MAX;
  assert_eq!(
    plan_plonk_stream_memory(4096, &overflow),
    Err(PlonkArithmetizationError::CountOverflow)
  );
  for change in 0..3 {
    let mut bad = plonk.clone();
    match change {
      0 => bad.padding_rows += 1,
      1 => bad.domain_size *= 2,
      2 => *bad.rows_by_phase.get_mut(&ConstraintPhase::Pcs).unwrap() += 1,
      _ => unreachable!(),
    }
    assert_eq!(
      plan_plonk_stream_memory(r1cs.variables(), &bad),
      Err(PlonkArithmetizationError::StreamCensusMismatch)
    );
  }
  assert_eq!(
    plan_plonk_stream_memory(0, &plonk),
    Err(PlonkArithmetizationError::StreamCensusMismatch)
  );
  assert_eq!(
    plan_plonk_stream_memory(1, &plonk),
    Err(PlonkArithmetizationError::StreamCensusMismatch)
  );
}

#[test]
fn independently_hashed_observer_cannot_substitute_a_same_size_matrix() {
  let (expected, plonk) = expected();
  let bytes = plan_plonk_stream_memory(expected.variables(), &plonk)
    .unwrap()
    .peak_payload_bytes;
  let stream =
    PlonkArithmetizationStreamV0::new(expected.clone(), plonk, bytes).unwrap();
  let mut observe = stream.observer();
  let mut first = true;
  let mut builder =
    R1csBuilder::new_shape_streamed_observed(expected, move |constraint| {
      let mut altered = constraint.clone();
      if first {
        altered.a = altered.a.scale(Fr::from(2u64));
        first = false;
      }
      observe(&altered)
    })
    .unwrap();
  fixture(&mut builder, 0).unwrap();
  builder.finish_streamed_shape().unwrap();
  assert_eq!(
    stream.finish(),
    Err(PlonkArithmetizationError::R1cs(R1csError::StreamMismatch))
  );
}

#[test]
fn stream_prefix_unknown_wire_wrong_census_and_live_observer_fail_closed() {
  let (expected, plonk) = expected();
  let bytes = plan_plonk_stream_memory(expected.variables(), &plonk)
    .unwrap()
    .peak_payload_bytes;
  let make = || {
    PlonkArithmetizationStreamV0::new(expected.clone(), plonk.clone(), bytes)
      .unwrap()
  };
  assert_eq!(
    make().finish(),
    Err(PlonkArithmetizationError::R1cs(R1csError::StreamMismatch))
  );
  let stream = make();
  let observe = stream.observer();
  assert_eq!(
    stream.finish(),
    Err(PlonkArithmetizationError::StreamObserverAttached)
  );
  drop(observe);
  let stream = make();
  let mut observe = stream.observer();
  let unknown = Variable::from_index(expected.variables());
  let row = Constraint {
    phase: ConstraintPhase::Pcs,
    a: LinearCombination::from_variable(unknown),
    b: LinearCombination::one(),
    c: LinearCombination::zero(),
  };
  assert_eq!(observe(&row), Err(R1csError::UnknownVariable(unknown)));
  assert_eq!(observe(&row), Err(R1csError::UnknownVariable(unknown)));
  drop(observe);
  assert_eq!(
    stream.finish(),
    Err(PlonkArithmetizationError::R1cs(R1csError::UnknownVariable(unknown)))
  );
  // A plausible but undersized PLONK census cannot let the gate or auxiliary
  // arrays grow. It also cannot turn an independently complete R1CS into a key.
  for reduce_auxiliaries in [false, true] {
    let mut small = plonk.clone();
    if reduce_auxiliaries {
      small.auxiliary_wires -= 1;
    } else {
      small.constraint_rows -= 1;
      *small.rows_by_phase.get_mut(&ConstraintPhase::Zerocheck).unwrap() -= 1;
      small = size_census(
        small.public_input_rows,
        small.constraint_rows,
        small.auxiliary_wires,
        small.rows_by_phase,
      )
      .unwrap();
    }
    let stream =
      PlonkArithmetizationStreamV0::new(expected.clone(), small, bytes)
        .unwrap();
    let mut builder = R1csBuilder::new_shape_streamed_observed(
      expected.clone(),
      stream.observer(),
    )
    .unwrap();
    let error = fixture(&mut builder, 0).unwrap_err();
    assert!(matches!(error, R1csError::ResourceLimit { .. }));
    assert_eq!(builder.finish_streamed_shape(), Err(error.clone()));
    assert_eq!(stream.finish(), Err(PlonkArithmetizationError::R1cs(error)));
  }
  let mut wrong_public = plonk;
  wrong_public.public_input_rows = 0;
  assert!(matches!(
    PlonkArithmetizationStreamV0::new(expected, wrong_public, bytes),
    Err(PlonkArithmetizationError::StreamCensusMismatch)
  ));
}

fn test_srs(degree: u64) -> KzgUniversalSrsV1 {
  let tau = Fr::from(29u64);
  let mut value = Fr::ONE;
  let powers = (0..=degree)
    .map(|_| {
      let point =
        G1Affine::generator().mul_bigint(value.into_bigint()).into_affine();
      value *= tau;
      point
    })
    .collect();
  KzgUniversalSrsV1::new(
    powers,
    G2Affine::generator(),
    G2Affine::generator().mul_bigint(tau.into_bigint()).into_affine(),
  )
  .unwrap()
}

#[test]
fn streamed_setup_and_checked_witness_keep_actual_file_key_and_proof_bytes() {
  let mut builder = R1csBuilder::new();
  fixture(&mut builder, 3).unwrap();
  let (r1cs, witness) = builder.finish().unwrap();
  let original = arithmetize_r1cs(&r1cs).unwrap();
  let (expected, plonk) = expected();
  let bytes = plan_plonk_stream_memory(expected.variables(), &plonk)
    .unwrap()
    .peak_payload_bytes;
  let stream =
    PlonkArithmetizationStreamV0::new(expected.clone(), plonk, bytes).unwrap();
  let mut builder =
    R1csBuilder::new_shape_streamed_observed(expected, stream.observer())
      .unwrap();
  fixture(&mut builder, 0).unwrap();
  builder.finish_streamed_shape().unwrap();
  let actual = stream.finish().unwrap();
  let srs =
    test_srs(required_fflonk_srs_degree(actual.census().domain_size).unwrap());
  let key = preprocess_fflonk(&srs, original).unwrap();
  let file =
    preprocess_fflonk_to_file(&srs, actual, Cursor::new(Vec::new())).unwrap();
  assert_eq!(key.digest(), file.digest());
  assert_eq!(key.verification_key(), file.verification_key());
  for blinding in [
    FflonkBlindingV1::default(),
    FflonkBlindingV1 {
      wire_evaluations: core::array::from_fn(|i| Fr::from(i as u64 + 41)),
      z_coefficients: [Fr::from(71u64), Fr::from(73u64), Fr::from(79u64)],
    },
  ] {
    let baseline = prove_fflonk(&srs, &key, &r1cs, &witness, blinding).unwrap();
    let memory =
      prove_fflonk_checked(&srs, &file, streamed_assignment(3), blinding)
        .unwrap();
    let streamed = prove_fflonk_checked_with_file_workspace(
      &srs,
      &file,
      streamed_assignment(3),
      blinding,
      Cursor::new(Vec::new()),
    )
    .unwrap();
    assert_eq!(memory, baseline);
    assert_eq!(streamed, baseline);
    assert_eq!(
      verify_fflonk(
        &file.verification_key(),
        &streamed.proof,
        &streamed.public_inputs
      ),
      Ok(true)
    );
    assert_eq!(
      verify_fflonk(
        &file.verification_key(),
        &streamed.proof,
        &[Fr::from(4u64)]
      ),
      Ok(false)
    );
    let mut corrupt = streamed.proof;
    corrupt.evaluations[0] += Fr::ONE;
    assert_eq!(
      verify_fflonk(
        &file.verification_key(),
        &corrupt,
        &streamed.public_inputs
      ),
      Ok(false)
    );
  }
  // A checked stream for another relation is still not a witness for this key.
  let empty = R1csBuilder::new_shape_projection().finish_projection().unwrap();
  let wrong = R1csBuilder::new_checked_streamed_observed(empty, 32, |_| Ok(()))
    .unwrap()
    .finish_checked_stream()
    .unwrap();
  assert!(matches!(
    prove_fflonk_checked(
      &srs,
      &file,
      FflonkCheckedWitnessV1::from_streamed(wrong),
      FflonkBlindingV1::default()
    ),
    Err(crate::FflonkProverError::Arithmetization(
      PlonkArithmetizationError::R1csDigestMismatch
    ))
  ));
}

#[test]
fn ranged_field_stream_lowers_the_complete_product_without_r1cs_matrices() {
  use ix_terminal_circuit::{
    F128PreparedProductV1, alloc_f128_private, constrain_f128_multiply,
  };
  let emit = |builder: &mut R1csBuilder, value: u8| {
    builder
      .enable_f128_preparation_cache_with_product(
        2,
        F128PreparedProductV1::PolynomialCarriesV1,
      )
      .unwrap();
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
  let projection = PlonkGateProjectionV1::new();
  let mut builder =
    R1csBuilder::new_shape_projection_observed(projection.observer());
  emit(&mut builder, 0);
  let expected = builder.finish_projection().unwrap();
  let plonk = projection.finish(&expected).unwrap();
  let bytes = plan_plonk_stream_memory(expected.variables(), &plonk)
    .unwrap()
    .peak_payload_bytes;
  let stream =
    PlonkArithmetizationStreamV0::new(expected.clone(), plonk, bytes).unwrap();
  let mut builder = R1csBuilder::new_checked_streamed_observed(
    expected.clone(),
    u64::from(expected.variables()) * 32,
    stream.observer(),
  )
  .unwrap();
  emit(&mut builder, 39);
  let checked = FflonkCheckedWitnessV1::from_streamed(
    builder.finish_checked_stream().unwrap(),
  );
  let actual = stream.finish().unwrap();
  let mut builder = R1csBuilder::new();
  emit(&mut builder, 39);
  let (r1cs, witness) = builder.finish().unwrap();
  assert_eq!(actual, arithmetize_r1cs(&r1cs).unwrap());
  assert_eq!(
    lower_checked_plonk_witness(&actual, &checked).unwrap(),
    lower_plonk_witness(&actual, &r1cs, &witness).unwrap()
  );
}
