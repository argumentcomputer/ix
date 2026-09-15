use super::{memory_summary, setup};
use flock_prover::{
  field::F128,
  matrix_fold::{Weight, bilinear},
};
use ix_stage4_trace::{
  BinaryLinearMapError, BinaryLinearMapLimitsV0, BinaryLinearMapV0,
  BinaryLinearReferenceV0 as Ref, BinaryLinearValidationLimitsV0,
  F128MatrixSideV1,
};
use std::time::Instant;

const SHAPE: BinaryLinearMapLimitsV0 =
  BinaryLinearMapLimitsV0 { inputs: 16_384, outputs: 16_384, xors: 100_000 };
const CHECK: BinaryLinearValidationLimitsV0 = BinaryLinearValidationLimitsV0 {
  coefficient_words: 64_000_000,
  source_entries: 48_000_000,
};

fn point(bits: u32, seed: u64) -> Vec<F128> {
  (0..bits)
    .map(|i| {
      F128::new(
        seed.wrapping_mul(u64::from(i) + 19),
        (seed ^ u64::from(i)).wrapping_mul(0x9e3779b97f4a7c15),
      )
    })
    .collect()
}

fn evaluate(map: &BinaryLinearMapV0, row: &[F128], column: &[F128]) -> F128 {
  let inputs = (0..map.inputs())
    .map(|i| {
      column.iter().enumerate().fold(F128::ONE, |p, (bit, x)| {
        p * (*x + if i >> bit & 1 == 0 { F128::ONE } else { F128::ZERO })
      })
    })
    .collect::<Vec<_>>();
  let resolve = |r, operations: &[F128]| match r {
    Ref::Zero => F128::ZERO,
    Ref::Input(i) => inputs[i as usize],
    Ref::Xor(i) => operations[i as usize],
  };
  let mut operations = Vec::with_capacity(map.xors().len());
  for &(left, right) in map.xors() {
    operations.push(resolve(left, &operations) + resolve(right, &operations));
  }
  let mut values =
    map.outputs().iter().map(|&r| resolve(r, &operations)).collect::<Vec<_>>();
  for x in row {
    values = values
      .as_chunks::<2>()
      .0
      .iter()
      .map(|p| p[0] + *x * (p[0] + p[1]))
      .collect();
  }
  assert_eq!(values.len(), 1);
  values[0]
}

#[test]
#[ignore = "exact approved BLAKE3 coefficient/native differential; no proof or terminal materialization"]
fn structural_blake3_maps_match_every_coefficient_and_native_value() {
  let setup = setup();
  let replay = crate::compile_exec_replay(&setup).unwrap();
  let started = Instant::now();
  let maps =
    crate::compile_exec_blake3_root_maps(&replay, SHAPE, CHECK).unwrap();
  eprintln!(
    "BLAKE3 exact linear-map compilation and coefficient check: {:.3}s; digest {:?}; {}",
    started.elapsed().as_secs_f64(),
    maps.digest(),
    memory_summary()
  );
  assert!(std::ptr::eq(maps.exec_setup(), &setup));
  for (id, map) in maps.matrices() {
    let ty = &setup.verifier_shape().registry.boolean_types()
      [usize::try_from(id.table).unwrap()];
    let matrix = match id.side {
      F128MatrixSideV1::A => &ty.a_0,
      F128MatrixSideV1::B => &ty.b_0,
    };
    eprintln!(
      "BLAKE3 {:?}: {} nonzeros, {} retained XORs, {} inputs, {} outputs, digest {:?}",
      id.side,
      matrix.rows.iter().map(Vec::len).sum::<usize>(),
      map.xors().len(),
      map.inputs(),
      map.outputs().len(),
      map.digest()
    );
    for seed in [0, 7, 0xa515] {
      let row = point(id.variables, seed);
      let column = point(id.variables, seed + 11);
      assert_eq!(
        evaluate(map, &row, &column),
        bilinear(&Weight::eq(row), &Weight::eq(column), matrix)
      );
    }
    // The actual constant-pin and final padding row are not exempt from the
    // exhaustive coefficient check. Altering either formula must fail.
    for (row, wrong) in [(11_706, Ref::Zero), (16_383, Ref::Input(0))] {
      let mut outputs = map.outputs().to_vec();
      outputs[row] = wrong;
      let bad = BinaryLinearMapV0::compile(
        map.inputs(),
        map.xors().to_vec(),
        outputs,
        SHAPE,
      )
      .unwrap();
      assert_eq!(
        bad.check_rows(&matrix.rows, CHECK),
        Err(BinaryLinearMapError::CoefficientMismatch(row))
      );
    }
  }
  for check in [
    BinaryLinearValidationLimitsV0 { source_entries: 44_442_497, ..CHECK },
    BinaryLinearValidationLimitsV0 { coefficient_words: 0, ..CHECK },
  ] {
    assert!(
      crate::compile_exec_blake3_root_maps(&replay, SHAPE, check).is_err()
    );
  }
}

#[test]
#[ignore = "matrix-free R1CS/PLONK census of BLAKE3 root components only, not a full relation proof"]
fn structural_blake3_root_component_constraint_census() {
  use ix_fflonk::PlonkGateProjectionV1;
  use ix_terminal_circuit::{
    ConstraintPhase, R1csBuilder, alloc_f128_private,
    constrain_f128_binary_linear_table,
  };
  fn bytes(x: F128) -> [u8; 16] {
    (u128::from(x.lo) | (u128::from(x.hi) << 64)).to_le_bytes()
  }
  let setup = setup();
  let replay = crate::compile_exec_replay(&setup).unwrap();
  let maps =
    crate::compile_exec_blake3_root_maps(&replay, SHAPE, CHECK).unwrap();
  for (id, map) in maps.matrices() {
    let started = Instant::now();
    let projection = PlonkGateProjectionV1::new();
    let mut observe = projection.observer();
    let mut count = 0u64;
    let side = id.side;
    let mut builder = R1csBuilder::new_projection_observed(move |c| {
      observe(c);
      count += 1;
      if count.is_multiple_of(10_000_000) {
        eprintln!(
          "BLAKE3 {side:?} component census: {count} constraints, {:.3}s; {}",
          started.elapsed().as_secs_f64(),
          memory_summary()
        );
      }
    });
    let row = point(id.variables, 7);
    let column = point(id.variables, 18);
    let expected = bytes(evaluate(map, &row, &column));
    let phase = ConstraintPhase::MatrixFold;
    let row = row
      .into_iter()
      .map(|x| alloc_f128_private(&mut builder, bytes(x), phase).unwrap())
      .collect::<Vec<_>>();
    let column = column
      .into_iter()
      .map(|x| alloc_f128_private(&mut builder, bytes(x), phase).unwrap())
      .collect::<Vec<_>>();
    let result = constrain_f128_binary_linear_table(
      &mut builder,
      map,
      &row,
      &column,
      phase,
    )
    .unwrap();
    assert_eq!(*result.value(), expected);
    let r1cs = builder.finish_projection().unwrap();
    let plonk = projection.finish_for_sizing(&r1cs).unwrap();
    eprintln!(
      "BLAKE3 {side:?} complete component census {:.3}s: {r1cs:?}; {plonk:?}; {}",
      started.elapsed().as_secs_f64(),
      memory_summary()
    );
  }
}
