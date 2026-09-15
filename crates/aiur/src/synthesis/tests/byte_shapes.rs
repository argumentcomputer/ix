// Copyright (c) 2026 Argument Computer Corporation.
// SPDX-License-Identifier: MIT OR Apache-2.0

use super::*;

fn fixed(heights: &[usize], active: &[bool], degrees: &[u8]) -> bool {
  fixed_trace_heights(heights.iter().copied(), active, degrees)
}

#[test]
fn fixed_heights_follow_active_positions_and_require_fixed_tables() {
  assert!(fixed(&[], &[], &[]));
  assert!(fixed(&[0, 0], &[false, false], &[]));
  assert!(fixed(&[0, 256, 0, 65536], &[true, true, false, true], &[3, 8, 16]));
  assert!(fixed(&[0, 256, 0, 65536], &[false, true, false, true], &[8, 16]));
  // The separate global budget guard bounds unfixed circuit degrees.
  assert!(fixed(&[0], &[true], &[255]));
  for (heights, active, degrees) in [
    (vec![256, 65536], vec![false, false], vec![]),
    (vec![], vec![false], vec![]),
    (vec![256], vec![], vec![]),
    (vec![256], vec![true], vec![]),
    (vec![256], vec![false], vec![8]),
    (vec![256], vec![true], vec![7]),
    (vec![256], vec![true], vec![9]),
    (vec![65536], vec![true], vec![15]),
    (vec![65536], vec![true], vec![17]),
    (vec![256, 65536], vec![true, true], vec![16, 8]),
    (vec![256, 65536], vec![false, true], vec![8, 16]),
    (vec![usize::MAX], vec![true], vec![255]),
  ] {
    assert!(!fixed(&heights, &active, &degrees));
  }
}

#[test]
fn public_verify_checks_fixed_byte_heights_before_openings() {
  let (cp, fp) = test_parameters();
  let system = AiurSystem::build(mul_toplevel(), cp, fp);
  let (claim, mut proof) =
    system.prove(0, &[G::ONE, G::ONE], &mut empty_io_buffer());
  system.verify(&claim, &proof).unwrap();
  let mut position = 0;
  for (circuit, &active) in system.system.circuits.iter().zip(&proof.active) {
    if active {
      let original = proof.log_degrees[position];
      if circuit.preprocessed_height != 0 {
        for changed in [original - 1, original + 1] {
          proof.log_degrees[position] = changed;
          // The generic shape check has no direct fixed-height condition.
          // Aiur must establish it before relying on fixed byte-table rows.
          system.system.verify_shape(&proof).unwrap();
          assert!(matches!(
            system.verify(&claim, &proof),
            Err(VerificationError::InvalidProofShape)
          ));
        }
      }
      proof.log_degrees[position] = original;
      position += 1;
    }
  }
  system.verify(&claim, &proof).unwrap();
}

#[test]
fn public_verify_checks_fixed_byte_activity_before_openings() {
  let (cp, fp) = test_parameters();
  let system = AiurSystem::build(mul_toplevel(), cp, fp);
  let claim = [function_channel(), G::ZERO, G::ONE, G::ONE, G::ONE];
  let traces = system
    .circuit_shapes()
    .iter()
    .enumerate()
    .map(|(index, shape)| {
      let height = if index == 0 { 4 } else { shape.preprocessed_height };
      let mut rows = vec![G::ZERO; height * shape.main_width];
      if index == 0 {
        rows[..4].fill(G::ONE);
        rows[4] = G::ONE;
      }
      RowMajorMatrix::new(rows, shape.main_width)
    })
    .collect();
  let mut witness = SystemWitness::from_stage_1(traces, &system.system);
  // There are no unary-byte queries. The generic shape check permits
  // omission, but the PCS rejects a matrix without opening points. Aiur
  // makes the required activity explicit before entering that verifier.
  witness.traces[1].values.clear();
  witness.lookups[1] =
    multi_stark::lookup::LookupValues::builder(0, &system.slot_arg_widths(1))
      .finish();
  let proof = system.system.prove(&system.key, &claim, witness);
  assert_eq!(proof.active, vec![true, false, true]);
  assert_eq!(proof.log_degrees, vec![2, 16]);
  system.system.verify_shape(&proof).unwrap();
  assert!(matches!(
    system.verify(&claim, &proof),
    Err(VerificationError::InvalidProofShape)
  ));
}
