// Copyright (c) 2026 Argument Computer Corporation.
// SPDX-License-Identifier: MIT OR Apache-2.0

use super::*;

/// Lookup compression zero-pads messages. An empty return must not become
/// an output of zero just because both messages have the same fingerprint.
#[test]
fn public_output_cannot_be_supplied_by_zero_padding() {
  let function = Function {
    body: Block { ops: vec![], ctrl: Ctrl::Return(0, vec![]) },
    layout: FunctionLayout {
      input_size: 0,
      selectors: 1,
      auxiliaries: 1,
      lookups: 1,
    },
    entry: true,
    constrained: true,
  };
  let (cp, fp) = test_parameters();
  let system =
    AiurSystem::build(with_singleton_circuits(vec![function], vec![]), cp, fp);
  let claim = [function_channel(), G::ZERO, G::ZERO];
  let traces = system
    .circuit_shapes()
    .iter()
    .enumerate()
    .map(|(index, shape)| {
      let height = if index == 0 { 4 } else { shape.preprocessed_height };
      let mut rows = vec![G::ZERO; height * shape.main_width];
      if index == 0 {
        // Active empty return, multiplicity one.
        rows[..2].copy_from_slice(&[G::ONE, G::ONE]);
      }
      RowMajorMatrix::new(rows, shape.main_width)
    })
    .collect();
  let witness = SystemWitness::from_stage_1(traces, &system.system);
  let proof = system.system.prove(&system.key, &claim, witness);
  system.system.verify(&claim, &proof).unwrap();
  assert!(
    matches!(
      system.verify(&claim, &proof),
      Err(VerificationError::InvalidClaim)
    ),
    "zero padding was accepted as a function output"
  );
  let (claim, proof) = system.prove(0, &[], &mut empty_io_buffer());
  system.verify(&claim, &proof).unwrap();
}

#[test]
#[should_panic(expected = "invalid Aiur lookup shapes")]
fn system_construction_rejects_mismatched_call_outputs() {
  let mut top = call_and_memory_toplevel();
  top.functions[0].body.ops[0] = Op::Call(1, vec![0], 2, false);
  // Reserve the extra output column so a layout error cannot mask the
  // mismatched function-message boundary.
  top.functions[0].layout.auxiliaries += 1;
  top.circuits[0].layout = top.functions[0].layout;
  let (cp, fp) = test_parameters();
  AiurSystem::build(top, cp, fp);
}

#[test]
fn public_claim_shape_checks_channel_visibility_and_arity() {
  let top = mul_toplevel();
  assert!(top.valid_claim_shape(&[G::ZERO, G::ZERO, G::ONE, G::ONE, G::ONE]));
  for claim in [
    vec![],
    vec![G::ZERO],
    vec![G::ONE, G::ZERO, G::ONE, G::ONE, G::ONE],
    vec![G::ZERO, G::ONE, G::ONE, G::ONE, G::ONE],
    vec![G::ZERO, G::ZERO, G::ONE],
    vec![G::ZERO, G::ZERO, G::ONE, G::ONE],
    vec![G::ZERO, G::ZERO, G::ONE, G::ONE, G::ONE, G::ZERO],
  ] {
    assert!(!top.valid_claim_shape(&claim));
  }
  for constrained in [true, false] {
    let mut top = mul_toplevel();
    top.functions[0].entry = !constrained;
    top.functions[0].constrained = constrained;
    assert!(!top.valid_claim_shape(&[G::ZERO; 5]));
  }
}

#[test]
fn constrained_calls_check_both_message_boundaries() {
  let top = call_and_memory_toplevel();
  top.validate_lookup_shapes().unwrap();
  for malformed in [
    Op::Call(1, vec![], 1, false),
    Op::Call(1, vec![0], 0, false),
    Op::Call(1, vec![0], 2, false),
    Op::Call(99, vec![0], 1, false),
  ] {
    let mut top = call_and_memory_toplevel();
    top.functions[0].body.ops.push(malformed);
    assert!(top.validate_lookup_shapes().is_err());
  }
  let mut top = call_and_memory_toplevel();
  top.functions[1].constrained = false;
  assert!(top.validate_lookup_shapes().is_err());
  // An unconstrained call supplies advice and emits no function lookup.
  let mut top = mul_toplevel();
  top.functions[0].body.ops.push(Op::Call(99, vec![], 17, true));
  top.validate_lookup_shapes().unwrap();
}

#[test]
fn nested_continuations_check_returns_and_yields() {
  fn returning(size: usize) -> Block {
    Block { ops: vec![], ctrl: Ctrl::Return(0, vec![0; size]) }
  }
  fn yielding(size: usize) -> Block {
    Block { ops: vec![], ctrl: Ctrl::Yield(0, vec![0; size]) }
  }
  fn continuation(arm: Block, continued: Block) -> Block {
    Block {
      ops: vec![],
      ctrl: Ctrl::MatchContinue(
        0,
        [(G::ZERO, arm)].into_iter().collect(),
        Some(Box::new(yielding(2))),
        2,
        0,
        0,
        Box::new(continued),
      ),
    }
  }
  for arm in [returning(1), yielding(2)] {
    let body = continuation(arm, returning(1));
    assert!(body.returns_have_size(1));
    assert!(!body.returns_have_size(0));
    let mut top = mul_toplevel();
    top.functions[0].body = body;
    top.validate_lookup_shapes().unwrap();
  }
  assert!(!continuation(returning(0), returning(1)).returns_have_size(1));
  assert!(!continuation(yielding(2), returning(0)).returns_have_size(1));
  for body in [
    yielding(2),
    continuation(yielding(1), returning(1)),
    continuation(yielding(2), yielding(2)),
    continuation(continuation(yielding(2), yielding(1)), returning(1)),
  ] {
    let mut top = mul_toplevel();
    top.functions[0].body = body;
    assert!(top.validate_lookup_shapes().is_err());
  }
  let mut top = mul_toplevel();
  top.functions[0].body =
    continuation(continuation(returning(1), yielding(2)), returning(1));
  top.validate_lookup_shapes().unwrap();
}
