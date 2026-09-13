// Copyright (c) 2026 Argument Computer Corporation.
// SPDX-License-Identifier: MIT OR Apache-2.0

use super::*;

fn snapshot_body(tag: usize) -> Block {
  fn ret(size: usize) -> Block {
    Block { ops: vec![], ctrl: Ctrl::Return(0, vec![0; size]) }
  }
  fn yield_values(size: usize) -> Block {
    Block { ops: vec![], ctrl: Ctrl::Yield(0, vec![0; size]) }
  }
  fn matched(arm: Option<Block>, fallback: Option<Block>) -> Block {
    Block {
      ops: vec![],
      ctrl: Ctrl::Match(
        0,
        arm.into_iter().map(|block| (G::ZERO, block)).collect(),
        fallback.map(Box::new),
      ),
    }
  }
  fn continued(arm: Block, continuation: Block) -> Block {
    Block {
      ops: vec![],
      ctrl: Ctrl::MatchContinue(
        0,
        [(G::ZERO, arm)].into_iter().collect(),
        Some(Box::new(yield_values(2))),
        2,
        0,
        0,
        Box::new(continuation),
      ),
    }
  }
  match tag {
    0..=2 => ret(tag),
    3 => yield_values(0),
    4 => yield_values(1),
    5 => matched(Some(ret(1)), Some(ret(1))),
    6 => matched(Some(ret(0)), Some(ret(1))),
    7 => matched(Some(ret(1)), None),
    8 => matched(None, None),
    9 => continued(yield_values(2), ret(1)),
    10 => continued(ret(1), ret(1)),
    11 => continued(ret(0), ret(1)),
    12 => continued(yield_values(1), ret(1)),
    13 => continued(yield_values(2), yield_values(0)),
    14 => continued(continued(yield_values(2), yield_values(2)), ret(1)),
    15 => continued(continued(yield_values(2), yield_values(1)), ret(1)),
    16 => matched(Some(continued(ret(1), ret(1))), Some(ret(1))),
    _ => unreachable!(),
  }
}

fn snapshot_function(
  body: Block,
  inputs: usize,
  entry: bool,
  constrained: bool,
) -> Function {
  Function {
    body,
    layout: FunctionLayout {
      input_size: inputs,
      selectors: 1,
      auxiliaries: 7,
      lookups: 4,
    },
    entry,
    constrained,
  }
}

/// Compare the Rust guards with the total Lean validators across nested
/// control forms, all small arities, visibility and advice-call modes.
/// These fixtures test structural checks independently of layout/value
/// validation; they are never passed to the constraint emitter.
#[test]
fn lookup_shape_snapshot() -> std::io::Result<()> {
  let header = b"Aiur lookup shapes v2\n";
  let mut out = header.to_vec();
  for tag in 0..17 {
    for size in 0..4 {
      out.push(u8::from(snapshot_body(tag).returns_have_size(size)));
    }
  }
  for tag in 0..17 {
    for callee_inputs in 0..4 {
      for caller_inputs in 0..4 {
        for outputs in 0..4 {
          for advice in [false, true] {
            for constrained in [false, true] {
              let caller = snapshot_function(
                Block {
                  ops: vec![Op::Call(
                    1,
                    vec![0; caller_inputs],
                    outputs,
                    advice,
                  )],
                  ctrl: Ctrl::Return(0, vec![]),
                },
                3,
                true,
                true,
              );
              let callee = snapshot_function(
                snapshot_body(tag),
                callee_inputs,
                false,
                constrained,
              );
              let top = Toplevel {
                functions: vec![caller, callee],
                memory_sizes: vec![],
                circuits: vec![],
                call_components: vec![],
              };
              out.push(u8::from(top.validate_lookup_shapes().is_ok()));
            }
          }
        }
      }
    }
  }
  for tag in 0..17 {
    for inputs in 0..4 {
      for entry in [false, true] {
        for constrained in [false, true] {
          let top = Toplevel {
            functions: vec![snapshot_function(
              snapshot_body(tag),
              inputs,
              entry,
              constrained,
            )],
            memory_sizes: vec![],
            circuits: vec![],
            call_components: vec![],
          };
          // Cache construction includes the structural program guard.
          let shapes = top.checked_claim_shapes();
          for channel in 0..3 {
            for function in [0, 1, 99] {
              for arguments in 0..7 {
                let mut claim = vec![G::from_u8(channel), G::from_u8(function)];
                claim.extend(std::iter::repeat_n(G::ZERO, arguments));
                out.push(u8::from(
                  shapes
                    .as_ref()
                    .is_ok_and(|shapes| valid_claim_shape(shapes, &claim)),
                ));
              }
            }
          }
        }
      }
    }
  }
  assert_eq!(out.len(), header.len() + 21_556);
  if let Some(path) = std::env::var_os("IX_LOOKUP_SHAPE_SNAPSHOT") {
    std::fs::write(path, out)?;
  }
  Ok(())
}

/// The public claim omits rank zero. A short return at rank seven must not
/// be interpreted as a public return value of seven through zero padding.
#[test]
fn public_output_cannot_be_supplied_by_a_displaced_rank() {
  let function = Function {
    body: Block { ops: vec![], ctrl: Ctrl::Return(0, vec![]) },
    layout: FunctionLayout {
      input_size: 0,
      selectors: 1,
      auxiliaries: 7,
      lookups: 4,
    },
    entry: true,
    constrained: true,
  };
  let (cp, fp) = test_parameters();
  let system =
    AiurSystem::build(with_singleton_circuits(vec![function], vec![]), cp, fp);
  let claim = [function_channel(), G::ZERO, G::from_u8(7)];
  let traces = system
    .circuit_shapes()
    .iter()
    .enumerate()
    .map(|(index, shape)| {
      let height = if index == 0 { 4 } else { shape.preprocessed_height };
      let mut rows = vec![G::ZERO; height * shape.main_width];
      if index == 0 {
        // Active empty return, multiplicity one, rank seven.
        rows[..3].copy_from_slice(&[G::ONE, G::ONE, G::from_u8(7)]);
      } else if index == 2 {
        // All three rank pairs are supplied by the fixed byte table.
        rows[6] = G::from_u8(2);
        rows[(7 * 256) * shape.main_width + 6] = G::ONE;
      }
      RowMajorMatrix::new(rows, shape.main_width)
    })
    .collect();
  let witness = SystemWitness::from_stage_1(traces, &system.system);
  let proof = system.system.prove(&system.key, &claim, witness);
  assert!(
    system.verify(&claim, &proof).is_err(),
    "a call-order rank was accepted as a function output"
  );
}

#[test]
fn public_claim_shape_checks_channel_visibility_and_arity() {
  let top = mul_toplevel();
  let shapes = top.checked_claim_shapes().unwrap();
  assert!(valid_claim_shape(
    &shapes,
    &[G::ZERO, G::ZERO, G::ONE, G::ONE, G::ONE]
  ));
  for claim in [
    vec![],
    vec![G::ZERO],
    vec![G::ONE, G::ZERO, G::ONE, G::ONE, G::ONE],
    vec![G::ZERO, G::ONE, G::ONE, G::ONE, G::ONE],
    vec![G::ZERO, G::ZERO, G::ONE],
    vec![G::ZERO, G::ZERO, G::ONE, G::ONE],
    vec![G::ZERO, G::ZERO, G::ONE, G::ONE, G::ONE, G::ZERO],
  ] {
    assert!(!valid_claim_shape(&shapes, &claim));
  }
  for constrained in [true, false] {
    let mut top = mul_toplevel();
    top.functions[0].entry = !constrained;
    top.functions[0].constrained = constrained;
    assert!(!valid_claim_shape(
      &top.checked_claim_shapes().unwrap(),
      &[G::ZERO; 5]
    ));
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
fn cached_arities_match_recursive_checks_for_nested_control_flow() {
  fn returning(size: usize) -> Block {
    Block { ops: vec![], ctrl: Ctrl::Return(0, vec![0; size]) }
  }
  fn yielding() -> Block {
    Block { ops: vec![], ctrl: Ctrl::Yield(0, vec![0; 2]) }
  }
  fn matching(arms: Vec<Block>, fallback: Option<Block>) -> Block {
    Block {
      ops: vec![],
      ctrl: Ctrl::Match(
        0,
        arms
          .into_iter()
          .enumerate()
          .map(|(i, b)| (G::from_usize(i), b))
          .collect(),
        fallback.map(Box::new),
      ),
    }
  }
  fn continued(arm: Block, continuation: Block) -> Block {
    Block {
      ops: vec![],
      ctrl: Ctrl::MatchContinue(
        0,
        [(G::ZERO, arm)].into_iter().collect(),
        Some(Box::new(yielding())),
        2,
        0,
        0,
        Box::new(continuation),
      ),
    }
  }
  let mut bodies = vec![
    matching(vec![], None),
    matching(vec![], Some(returning(0))),
    continued(yielding(), matching(vec![], None)),
  ];
  for a in 0..3 {
    bodies.push(returning(a));
    bodies.push(continued(yielding(), returning(a)));
    bodies.push(continued(continued(returning(a), yielding()), returning(a)));
    for b in 0..3 {
      bodies.push(matching(vec![returning(a), returning(b)], None));
      bodies.push(matching(vec![returning(a)], Some(returning(b))));
      bodies.push(continued(returning(a), returning(b)));
      bodies.push(continued(continued(returning(a), yielding()), returning(b)));
    }
  }
  for body in bodies {
    let mut top = call_and_memory_toplevel();
    // Test the cached public boundary and each call-site boundary against
    // the original recursive predicate, including vacuous and mixed returns.
    top.functions[0].body.ops.clear();
    top.functions[1].entry = true;
    top.functions[1].body = body;
    let shapes = top.checked_claim_shapes().unwrap();
    for outputs in 0..4 {
      let expected = top.functions[1].body.returns_have_size(outputs);
      let mut claim = vec![function_channel(), G::ONE, G::ZERO];
      claim.resize(3 + outputs, G::ZERO);
      assert_eq!(valid_claim_shape(&shapes, &claim), expected);
      top.functions[0].body.ops = vec![Op::Call(1, vec![0], outputs, false)];
      assert_eq!(top.validate_lookup_shapes().is_ok(), expected);
    }
  }
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
