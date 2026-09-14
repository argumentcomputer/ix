// Copyright (c) 2026 Argument Computer Corporation.
// SPDX-License-Identifier: MIT OR Apache-2.0

use super::*;
use crate::FxIndexMap;
use multi_stark::eval::{VarValues, eval_expr};

fn empty_branch_toplevel() -> Toplevel {
  let dead = Block {
    ops: vec![Op::Store(vec![])],
    ctrl: Ctrl::Match(0, FxIndexMap::default(), None),
  };
  let called = Block {
    ops: vec![Op::Call(1, vec![], 1, false)],
    ctrl: Ctrl::Return(0, vec![1]),
  };
  let caller = Function {
    body: Block {
      ops: vec![],
      ctrl: Ctrl::Match(
        0,
        [(G::ZERO, dead), (G::ONE, called)].into_iter().collect(),
        None,
      ),
    },
    layout: FunctionLayout {
      input_size: 1,
      selectors: 1,
      auxiliaries: 14,
      lookups: 8,
    },
    entry: true,
    constrained: true,
  };
  let callee = Function {
    body: Block {
      ops: vec![Op::Const(G::ONE)],
      ctrl: Ctrl::Return(0, vec![0]),
    },
    layout: FunctionLayout {
      input_size: 0,
      selectors: 1,
      auxiliaries: 7,
      lookups: 4,
    },
    entry: false,
    constrained: true,
  };
  with_singleton_circuits(vec![caller, callee], vec![0, 1])
}

#[test]
fn empty_branch_preserves_honest_execution() {
  let (cp, fp) = test_parameters();
  let system = AiurSystem::build(empty_branch_toplevel(), cp, fp);
  let (claim, proof) = system.prove(0, &[G::ONE], &mut empty_io_buffer());
  assert_eq!(claim, vec![function_channel(), G::ZERO, G::ONE, G::ONE]);
  system.verify(&claim, &proof).unwrap();
}

/// A zero-leaf branch can still emit a lookup. Its inactive store must not
/// turn the selected call's function channel into a memory channel merely
/// because the entire circuit has one return selector.
#[test]
fn empty_branch_cannot_redirect_a_call_to_memory() {
  let top = empty_branch_toplevel();
  top.validate_lookup_shapes().unwrap();
  top.validate_row_counts().unwrap();
  assert!(!top.circuit_is_branchless(0));
  assert!(top.circuit_is_branchless(1));
  let (_, expected) =
    top.execute(0, vec![G::ONE], &mut empty_io_buffer()).unwrap();
  assert_eq!(expected, vec![G::ONE]);
  let forged = G::from_u8(7);
  assert_ne!(expected, vec![forged]);
  let (constraints, lookups) = top.build_constraints(0);
  let mut row = vec![G::ZERO; constraints.width];
  row[0] = G::ONE;
  row[1] = G::ONE;
  row[2] = G::ONE;
  row[9] = forged;
  let values = VarValues {
    preprocessed: [&[], &[]],
    main: [&row, &row],
    stage2: [&[], &[]],
    publics: &[],
    is_first_row: G::ONE,
    is_last_row: G::ZERO,
    is_transition: G::ONE,
  };
  assert!(constraints.zeros.iter().all(|c| eval_expr(c, &values) == G::ZERO));
  let combined: Vec<_> =
    lookups[4].args.iter().map(|arg| eval_expr(arg, &values)).collect();
  assert_eq!(combined, vec![function_channel(), G::ONE, forged, G::ONE]);
  let (cp, fp) = test_parameters();
  let system = AiurSystem::build(top, cp, fp);
  let claim = vec![function_channel(), G::ZERO, G::ONE, forged];
  let traces = system
    .circuit_shapes()
    .iter()
    .enumerate()
    .map(|(index, shape)| {
      let height = if index < 4 { 4 } else { shape.preprocessed_height };
      let mut rows = vec![G::ZERO; height * shape.main_width];
      if index == 0 {
        rows[..shape.main_width].copy_from_slice(&row);
      } else if index == 3 {
        // Supply the redirected memory lookup, with no callee row.
        rows[..4].copy_from_slice(&[G::ONE, G::ONE, forged + forged, G::ONE]);
      } else if index == 5 {
        // The caller's root rank and all three call-gap pairs are zero.
        rows[Bytes2::RANGE_CHECK_COLUMN] = G::from_u8(6);
      }
      RowMajorMatrix::new(rows, shape.main_width)
    })
    .collect();
  let witness = SystemWitness::from_stage_1(traces, &system.system);
  let proof = system.system.prove(&system.key, &claim, witness);
  assert!(
    system.verify(&claim, &proof).is_err(),
    "an inactive empty branch redirected a call to memory and supplied a false public result"
  );
}
