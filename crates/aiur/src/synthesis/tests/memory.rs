// Copyright (c) 2026 Argument Computer Corporation.
// SPDX-License-Identifier: MIT OR Apache-2.0

use super::*;
use multi_stark::eval::{VarValues, eval_expr};

fn values<'a>(row: &'a [G], next: &'a [G]) -> VarValues<'a, G> {
  VarValues {
    preprocessed: [&[], &[]],
    main: [row, next],
    stage2: [&[], &[]],
    publics: &[],
    is_first_row: G::ZERO,
    is_last_row: G::ZERO,
    is_transition: G::ONE,
  }
}

#[test]
fn memory_transitions_allow_wrap_but_reject_duplicate_pointers() {
  for width in [1, 4, 8] {
    let (memory, constraints, _) = Memory::build(width);
    for first in [G::from_u8(7), -G::from_u8(2)] {
      let rows: Vec<_> = (0..4)
        .map(|index| {
          let mut row = vec![G::ZERO; memory.width];
          row[0] = G::ONE;
          row[1] = G::ONE;
          row[2] = first + G::from_u64(index);
          row[3..].fill(G::from_u64(index + 3));
          row
        })
        .collect();
      for pair in rows.windows(2) {
        assert!(constraints.iter().all(|constraint| eval_expr(
          constraint,
          &values(&pair[0], &pair[1])
        ) == G::ZERO));
      }
      let mut duplicate = rows[1].clone();
      duplicate[2] = rows[0][2];
      assert_ne!(
        eval_expr(&constraints[3], &values(&rows[0], &duplicate)),
        G::ZERO,
        "the pointer transition must reject consecutive duplicates"
      );
      let mut inactive = rows[0].clone();
      inactive[0] = G::ZERO;
      inactive[1] = G::ZERO;
      assert_ne!(
        eval_expr(&constraints[2], &values(&inactive, &rows[1])),
        G::ZERO,
        "an active successor requires an active predecessor"
      );
    }
  }
}

/// The memory table is immutable witness data, with no first-pointer-zero
/// constraint or requirement for a preceding runtime store. Here pointers
/// start at p-1 and wrap to zero. The zero pointer must load the second row.
#[test]
fn supplied_wrapping_memory_load_verifies() {
  let function = Function {
    body: Block { ops: vec![Op::Load(1, 0)], ctrl: Ctrl::Return(0, vec![1]) },
    layout: FunctionLayout {
      input_size: 1,
      selectors: 1,
      auxiliaries: 8,
      lookups: 5,
    },
    entry: true,
    constrained: true,
  };
  let (cp, fp) = test_parameters();
  let system =
    AiurSystem::build(with_singleton_circuits(vec![function], vec![1]), cp, fp);
  let expected = G::from_u8(8);
  let claim = [function_channel(), G::ZERO, G::ZERO, expected];
  let traces = system
    .circuit_shapes()
    .iter()
    .enumerate()
    .map(|(index, shape)| {
      let height = if index < 2 { 4 } else { shape.preprocessed_height };
      let mut rows = vec![G::ZERO; height * shape.main_width];
      if index == 0 {
        rows[1] = G::ONE;
        rows[2] = G::ONE;
        rows[9] = expected;
      } else if index == 1 {
        assert_eq!(shape.main_width, 4);
        rows[..8].copy_from_slice(&[
          G::ZERO,
          G::ONE,
          -G::ONE,
          G::from_u8(7),
          G::ONE,
          G::ONE,
          G::ZERO,
          expected,
        ]);
      } else if index == 3 {
        rows[6] = G::from_u8(3);
      }
      RowMajorMatrix::new(rows, shape.main_width)
    })
    .collect();
  let witness = SystemWitness::from_stage_1(traces, &system.system);
  let proof = system.system.prove(&system.key, &claim, witness);
  system.verify(&claim, &proof).expect("wrapping immutable memory is allowed");
}
