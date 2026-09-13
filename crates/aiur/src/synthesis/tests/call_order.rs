// Copyright (c) 2026 Argument Computer Corporation.
// SPDX-License-Identifier: MIT OR Apache-2.0

use super::*;
use crate::call_order::{RANK_BOUND, RANK_BYTES, RankRanges};
use multi_stark::eval::{VarValues, eval_expr};

fn cycle_toplevel(grouped: bool) -> Toplevel {
  // Public f calls g; g and h call each other without a base case.
  let functions = [1, 2, 1]
    .into_iter()
    .enumerate()
    .map(|(i, callee)| Function {
      body: Block {
        ops: vec![Op::Call(callee, vec![0], 1, false)],
        ctrl: Ctrl::Return(0, vec![1]),
      },
      layout: FunctionLayout {
        input_size: 1,
        selectors: 1,
        auxiliaries: 15,
        lookups: 8,
      },
      entry: i == 0,
      constrained: true,
    })
    .collect();
  let mut top = with_singleton_circuits(functions, vec![]);
  if grouped {
    top.circuits.truncate(1);
    top.circuits.push(crate::bytecode::Circuit {
      members: vec![1, 2],
      layout: FunctionLayout {
        input_size: 1,
        selectors: 2,
        auxiliaries: 15,
        lookups: 8,
      },
    });
  }
  top
}

fn fill_bytes(row: &mut [G], value: u64, ranges: &mut RankRanges) {
  assert!(value < RANK_BOUND);
  let bytes = value.to_le_bytes();
  for (field, byte) in row.iter_mut().zip(&bytes[..RANK_BYTES]) {
    *field = G::from_u8(*byte);
  }
  for pair in bytes[..RANK_BYTES].as_chunks::<2>().0 {
    *ranges.entry([pair[0], pair[1]]).or_insert(G::ZERO) += G::ONE;
  }
}

fn row_values(row: &[G]) -> VarValues<'_, G> {
  VarValues {
    preprocessed: [&[], &[]],
    main: [row, row],
    stage2: [&[], &[]],
    publics: &[],
    is_first_row: G::ONE,
    is_last_row: G::ZERO,
    is_transition: G::ONE,
  }
}

fn normalized(mut args: Vec<G>) -> Vec<G> {
  while args.last() == Some(&G::ZERO) {
    args.pop();
  }
  args
}

/// Verify exact tuple balance independently of random lookup compression.
fn assert_lookup_balance(
  top: &Toplevel,
  traces: &[RowMajorMatrix<G>],
  ranges: &RankRanges,
  claim: &[G],
) {
  let mut balance = FxHashMap::<Vec<G>, G>::default();
  *balance.entry(normalized(claim.to_vec())).or_insert(G::ZERO) += G::ONE;
  for (i, circuit) in top.circuits.iter().enumerate() {
    let (_, lookups) = top.build_constraints(i);
    for row in traces[i].values.chunks_exact(circuit.layout.width()) {
      let values = row_values(row);
      for lookup in &lookups {
        let args =
          lookup.args.iter().map(|arg| eval_expr(arg, &values)).collect();
        *balance.entry(normalized(args)).or_insert(G::ZERO) +=
          eval_expr(&lookup.multiplicity, &values);
      }
    }
  }
  for ([a, b], count) in ranges {
    *balance
      .entry(normalized(vec![
        crate::u8_range_check_channel(),
        G::from_u8(*a),
        G::from_u8(*b),
      ]))
      .or_insert(G::ZERO) -= *count;
  }
  assert!(
    balance.values().all(|count| *count == G::ZERO),
    "unbalanced supplied witness"
  );
}

#[test]
fn mutual_cycles_reject_with_balanced_lookups_in_both_partitions() {
  for grouped in [false, true] {
    let (cp, fp) = test_parameters();
    let system = AiurSystem::build(cycle_toplevel(grouped), cp, fp);
    let input = G::from_u8(3);
    let output = G::from_u8(7);
    let claim = vec![function_channel(), G::ZERO, input, output];
    let mut ranges = RankRanges::default();
    let mut traces = Vec::new();
    let mut violated = 0;
    for (i, shape) in system.circuit_shapes().iter().enumerate() {
      let is_function = i < system.toplevel.circuits.len();
      let height = if is_function { 4 } else { shape.preprocessed_height };
      let mut rows = vec![G::ZERO; height * shape.main_width];
      if is_function {
        let circuit = &system.toplevel.circuits[i];
        let (constraints, _) = system.toplevel.build_constraints(i);
        for (offset, &member) in circuit.members.iter().enumerate() {
          let row = &mut rows
            [offset * shape.main_width..(offset + 1) * shape.main_width];
          row[0] = input;
          row[1 + offset] = G::ONE;
          let aux = 1 + circuit.layout.selectors;
          row[aux] = if member == 1 { G::from_u8(2) } else { G::ONE };
          fill_bytes(&mut row[aux + 1..aux + 7], member as u64, &mut ranges);
          row[aux + 7] = output;
          row[aux + 8] =
            G::from_usize(if member == 2 { 1 } else { member + 1 });
          let gap = if member == 2 { RANK_BOUND - 2 } else { 0 };
          fill_bytes(&mut row[aux + 9..aux + 15], gap, &mut ranges);
          violated += constraints
            .zeros
            .iter()
            .filter(|expr| eval_expr(expr, &row_values(row)) != G::ZERO)
            .count();
        }
      } else if i == system.toplevel.circuits.len() + 1 {
        // Bytes2 is the last circuit (there are no memories).
        for ([a, b], count) in &ranges {
          rows[(256 * usize::from(*a) + usize::from(*b)) * shape.main_width
            + 6] = *count;
        }
      }
      traces.push(RowMajorMatrix::new(rows, shape.main_width));
    }
    assert_eq!(
      violated, 1,
      "only the closing h -> g call should violate a polynomial"
    );
    assert_lookup_balance(&system.toplevel, &traces, &ranges, &claim);
    let witness = SystemWitness::from_stage_1(traces, &system.system);
    let proof = system.system.prove(&system.key, &claim, witness);
    assert!(
      system.verify(&claim, &proof).is_err(),
      "cyclic return accepted (grouped={grouped})"
    );
  }
}

#[test]
fn call_order_polynomial_checks_strict_unsigned_order() {
  let top = cycle_toplevel(false);
  let (constraints, _) = top.build_constraints(0);
  for (parent, child, gap, accepted) in [
    (0, 1, 0, true),
    (0, RANK_BOUND - 1, RANK_BOUND - 2, true),
    (RANK_BOUND - 2, RANK_BOUND - 1, 0, true),
    (0, 0, 0, false),
    (1, 0, RANK_BOUND - 2, false),
    (RANK_BOUND - 1, 0, 0, false),
  ] {
    let mut row = vec![G::ZERO; constraints.width];
    let mut ranges = RankRanges::default();
    row[1] = G::ONE;
    row[2] = G::ONE;
    fill_bytes(&mut row[3..9], parent, &mut ranges);
    row[10] = G::from_u64(child);
    fill_bytes(&mut row[11..17], gap, &mut ranges);
    let satisfied = constraints
      .zeros
      .iter()
      .all(|expr| eval_expr(expr, &row_values(&row)) == G::ZERO);
    assert_eq!(satisfied, accepted, "ranks {parent} -> {child}, gap {gap}");
  }
}

#[test]
fn out_of_range_gaps_cannot_hide_a_cycle_in_field_arithmetic() {
  let (cp, fp) = test_parameters();
  let system = AiurSystem::build(cycle_toplevel(false), cp, fp);
  let claim = vec![function_channel(), G::ZERO, G::from_u8(3), G::from_u8(7)];
  let traces =
    system
      .circuit_shapes()
      .iter()
      .enumerate()
      .map(|(i, shape)| {
        let mut rows = vec![
          G::ZERO;
          if i < 3 {
            4 * shape.main_width
          } else {
            shape.preprocessed_height * shape.main_width
          }
        ];
        if i < 3 {
          rows[0] = claim[2];
          rows[1] = G::ONE;
          rows[2] = G::from_u8(if i == 1 { 2 } else { 1 });
          rows[9] = claim[3];
          // All ranks are zero. A forged "byte" -1 makes 0 - 0 - 1 - gap
          // vanish as a field expression, but cannot pass the byte table.
          rows[11] = -G::ONE;
          let (constraints, _) = system.toplevel.build_constraints(i);
          assert!(constraints.zeros.iter().all(|expr| eval_expr(
            expr,
            &row_values(&rows[..shape.main_width])
          ) == G::ZERO));
        } else if i == 4 {
          // Five valid zero-byte pairs per function, plus one impossible
          // (-1, 0) pair. Supply every valid pair and no fabricated table row.
          rows[6] = G::from_u8(15);
        }
        RowMajorMatrix::new(rows, shape.main_width)
      })
      .collect();
  let witness = SystemWitness::from_stage_1(traces, &system.system);
  let proof = system.system.prove(&system.key, &claim, witness);
  assert!(
    system.verify(&claim, &proof).is_err(),
    "unbounded gap allowed cyclic justification"
  );
}

#[test]
fn out_of_range_function_rank_is_rejected_by_the_byte_table() {
  let mut top = cycle_toplevel(false);
  top.functions.truncate(2);
  top.circuits.truncate(2);
  top.functions[1].body = Block {
    ops: vec![Op::Const(G::from_u8(7))],
    ctrl: Ctrl::Return(0, vec![1]),
  };
  top.functions[1].layout.auxiliaries = 7;
  top.functions[1].layout.lookups = 4;
  top.circuits[1].layout = top.functions[1].layout;
  let (cp, fp) = test_parameters();
  let system = AiurSystem::build(top, cp, fp);
  let claim = vec![function_channel(), G::ZERO, G::from_u8(3), G::from_u8(7)];
  let traces =
    system
      .circuit_shapes()
      .iter()
      .enumerate()
      .map(|(i, shape)| {
        let mut rows = vec![
          G::ZERO;
          if i < 2 {
            4 * shape.main_width
          } else {
            shape.preprocessed_height * shape.main_width
          }
        ];
        if i < 2 {
          rows[0] = claim[2];
          rows[1] = G::ONE;
          rows[2] = G::ONE;
          if i == 0 {
            rows[9] = claim[3];
            rows[10] = G::from_u64(RANK_BOUND);
            rows[11..17].fill(G::from_u8(255));
          } else {
            // 256 in the high byte packs to 2^48. The edge's field equality
            // and all ordinary constraints hold; the rank range check must fail.
            rows[8] = G::from_u64(256);
          }
          let (constraints, _) = system.toplevel.build_constraints(i);
          assert!(constraints.zeros.iter().all(|expr| eval_expr(
            expr,
            &row_values(&rows[..shape.main_width])
          ) == G::ZERO));
        } else if i == 3 {
          rows[6] = G::from_u8(5);
          rows[(256 * 255 + 255) * shape.main_width + 6] = G::from_u8(3);
        }
        RowMajorMatrix::new(rows, shape.main_width)
      })
      .collect();
  let witness = SystemWitness::from_stage_1(traces, &system.system);
  let proof = system.system.prove(&system.key, &claim, witness);
  assert!(
    system.verify(&claim, &proof).is_err(),
    "unbounded function rank accepted"
  );
}

#[test]
fn finite_recursive_calls_verify() {
  let base = Block {
    ops: vec![Op::Const(G::from_u8(7))],
    ctrl: Ctrl::Return(0, vec![1]),
  };
  let step = Block {
    ops: vec![Op::Const(G::ONE), Op::Sub(0, 1), Op::Call(0, vec![2], 1, false)],
    ctrl: Ctrl::Return(1, vec![3]),
  };
  let function = Function {
    body: Block {
      ops: vec![],
      ctrl: Ctrl::Match(
        0,
        [(G::ZERO, base)].into_iter().collect(),
        Some(Box::new(step)),
      ),
    },
    layout: FunctionLayout {
      input_size: 1,
      selectors: 2,
      auxiliaries: 16,
      lookups: 8,
    },
    entry: true,
    constrained: true,
  };
  let (cp, fp) = test_parameters();
  let system =
    AiurSystem::build(with_singleton_circuits(vec![function], vec![]), cp, fp);
  for n in [0, 1, 7] {
    let (claim, proof) =
      system.prove(0, &[G::from_u8(n)], &mut empty_io_buffer());
    assert_eq!(
      claim,
      vec![function_channel(), G::ZERO, G::from_u8(n), G::from_u8(7)]
    );
    system.verify(&claim, &proof).expect("finite recursion must verify");
  }
}

#[test]
fn shared_callee_keeps_one_consistent_rank() {
  let root = Function {
    body: Block {
      ops: vec![
        Op::Call(1, vec![0], 1, false),
        Op::Call(1, vec![0], 1, false),
        Op::Add(1, 2),
      ],
      ctrl: Ctrl::Return(0, vec![3]),
    },
    layout: FunctionLayout {
      input_size: 1,
      selectors: 1,
      auxiliaries: 23,
      lookups: 12,
    },
    entry: true,
    constrained: true,
  };
  let leaf = Function {
    body: Block {
      ops: vec![Op::Const(G::ONE), Op::Add(0, 1)],
      ctrl: Ctrl::Return(0, vec![2]),
    },
    layout: FunctionLayout {
      input_size: 1,
      selectors: 1,
      auxiliaries: 7,
      lookups: 4,
    },
    entry: false,
    constrained: true,
  };
  let (cp, fp) = test_parameters();
  let system = AiurSystem::build(
    with_singleton_circuits(vec![root, leaf], vec![]),
    cp,
    fp,
  );
  let (claim, proof) =
    system.prove(0, &[G::from_u8(3)], &mut empty_io_buffer());
  assert_eq!(
    claim,
    vec![function_channel(), G::ZERO, G::from_u8(3), G::from_u8(8)]
  );
  system.verify(&claim, &proof).expect("shared callee must verify");
}
