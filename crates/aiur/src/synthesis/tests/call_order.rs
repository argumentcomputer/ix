// Copyright (c) 2026 Argument Computer Corporation.
// SPDX-License-Identifier: MIT OR Apache-2.0

use super::*;
use crate::bytecode::{CallComponent, Circuit};
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
        auxiliaries: 14,
        lookups: 8,
      },
      entry: i == 0,
      constrained: true,
    })
    .collect();
  let mut top = with_singleton_circuits(functions, vec![]);
  if grouped {
    top.circuits.truncate(1);
    top.circuits.push(Circuit {
      members: vec![1, 2],
      layout: FunctionLayout {
        input_size: 1,
        selectors: 2,
        auxiliaries: 14,
        lookups: 8,
      },
    });
  }
  top
}

fn component_cycle_toplevel(grouped: bool) -> Toplevel {
  let mut top = cycle_toplevel(grouped);
  top.call_components = vec![
    CallComponent { order: 0, ranked: false },
    CallComponent { order: 1, ranked: true },
    CallComponent { order: 1, ranked: true },
  ];
  // The acyclic root keeps only multiplicity, output and the bound callee
  // rank. The mutually recursive providers retain all their rank checks.
  top.functions[0].layout.auxiliaries = 3;
  top.functions[0].layout.lookups = 2;
  top.circuits[0].layout = top.functions[0].layout;
  top
}

#[test]
fn component_certificates_reject_unranked_cycles_and_invalid_orders() {
  let mut top = component_cycle_toplevel(false);
  assert_eq!(top.validate_call_components(), Ok(()));
  top.call_components[1].ranked = false;
  assert!(top.validate_call_components().is_err());
  top.call_components[1].ranked = true;
  top.call_components[2].order = 2;
  assert!(top.validate_call_components().is_err(), "backward edge");
  top.call_components[2].order = 1;
  top.call_components[0].order = 3;
  assert!(top.validate_call_components().is_err(), "out-of-bounds order");
  top.call_components.pop();
  assert!(top.validate_call_components().is_err(), "missing component");

  let mut top = component_cycle_toplevel(false);
  top.functions[0].body.ops = vec![Op::Call(3, vec![0], 1, false)];
  assert!(top.validate_call_components().is_err(), "missing callee");
}

#[test]
fn component_checker_visits_branches_defaults_and_continuations() {
  for location in 0..3 {
    let mut top = component_cycle_toplevel(false);
    let backedge = || Block {
      ops: vec![Op::Call(0, vec![0], 1, false)],
      ctrl: Ctrl::Yield(0, vec![1]),
    };
    let empty = || Block { ops: vec![], ctrl: Ctrl::Yield(0, vec![0]) };
    top.functions[1].body = Block {
      ops: vec![],
      ctrl: Ctrl::MatchContinue(
        0,
        [(G::ZERO, if location == 0 { backedge() } else { empty() })]
          .into_iter()
          .collect(),
        Some(Box::new(if location == 1 { backedge() } else { empty() })),
        1,
        0,
        0,
        Box::new(if location == 2 { backedge() } else { empty() }),
      ),
    };
    assert!(
      top.validate_call_components().is_err(),
      "hidden edge at {location}"
    );
  }
}

#[test]
#[should_panic(expected = "call violates the static component order")]
fn system_construction_rejects_a_forged_component_certificate() {
  let mut top = component_cycle_toplevel(false);
  top.call_components[2].ranked = false;
  let (cp, fp) = test_parameters();
  let _ = AiurSystem::build(top, cp, fp);
}

/// f promotes and shares g(n); g recurses to zero, then calls acyclic h.
/// Values above 255 also detect accidental range checks on acyclic members
/// when their operation columns overlap a recursive member's rank bytes.
fn component_promotion_toplevel(grouped: bool) -> Toplevel {
  let root = Function {
    body: Block {
      ops: vec![
        Op::Call(1, vec![0], 1, true),
        Op::Call(1, vec![0], 1, false),
        Op::Call(1, vec![0], 1, false),
        Op::Add(2, 3),
      ],
      ctrl: Ctrl::Return(0, vec![4]),
    },
    layout: FunctionLayout {
      input_size: 1,
      selectors: 1,
      auxiliaries: 6,
      lookups: 3,
    },
    entry: true,
    constrained: true,
  };
  let recursive = Function {
    body: Block {
      ops: vec![],
      ctrl: Ctrl::Match(
        0,
        [(
          G::ZERO,
          Block {
            ops: vec![Op::Call(2, vec![0], 1, false)],
            ctrl: Ctrl::Return(0, vec![1]),
          },
        )]
        .into_iter()
        .collect(),
        Some(Box::new(Block {
          ops: vec![
            Op::Const(G::ONE),
            Op::Sub(0, 1),
            Op::Call(1, vec![2], 1, false),
          ],
          ctrl: Ctrl::Return(1, vec![3]),
        })),
      ),
    },
    layout: FunctionLayout {
      input_size: 1,
      selectors: 2,
      auxiliaries: 15,
      lookups: 8,
    },
    entry: false,
    constrained: true,
  };
  let leaf = Function {
    body: Block {
      ops: vec![Op::Const(G::from_u64(1_000)), Op::Add(0, 1)],
      ctrl: Ctrl::Return(0, vec![2]),
    },
    layout: FunctionLayout {
      input_size: 1,
      selectors: 1,
      auxiliaries: 1,
      lookups: 1,
    },
    entry: false,
    constrained: true,
  };
  let mut top = with_singleton_circuits(vec![root, recursive, leaf], vec![]);
  top.call_components = vec![
    CallComponent { order: 0, ranked: false },
    CallComponent { order: 1, ranked: true },
    CallComponent { order: 2, ranked: false },
  ];
  if grouped {
    top.circuits = vec![Circuit {
      members: vec![0, 1, 2],
      layout: FunctionLayout {
        input_size: 1,
        selectors: 4,
        auxiliaries: 15,
        lookups: 8,
      },
    }];
  }
  top
}

#[test]
fn component_boundaries_preserve_promotion_sharing_and_mixed_groups() {
  for grouped in [false, true] {
    let (cp, fp) = test_parameters();
    let system =
      AiurSystem::build(component_promotion_toplevel(grouped), cp, fp);
    for n in [0, 4] {
      let (claim, proof) =
        system.prove(0, &[G::from_u8(n)], &mut empty_io_buffer());
      assert_eq!(
        claim,
        vec![function_channel(), G::ZERO, G::from_u8(n), G::from_u64(2_000)]
      );
      system
        .verify(&claim, &proof)
        .expect("component boundary proof must verify");
    }
  }
}

#[test]
fn component_boundary_cannot_displace_a_recursive_provider_rank() {
  let (cp, fp) = test_parameters();
  let system = AiurSystem::build(component_promotion_toplevel(false), cp, fp);
  let mut io = empty_io_buffer();
  let input = vec![G::from_u8(4)];
  let (mut record, output) =
    system.toplevel.execute(0, input.clone(), &mut io).unwrap();
  let mut traces = Vec::new();
  let mut ranges = RankRanges::default();
  for i in 0..system.toplevel.circuits.len() {
    let (trace, _, counts) =
      system.toplevel.witness_data(i, &record, &io, &system.slot_arg_widths(i));
    ranges = crate::call_order::merge_ranges(ranges, counts);
    traces.push(trace);
  }
  record.bytes2_queries.add_rank_ranges(ranges.clone());
  traces.push(Bytes1.witness_data(&record, &system.slot_arg_widths(3)).0);
  traces.push(Bytes2.witness_data(&record, &system.slot_arg_widths(4)).0);
  let mut claim = vec![function_channel(), G::ZERO];
  claim.extend(input);
  claim.extend(output);
  assert!(
    lookup_balance(&system.toplevel, &traces, &ranges, &claim).is_empty()
  );

  // Root columns: input, selector, multiplicity, hint output, call output,
  // bound rank, second call output, bound rank. Replace only one binding.
  assert_ne!(traces[0].values[5], G::ZERO);
  traces[0].values[5] = G::ZERO;
  let (constraints, _) = system.toplevel.build_constraints(0);
  assert!(constraints.zeros.iter().all(|expr| eval_expr(
    expr,
    &row_values(&traces[0].values[..constraints.width])
  ) == G::ZERO));
  assert_eq!(
    lookup_balance(&system.toplevel, &traces, &ranges, &claim).len(),
    2
  );
  let witness = SystemWitness::from_stage_1(traces, &system.system);
  let proof = system.system.prove(&system.key, &claim, witness);
  assert!(
    system.verify(&claim, &proof).is_err(),
    "boundary rank must bind the provider"
  );
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

/// Compute exact tuple balance independently of random lookup compression.
fn lookup_balance(
  top: &Toplevel,
  traces: &[RowMajorMatrix<G>],
  ranges: &RankRanges,
  claim: &[G],
) -> FxHashMap<Vec<G>, G> {
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
  balance.retain(|_, count| *count != G::ZERO);
  balance
}

#[test]
fn mutual_cycles_reject_at_the_closing_lookup_in_both_partitions() {
  for (grouped, specialized) in
    [(false, false), (true, false), (false, true), (true, true)]
  {
    let (cp, fp) = test_parameters();
    let top = if specialized {
      component_cycle_toplevel(grouped)
    } else {
      cycle_toplevel(grouped)
    };
    let system = AiurSystem::build(top, cp, fp);
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
          if specialized && member == 0 {
            row[aux + 1] = output;
            row[aux + 2] = G::ONE;
          } else {
            fill_bytes(&mut row[aux + 1..aux + 7], member as u64, &mut ranges);
            row[aux + 7] = output;
            let gap = if member == 2 { RANK_BOUND - 2 } else { 0 };
            fill_bytes(&mut row[aux + 8..aux + 14], gap, &mut ranges);
          }
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
    assert_eq!(violated, 0, "all local polynomial constraints hold");
    // Only the closing h -> g lookup fails: its derived rank exceeds the
    // bounded rank on g's return. All byte-range lookups balance exactly.
    let message =
      |rank| vec![function_channel(), G::ONE, input, output, G::from_u64(rank)];
    assert_eq!(
      lookup_balance(&system.toplevel, &traces, &ranges, &claim),
      [(message(RANK_BOUND + 1), G::ONE), (message(1), -G::ONE)]
        .into_iter()
        .collect()
    );
    let witness = SystemWitness::from_stage_1(traces, &system.system);
    let proof = system.system.prove(&system.key, &claim, witness);
    assert!(
      system.verify(&claim, &proof).is_err(),
      "cyclic return accepted (grouped={grouped}, specialized={specialized})"
    );
  }
}

#[test]
fn call_lookup_checks_strict_unsigned_order() {
  let top = cycle_toplevel(false);
  let (constraints, lookups) = top.build_constraints(0);
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
    fill_bytes(&mut row[10..16], gap, &mut ranges);
    assert!(
      constraints
        .zeros
        .iter()
        .all(|expr| eval_expr(expr, &row_values(&row)) == G::ZERO)
    );
    let requested_rank =
      eval_expr(lookups[4].args.last().unwrap(), &row_values(&row));
    assert_eq!(
      requested_rank == G::from_u64(child),
      accepted,
      "ranks {parent} -> {child}, gap {gap}"
    );
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
          // All ranks are zero. A forged "byte" -1 makes caller + 1 + gap
          // request rank zero, but cannot pass the byte table.
          rows[10] = -G::ONE;
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
            rows[10..16].fill(G::from_u8(255));
          } else {
            // 256 in the high byte packs to 2^48. The call lookup matches
            // this rank, but the function's rank range check must fail.
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
      auxiliaries: 15,
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
      auxiliaries: 21,
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
