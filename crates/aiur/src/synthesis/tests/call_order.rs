// Copyright (c) 2026 Argument Computer Corporation.
// SPDX-License-Identifier: MIT OR Apache-2.0

use super::*;
use crate::bytecode::{CallComponent, Circuit};
use crate::call_order::{RANK_BOUND, RANK_LIMBS, RankRanges};
use multi_stark::eval::{VarValues, eval_expr};
use multi_stark::p3_field::{Field, PrimeField64};

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
        auxiliaries: 8,
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
        auxiliaries: 8,
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
/// Values above 65,535 also detect accidental range checks on acyclic members
/// when their operation columns overlap a recursive member's rank limbs.
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
      auxiliaries: 9,
      lookups: 8,
    },
    entry: false,
    constrained: true,
  };
  let leaf = Function {
    body: Block {
      ops: vec![Op::Const(G::from_u64(1_000_000)), Op::Add(0, 1)],
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
        auxiliaries: 9,
        lookups: 8,
      },
    }];
  }
  top
}

#[test]
fn acyclic_maps_omit_timestamps_without_changing_promoted_call_order() {
  let top = component_promotion_toplevel(false);
  let (record, output) =
    top.execute(0, vec![G::from_u8(4)], &mut empty_io_buffer()).unwrap();
  assert_eq!(output, vec![G::from_u64(2_000_000)]);
  for i in [0, 2] {
    let map = &record.function_queries[i];
    assert_eq!(map.len(), 1);
    assert_eq!(map.completion_entries(), 0);
    assert_eq!(map.get_index(0).unwrap().1.rank, 0);
  }
  let recursive = &record.function_queries[1];
  assert_eq!(recursive.len(), 5);
  assert_eq!(recursive.completion_entries(), 5);
  for n in 0..=4 {
    let row = recursive.get(&[G::from_u64(n)]).unwrap();
    assert_eq!(row.rank, 4 - n, "promoted children finish before parents");
    assert_eq!(row.multiplicity, G::from_u8(if n == 4 { 2 } else { 1 }));
  }
  let payload: usize =
    record.function_queries.iter().map(|m| m.retained_bytes()).sum();
  let entries: usize = record.function_queries.iter().map(|m| m.len()).sum();
  assert_eq!(
    crate::execute::record_retained_bytes(&record),
    payload + entries * 21 + 5 * size_of::<u64>()
  );
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
        vec![
          function_channel(),
          G::ZERO,
          G::from_u8(n),
          G::from_u64(2_000_000)
        ]
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
  traces[0].values[5] += G::ONE;
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

fn fill_limbs(row: &mut [G], value: u64, ranges: &mut RankRanges) {
  assert!(value < RANK_BOUND);
  assert_eq!(row.len(), RANK_LIMBS);
  for (field, pair) in
    row.iter_mut().zip(value.to_le_bytes().as_chunks::<2>().0)
  {
    let limb = u16::from_le_bytes(*pair);
    *field = G::from_u16(limb);
    *ranges.entry(limb).or_insert(G::ZERO) += G::ONE;
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
  for (limb, count) in ranges {
    *balance
      .entry(normalized(vec![
        crate::u16_range_check_channel(),
        G::from_u16(*limb),
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
            fill_limbs(&mut row[aux + 1..aux + 4], member as u64, &mut ranges);
            row[aux + 4] = output;
            let gap = if member == 2 { RANK_BOUND - 2 } else { 0 };
            fill_limbs(&mut row[aux + 5..aux + 8], gap, &mut ranges);
          }
          violated += constraints
            .zeros
            .iter()
            .filter(|expr| eval_expr(expr, &row_values(row)) != G::ZERO)
            .count();
        }
      } else if i == system.toplevel.circuits.len() + 1 {
        // Bytes2 is the last circuit (there are no memories).
        for (limb, count) in &ranges {
          rows[usize::from(*limb) * shape.main_width
            + Bytes2::U16_RANGE_CHECK_COLUMN] = *count;
        }
      }
      traces.push(RowMajorMatrix::new(rows, shape.main_width));
    }
    assert_eq!(violated, 0, "all local polynomial constraints hold");
    // Only the closing h -> g lookup fails: its derived rank exceeds the
    // bounded rank on g's return. All u16-range lookups balance exactly.
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
    fill_limbs(&mut row[3..6], parent, &mut ranges);
    fill_limbs(&mut row[7..10], gap, &mut ranges);
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
  for limb in 0..3 {
    // Isolate each range check: this forged limb packs to gap -1, so all
    // function messages balance around the cycle by field arithmetic.
    let forged = -G::from_u64(1 << (16 * limb)).inverse();
    assert!(forged.as_canonical_u64() >= 65_536);
    let traces = system
      .circuit_shapes()
      .iter()
      .enumerate()
      .map(|(i, shape)| {
        let height = if i < 3 { 4 } else { shape.preprocessed_height };
        let mut rows = vec![G::ZERO; height * shape.main_width];
        if i < 3 {
          rows[0] = claim[2];
          rows[1] = G::ONE;
          rows[2] = G::from_u8(if i == 1 { 2 } else { 1 });
          rows[6] = claim[3];
          rows[7 + limb] = forged;
          let (constraints, _) = system.toplevel.build_constraints(i);
          assert!(constraints.zeros.iter().all(|expr| eval_expr(
            expr,
            &row_values(&rows[..shape.main_width])
          ) == G::ZERO));
        } else if i == 4 {
          // Five valid zero limbs per function and one invalid limb.
          rows[Bytes2::U16_RANGE_CHECK_COLUMN] = G::from_u8(15);
        }
        RowMajorMatrix::new(rows, shape.main_width)
      })
      .collect::<Vec<_>>();
    let ranges = [(0, G::from_u8(15))].into_iter().collect();
    assert_eq!(
      lookup_balance(&system.toplevel, &traces, &ranges, &claim),
      [(vec![crate::u16_range_check_channel(), forged], G::from_u8(3))]
        .into_iter()
        .collect()
    );
    let witness = SystemWitness::from_stage_1(traces, &system.system);
    let proof = system.system.prove(&system.key, &claim, witness);
    assert!(
      system.verify(&claim, &proof).is_err(),
      "unbounded gap limb {limb} allowed cyclic justification"
    );
  }
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
  top.functions[1].layout.auxiliaries = 4;
  top.functions[1].layout.lookups = 4;
  top.circuits[1].layout = top.functions[1].layout;
  let (cp, fp) = test_parameters();
  let system = AiurSystem::build(top, cp, fp);
  let claim = vec![function_channel(), G::ZERO, G::from_u8(3), G::from_u8(7)];
  for limb in 0..3 {
    // 65,536 in each limb gives rank 2^16, 2^32 or 2^48. The call can
    // request all three using an honest bounded gap. Only the provider's
    // limb range check distinguishes these noncanonical representations.
    let requested_rank = 1_u64 << (16 * (limb + 1));
    let mut ranges = RankRanges::default();
    let traces = system
      .circuit_shapes()
      .iter()
      .enumerate()
      .map(|(i, shape)| {
        let height = if i < 2 { 4 } else { shape.preprocessed_height };
        let mut rows = vec![G::ZERO; height * shape.main_width];
        if i < 2 {
          rows[0] = claim[2];
          rows[1] = G::ONE;
          rows[2] = G::ONE;
          if i == 0 {
            rows[6] = claim[3];
            fill_limbs(&mut rows[3..6], 0, &mut ranges);
            fill_limbs(&mut rows[7..10], requested_rank - 1, &mut ranges);
          } else {
            rows[3 + limb] = G::from_u32(65_536);
            *ranges.entry(0).or_insert(G::ZERO) += G::TWO;
          }
          let (constraints, _) = system.toplevel.build_constraints(i);
          assert!(constraints.zeros.iter().all(|expr| eval_expr(
            expr,
            &row_values(&rows[..shape.main_width])
          ) == G::ZERO));
        } else if i == 3 {
          for (&value, &count) in &ranges {
            rows[usize::from(value) * shape.main_width
              + Bytes2::U16_RANGE_CHECK_COLUMN] = count;
          }
        }
        RowMajorMatrix::new(rows, shape.main_width)
      })
      .collect::<Vec<_>>();
    assert_eq!(
      lookup_balance(&system.toplevel, &traces, &ranges, &claim),
      [(vec![crate::u16_range_check_channel(), G::from_u32(65_536)], G::ONE)]
        .into_iter()
        .collect()
    );
    let witness = SystemWitness::from_stage_1(traces, &system.system);
    let proof = system.system.prove(&system.key, &claim, witness);
    assert!(
      system.verify(&claim, &proof).is_err(),
      "unbounded function rank limb {limb} accepted"
    );
  }
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
      auxiliaries: 9,
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
      auxiliaries: 12,
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
      auxiliaries: 4,
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
  let (record, _) = system
    .toplevel
    .execute(0, vec![G::from_u8(3)], &mut empty_io_buffer())
    .unwrap();
  for (i, map) in record.function_queries.iter().enumerate() {
    assert_eq!(map.completion_entries(), 1, "generic functions retain ranks");
    assert_eq!(map.get_index(0).unwrap().1.rank, i as u64);
  }
  let (claim, proof) =
    system.prove(0, &[G::from_u8(3)], &mut empty_io_buffer());
  assert_eq!(
    claim,
    vec![function_channel(), G::ZERO, G::from_u8(3), G::from_u8(8)]
  );
  system.verify(&claim, &proof).expect("shared callee must verify");
}

fn counter_promotion_toplevel(grouped: bool) -> Toplevel {
  let mut top = component_promotion_toplevel(false);
  top.call_components[1].ranked = false;
  top.functions[0].layout.auxiliaries = 4;
  top.functions[1].layout.auxiliaries = 3;
  top.functions[1].layout.lookups = 2;
  for circuit in &mut top.circuits {
    circuit.layout = top.functions[circuit.members[0]].layout;
  }
  if grouped {
    top.circuits = vec![Circuit {
      members: vec![0, 1, 2],
      layout: FunctionLayout {
        input_size: 1,
        selectors: 4,
        auxiliaries: 4,
        lookups: 3,
      },
    }];
  }
  top
}

#[test]
fn unit_counters_preserve_promotion_sharing_and_grouped_proofs() {
  for grouped in [false, true] {
    let (cp, fp) = test_parameters();
    let system = AiurSystem::build(counter_promotion_toplevel(grouped), cp, fp);
    for n in [0, 4] {
      let input = vec![G::from_u8(n)];
      let (record, output) = system
        .toplevel
        .execute(0, input.clone(), &mut empty_io_buffer())
        .unwrap();
      assert_eq!(output, vec![G::from_u64(2_000_000)]);
      for map in &record.function_queries {
        assert_eq!(map.completion_entries(), 0);
        for (_, row) in map.iter() {
          assert_eq!(row.rank, 0);
        }
      }
      assert_eq!(record.function_queries[1].len(), usize::from(n) + 1);
      assert_eq!(
        record.function_queries[1].get(&input).unwrap().multiplicity,
        G::TWO
      );
      let (claim, proof) = system.prove(0, &input, &mut empty_io_buffer());
      assert_eq!(claim, vec![function_channel(), G::ZERO, input[0], output[0]]);
      system.verify(&claim, &proof).expect("counter proof must verify");
    }
  }
}

fn unit_cycle_toplevel(
  output_counter: bool,
  step: G,
  grouped: bool,
) -> Toplevel {
  let ops = if output_counter {
    vec![Op::Call(0, vec![0], 1, false), Op::Const(step), Op::Add(1, 2)]
  } else {
    vec![Op::Const(step), Op::Add(0, 1), Op::Call(0, vec![2], 1, false)]
  };
  let layout =
    FunctionLayout { input_size: 1, selectors: 1, auxiliaries: 2, lookups: 2 };
  let mut top = with_singleton_circuits(
    vec![Function {
      body: Block { ops, ctrl: Ctrl::Return(0, vec![3]) },
      layout,
      entry: true,
      constrained: true,
    }],
    vec![],
  );
  top.call_components = vec![CallComponent { order: 0, ranked: false }];
  if grouped {
    top.functions.push(Function {
      body: Block { ops: vec![], ctrl: Ctrl::Return(0, vec![0]) },
      layout: FunctionLayout { auxiliaries: 1, lookups: 1, ..layout },
      entry: false,
      constrained: true,
    });
    top.call_components.push(CallComponent { order: 1, ranked: false });
    top.circuits[0] = Circuit {
      members: vec![0, 1],
      layout: FunctionLayout { selectors: 2, ..layout },
    };
  }
  top
}

#[test]
fn unit_counter_cycles_fail_the_closing_lookup_across_field_wrap() {
  for output_counter in [false, true] {
    for step in [G::ONE, -G::ONE] {
      for grouped in [false, true] {
        let (cp, fp) = test_parameters();
        let system = AiurSystem::build(
          unit_cycle_toplevel(output_counter, step, grouped),
          cp,
          fp,
        );
        let start = if output_counter { G::ZERO } else { -step };
        let claim = vec![
          function_channel(),
          G::ZERO,
          if output_counter { G::from_u8(7) } else { start },
          if output_counter { start } else { G::from_u8(7) },
        ];
        let circuit = &system.toplevel.circuits[0];
        let aux = circuit.layout.input_size + circuit.layout.selectors;
        let (constraints, _) = system.toplevel.build_constraints(0);
        let traces = system
          .circuit_shapes()
          .iter()
          .enumerate()
          .map(|(i, shape)| {
            let height = if i == 0 { 4 } else { shape.preprocessed_height };
            let mut rows = vec![G::ZERO; height * shape.main_width];
            if i == 0 {
              for j in 0..3 {
                let row =
                  &mut rows[j * shape.main_width..(j + 1) * shape.main_width];
                let counter = start
                  + G::from_usize(j)
                    * if output_counter { -step } else { step };
                row[0] = if output_counter { claim[2] } else { counter };
                row[1] = G::ONE;
                row[aux] = if j == 0 { G::TWO } else { G::ONE };
                row[aux + 1] =
                  if output_counter { counter - step } else { claim[3] };
                assert!(
                  constraints
                    .zeros
                    .iter()
                    .all(|expr| eval_expr(expr, &row_values(row)) == G::ZERO)
                );
              }
            }
            RowMajorMatrix::new(rows, shape.main_width)
          })
          .collect::<Vec<_>>();
        let closing =
          start + G::from_u8(3) * if output_counter { -step } else { step };
        let missing = vec![
          function_channel(),
          G::ZERO,
          if output_counter { claim[2] } else { closing },
          if output_counter { closing } else { claim[3] },
        ];
        assert_eq!(
          lookup_balance(
            &system.toplevel,
            &traces,
            &RankRanges::default(),
            &claim
          ),
          [(normalized(claim.clone()), -G::ONE), (normalized(missing), G::ONE)]
            .into_iter()
            .collect()
        );
        let witness = SystemWitness::from_stage_1(traces, &system.system);
        let proof = system.system.prove(&system.key, &claim, witness);
        assert!(
          system.verify(&claim, &proof).is_err(),
          "counter cycle accepted (output={output_counter}, grouped={grouped}, step={step:?})"
        );
      }
    }
  }
}

#[test]
#[should_panic(expected = "call violates the static component order")]
fn construction_rechecks_forged_unit_counter_arithmetic() {
  let mut top = unit_cycle_toplevel(false, G::ONE, false);
  top.functions[0].body.ops[0] = Op::Const(G::ZERO);
  let (cp, fp) = test_parameters();
  let _ = AiurSystem::build(top, cp, fp);
}

fn output_length_toplevel(n: usize, grouped: bool) -> Toplevel {
  // The next pointer comes from memory, so only the constrained output + 1
  // equation can certify recursion. The nil pointer is a real stored row.
  let mut ops =
    vec![Op::Const(G::ZERO), Op::Store(vec![0, 0]), Op::Const(G::ONE)];
  let mut pointer = 1;
  for _ in 0..n {
    ops.push(Op::Store(vec![2, pointer]));
    pointer = ops.len() - 1;
  }
  let result = ops.len();
  ops.push(Op::Call(1, vec![pointer], 1, false));
  let root = Function {
    body: Block { ops, ctrl: Ctrl::Return(0, vec![result]) },
    layout: FunctionLayout {
      input_size: 0,
      selectors: 1,
      auxiliaries: n + 3,
      lookups: n + 3,
    },
    entry: true,
    constrained: true,
  };
  let length = Function {
    body: Block {
      ops: vec![Op::Load(2, 0)],
      ctrl: Ctrl::Match(
        1,
        [(
          G::ZERO,
          Block {
            ops: vec![Op::Const(G::ZERO)],
            ctrl: Ctrl::Return(0, vec![3]),
          },
        )]
        .into_iter()
        .collect(),
        Some(Box::new(Block {
          ops: vec![
            Op::Call(1, vec![2], 1, false),
            Op::Const(G::ONE),
            Op::Add(3, 4),
          ],
          ctrl: Ctrl::Return(1, vec![5]),
        })),
      ),
    },
    layout: FunctionLayout {
      input_size: 1,
      selectors: 2,
      auxiliaries: 5,
      lookups: 3,
    },
    entry: false,
    constrained: true,
  };
  let mut top = with_singleton_circuits(vec![root, length], vec![2]);
  top.call_components = vec![
    CallComponent { order: 0, ranked: false },
    CallComponent { order: 1, ranked: false },
  ];
  if grouped {
    // Entry inputs must have their declared public arity; keep the zero-input
    // root separate and test grouping the recursive function with a leaf.
    top.functions.push(Function {
      body: Block { ops: vec![], ctrl: Ctrl::Return(0, vec![0]) },
      layout: FunctionLayout {
        input_size: 1,
        selectors: 1,
        auxiliaries: 1,
        lookups: 1,
      },
      entry: false,
      constrained: true,
    });
    top.call_components.push(CallComponent { order: 2, ranked: false });
    top.circuits[1] = Circuit {
      members: vec![1, 2],
      layout: FunctionLayout { selectors: 3, ..top.functions[1].layout },
    };
  }
  top
}

#[test]
fn output_counters_verify_for_memory_lists_without_input_progress_equations() {
  for grouped in [false, true] {
    for n in [0, 1, 3] {
      let (cp, fp) = test_parameters();
      let system =
        AiurSystem::build(output_length_toplevel(n, grouped), cp, fp);
      let (record, output) =
        system.toplevel.execute(0, vec![], &mut empty_io_buffer()).unwrap();
      assert_eq!(output, vec![G::from_usize(n)]);
      assert_eq!(record.function_queries[1].len(), n + 1);
      assert_eq!(record.function_queries[1].completion_entries(), 0);
      let (claim, proof) = system.prove(0, &[], &mut empty_io_buffer());
      assert_eq!(claim, vec![function_channel(), G::ZERO, output[0]]);
      system
        .verify(&claim, &proof)
        .expect("output-counter list proof must verify");
    }
  }
}

#[test]
fn all_u16_limbs_match_each_compiled_rank_and_gap_lookup() {
  let top = cycle_toplevel(false);
  let (constraints, requests) = top.build_constraints(0);
  let table = Bytes2.preprocessed().unwrap();
  let providers = Bytes2.lookups();
  assert_eq!(constraints.width, 10);
  assert_eq!(providers.len(), 8);
  assert_eq!(table.width, 11);
  let table_row = [G::ZERO; 8];
  let mut row = vec![G::ZERO; constraints.width];
  row[1] = G::ONE;
  row[2] = G::ONE;
  let mut seen = vec![false; 65_536];
  for value in 0..=u16::MAX {
    let field = G::from_u16(value);
    row[3..6].fill(field);
    row[7..10].fill(field);
    let preprocessed =
      &table.values[usize::from(value) * table.width..][..table.width];
    let mut table_values = row_values(&table_row);
    table_values.preprocessed = [preprocessed, preprocessed];
    let scalar_message: Vec<_> = providers[Bytes2::U16_RANGE_CHECK_COLUMN]
      .args
      .iter()
      .map(|e| eval_expr(e, &table_values))
      .collect();
    assert_eq!(scalar_message, [crate::u16_range_check_channel(), field]);
    let scalar = usize::try_from(scalar_message[1].as_canonical_u64()).unwrap();
    assert!(!seen[scalar]);
    seen[scalar] = true;
    let byte_message: Vec<_> = providers[Bytes2::RANGE_CHECK_COLUMN]
      .args
      .iter()
      .map(|e| eval_expr(e, &table_values))
      .collect();
    assert_eq!(
      byte_message,
      [
        crate::u8_range_check_channel(),
        G::from_u16(value >> 8),
        G::from_u16(value & 255)
      ]
    );
    assert_ne!(normalized(byte_message), normalized(scalar_message.clone()));
    for slot in [1, 2, 3, 5, 6, 7] {
      let request: Vec<_> = requests[slot]
        .args
        .iter()
        .map(|e| eval_expr(e, &row_values(&row)))
        .collect();
      assert_eq!(request, scalar_message);
      assert_eq!(
        eval_expr(&requests[slot].multiplicity, &row_values(&row)),
        G::ONE
      );
    }
  }
  assert!(seen.into_iter().all(|present| present));
}

#[test]
fn supplied_large_ranks_verify_in_both_partitions_and_decoded_keys() {
  for grouped in [false, true] {
    let mut top = cycle_toplevel(false);
    top.functions.truncate(2);
    top.circuits.truncate(2);
    top.functions[1].body = Block {
      ops: vec![Op::Const(G::from_u8(7))],
      ctrl: Ctrl::Return(0, vec![1]),
    };
    top.functions[1].layout.auxiliaries = 4;
    top.functions[1].layout.lookups = 4;
    top.circuits[1].layout = top.functions[1].layout;
    if grouped {
      top.circuits = vec![Circuit {
        members: vec![0, 1],
        layout: FunctionLayout { selectors: 2, ..top.functions[0].layout },
      }];
    }
    let (cp, fp) = test_parameters();
    let system = AiurSystem::build(top, cp, fp);
    let encoded = crate::vk_codec::aiur_system_to_bytes(&system).unwrap();
    let (decoded, _, _) = crate::vk_codec::from_bytes(&encoded).unwrap();
    let claim = vec![function_channel(), G::ZERO, G::from_u8(3), G::from_u8(7)];
    for child in [1, 65_535, 65_536, (1 << 32) - 1, 1 << 32, RANK_BOUND - 1] {
      let mut ranges = RankRanges::default();
      let mut traces = Vec::new();
      for (index, shape) in system.circuit_shapes().iter().enumerate() {
        let is_function = index < system.toplevel.circuits.len();
        let height = if is_function { 4 } else { shape.preprocessed_height };
        let mut rows = vec![G::ZERO; height * shape.main_width];
        if is_function {
          let circuit = &system.toplevel.circuits[index];
          let (constraints, _) = system.toplevel.build_constraints(index);
          for (offset, &member) in circuit.members.iter().enumerate() {
            let row =
              &mut rows[offset * shape.main_width..][..shape.main_width];
            row[0] = claim[2];
            row[1 + offset] = G::ONE;
            let aux = 1 + circuit.layout.selectors;
            row[aux] = G::ONE;
            fill_limbs(
              &mut row[aux + 1..aux + 4],
              if member == 0 { 0 } else { child },
              &mut ranges,
            );
            if member == 0 {
              row[aux + 4] = claim[3];
              fill_limbs(&mut row[aux + 5..aux + 8], child - 1, &mut ranges);
            }
            assert!(
              constraints
                .zeros
                .iter()
                .all(|e| eval_expr(e, &row_values(row)) == G::ZERO)
            );
          }
        } else if index == system.toplevel.circuits.len() + 1 {
          for (&limb, &count) in &ranges {
            rows[usize::from(limb) * shape.main_width
              + Bytes2::U16_RANGE_CHECK_COLUMN] = count;
          }
        }
        traces.push(RowMajorMatrix::new(rows, shape.main_width));
      }
      assert!(
        lookup_balance(&system.toplevel, &traces, &ranges, &claim).is_empty()
      );
      let witness = SystemWitness::from_stage_1(traces, &system.system);
      let proof = system.system.prove(&system.key, &claim, witness);
      system.verify(&claim, &proof).unwrap();
      decoded.verify(&claim, &proof).unwrap();
    }
  }
}

#[test]
fn scalar_range_providers_cannot_supply_non_byte_pairs() {
  let function = Function {
    body: Block {
      ops: vec![Op::U8RangeCheck(0, 1)],
      ctrl: Ctrl::Return(0, vec![0, 1]),
    },
    layout: FunctionLayout {
      input_size: 2,
      selectors: 1,
      auxiliaries: 1,
      lookups: 2,
    },
    entry: true,
    constrained: true,
  };
  let mut top = with_singleton_circuits(vec![function], vec![]);
  top.call_components = vec![CallComponent { order: 0, ranked: false }];
  let (cp, fp) = test_parameters();
  let system = AiurSystem::build(top, cp, fp);
  // With a shared channel, lookup padding would identify (channel, x, 0)
  // and (channel, x), allowing a scalar u16 to masquerade as a byte pair.
  for value in [256_u16, 65_535] {
    let x = G::from_u16(value);
    let claim = vec![function_channel(), G::ZERO, x, G::ZERO, x, G::ZERO];
    let traces = system
      .circuit_shapes()
      .iter()
      .enumerate()
      .map(|(i, shape)| {
        let height = if i == 0 { 4 } else { shape.preprocessed_height };
        let mut rows = vec![G::ZERO; height * shape.main_width];
        if i == 0 {
          rows[..4].copy_from_slice(&[x, G::ZERO, G::ONE, G::ONE]);
          let (constraints, _) = system.toplevel.build_constraints(0);
          assert!(
            constraints
              .zeros
              .iter()
              .all(|e| eval_expr(e, &row_values(&rows[..shape.main_width]))
                == G::ZERO)
          );
        } else if i == 2 {
          rows[usize::from(value) * shape.main_width
            + Bytes2::U16_RANGE_CHECK_COLUMN] = G::ONE;
        }
        RowMajorMatrix::new(rows, shape.main_width)
      })
      .collect::<Vec<_>>();
    let ranges = [(value, G::ONE)].into_iter().collect();
    assert_eq!(
      lookup_balance(&system.toplevel, &traces, &ranges, &claim),
      [
        (vec![crate::u8_range_check_channel(), x], G::ONE),
        (vec![crate::u16_range_check_channel(), x], -G::ONE)
      ]
      .into_iter()
      .collect()
    );
    let witness = SystemWitness::from_stage_1(traces, &system.system);
    let proof = system.system.prove(&system.key, &claim, witness);
    assert!(
      system.verify(&claim, &proof).is_err(),
      "u16 provider supplied byte {value}"
    );
  }
}

#[test]
fn packed_u32_words_keep_byte_weights_with_u16_ranks() {
  for ranked in [false, true] {
    let function = Function {
      body: Block {
        ops: vec![
          Op::U8RangeCheck(0, 1),
          Op::U8RangeCheck(2, 3),
          Op::U32ToField(vec![0, 1, 2, 3]),
        ],
        ctrl: Ctrl::Return(0, vec![4]),
      },
      layout: FunctionLayout {
        input_size: 4,
        selectors: 1,
        auxiliaries: if ranked { 4 } else { 1 },
        lookups: if ranked { 6 } else { 3 },
      },
      entry: true,
      constrained: true,
    };
    let mut top = with_singleton_circuits(vec![function], vec![]);
    if !ranked {
      top.call_components = vec![CallComponent { order: 0, ranked: false }];
    }
    let (cp, fp) = test_parameters();
    let system = AiurSystem::build(top, cp, fp);
    for word in [0_u32, 1, 256, 65_536, 16_777_216, u32::MAX] {
      let input = word.to_le_bytes().map(G::from_u8);
      let (mut claim, proof) = system.prove(0, &input, &mut empty_io_buffer());
      assert_eq!(claim.last(), Some(&G::from_u32(word)));
      system.verify(&claim, &proof).unwrap();
      *claim.last_mut().unwrap() += G::ONE;
      assert!(system.verify(&claim, &proof).is_err());
    }
  }
}
