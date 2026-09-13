// Copyright (c) 2026 Argument Computer Corporation.
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Compare the actual argument combiner, selector expressions and escaping
//! yield collector with the checked Lean selector model. The control fixtures
//! have no operations and zero-width yields, allowing their selector-only
//! polynomial positions to be identified without evaluating an executor.

use std::{
  fs::File,
  io::{self, BufWriter, Write},
};

use multi_stark::{
  eval::{VarValues, eval_expr},
  p3_field::PrimeField64,
};

use super::*;

mod block_expressions;
mod block_rows;
mod circuit_expressions;
mod circuit_rows;
mod frontend_expressions;
mod memory_rows;
mod operation_expressions;
mod operation_rows;

fn write_u64(out: &mut impl Write, value: u64) -> io::Result<()> {
  out.write_all(&value.to_le_bytes())
}

fn write_values(out: &mut impl Write, values: &[G]) -> io::Result<()> {
  write_u64(out, values.len() as u64)?;
  for value in values {
    write_u64(out, value.as_canonical_u64())?;
  }
  Ok(())
}

fn local_values(row: &[G]) -> VarValues<'_, G> {
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

fn state(selector_count: usize, branchless: bool) -> ConstraintState {
  ConstraintState {
    function_index: G::from_u64(37),
    rank: konst(G::from_u64(257)),
    branchless,
    input_size: 2,
    sel_base: 2,
    column: 2 + selector_count,
    lookup: 1,
    lookups: vec![empty_lookup()],
    map: vec![(var(0), 1), (var(1), 1)],
    constraints: Constraints {
      zeros: vec![],
      selectors: 2..2 + selector_count,
      width: 2 + selector_count + 1024,
    },
    // A nested continuation must preserve yields collected before its own
    // branch region. These distinct markers are never selector columns.
    yield_info: vec![
      (konst(G::from_u64(99)), vec![]),
      (konst(G::from_u64(100)), vec![]),
    ],
  }
}

fn fixture(depth: usize, seed: usize, next_selector: &mut usize) -> Block {
  let ctrl = if depth == 0 || seed.is_multiple_of(5) {
    let selector = *next_selector;
    *next_selector += 1;
    if seed.is_multiple_of(2) {
      Ctrl::Return(selector, vec![])
    } else {
      Ctrl::Yield(selector, vec![])
    }
  } else {
    let mut cases = FxIndexMap::default();
    cases.insert(G::ZERO, fixture(depth - 1, seed * 3 + 1, next_selector));
    cases.insert(G::ONE, fixture(depth - 1, seed * 3 + 2, next_selector));
    let fallback = seed
      .is_multiple_of(2)
      .then(|| Box::new(fixture(depth - 1, seed * 3 + 3, next_selector)));
    if seed.is_multiple_of(3) {
      Ctrl::Match(0, cases, fallback)
    } else {
      Ctrl::MatchContinue(
        0,
        cases,
        fallback,
        0,
        0,
        0,
        Box::new(fixture(depth - 1, seed * 3 + 4, next_selector)),
      )
    }
  };
  Block { ops: vec![], ctrl }
}

/// Locate selector booleans and continuation links in the actual emitted
/// constraint vector. All skipped entries are case/default-match equations;
/// the zero-width fixtures have no merge-column equations or operations.
fn selector_equation_indices(
  block: &Block,
  cursor: &mut usize,
  selected: &mut Vec<usize>,
) {
  assert!(block.ops.is_empty());
  selected.push(*cursor);
  *cursor += 1;
  match &block.ctrl {
    Ctrl::Return(..) | Ctrl::Yield(..) => {},
    Ctrl::Match(_, cases, fallback)
    | Ctrl::MatchContinue(_, cases, fallback, ..) => {
      for branch in cases.values() {
        *cursor += 1;
        selector_equation_indices(branch, cursor, selected);
      }
      if let Some(branch) = fallback {
        *cursor += cases.len();
        selector_equation_indices(branch, cursor, selected);
      }
      if let Ctrl::MatchContinue(_, _, _, outputs, _, _, continuation) =
        &block.ctrl
      {
        assert_eq!(*outputs, 0);
        selected.push(*cursor);
        *cursor += 1;
        selector_equation_indices(continuation, cursor, selected);
      }
    },
  }
}

fn assignment(pattern: usize, index: usize, count: usize) -> G {
  match pattern {
    0 => G::ZERO,
    1 => G::ONE,
    2 => G::TWO,
    3 => -G::ONE,
    4 => G::from_usize(index + 1),
    5 => -G::from_usize(index + 1),
    6 => G::from_bool(index.is_multiple_of(2)),
    7 => [G::ZERO, -G::ONE, G::ONE, G::TWO][index % 4],
    hot if hot < 8 + count => G::from_bool(index == hot - 8),
    cold => G::from_bool(index != cold - 8 - count),
  }
}

fn export_control(out: &mut impl Write) -> io::Result<usize> {
  write_u64(out, 48)?;
  let mut checked = 0;
  let mut satisfying = 0;
  for depth in 0..4 {
    for seed in 0..12 {
      let mut selector_count = 0;
      let block = fixture(depth, seed, &mut selector_count);
      let mut state = state(selector_count, false);
      let entry = block.get_block_selector(&state);
      block.collect_constraints(entry.clone(), &mut state);
      let mut equation_indices = vec![];
      let mut cursor = 0;
      selector_equation_indices(&block, &mut cursor, &mut equation_indices);
      assert_eq!(cursor, state.constraints.zeros.len());
      assert!(state.column <= state.constraints.width);
      let mut row: Vec<G> =
        (0..state.constraints.width).map(|i| G::from_usize(i + 11)).collect();
      row[0] = G::from_u64(3);
      row[1] = G::from_u64(19);
      write_u64(out, selector_count as u64)?;
      write_u64(out, (8 + 2 * selector_count) as u64)?;
      for pattern in 0..8 + 2 * selector_count {
        for index in 0..selector_count {
          row[index + 2] = assignment(pattern, index, selector_count);
        }
        let values = local_values(&row);
        let entry = eval_expr(&entry, &values);
        let yields: Vec<_> = state
          .yield_info
          .iter()
          .map(|(selector, outputs)| {
            assert!(outputs.is_empty());
            eval_expr(selector, &values)
          })
          .collect();
        assert_eq!(&yields[..2], &[G::from_u64(99), G::from_u64(100)]);
        let equations: Vec<_> = equation_indices
          .iter()
          .map(|&index| eval_expr(&state.constraints.zeros[index], &values))
          .collect();
        let message: Vec<_> = state.lookups[0]
          .args
          .iter()
          .map(|expr| eval_expr(expr, &values))
          .collect();
        if equations.iter().all(|value| value.is_zero()) {
          let return_sum =
            message.get(1).copied().unwrap_or(G::ZERO) / G::from_u64(37);
          assert_eq!(
            entry,
            return_sum + yields[2..].iter().copied().sum::<G>()
          );
          satisfying += 1;
        }
        write_u64(out, entry.as_canonical_u64())?;
        write_values(out, &yields)?;
        write_values(out, &equations)?;
        write_values(out, &message)?;
        checked += 1;
      }
    }
  }
  assert!(satisfying > 100, "exercise active and inactive solutions");
  Ok(checked)
}

fn export_messages(out: &mut impl Write) -> io::Result<usize> {
  write_u64(out, 2 * 7 * 32 * 8)?;
  let values = local_values(&[]);
  let mut checked = 0;
  for branchless in [false, true] {
    let state = state(0, branchless);
    for count in 0..7 {
      for seed in 0..32 {
        for pattern in 0..8 {
          let mut lookup = empty_lookup();
          for index in 0..count {
            let selector = konst(assignment(pattern, index, count));
            let message = (0..(seed + index * 3) % 8).map(|offset| {
              let value = G::from_usize(17 + seed + index * 5 + offset * 11);
              state.gate(
                &selector,
                konst(if (seed + offset).is_multiple_of(2) {
                  value
                } else {
                  -value
                }),
              )
            });
            combine_lookup_args(&mut lookup, message);
            lookup.multiplicity = lookup.multiplicity + selector;
          }
          write_u64(
            out,
            eval_expr(&lookup.multiplicity, &values).as_canonical_u64(),
          )?;
          let message: Vec<_> =
            lookup.args.iter().map(|expr| eval_expr(expr, &values)).collect();
          write_values(out, &message)?;
          checked += 1;
        }
      }
    }
  }
  Ok(checked)
}

#[test]
fn selector_control_snapshot() -> io::Result<()> {
  let mut out = Vec::new();
  out.write_all(b"Aiur selector control v1\n")?;
  let controls = export_control(&mut out)?;
  let messages = export_messages(&mut out)?;
  assert_eq!(messages, 3584);
  if let Some(path) = std::env::var_os("IX_SELECTOR_CONTROL_SNAPSHOT") {
    let mut file = BufWriter::new(File::create(path)?);
    file.write_all(&out)?;
    file.flush()?;
  }
  eprintln!(
    "selector control: {controls} assignments, {messages} shared messages"
  );
  Ok(())
}
