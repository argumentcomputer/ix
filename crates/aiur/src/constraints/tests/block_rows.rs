// Copyright (c) 2026 Argument Computer Corporation.
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Full block emission with shared branch storage and nonempty yields.
//! Rows include arbitrary selectors and advice, without an executor filter.

use super::*;

pub(super) fn block_fixture(
  depth: usize,
  seed: usize,
  initial_values: usize,
  next_selector: &mut usize,
) -> Block {
  let size = seed % 3;
  let pointer = initial_values + 3 + size;
  let count = initial_values + 6 + 2 * size;
  let ops = vec![
    Op::Const(G::from_usize(seed + 17)),
    Op::Mul(0, 1),
    Op::EqZero(if seed.is_multiple_of(2) { initial_values } else { 0 }),
    Op::Call(17, vec![0, initial_values], size, false),
    Op::Store(vec![0, initial_values + 1]),
    Op::Load(size, pointer),
    Op::U8Add(0, 1),
    Op::AssertEq(vec![initial_values + 1], vec![0], None),
  ];
  let ctrl = if depth == 0 || seed.is_multiple_of(5) {
    let selector = *next_selector;
    *next_selector += 1;
    let outputs = vec![count - 2, count - 1];
    if seed.is_multiple_of(2) {
      Ctrl::Return(selector, outputs)
    } else {
      Ctrl::Yield(selector, outputs)
    }
  } else {
    let mut cases = FxIndexMap::default();
    cases.insert(
      G::ZERO,
      block_fixture(depth - 1, seed * 3 + 1, count, next_selector),
    );
    cases.insert(
      G::ONE,
      block_fixture(depth - 1, seed * 3 + 2, count, next_selector),
    );
    let fallback = seed.is_multiple_of(2).then(|| {
      Box::new(block_fixture(depth - 1, seed * 3 + 3, count, next_selector))
    });
    let matched = if seed.is_multiple_of(2) { initial_values } else { 0 };
    if seed.is_multiple_of(3) {
      Ctrl::Match(matched, cases, fallback)
    } else {
      Ctrl::MatchContinue(
        matched,
        cases,
        fallback,
        2,
        0,
        0,
        Box::new(block_fixture(
          depth - 1,
          seed * 3 + 4,
          count + 2,
          next_selector,
        )),
      )
    }
  };
  Block { ops, ctrl }
}

fn write_map(
  out: &mut impl Write,
  map: &[(Expr, Degree)],
  values: &VarValues<'_, G>,
) -> io::Result<()> {
  write_u64(out, map.len() as u64)?;
  for (expr, degree) in map {
    write_u64(out, eval_expr(expr, values).as_canonical_u64())?;
    write_u64(out, u64::from(*degree))?;
    write_u64(out, u64::from(matches!(expr, Expr::Const(_))))?;
  }
  Ok(())
}

#[test]
fn block_rows_snapshot() -> io::Result<()> {
  let choices = [
    G::ZERO,
    G::ONE,
    -G::ONE,
    G::from_u64(255),
    G::from_u64(256),
    G::from_u64(1 << 32),
    G::from_u64((1 << 48) - 1),
    G::from_u64(17),
  ];
  let mut out = Vec::new();
  out.write_all(b"Aiur block rows v1\n")?;
  write_u64(&mut out, 96)?;
  let mut checked = 0;
  for branchless in [false, true] {
    for depth in 0..4 {
      for seed in 0..12 {
        let mut selector_count = 0;
        let block = block_fixture(depth, seed, 2, &mut selector_count);
        let mut state = state(selector_count, branchless);
        state.constraints.width = 2 + selector_count + 4096;
        state.lookups = (0..4096).map(|_| empty_lookup()).collect();
        for (_, values) in &mut state.yield_info {
          *values = vec![(var(0), 1), (var(1), 1)];
        }
        let entry = block.get_block_selector(&state);
        block.collect_constraints(entry, &mut state);
        assert!(state.column <= state.constraints.width);
        assert!(state.lookup <= state.lookups.len());
        let mut row: Vec<_> = (0..state.constraints.width)
          .map(|index| choices[(seed + 5 * index) % choices.len()])
          .collect();
        write_u64(&mut out, selector_count as u64)?;
        write_u64(&mut out, (8 + 2 * selector_count) as u64)?;
        for pattern in 0..8 + 2 * selector_count {
          for index in 0..selector_count {
            row[index + 2] = assignment(pattern, index, selector_count);
          }
          let values = local_values(&row);
          write_u64(&mut out, state.column as u64)?;
          write_u64(&mut out, state.lookup as u64)?;
          write_map(&mut out, &state.map, &values)?;
          let equations: Vec<_> = state
            .constraints
            .zeros
            .iter()
            .map(|expr| eval_expr(expr, &values))
            .collect();
          write_values(&mut out, &equations)?;
          for lookup in &state.lookups[..state.lookup] {
            write_u64(
              &mut out,
              eval_expr(&lookup.multiplicity, &values).as_canonical_u64(),
            )?;
            let args: Vec<_> =
              lookup.args.iter().map(|expr| eval_expr(expr, &values)).collect();
            write_values(&mut out, &args)?;
          }
          write_u64(&mut out, state.yield_info.len() as u64)?;
          for (selector, map) in &state.yield_info {
            write_u64(
              &mut out,
              eval_expr(selector, &values).as_canonical_u64(),
            )?;
            write_map(&mut out, map, &values)?;
          }
          checked += 1;
        }
      }
    }
  }
  assert_eq!(checked, 2028);
  if let Some(path) = std::env::var_os("IX_BLOCK_ROW_SNAPSHOT") {
    let mut file = BufWriter::new(File::create(path)?);
    file.write_all(&out)?;
    file.flush()?;
  }
  eprintln!("block rows: {checked} assignments with shared columns and slots");
  Ok(())
}
