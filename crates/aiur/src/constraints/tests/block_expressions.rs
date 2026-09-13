// Copyright (c) 2026 Argument Computer Corporation.
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Exact expression reflection for complete blocks. The transport includes
//! the actual control tree, so Lean does not reconstruct an independent fixture.

use super::{
  frontend_expressions::write_expr,
  operation_expressions::{write_exprs, write_indices, write_map, write_op},
  *,
};

pub(super) fn write_block(
  out: &mut impl Write,
  block: &Block,
) -> io::Result<()> {
  write_u64(out, block.ops.len() as u64)?;
  for op in &block.ops {
    write_op(out, op)?;
  }
  match &block.ctrl {
    Ctrl::Return(index, values) | Ctrl::Yield(index, values) => {
      out.write_all(&[u8::from(matches!(block.ctrl, Ctrl::Yield(..)))])?;
      write_u64(out, *index as u64)?;
      write_indices(out, values)
    },
    Ctrl::Match(index, cases, fallback)
    | Ctrl::MatchContinue(index, cases, fallback, ..) => {
      let continued = matches!(block.ctrl, Ctrl::MatchContinue(..));
      out.write_all(&[if continued { 3 } else { 2 }])?;
      write_u64(out, *index as u64)?;
      write_u64(out, cases.len() as u64)?;
      for (value, block) in cases {
        write_u64(out, value.as_canonical_u64())?;
        write_block(out, block)?;
      }
      out.write_all(&[u8::from(fallback.is_some())])?;
      if let Some(block) = fallback {
        write_block(out, block)?;
      }
      if let Ctrl::MatchContinue(_, _, _, size, aux, slots, block) = &block.ctrl
      {
        write_u64(out, *size as u64)?;
        write_u64(out, *aux as u64)?;
        write_u64(out, *slots as u64)?;
        write_block(out, block)?;
      }
      Ok(())
    },
  }
}

fn write_evaluated_map(
  out: &mut impl Write,
  map: &[(Expr, Degree)],
  values: &VarValues<'_, G>,
) -> io::Result<()> {
  for (expr, degree) in map {
    write_u64(out, eval_expr(expr, values).as_canonical_u64())?;
    write_u64(out, u64::from(*degree))?;
    out.write_all(&[u8::from(matches!(expr, Expr::Const(_)))])?;
  }
  Ok(())
}

#[test]
fn block_expressions_snapshot() -> io::Result<()> {
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
  out.write_all(b"Aiur block expressions v1\n")?;
  write_u64(&mut out, 384)?;
  let mut reports = 0;
  let mut checked = 0;
  for branchless in [false, true] {
    for populated in [false, true] {
      for external_gate in [false, true] {
        for depth in 0..4 {
          for seed in 0..12 {
            let mut selector_count = 0;
            let block = if populated {
              block_rows::block_fixture(depth, seed, 2, &mut selector_count)
            } else {
              fixture(depth, seed, &mut selector_count)
            };
            let mut state = state(selector_count, branchless);
            state.constraints.width = 2 + selector_count + 4096;
            state.lookups = (0..4096).map(|_| empty_lookup()).collect();
            for (_, values) in &mut state.yield_info {
              *values = state.map.clone();
            }
            let selectors: Vec<_> = (0..selector_count)
              .map(|index| var(state.sel_base + index))
              .collect();
            let entry = block.get_block_selector(&state);
            let incoming = if external_gate {
              konst(G::TWO) - var(0)
            } else {
              entry.clone()
            };
            out.write_all(&[u8::from(branchless)])?;
            write_u64(&mut out, state.function_index.as_canonical_u64())?;
            write_u64(&mut out, state.input_size as u64)?;
            write_expr(&mut out, &state.rank)?;
            write_exprs(&mut out, &selectors)?;
            write_u64(&mut out, state.column as u64)?;
            write_u64(&mut out, state.lookup as u64)?;
            write_expr(&mut out, &incoming)?;
            write_map(&mut out, &state.map)?;
            write_block(&mut out, &block)?;
            write_expr(&mut out, &entry)?;
            block.collect_constraints(incoming, &mut state);
            assert!(state.column <= state.constraints.width);
            assert!(state.lookup + 2 <= state.lookups.len());
            write_u64(&mut out, state.column as u64)?;
            write_u64(&mut out, state.lookup as u64)?;
            write_map(&mut out, &state.map)?;
            write_exprs(&mut out, &state.constraints.zeros)?;
            // Include unused slots as well as the shared return channel.
            write_u64(&mut out, (state.lookup + 2) as u64)?;
            for lookup in &state.lookups[..state.lookup + 2] {
              write_expr(&mut out, &lookup.multiplicity)?;
              write_exprs(&mut out, &lookup.args)?;
            }
            write_u64(&mut out, state.yield_info.len() as u64)?;
            for (gate, map) in &state.yield_info {
              write_expr(&mut out, gate)?;
              write_map(&mut out, map)?;
            }
            write_u64(&mut out, 4)?;
            for pattern in [0, 1, 2, 7] {
              let mut row: Vec<_> = (0..state.column)
                .map(|index| {
                  choices[(seed + 5 * index + pattern) % choices.len()]
                })
                .collect();
              for index in 0..selector_count {
                row[index + 2] = assignment(pattern, index, selector_count);
              }
              write_values(&mut out, &row)?;
              let values = local_values(&row);
              write_evaluated_map(&mut out, &state.map, &values)?;
              for expr in &state.constraints.zeros {
                write_u64(
                  &mut out,
                  eval_expr(expr, &values).as_canonical_u64(),
                )?;
              }
              for lookup in &state.lookups[..state.lookup + 2] {
                write_u64(
                  &mut out,
                  eval_expr(&lookup.multiplicity, &values).as_canonical_u64(),
                )?;
                for arg in &lookup.args {
                  write_u64(
                    &mut out,
                    eval_expr(arg, &values).as_canonical_u64(),
                  )?;
                }
              }
              for (gate, map) in &state.yield_info {
                write_u64(
                  &mut out,
                  eval_expr(gate, &values).as_canonical_u64(),
                )?;
                write_evaluated_map(&mut out, map, &values)?;
              }
              checked += 1;
            }
            reports += 1;
          }
        }
      }
    }
  }
  assert_eq!((reports, checked), (384, 1536));
  if let Some(path) = std::env::var_os("IX_BLOCK_EXPRESSION_SNAPSHOT") {
    let mut file = BufWriter::new(File::create(path)?);
    file.write_all(&out)?;
    file.flush()?;
  }
  eprintln!(
    "block expressions: {reports} control trees, {checked} assignments"
  );
  Ok(())
}
