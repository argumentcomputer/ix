// Copyright (c) 2026 Argument Computer Corporation.
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Export actual operations, incoming expression maps, and complete native
//! emission. Multiple writers restart their lookup cursors to exercise exact
//! argument superposition, with different message widths and input metadata.

use std::collections::HashSet;

use super::{frontend_expressions::write_expr, operation_rows, *};

pub(super) fn write_indices(
  out: &mut impl Write,
  indices: &[usize],
) -> io::Result<()> {
  write_u64(out, indices.len() as u64)?;
  for index in indices {
    write_u64(out, *index as u64)?;
  }
  Ok(())
}

fn write_string(out: &mut impl Write, value: &str) -> io::Result<()> {
  write_u64(out, value.len() as u64)?;
  out.write_all(value.as_bytes())
}

fn write_option<W: Write, T>(
  out: &mut W,
  value: Option<&T>,
  write: impl FnOnce(&mut W, &T) -> io::Result<()>,
) -> io::Result<()> {
  match value {
    None => out.write_all(&[0]),
    Some(value) => {
      out.write_all(&[1])?;
      write(out, value)
    },
  }
}

// Test transport tags are explicit and exhaustive, independent of Rust enum
// layout. The Lean reader receives the operations used by collect_constraints.
pub(super) fn write_op(out: &mut impl Write, op: &Op) -> io::Result<()> {
  use Op::*;
  let tag = match op {
    Const(_) => 0,
    Add(..) => 1,
    Sub(..) => 2,
    Mul(..) => 3,
    EqZero(_) => 4,
    Call(..) => 5,
    Store(_) => 6,
    Load(..) => 7,
    AssertEq(..) => 8,
    IOGetInfo(..) => 9,
    IOSetInfo(..) => 10,
    IORead(..) => 11,
    IOWrite(..) => 12,
    U8BitDecomposition(_) => 13,
    U8ShiftLeft(_) => 14,
    U8ShiftRight(_) => 15,
    U8Xor(..) => 16,
    U8Add(..) => 17,
    U8Mul(..) => 18,
    U8Sub(..) => 19,
    U8And(..) => 20,
    U8Or(..) => 21,
    U8LessThan(..) => 22,
    U32LessThan(..) => 23,
    U8XorSplit7(..) => 24,
    U8XorSplit4(..) => 25,
    Debug(..) => 26,
    U8RangeCheck(..) => 27,
    UnconstrainedBigUintDivMod(..) => 28,
    UnconstrainedGToBytes(_) => 29,
    UnconstrainedGInverse(_) => 30,
    UnconstrainedU32Add(..) => 31,
    UnconstrainedU32Add3(..) => 32,
    U32ToField(_) => 33,
  };
  out.write_all(&[tag])?;
  match op {
    Const(value) => write_u64(out, value.as_canonical_u64()),
    Add(a, b)
    | Sub(a, b)
    | Mul(a, b)
    | U8Xor(a, b)
    | U8Add(a, b)
    | U8Mul(a, b)
    | U8Sub(a, b)
    | U8And(a, b)
    | U8Or(a, b)
    | U8LessThan(a, b)
    | U32LessThan(a, b)
    | U8XorSplit7(a, b)
    | U8XorSplit4(a, b)
    | U8RangeCheck(a, b)
    | UnconstrainedBigUintDivMod(a, b)
    | Load(a, b) => {
      write_u64(out, *a as u64)?;
      write_u64(out, *b as u64)
    },
    EqZero(a)
    | U8BitDecomposition(a)
    | U8ShiftLeft(a)
    | U8ShiftRight(a)
    | UnconstrainedGToBytes(a)
    | UnconstrainedGInverse(a) => write_u64(out, *a as u64),
    Call(function, indices, size, unconstrained) => {
      write_u64(out, *function as u64)?;
      write_indices(out, indices)?;
      write_u64(out, *size as u64)?;
      out.write_all(&[u8::from(*unconstrained)])
    },
    Store(indices) | U32ToField(indices) => write_indices(out, indices),
    AssertEq(xs, ys, message) => {
      write_indices(out, xs)?;
      write_indices(out, ys)?;
      write_option(out, message.as_ref(), |out, value| write_string(out, value))
    },
    IOGetInfo(a, indices) | IOWrite(a, indices) => {
      write_u64(out, *a as u64)?;
      write_indices(out, indices)
    },
    IOSetInfo(a, indices, b, c) => {
      write_u64(out, *a as u64)?;
      write_indices(out, indices)?;
      write_u64(out, *b as u64)?;
      write_u64(out, *c as u64)
    },
    IORead(a, b, size) => {
      write_u64(out, *a as u64)?;
      write_u64(out, *b as u64)?;
      write_u64(out, *size as u64)
    },
    Debug(message, indices) => {
      write_string(out, message)?;
      write_option(out, indices.as_ref(), |out, values| {
        write_indices(out, values)
      })
    },
    UnconstrainedU32Add(a, b) => {
      write_indices(out, a)?;
      write_indices(out, b)
    },
    UnconstrainedU32Add3(a, b, c) => {
      write_indices(out, a)?;
      write_indices(out, b)?;
      write_indices(out, c)
    },
  }
}

pub(super) fn write_exprs(
  out: &mut impl Write,
  exprs: &[Expr],
) -> io::Result<()> {
  write_u64(out, exprs.len() as u64)?;
  for expr in exprs {
    write_expr(out, expr)?;
  }
  Ok(())
}

pub(super) fn write_map(
  out: &mut impl Write,
  map: &[(Expr, Degree)],
) -> io::Result<()> {
  write_u64(out, map.len() as u64)?;
  for (expr, degree) in map {
    write_expr(out, expr)?;
    write_u64(out, u64::from(*degree))?;
  }
  Ok(())
}

#[test]
fn operation_expressions_snapshot() -> io::Result<()> {
  let mut fixtures = operation_rows::fixtures();
  fixtures.extend(operation_rows::constant_degree_fixtures());
  assert_eq!(fixtures.len(), 73);
  let kinds: HashSet<_> =
    fixtures.iter().flatten().map(std::mem::discriminant).collect();
  assert_eq!(kinds.len(), 34);

  let rows: Vec<_> = [G::ZERO, G::ONE, G::TWO, -G::ONE]
    .into_iter()
    .enumerate()
    .map(|(seed, selector)| operation_rows::row(seed, selector))
    .collect();
  let mut out = Vec::new();
  out.write_all(b"Aiur operation expressions v1\n")?;
  write_u64(&mut out, rows.len() as u64)?;
  for row in &rows {
    write_values(&mut out, row)?;
  }
  write_u64(&mut out, 876)?;
  let mut reports = 0;
  let mut sequences = 0;
  let mut shared_slots = 0;
  for branchless in [false, true] {
    for metadata in 0..3 {
      for fixture in 0..fixtures.len() {
        for writers in [1_usize, 3] {
          out.write_all(&[u8::from(branchless)])?;
          write_u64(&mut out, writers as u64)?;
          let mut state = state(0, branchless);
          state.lookups = (0..64).map(|_| empty_lookup()).collect();
          let mut lookup_end = 0;
          for writer in 0..writers {
            let ops = &fixtures[(fixture + 23 * writer) % fixtures.len()];
            state.column = 4 + 40 * writer;
            state.lookup = writer % 2;
            state.rank =
              if writer == 2 { konst(G::from_u64(257)) } else { var(2) };
            state.map = operation_rows::input_map();
            // Degree tracking is independent of frontend constant folding.
            // Exercise zero, ordinary, and conservative positive metadata.
            if metadata != 1 {
              state.map[0].1 = metadata;
              state.map[3].1 = metadata;
              state.map[5].1 = 2 * metadata;
            }
            let selector = var(3 + writer);
            write_u64(&mut out, state.column as u64)?;
            write_u64(&mut out, state.lookup as u64)?;
            write_expr(&mut out, &selector)?;
            write_expr(&mut out, &state.rank)?;
            write_map(&mut out, &state.map)?;
            write_u64(&mut out, ops.len() as u64)?;
            for op in ops {
              write_op(&mut out, op)?;
            }
            let equation_start = state.constraints.zeros.len();
            for op in ops {
              op.collect_constraints(&selector, &mut state);
            }
            let equations = &state.constraints.zeros[equation_start..];
            assert!(state.column <= rows[0].len());
            write_u64(&mut out, state.column as u64)?;
            write_u64(&mut out, state.lookup as u64)?;
            write_map(&mut out, &state.map)?;
            write_exprs(&mut out, equations)?;
            for row in &rows {
              let values = local_values(row);
              for (expr, _) in &state.map {
                write_u64(
                  &mut out,
                  eval_expr(expr, &values).as_canonical_u64(),
                )?;
                out.write_all(&[u8::from(matches!(expr, Expr::Const(_)))])?;
              }
              for expr in equations {
                write_u64(
                  &mut out,
                  eval_expr(expr, &values).as_canonical_u64(),
                )?;
              }
            }
            lookup_end = lookup_end.max(state.lookup);
            sequences += 1;
          }
          // Include untouched slots as well as all slots with contributions.
          write_u64(&mut out, (lookup_end + 2) as u64)?;
          for lookup in &state.lookups[..lookup_end + 2] {
            write_expr(&mut out, &lookup.multiplicity)?;
            write_exprs(&mut out, &lookup.args)?;
            for row in &rows {
              let values = local_values(row);
              write_u64(
                &mut out,
                eval_expr(&lookup.multiplicity, &values).as_canonical_u64(),
              )?;
              let args: Vec<_> = lookup
                .args
                .iter()
                .map(|expr| eval_expr(expr, &values))
                .collect();
              write_values(&mut out, &args)?;
            }
          }
          if writers == 3 {
            shared_slots += 1;
          }
          reports += 1;
        }
      }
    }
  }
  assert_eq!((reports, sequences, shared_slots), (876, 1752, 438));
  if let Some(path) = std::env::var_os("IX_OPERATION_EXPRESSION_SNAPSHOT") {
    let mut file = BufWriter::new(File::create(path)?);
    file.write_all(&out)?;
    file.flush()?;
  }
  eprintln!(
    "operation expressions: {reports} reports, {sequences} native sequences, {shared_slots} shared-slot cases"
  );
  Ok(())
}
