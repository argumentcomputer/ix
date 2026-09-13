// Copyright (c) 2026 Argument Computer Corporation.
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Export actual smart-constructor trees and scalar operation emission.
//! Deliberate raw negated constants test the boundary of the folding invariant.

use super::*;
use multi_stark::expr::{ColRef, RowOffset, Source};

fn fixtures() -> Vec<Expr> {
  let mut result =
    vec![konst(G::ZERO), konst(G::ONE), konst(-G::ONE), konst(G::from_u64(17))];
  for source in [Source::Preprocessed, Source::Main, Source::Stage2] {
    for offset in [RowOffset::Current, RowOffset::Next] {
      result.push(Expr::Var(ColRef { source, offset, index: 2 }));
    }
  }
  result.extend([
    Expr::Public(0),
    Expr::Public(2),
    Expr::IsFirstRow,
    Expr::IsLastRow,
    Expr::IsTransition,
    -var(0),
    Expr::Add(Box::new(var(0)), Box::new(var(1))),
    Expr::Sub(Box::new(konst(G::ZERO)), Box::new(var(0))),
    Expr::Mul(Box::new(konst(G::ZERO)), Box::new(var(1))),
    Expr::Neg(Box::new(konst(G::ZERO))),
    Expr::Neg(Box::new(konst(G::ONE))),
    Expr::Neg(Box::new(Expr::Neg(Box::new(var(0))))),
    Expr::Neg(Box::new(Expr::Neg(Box::new(konst(G::ONE))))),
    Expr::Add(Box::new(konst(G::ONE)), Box::new(konst(G::ONE))),
  ]);
  result
}

fn write_expr(out: &mut impl Write, expr: &Expr) -> io::Result<()> {
  match expr {
    Expr::Const(value) => {
      out.write_all(&[0])?;
      write_u64(out, value.as_canonical_u64())
    },
    Expr::Var(column) => {
      let source = match column.source {
        Source::Preprocessed => 0,
        Source::Main => 1,
        Source::Stage2 => 2,
      };
      let offset = match column.offset {
        RowOffset::Current => 0,
        RowOffset::Next => 1,
      };
      out.write_all(&[1, source, offset])?;
      write_u64(out, u64::from(column.index))
    },
    Expr::Public(index) => {
      out.write_all(&[2])?;
      write_u64(out, u64::from(*index))
    },
    Expr::IsFirstRow => out.write_all(&[3]),
    Expr::IsLastRow => out.write_all(&[4]),
    Expr::IsTransition => out.write_all(&[5]),
    Expr::Add(a, b) | Expr::Sub(a, b) | Expr::Mul(a, b) => {
      let tag = match expr {
        Expr::Add(..) => 6,
        Expr::Sub(..) => 7,
        _ => 8,
      };
      out.write_all(&[tag])?;
      write_expr(out, a)?;
      write_expr(out, b)
    },
    Expr::Neg(child) => {
      out.write_all(&[9])?;
      write_expr(out, child)
    },
  }
}

fn assignment(seed: usize) -> [[G; 16]; 7] {
  let choices = [
    G::ZERO,
    G::ONE,
    G::TWO,
    G::from_u64(17),
    G::from_u64(255),
    G::from_u64(256),
    G::from_u64(65536),
    -G::ONE,
  ];
  let mut rows = array::from_fn(|slot| {
    array::from_fn(|index| {
      choices[(slot * 3 + seed * 5 + index * 7) % choices.len()]
    })
  });
  rows[2][6] = [G::ZERO, G::ONE, G::TWO, -G::ONE][seed];
  rows
}

fn eval(expr: &Expr, rows: &[[G; 16]; 7], seed: usize) -> G {
  eval_expr(
    expr,
    &VarValues {
      preprocessed: [&rows[0], &rows[1]],
      main: [&rows[2], &rows[3]],
      stage2: [&rows[4], &rows[5]],
      publics: &rows[6],
      is_first_row: G::from_bool(seed == 0),
      is_last_row: G::from_bool(seed == 3),
      is_transition: G::from_bool(seed != 3),
    },
  )
}

fn write_smart(
  out: &mut impl Write,
  tag: u8,
  left: usize,
  right: usize,
  expr: &Expr,
) -> io::Result<()> {
  out.write_all(&[tag])?;
  write_u64(out, left as u64)?;
  write_u64(out, right as u64)?;
  write_expr(out, expr)?;
  write_u64(out, u64::from(matches!(expr, Expr::Const(_))))?;
  for seed in 0..4 {
    write_u64(out, eval(expr, &assignment(seed), seed).as_canonical_u64())?;
  }
  Ok(())
}

fn write_emission(
  out: &mut impl Write,
  fixtures: &[Expr],
  left: usize,
  right: usize,
  a_degree: Degree,
  b_degree: Degree,
  kind: u8,
) -> io::Result<()> {
  let mut state = state(5, false);
  state.map = vec![
    (fixtures[left].clone(), a_degree),
    (fixtures[right].clone(), b_degree),
  ];
  state.lookup = 0;
  state.lookups.clear();
  let op = match kind {
    0 => Op::EqZero(0),
    1 => Op::Add(0, 1),
    2 => Op::Sub(0, 1),
    3 => Op::Mul(0, 1),
    _ => unreachable!(),
  };
  op.collect_constraints(&var(6), &mut state);
  assert_eq!(state.map.len(), 3);
  assert_eq!(state.lookup, 0);
  assert!(state.lookups.is_empty());
  let (output, degree) = &state.map[2];
  out.write_all(&[kind])?;
  for number in [
    left,
    right,
    a_degree as usize,
    b_degree as usize,
    state.column - 7,
    *degree as usize,
  ] {
    write_u64(out, number as u64)?;
  }
  write_expr(out, output)?;
  write_u64(out, state.constraints.zeros.len() as u64)?;
  for expr in &state.constraints.zeros {
    write_expr(out, expr)?;
  }
  for seed in 0..4 {
    let rows = assignment(seed);
    write_u64(out, eval(output, &rows, seed).as_canonical_u64())?;
    write_u64(out, u64::from(matches!(output, Expr::Const(_))))?;
    for expr in &state.constraints.zeros {
      write_u64(out, eval(expr, &rows, seed).as_canonical_u64())?;
    }
  }
  Ok(())
}

#[test]
fn frontend_expressions_snapshot() -> io::Result<()> {
  let fixtures = fixtures();
  assert_eq!(fixtures.len(), 24);
  let mut out = Vec::new();
  out.write_all(b"Aiur frontend expressions v1\n")?;
  write_u64(&mut out, fixtures.len() as u64)?;
  for expr in &fixtures {
    write_expr(&mut out, expr)?;
  }
  write_u64(&mut out, 1752)?;
  let mut smart = 0;
  for (left, a) in fixtures.iter().enumerate() {
    write_smart(&mut out, 3, left, left, &-a.clone())?;
    smart += 1;
    for (right, b) in fixtures.iter().enumerate() {
      for (tag, expr) in [
        (0, a.clone() + b.clone()),
        (1, a.clone() - b.clone()),
        (2, a.clone() * b.clone()),
      ] {
        write_smart(&mut out, tag, left, right, &expr)?;
        smart += 1;
      }
    }
  }
  assert_eq!(smart, 1752);
  write_u64(&mut out, 9804)?;
  let mut emitted = 0;
  for left in 0..19 {
    for a_degree in 0..3 {
      write_emission(&mut out, &fixtures, left, left, a_degree, a_degree, 0)?;
      emitted += 1;
      for right in 0..19 {
        for b_degree in 0..3 {
          for kind in 1..4 {
            write_emission(
              &mut out, &fixtures, left, right, a_degree, b_degree, kind,
            )?;
            emitted += 1;
          }
        }
      }
    }
  }
  assert_eq!(emitted, 9804);
  if let Some(path) = std::env::var_os("IX_FRONTEND_EXPRESSION_SNAPSHOT") {
    std::fs::write(path, out)?;
  }
  Ok(())
}
