// Copyright (c) 2026 Argument Computer Corporation.
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Evaluate all operation forms against arbitrary rows, including metadata,
//! allocation, polynomial values and every lookup argument. Sequences reuse
//! logical outputs and advance the native auxiliary/lookup cursors.

use std::collections::HashSet;

use super::*;

pub(super) fn fixtures() -> Vec<Vec<Op>> {
  use Op::*;
  vec![
    vec![Const(G::ZERO)],
    vec![Const(G::ONE)],
    vec![Const(-G::ONE)],
    vec![Add(0, 1)],
    vec![Add(0, 3)],
    vec![Add(3, 4)],
    vec![Sub(1, 2)],
    vec![Sub(0, 3)],
    vec![Sub(3, 4)],
    vec![Mul(0, 3)],
    vec![Mul(1, 3)],
    vec![Mul(2, 1)],
    vec![Mul(3, 4)],
    vec![Mul(5, 6)],
    vec![EqZero(0)],
    vec![EqZero(1)],
    vec![EqZero(2)],
    vec![EqZero(3)],
    vec![EqZero(4)],
    vec![EqZero(5)],
    vec![Call(17, vec![3, 4, 5], 0, false)],
    vec![Call(17, vec![3, 4, 5], 2, false)],
    vec![Call(17, vec![3, 4, 5], 0, true)],
    vec![Call(17, vec![3, 4, 5], 2, true)],
    vec![Store(vec![])],
    vec![Store(vec![0, 3, 4])],
    vec![Load(0, 3)],
    vec![Load(3, 4)],
    vec![AssertEq(vec![], vec![], None)],
    vec![AssertEq(vec![0, 3, 4], vec![1, 4, 3], Some("row".into()))],
    vec![IOGetInfo(0, vec![1, 2])],
    vec![IORead(0, 0, 0)],
    vec![IORead(0, 3, 2)],
    vec![IOSetInfo(0, vec![1, 2], 3, 4)],
    vec![IOWrite(0, vec![3, 4])],
    vec![Debug("row".into(), None)],
    vec![Debug("row".into(), Some(vec![3, 4]))],
    vec![U8BitDecomposition(3)],
    vec![U8ShiftLeft(3)],
    vec![U8ShiftRight(3)],
    vec![U8Xor(3, 4)],
    vec![U8Add(3, 4)],
    vec![U8Sub(3, 4)],
    vec![U8And(3, 4)],
    vec![U8Or(3, 4)],
    vec![U8LessThan(3, 4)],
    vec![U8RangeCheck(3, 4)],
    vec![U8Mul(3, 4)],
    vec![U8XorSplit7(3, 4)],
    vec![U8XorSplit4(3, 4)],
    vec![U32LessThan(3, 4)],
    vec![UnconstrainedBigUintDivMod(3, 4)],
    vec![UnconstrainedGToBytes(3)],
    vec![UnconstrainedGInverse(4)],
    vec![UnconstrainedU32Add(vec![0, 1, 2, 3], vec![4, 5, 6, 7])],
    vec![UnconstrainedU32Add3(
      vec![0, 1, 2, 3],
      vec![4, 5, 6, 7],
      vec![7, 6, 5, 4],
    )],
    vec![U32ToField(vec![0, 1, 2, 3])],
    vec![],
    vec![Const(G::ZERO), Mul(8, 3)],
    vec![Mul(3, 4), Add(8, 3), EqZero(9)],
    vec![
      UnconstrainedGToBytes(3),
      U8RangeCheck(8, 9),
      U8Add(8, 9),
      AssertEq(vec![16], vec![3], None),
      UnconstrainedGInverse(17),
    ],
    vec![
      Store(vec![3, 4]),
      Load(2, 8),
      Call(17, vec![9, 10], 2, false),
      U8Xor(11, 12),
    ],
    vec![
      IORead(0, 0, 4),
      UnconstrainedU32Add(vec![8, 9, 10, 11], vec![0, 1, 2, 7]),
      U32ToField(vec![12, 13, 14, 15]),
    ],
    vec![EqZero(0), Add(8, 1), Sub(9, 1), Mul(10, 7)],
    vec![
      UnconstrainedBigUintDivMod(3, 4),
      Call(17, vec![8, 9], 0, false),
      Debug("row".into(), None),
    ],
  ]
}

pub(super) fn input_map() -> Vec<(Expr, Degree)> {
  vec![
    (konst(G::ZERO), 0),
    (konst(G::ONE), 0),
    (konst(-G::ONE), 0),
    (var(0), 1),
    (var(1), 1),
    (var(0) + var(1), 1),
    (var(2), 1),
    (konst(G::from_u64(257)), 0),
  ]
}

pub(super) fn row(seed: usize, selector: G) -> Vec<G> {
  let choices = [
    G::ZERO,
    G::ONE,
    G::from_u64(255),
    G::from_u64(256),
    -G::ONE,
    -G::TWO,
    G::from_u64((1 << 32) - 1),
    G::from_u64(1 << 32),
    G::from_u64((1 << 48) - 1),
    G::from_u64(17),
    G::from_u64(3),
    G::from_u64(65536),
  ];
  let mut row: Vec<_> =
    (0..512).map(|i| choices[(seed + 5 * i) % choices.len()]).collect();
  row[0] = choices[seed];
  row[1] = choices[(seed + 1) % choices.len()];
  row[2] = choices[(seed + 2) % choices.len()];
  row[3] = selector;
  row
}

fn write_corpus(
  header: &[u8],
  fixtures: &[Vec<Op>],
) -> io::Result<(Vec<u8>, usize)> {
  let mut out = Vec::new();
  out.write_all(header)?;
  write_u64(&mut out, fixtures.len() as u64)?;
  let mut checked = 0;
  for branchless in [false, true] {
    for seed in 0..12 {
      for selector in [G::ZERO, G::ONE, G::TWO, -G::ONE] {
        let row = row(seed, selector);
        let values = local_values(&row);
        for ops in fixtures {
          let mut state = state(0, branchless);
          state.column = 4;
          state.lookup = 0;
          state.lookups = (0..64).map(|_| empty_lookup()).collect();
          state.rank = var(2);
          state.map = input_map();
          for op in ops {
            op.collect_constraints(&var(3), &mut state);
          }
          assert!(state.column <= row.len());
          write_u64(&mut out, state.column as u64)?;
          write_u64(&mut out, state.map.len() as u64)?;
          for (expr, degree) in &state.map {
            write_u64(&mut out, eval_expr(expr, &values).as_canonical_u64())?;
            write_u64(&mut out, u64::from(*degree))?;
            write_u64(&mut out, u64::from(matches!(expr, Expr::Const(_))))?;
          }
          let equations: Vec<_> = state
            .constraints
            .zeros
            .iter()
            .map(|expr| eval_expr(expr, &values))
            .collect();
          write_values(&mut out, &equations)?;
          write_u64(&mut out, state.lookup as u64)?;
          for lookup in &state.lookups[..state.lookup] {
            write_u64(
              &mut out,
              eval_expr(&lookup.multiplicity, &values).as_canonical_u64(),
            )?;
            let args: Vec<_> =
              lookup.args.iter().map(|expr| eval_expr(expr, &values)).collect();
            write_values(&mut out, &args)?;
          }
          checked += 1;
        }
      }
    }
  }
  Ok((out, checked))
}

#[test]
fn operation_rows_snapshot() -> io::Result<()> {
  let fixtures = fixtures();
  let kinds: HashSet<_> =
    fixtures.iter().flatten().map(std::mem::discriminant).collect();
  assert_eq!(kinds.len(), 34, "every bytecode operation constructor");
  assert_eq!(fixtures.len(), 65, "operation and sequence corpus");
  let (out, checked) = write_corpus(b"Aiur operation rows v1\n", &fixtures)?;
  assert_eq!(checked, 6240);
  if let Some(path) = std::env::var_os("IX_OPERATION_ROW_SNAPSHOT") {
    let mut file = BufWriter::new(File::create(path)?);
    file.write_all(&out)?;
    file.flush()?;
  }
  eprintln!("operation rows: {checked} assignments across all 34 constructors");
  Ok(())
}

pub(super) fn constant_degree_fixtures() -> Vec<Vec<Op>> {
  use Op::*;
  vec![
    vec![Const(G::ZERO), Mul(8, 3), EqZero(9)],
    vec![Const(G::ZERO), Mul(3, 8), EqZero(9)],
    vec![Mul(0, 3), Add(8, 1), EqZero(9)],
    vec![Mul(0, 3), Sub(0, 8), EqZero(9)],
    vec![Mul(0, 3), EqZero(8), EqZero(9)],
    vec![Mul(0, 3), EqZero(8), Mul(9, 3)],
    vec![Mul(0, 3), Mul(8, 1), EqZero(9)],
    vec![Mul(0, 3), Sub(2, 8), EqZero(9)],
  ]
}

#[test]
fn constant_degree_rows_snapshot() -> io::Result<()> {
  let fixtures = constant_degree_fixtures();
  let (out, checked) =
    write_corpus(b"Aiur constant degree rows v1\n", &fixtures)?;
  assert_eq!(checked, 768);
  if let Some(path) = std::env::var_os("IX_CONSTANT_DEGREE_ROW_SNAPSHOT") {
    let mut file = BufWriter::new(File::create(path)?);
    file.write_all(&out)?;
    file.flush()?;
  }
  eprintln!(
    "constant degree rows: {checked} arbitrary assignments across eight sequences"
  );
  Ok(())
}
