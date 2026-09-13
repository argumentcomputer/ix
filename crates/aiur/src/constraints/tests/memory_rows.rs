// Copyright (c) 2026 Argument Computer Corporation.
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Evaluate the actual memory chip's four equations and its physical lookup,
//! including cyclic next-row openings and the disabled final transition.

use super::*;
use crate::memory::Memory;

fn row(height: usize, pattern: usize, index: usize, width: usize) -> Vec<G> {
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
  let selector = match pattern % 8 {
    0 => G::ZERO,
    1 => G::ONE,
    2 => G::from_bool(index < height.div_ceil(2)),
    3 => G::from_bool(index + 1 == height),
    4 => G::from_bool(index.is_multiple_of(2)),
    5 => G::TWO,
    6 => -G::ONE,
    _ => choices[(index + pattern) % 8],
  };
  (0..width)
    .map(|column| {
      if pattern == 0 {
        return G::ZERO;
      }
      match column {
        0 if pattern < 8 && selector == G::ZERO => G::ZERO,
        0 => choices[(3 * index + pattern) % 8],
        1 => selector,
        2 if pattern < 16 => -G::ONE + G::from_usize(index),
        2 => G::from_usize(255 + 2 * index),
        _ => choices[(5 * column + 3 * index + pattern) % 8],
      }
    })
    .collect()
}

#[test]
fn memory_rows_snapshot() -> io::Result<()> {
  let mut out = Vec::new();
  out.write_all(b"Aiur memory rows v1\n")?;
  write_u64(&mut out, 25)?;
  let mut checked = 0;
  for size in [0, 1, 2, 4, 8] {
    let (memory, constraints, lookups) = Memory::build(size);
    assert_eq!(memory.width, 3 + size);
    assert_eq!(constraints.len(), 4);
    assert_eq!(lookups.len(), 1);
    for height in [0, 1, 2, 4, 8] {
      for value in [size, height, memory.width, lookups.len(), 24] {
        write_u64(&mut out, value as u64)?;
      }
      for pattern in 0..24 {
        for index in 0..height {
          let current = row(height, pattern, index, memory.width);
          let next = row(height, pattern, (index + 1) % height, memory.width);
          let values = VarValues {
            preprocessed: [&[], &[]],
            main: [&current, &next],
            stage2: [&[], &[]],
            publics: &[],
            is_first_row: G::from_bool(index == 0),
            is_last_row: G::from_bool(index + 1 == height),
            is_transition: G::from_bool(index + 1 < height),
          };
          let equations: Vec<_> =
            constraints.iter().map(|expr| eval_expr(expr, &values)).collect();
          write_values(&mut out, &equations)?;
          for lookup in &lookups {
            write_u64(
              &mut out,
              eval_expr(&lookup.multiplicity, &values).as_canonical_u64(),
            )?;
            let message: Vec<_> =
              lookup.args.iter().map(|expr| eval_expr(expr, &values)).collect();
            write_values(&mut out, &message)?;
          }
          checked += 1;
        }
      }
    }
  }
  assert_eq!(checked, 1800);
  if let Some(path) = std::env::var_os("IX_MEMORY_ROW_SNAPSHOT") {
    let mut file = BufWriter::new(File::create(path)?);
    file.write_all(&out)?;
    file.flush()?;
  }
  eprintln!("memory rows: {checked} assignments across 25 width/height pairs");
  Ok(())
}
