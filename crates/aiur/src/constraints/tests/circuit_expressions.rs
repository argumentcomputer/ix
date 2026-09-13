// Copyright (c) 2026 Argument Computer Corporation.
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Transport actual programs and complete circuit-builder expressions.

use super::{
  block_expressions::write_block,
  circuit_rows::{circuit_layout, fixture_function},
  frontend_expressions::write_expr,
  operation_expressions::{write_exprs, write_indices},
  *,
};
use crate::bytecode::{Circuit, FunctionLayout};

pub(super) fn write_layout(
  out: &mut impl Write,
  layout: FunctionLayout,
) -> io::Result<()> {
  for count in
    [layout.input_size, layout.selectors, layout.auxiliaries, layout.lookups]
  {
    write_u64(out, count as u64)?;
  }
  Ok(())
}

#[test]
fn circuit_expressions_snapshot() -> io::Result<()> {
  let groups: &[&[usize]] =
    &[&[0], &[1], &[2], &[3], &[0, 1], &[2, 0, 3], &[3, 2, 1, 0], &[]];
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
  out.write_all(b"Aiur circuit expressions v1\n")?;
  write_u64(&mut out, 12)?;
  let mut reports = 0;
  let mut checked = 0;
  for seed in 0..12 {
    let functions: Vec<_> =
      (0..4).map(|index| fixture_function(seed, index)).collect();
    let circuits = groups
      .iter()
      .map(|members| Circuit {
        members: members.to_vec(),
        layout: circuit_layout(&functions, members),
      })
      .collect();
    let top = Toplevel {
      functions,
      circuits,
      memory_sizes: vec![],
      call_components: vec![],
    };
    assert!(top.validate_row_counts().is_ok());
    assert!(top.validate_emission().is_ok());
    write_u64(&mut out, top.functions.len() as u64)?;
    for function in &top.functions {
      write_block(&mut out, &function.body)?;
      write_layout(&mut out, function.layout)?;
      out.write_all(&[
        u8::from(function.entry),
        u8::from(function.constrained),
      ])?;
    }
    write_u64(&mut out, top.circuits.len() as u64)?;
    for circuit in &top.circuits {
      write_indices(&mut out, &circuit.members)?;
      write_layout(&mut out, circuit.layout)?;
    }
    for (index, circuit) in top.circuits.iter().enumerate() {
      out.write_all(&[u8::from(top.circuit_is_branchless(index))])?;
      let (constraints, lookups) = top.build_constraints(index);
      let inactive_row = vec![G::ZERO; constraints.width];
      let inactive_values = local_values(&inactive_row);
      assert!(
        constraints
          .zeros
          .iter()
          .all(|expr| eval_expr(expr, &inactive_values) == G::ZERO)
      );
      write_u64(&mut out, constraints.width as u64)?;
      write_u64(&mut out, constraints.selectors.start as u64)?;
      write_u64(&mut out, constraints.selectors.len() as u64)?;
      write_exprs(&mut out, &constraints.zeros)?;
      write_u64(&mut out, lookups.len() as u64)?;
      for lookup in &lookups {
        write_expr(&mut out, &lookup.multiplicity)?;
        write_exprs(&mut out, &lookup.args)?;
      }
      write_u64(&mut out, 4)?;
      for pattern in [0, 1, 2, 7] {
        let mut row: Vec<_> = (0..constraints.width)
          .map(|column| {
            choices[(seed + 5 * column + 3 * pattern) % choices.len()]
          })
          .collect();
        for column in 0..circuit.layout.selectors {
          row[constraints.selectors.start + column] =
            assignment(pattern, column, circuit.layout.selectors);
        }
        write_values(&mut out, &row)?;
        let values = local_values(&row);
        for expr in &constraints.zeros {
          write_u64(&mut out, eval_expr(expr, &values).as_canonical_u64())?;
        }
        for lookup in &lookups {
          write_u64(
            &mut out,
            eval_expr(&lookup.multiplicity, &values).as_canonical_u64(),
          )?;
          for arg in &lookup.args {
            write_u64(&mut out, eval_expr(arg, &values).as_canonical_u64())?;
          }
        }
        checked += 1;
      }
      reports += 1;
    }
  }
  assert_eq!((reports, checked), (96, 384));
  if let Some(path) = std::env::var_os("IX_CIRCUIT_EXPRESSION_SNAPSHOT") {
    let mut file = BufWriter::new(File::create(path)?);
    file.write_all(&out)?;
    file.flush()?;
  }
  eprintln!(
    "circuit expressions: {reports} circuits, {checked} assignments, {reports} inactive zero rows"
  );
  Ok(())
}
