// Copyright (c) 2026 Argument Computer Corporation.
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Arithmetic from the pinned field implementation, including full-width
//! exponents and arbitrary quadratic values in the actual compiled graphs.

use super::*;
use multi_stark::{
  eval::VarValues,
  p3_field::{BasedVectorSpace, Field, extension::HasFrobenius},
  types::ExtVal,
};
use std::io;

fn nat(out: &mut Vec<u8>, value: usize) {
  out.extend(u64::try_from(value).unwrap().to_le_bytes());
}

fn field(out: &mut Vec<u8>, value: Val) {
  out.extend(value.as_canonical_u64().to_le_bytes());
}

fn extension(out: &mut Vec<u8>, value: ExtVal) {
  for &coordinate in value.as_basis_coefficients_slice() {
    field(out, coordinate);
  }
}

fn extensions(out: &mut Vec<u8>, values: &[ExtVal]) {
  nat(out, values.len());
  for &value in values {
    extension(out, value);
  }
}

fn inverse(out: &mut Vec<u8>, value: Option<ExtVal>) {
  out.push(u8::from(value.is_some()));
  if let Some(value) = value {
    extension(out, value);
  }
}

fn scalars() -> Vec<Val> {
  let p = Val::ORDER_U64;
  [
    0,
    1,
    2,
    7,
    17,
    255,
    256,
    65535,
    65536,
    (1 << 32) - 1,
    1 << 32,
    (1 << 48) - 1,
    1 << 63,
    p - 3,
    p - 2,
    p - 1,
  ]
  .into_iter()
  .map(Val::from_u64)
  .collect()
}

fn values() -> Vec<ExtVal> {
  let scalars = scalars();
  let mut values = Vec::new();
  for &first in &scalars {
    for &second in &scalars {
      values.push(ExtVal::new([first, second]));
    }
  }
  // Reproducible full-word coordinates, independent in the two slots.
  let mut state = 0x19a9_391d_0582_a7a5_u64;
  let mut next = || {
    state ^= state << 13;
    state ^= state >> 7;
    state ^= state << 17;
    Val::from_u64(state)
  };
  for _ in 0..128 {
    values.push(ExtVal::new([next(), next()]));
  }
  values
}

fn exponents() -> [u128; 20] {
  let p = u128::from(Val::ORDER_U64);
  [
    0,
    1,
    2,
    3,
    7,
    8,
    15,
    16,
    31,
    32,
    63,
    64,
    p - 2,
    p - 1,
    p,
    u128::from(u64::MAX),
    1 << 64,
    p * p - 2,
    (1 << 127) + 1,
    u128::MAX,
  ]
}

fn native_power(value: ExtVal, exponent: u128) -> ExtVal {
  let low = u64::try_from(exponent & u128::from(u64::MAX)).unwrap();
  let high = u64::try_from(exponent >> 64).unwrap();
  value.exp_u64(low) * value.exp_u64(high).exp_power_of_2(64)
}

#[test]
fn extension_arithmetic_snapshot() -> io::Result<()> {
  let mut out = b"Aiur extension arithmetic v1\n".to_vec();
  let scalars = scalars();
  nat(&mut out, scalars.len());
  for value in scalars {
    field(&mut out, value);
    field(&mut out, value.try_inverse().unwrap_or(Val::ZERO));
  }
  let values = values();
  let exponents = exponents();
  extensions(&mut out, &values);
  nat(&mut out, exponents.len());
  for exponent in exponents {
    out.extend(exponent.to_le_bytes());
  }
  let mut inverses = 0;
  for &value in &values {
    extension(&mut out, -value);
    extension(&mut out, value.square());
    extension(&mut out, value.frobenius());
    let norm = value * value.frobenius();
    let norm_coordinates: &[Val] = norm.as_basis_coefficients_slice();
    assert_eq!(norm_coordinates[1], Val::ZERO);
    field(&mut out, norm_coordinates[0]);
    let inv = value.try_inverse();
    if let Some(inv) = inv {
      assert_eq!(value * inv, ExtVal::ONE);
      inverses += 1;
    }
    inverse(&mut out, inv);
    for exponent in exponents {
      extension(&mut out, native_power(value, exponent));
    }
  }
  for &left in &values {
    for &right in &values {
      extension(&mut out, left + right);
      extension(&mut out, left - right);
      extension(&mut out, left * right);
    }
  }
  assert_eq!((values.len(), inverses), (384, 383));
  if let Some(path) = std::env::var_os("IX_EXTENSION_ARITHMETIC_SNAPSHOT") {
    std::fs::write(path, out)?;
  }
  eprintln!(
    "extension arithmetic: {} values, {} powers, {} ordered pairs",
    values.len(),
    values.len() * exponents.len(),
    values.len() * values.len()
  );
  Ok(())
}

fn assignment(
  values: &[ExtVal],
  width: usize,
  slot: usize,
  seed: usize,
) -> Vec<ExtVal> {
  (0..width)
    .map(|index| match seed {
      0 => ExtVal::ZERO,
      1 => ExtVal::ONE,
      2 => -ExtVal::ONE,
      _ => values[(index * 37 + slot * 61 + seed * 19) % values.len()],
    })
    .collect()
}

#[test]
fn extension_graph_snapshot() -> io::Result<()> {
  let system = graph_tests::graph_system();
  let values = values();
  let mut out = b"Aiur extension graphs v1\n".to_vec();
  nat(&mut out, system.circuits.len());
  let mut nodes = 0;
  for circuit in &system.circuits {
    let mut encoded = Vec::new();
    encode_circuit(&mut encoded, circuit);
    nat(&mut out, encoded.len());
    out.extend(encoded);
    nat(&mut out, 24);
    for seed in 0..24 {
      let widths = [
        circuit.preprocessed_width,
        circuit.preprocessed_width,
        circuit.main_width,
        circuit.main_width,
        circuit.stage_2_width,
        circuit.stage_2_width,
        circuit.num_publics,
      ];
      let rows: Vec<_> = widths
        .into_iter()
        .enumerate()
        .map(|(slot, width)| assignment(&values, width, slot, seed))
        .collect();
      for row in &rows {
        extensions(&mut out, row);
      }
      let selectors = assignment(&values, 3, 7, seed);
      for &selector in &selectors {
        extension(&mut out, selector);
      }
      let view = VarValues {
        preprocessed: [&rows[0], &rows[1]],
        main: [&rows[2], &rows[3]],
        stage2: [&rows[4], &rows[5]],
        publics: &rows[6],
        is_first_row: selectors[0],
        is_last_row: selectors[1],
        is_transition: selectors[2],
      };
      let mut buffer = Vec::new();
      circuit.graph.sweep(&view, &mut buffer);
      nodes += buffer.len();
      extensions(&mut out, &buffer);
      extensions(&mut out, &circuit.graph.constraint_values(&buffer));
      let lookups = circuit.graph.lookup_values(&buffer);
      nat(&mut out, lookups.len());
      for lookup in lookups {
        extension(&mut out, lookup.multiplicity);
        extensions(&mut out, &lookup.args);
      }
    }
  }
  assert_eq!((system.circuits.len(), nodes), (10, 8016));
  if let Some(path) = std::env::var_os("IX_EXTENSION_GRAPH_SNAPSHOT") {
    std::fs::write(path, out)?;
  }
  eprintln!("extension graphs: 240 native assignments, {nodes} node values");
  Ok(())
}
