// Copyright (c) 2026 Argument Computer Corporation.
// SPDX-License-Identifier: MIT OR Apache-2.0

//! The pinned direct evaluator in both scalar domains, its independent
//! symbolic specification, and the actual grouped stage-2 trace builder.

use super::*;
use multi_stark::{
  eval::{VarValues, eval_ext_expr},
  expr::Expr,
  graph::ExtensionParams,
  lookup::{
    LookupValues, logup_constraint_values, stage2_width, synthesize_lookups,
  },
  p3_field::{
    Algebra, BasedVectorSpace, Field, TwoAdicField,
    extension::BinomiallyExtendable,
  },
  types::ExtVal,
};
use std::io;

const COUNTS: [usize; 22] = [
  0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 15, 16, 17, 23, 24, 25, 31, 32, 33, 63, 64, 65,
];
const ARITIES: [usize; 10] = [0, 1, 2, 3, 4, 7, 8, 9, 16, 17];
const SEEDS: usize = 12;

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

fn vector<W: Copy>(
  out: &mut Vec<u8>,
  values: &[W],
  encode: fn(&mut Vec<u8>, W),
) {
  nat(out, values.len());
  for &value in values {
    encode(out, value);
  }
}

fn scalar(seed: usize, slot: usize, index: usize) -> Val {
  let mut value = 0x508c_4dd3_50c9_1a2b_u64
    .wrapping_add(u64::try_from(seed).unwrap().wrapping_mul(0x36d3_2817))
    .wrapping_add(u64::try_from(slot).unwrap().wrapping_mul(0x792b_586f))
    .wrapping_add(u64::try_from(index).unwrap().wrapping_mul(0x650d_810b));
  for _ in 0..4 {
    value ^= value << 13;
    value ^= value >> 7;
    value ^= value << 17;
  }
  if seed < 6 {
    let boundary = [
      0,
      1,
      2,
      7,
      255,
      65536,
      (1 << 32) - 1,
      1 << 63,
      Val::ORDER_U64 - 2,
      Val::ORDER_U64 - 1,
    ];
    Val::from_u64(boundary[(seed + slot + index) % boundary.len()])
  } else {
    Val::from_u64(value)
  }
}

fn assignment<W: Field>(
  seed: usize,
  slot: usize,
  length: usize,
  make: fn(Val, Val) -> W,
) -> Vec<W> {
  (0..length)
    .map(|index| match seed {
      0 => W::ZERO,
      1 => W::ONE,
      2 => W::NEG_ONE,
      _ => {
        make(scalar(seed, 2 * slot, index), scalar(seed, 2 * slot + 1, index))
      },
    })
    .collect()
}

fn lookup_ids(count: usize) -> (Vec<Lookup<NodeId>>, usize) {
  let mut next = 1;
  let lookups = (0..count)
    .map(|index| {
      let multiplicity = NodeId(u32::try_from(next).unwrap());
      next += 1;
      let args = (0..ARITIES[index % ARITIES.len()])
        .map(|arg| {
          let id = if arg % 3 == 2 { 0 } else { next };
          next += 1;
          NodeId(u32::try_from(id).unwrap())
        })
        .collect();
      Lookup { multiplicity, args }
    })
    .collect();
  (lookups, next)
}

fn encode_ids(out: &mut Vec<u8>, lookups: &[Lookup<NodeId>]) {
  nat(out, lookups.len());
  for lookup in lookups {
    nat(out, lookup.multiplicity.index());
    nat(out, lookup.args.len());
    for &arg in &lookup.args {
      nat(out, arg.index());
    }
  }
}

fn direct_cases<W: Field + Algebra<Val>>(
  out: &mut Vec<u8>,
  make: fn(Val, Val) -> W,
  encode: fn(&mut Vec<u8>, W),
) {
  nat(out, COUNTS.len() * 9 * SEEDS);
  for count in COUNTS {
    let (lookups, nodes) = lookup_ids(count);
    let symbolic: Vec<Lookup<Expr<W>>> = lookups
      .iter()
      .map(|lookup| Lookup {
        multiplicity: Expr::main(lookup.multiplicity.0),
        args: lookup.args.iter().map(|id| Expr::main(id.0)).collect(),
      })
      .collect();
    for group_size in 0..=8 {
      let expressions = synthesize_lookups(&symbolic, 2, group_size);
      let params = ExtensionParams {
        degree: 2,
        w: W::from(Val::from_u8(7)),
        karatsuba: false,
      };
      for seed in 0..SEEDS {
        nat(out, count);
        nat(out, group_size);
        nat(out, seed);
        encode_ids(out, &lookups);
        let node_values = assignment(seed, 0, nodes, make);
        let width = stage2_width(count, group_size, 2);
        let current = assignment(seed, 1, width, make);
        let next = assignment(seed, 2, width, make);
        let publics = assignment(seed, 3, 8, make);
        let delta = [publics[6] - publics[4], publics[7] - publics[5]];
        let is_last = assignment(seed, 4, 1, make)[0];
        let view = VarValues {
          preprocessed: [&[], &[]],
          main: [&node_values, &[]],
          stage2: [&current, &next],
          publics: &publics,
          is_first_row: W::ZERO,
          is_last_row: is_last,
          is_transition: W::ONE,
        };
        let reference: Vec<W> = expressions
          .iter()
          .flat_map(|expression| eval_ext_expr(expression, &view, &params))
          .collect();
        // Appending must retain the user constraints that precede logUp.
        let mut direct = vec![W::from_u8(3), W::from_u8(9)];
        logup_constraint_values(
          &lookups,
          &node_values,
          &current,
          &next,
          &publics,
          &delta,
          is_last,
          Val::from_u8(7),
          2,
          group_size,
          &mut direct,
        );
        assert_eq!(&direct[..2], &[W::from_u8(3), W::from_u8(9)]);
        assert_eq!(&direct[2..], reference);
        assert_eq!(reference.len(), width);
        for values in [&node_values, &current, &next, &publics] {
          vector(out, values, encode);
        }
        vector(out, &delta, encode);
        encode(out, is_last);
        vector(out, &direct[2..], encode);
      }
    }
  }
}

#[test]
fn logup_snapshot() -> io::Result<()> {
  assert_eq!(<ExtVal as BasedVectorSpace<Val>>::DIMENSION, 2);
  assert_eq!(<Val as BinomiallyExtendable<2>>::W, Val::from_u8(7));
  let mut out = b"Aiur grouped logup v1\n".to_vec();
  direct_cases(&mut out, |first, _| first, field);
  direct_cases(
    &mut out,
    |first, second| ExtVal::new([first, second]),
    extension,
  );
  if let Some(path) = std::env::var_os("IX_LOGUP_SNAPSHOT") {
    std::fs::write(path, out)?;
  }
  eprintln!(
    "grouped logup: {} direct/reference cases",
    2 * COUNTS.len() * 9 * SEEDS
  );
  Ok(())
}

fn flatten(values: &[ExtVal]) -> Vec<Val> {
  values
    .iter()
    .flat_map(|value| value.as_basis_coefficients_slice().iter().copied())
    .collect()
}

fn rows(circuit: usize, seed: usize) -> Vec<Vec<Lookup<Val>>> {
  let height = [1, 2, 4, 8, 4][circuit];
  let count = [0, 1, 9, 17, 25][circuit];
  (0..height)
    .map(|row| {
      (0..count)
        .map(|lookup| Lookup {
          multiplicity: scalar(seed + 3, row, lookup),
          args: (0..ARITIES[(lookup + row) % ARITIES.len()])
            .map(|arg| scalar(seed + 7, lookup, arg + row * 31))
            .collect(),
        })
        .collect()
    })
    .collect()
}

fn message(beta: ExtVal, gamma: ExtVal, args: &[Val]) -> ExtVal {
  beta + args.iter().rev().fold(ExtVal::ZERO, |acc, &arg| acc * gamma + arg)
}

#[test]
fn logup_stage_snapshot() -> io::Result<()> {
  let mut out = b"Aiur grouped logup stages v1\n".to_vec();
  nat(&mut out, 27);
  let mut row_count = 0;
  for group_size in 0..=8 {
    for seed in 0..3 {
      let beta = ExtVal::new([Val::from_usize(5 + seed), Val::from_u8(13)]);
      let gamma = ExtVal::new([Val::from_u8(7), Val::from_usize(11 + seed)]);
      let initial = ExtVal::new([Val::from_u8(17), Val::from_usize(19 + seed)]);
      let raw: Vec<_> = (0..5).map(|circuit| rows(circuit, seed)).collect();
      for row in raw.iter().flatten() {
        for lookup in row {
          assert!(message(beta, gamma, &lookup.args).try_inverse().is_some());
        }
      }
      let circuits: Vec<_> =
        raw.iter().cloned().map(LookupValues::from_rows).collect();
      let (traces, accumulators) = LookupValues::stage_2_traces(
        &circuits,
        &[group_size; 5],
        beta,
        &gamma,
        initial,
      );
      nat(&mut out, group_size);
      nat(&mut out, seed);
      extension(&mut out, beta);
      extension(&mut out, gamma);
      extension(&mut out, initial);
      nat(&mut out, raw.len());
      let mut entering = initial;
      for ((rows, trace), &leaving) in
        raw.iter().zip(&traces).zip(&accumulators)
      {
        nat(&mut out, rows.len());
        nat(&mut out, rows[0].len());
        nat(&mut out, trace.width);
        vector(&mut out, &trace.values, extension);
        extension(&mut out, leaving);
        let normalizer = Val::from_usize(rows.len())
          * Val::two_adic_generator(
            usize::try_from(rows.len().ilog2()).unwrap(),
          );
        field(&mut out, normalizer);
        let delta = flatten(&[(leaving - entering) * normalizer.inverse()]);
        let publics = flatten(&[beta, gamma, entering, leaving]);
        for (row_index, row) in rows.iter().enumerate() {
          nat(&mut out, row.len());
          let mut node_values = Vec::new();
          let mut ids = Vec::new();
          for lookup in row {
            field(&mut out, lookup.multiplicity);
            vector(&mut out, &lookup.args, field);
            let multiplicity =
              NodeId(u32::try_from(node_values.len()).unwrap());
            node_values.push(lookup.multiplicity);
            let mut args = Vec::new();
            for &arg in &lookup.args {
              args.push(NodeId(u32::try_from(node_values.len()).unwrap()));
              node_values.push(arg);
            }
            ids.push(Lookup { multiplicity, args });
          }
          let start = row_index * trace.width;
          let next_start = (row_index + 1) % rows.len() * trace.width;
          let current = flatten(&trace.values[start..start + trace.width]);
          let next =
            flatten(&trace.values[next_start..next_start + trace.width]);
          let is_last =
            if row_index + 1 == rows.len() { normalizer } else { Val::ZERO };
          let mut equations = Vec::new();
          logup_constraint_values(
            &ids,
            &node_values,
            &current,
            &next,
            &publics,
            &delta,
            is_last,
            Val::from_u8(7),
            2,
            group_size,
            &mut equations,
          );
          assert!(equations.iter().all(|&value| value == Val::ZERO));
          vector(&mut out, &equations, field);
          row_count += 1;
        }
        entering = leaving;
      }
    }
  }
  assert_eq!(row_count, 513);
  if let Some(path) = std::env::var_os("IX_LOGUP_STAGE_SNAPSHOT") {
    std::fs::write(path, out)?;
  }
  eprintln!("grouped stages: 27 batches, 135 circuits, {row_count} rows");
  Ok(())
}
