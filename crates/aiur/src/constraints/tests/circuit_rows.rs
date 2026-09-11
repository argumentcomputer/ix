// Copyright (c) 2026 Argument Computer Corporation.
// SPDX-License-Identifier: MIT OR Apache-2.0

//! The actual whole-circuit builder, including grouped member offsets,
//! shared multiplicity/rank columns, and all physical lookup slots.

use super::*;
use crate::bytecode::{Circuit, Function, FunctionLayout};

fn close_returns(block: &mut Block, width: usize, escapes: bool) {
  match &mut block.ctrl {
    Ctrl::Return(_, outputs) => outputs.truncate(width),
    Ctrl::Yield(selector, outputs) => {
      if escapes {
        block.ctrl = Ctrl::Return(*selector, outputs[..width].to_vec());
      }
    },
    Ctrl::Match(_, cases, fallback) => {
      for body in cases.values_mut() {
        close_returns(body, width, escapes);
      }
      if let Some(body) = fallback {
        close_returns(body, width, escapes);
      }
    },
    Ctrl::MatchContinue(_, cases, fallback, _, _, _, continuation) => {
      for body in cases.values_mut() {
        close_returns(body, width, false);
      }
      if let Some(body) = fallback {
        close_returns(body, width, false);
      }
      close_returns(continuation, width, escapes);
    },
  }
}

fn fixture_function(seed: usize, index: usize) -> Function {
  let input_size = 2 + (seed + index) % 3;
  let depth = (seed + index) % 3;
  let mut selectors = 0;
  let mut body = block_rows::block_fixture(
    depth,
    seed * 4 + index,
    input_size,
    &mut selectors,
  );
  close_returns(&mut body, index % 3, true);
  if seed.is_multiple_of(4) && index == 0 {
    body = Block {
      ops: vec![],
      ctrl: Ctrl::Match(
        0,
        [
          (
            G::ZERO,
            Block {
              ops: vec![Op::Store(vec![])],
              ctrl: Ctrl::Match(0, FxIndexMap::default(), None),
            },
          ),
          (G::ONE, body),
        ]
        .into_iter()
        .collect(),
        None,
      ),
    };
  }
  let mut measured = state(selectors, false);
  measured.input_size = input_size;
  measured.sel_base = input_size;
  measured.column = input_size + selectors + 7;
  measured.lookup = 4;
  measured.map = (0..input_size).map(|i| (var(i), 1)).collect();
  measured.lookups = (0..4096).map(|_| empty_lookup()).collect();
  measured.yield_info.clear();
  let selector = body.get_block_selector(&measured);
  body.collect_constraints(selector, &mut measured);
  assert!(measured.yield_info.is_empty());
  Function {
    body,
    layout: FunctionLayout {
      input_size,
      selectors,
      auxiliaries: measured.column - input_size - selectors,
      lookups: measured.lookup,
    },
    entry: true,
    constrained: true,
  }
}

fn circuit_layout(functions: &[Function], members: &[usize]) -> FunctionLayout {
  let mut layout =
    FunctionLayout { input_size: 0, selectors: 0, auxiliaries: 7, lookups: 4 };
  for &member in members {
    let next = functions[member].layout;
    layout.input_size = layout.input_size.max(next.input_size);
    layout.selectors += next.selectors;
    layout.auxiliaries = layout.auxiliaries.max(next.auxiliaries);
    layout.lookups = layout.lookups.max(next.lookups);
  }
  layout
}

#[test]
fn circuit_rows_snapshot() -> io::Result<()> {
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
  out.write_all(b"Aiur circuit rows v3\n")?;
  write_u64(&mut out, (12 * groups.len()) as u64)?;
  let mut checked = 0;
  for seed in 0..12 {
    let functions: Vec<_> = (0..4).map(|i| fixture_function(seed, i)).collect();
    let circuits = groups
      .iter()
      .map(|members| Circuit {
        members: members.to_vec(),
        layout: circuit_layout(&functions, members),
      })
      .collect();
    let top = Toplevel { functions, circuits, memory_sizes: vec![] };
    for function in &top.functions {
      let counts = function.body.control_counts().expect("control counts fit");
      assert_eq!(counts.leaves, function.layout.selectors);
      for count in [counts.nodes, counts.leaves, counts.returns, counts.yields]
      {
        write_u64(&mut out, count as u64)?;
      }
    }
    assert!(top.validate_row_counts().is_ok());
    out.push(u8::from(top.validate_row_counts().is_ok()));
    for circuit_index in 0..groups.len() {
      let circuit = &top.circuits[circuit_index];
      let count = circuit.layout.selectors;
      for limit in [0, count.saturating_sub(1), count, count + 1] {
        let variant = Circuit {
          members: circuit.members.clone(),
          layout: FunctionLayout { selectors: limit, ..circuit.layout },
        };
        out.push(u8::from(variant.validate_row_counts(&top).is_ok()));
      }
      let mut missing = circuit.members.clone();
      missing.push(top.functions.len());
      let missing = Circuit { members: missing, layout: circuit.layout };
      assert!(missing.validate_row_counts(&top).is_err());
      out.push(u8::from(missing.validate_row_counts(&top).is_ok()));
      let doubled =
        Circuit { members: circuit.members.repeat(2), layout: circuit.layout };
      out.push(u8::from(doubled.validate_row_counts(&top).is_ok()));
      out.push(u8::from(top.circuit_is_branchless(circuit_index)));
      let (constraints, lookups) = top.build_constraints(circuit_index);
      let selector_count = constraints.selectors.len();
      write_u64(&mut out, constraints.width as u64)?;
      write_u64(&mut out, constraints.selectors.start as u64)?;
      write_u64(&mut out, selector_count as u64)?;
      write_u64(&mut out, lookups.len() as u64)?;
      write_u64(&mut out, (8 + 2 * selector_count) as u64)?;
      for pattern in 0..8 + 2 * selector_count {
        let mut row: Vec<_> = (0..constraints.width)
          .map(|index| {
            choices[(seed + 5 * index + 3 * pattern) % choices.len()]
          })
          .collect();
        for index in 0..selector_count {
          row[constraints.selectors.start + index] =
            assignment(pattern, index, selector_count);
        }
        let values = local_values(&row);
        let equations: Vec<_> = constraints
          .zeros
          .iter()
          .map(|expr| eval_expr(expr, &values))
          .collect();
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
  assert_eq!(checked, 2022);
  if let Some(path) = std::env::var_os("IX_CIRCUIT_ROW_SNAPSHOT") {
    let mut file = BufWriter::new(File::create(path)?);
    file.write_all(&out)?;
    file.flush()?;
  }
  eprintln!(
    "circuit rows: {checked} assignments, 48 control counts, 588 count checks, 96 branchless decisions"
  );
  Ok(())
}
