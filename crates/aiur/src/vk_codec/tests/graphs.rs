// Copyright (c) 2026 Argument Computer Corporation.
// SPDX-License-Identifier: MIT OR Apache-2.0

use super::*;
use crate::{
  bytecode::{
    Block, Circuit as BytecodeCircuit, Ctrl, Function, FunctionLayout, Op,
    Toplevel,
  },
  gadgets::{AiurGadget, bytes1::Bytes1, bytes2::Bytes2},
  memory::Memory,
};
use multi_stark::{
  eval::VarValues,
  expr::{Expr, ExtExpr},
  p3_matrix::dense::RowMajorMatrix,
  system::CircuitInputs,
};
use std::{
  fs::File,
  io::{self, Write},
};

fn expression_input() -> CircuitInputs<Val> {
  let x = Expr::main(0);
  let y = Expr::main_next(1);
  let constraints = vec![
    x.clone() + Expr::preprocessed(0),
    y.clone() - Expr::public(1),
    -x.clone(),
    Expr::IsTransition * (x.clone() * x.clone() - y.clone()),
    // Exercise explicit frontend nodes, folding and duplicate roots.
    Expr::Add(Box::new(Expr::Const(Val::ZERO)), Box::new(x.clone())),
    Expr::Sub(Box::new(x.clone()), Box::new(x.clone())),
    x.clone(),
    x.clone(),
  ];
  let ext = ExtExpr::stage2(0, 2, RowOffset::Current);
  let ext_constraints = vec![
    ext.clone() * ext.clone() - ExtExpr::stage2(0, 2, RowOffset::Next),
    -ext + ExtExpr::Coords(vec![x.clone(), y.clone()]),
  ];
  let lookups = vec![Lookup {
    multiplicity: -x.clone(),
    args: vec![
      x,
      y,
      Expr::preprocessed(1),
      Expr::preprocessed_next(0),
      Expr::public(0),
      Expr::IsFirstRow,
      Expr::IsLastRow,
      Expr::IsTransition,
      Expr::Const(Val::from_u64(65536)),
      Expr::Const(-Val::ONE),
      // Compilation interns Main(2), then folds the expression to zero.
      // The compiler's lookup prefix can therefore exceed the root-derived
      // prefix reconstructed by the codec, without changing lookup values.
      Expr::Mul(Box::new(Expr::Const(Val::ZERO)), Box::new(Expr::main(2))),
    ],
  }];
  CircuitInputs {
    main_width: 3,
    preprocessed: Some(RowMajorMatrix::new(vec![Val::ZERO; 4], 2)),
    constraints,
    ext_constraints,
    lookups,
    lookup_group_size: 1,
  }
}

fn function_inputs() -> Vec<CircuitInputs<Val>> {
  let layout =
    FunctionLayout { input_size: 2, selectors: 1, auxiliaries: 8, lookups: 4 };
  let function = || Function {
    body: Block { ops: vec![Op::Mul(0, 1)], ctrl: Ctrl::Return(0, vec![2]) },
    layout,
    entry: true,
    constrained: true,
  };
  let top = Toplevel {
    functions: vec![function(), function()],
    circuits: vec![
      BytecodeCircuit { members: vec![0], layout },
      BytecodeCircuit {
        members: vec![0, 1],
        layout: FunctionLayout { selectors: 2, ..layout },
      },
    ],
    memory_sizes: vec![],
  };
  (0..top.circuits.len())
    .map(|index| {
      let (constraints, lookups) = top.build_constraints(index);
      CircuitInputs {
        main_width: constraints.width,
        constraints: constraints.zeros,
        lookups,
        lookup_group_size: 1,
        ..CircuitInputs::default()
      }
    })
    .collect()
}

pub(super) fn graph_system() -> System<AiurConfig> {
  let mut inputs = vec![expression_input()];
  for size in [0, 1, 2, 4, 8] {
    let (memory, constraints, lookups) = Memory::build(size);
    inputs.push(CircuitInputs {
      main_width: memory.width,
      constraints,
      lookups,
      lookup_group_size: 1,
      ..CircuitInputs::default()
    });
  }
  inputs.extend([
    CircuitInputs {
      main_width: Bytes1.main_width(),
      preprocessed: Bytes1.preprocessed(),
      lookups: Bytes1.lookups(),
      lookup_group_size: 1,
      ..CircuitInputs::default()
    },
    CircuitInputs {
      main_width: Bytes2.main_width(),
      preprocessed: Bytes2.preprocessed(),
      lookups: Bytes2.lookups(),
      lookup_group_size: 2,
      ..CircuitInputs::default()
    },
  ]);
  inputs.extend(function_inputs());
  let cp = CommitmentParameters { log_blowup: 1, cap_height: 0 };
  let fp = FriParameters {
    log_final_poly_len: 0,
    max_log_arity: 1,
    num_queries: 64,
    commit_proof_of_work_bits: 0,
    query_proof_of_work_bits: 0,
  };
  System::new(AiurConfig::new(cp, fp), inputs).0
}

fn write_nat(out: &mut Vec<u8>, value: usize) {
  out.extend_from_slice(&(value as u64).to_le_bytes());
}

fn write_values(out: &mut Vec<u8>, values: &[Val]) {
  write_nat(out, values.len());
  for value in values {
    out.extend_from_slice(&value.as_canonical_u64().to_le_bytes());
  }
}

fn assignment(width: usize, matrix: usize, pattern: usize) -> Vec<Val> {
  let choices = [
    Val::ZERO,
    Val::ONE,
    -Val::ONE,
    Val::from_u64(255),
    Val::from_u64(256),
    Val::from_u64(1 << 32),
    Val::from_u64((1 << 48) - 1),
    Val::from_u64(17),
  ];
  (0..width)
    .map(|index| match pattern {
      0 => Val::ZERO,
      1 => Val::ONE,
      2 => -Val::ONE,
      _ => choices[(5 * index + 3 * pattern + matrix) % choices.len()],
    })
    .collect()
}

#[test]
fn expression_graph_snapshot() -> io::Result<()> {
  let system = graph_system();
  let mut out = b"Aiur expression graphs v1\n".to_vec();
  write_nat(&mut out, system.circuits.len());
  let mut checked = 0;
  let mut nodes_evaluated = 0;
  let mut shortened_prefixes = 0;
  for circuit in &system.circuits {
    let mut encoded = Vec::new();
    encode_circuit(&mut encoded, circuit);
    // Exercise the production decoder's new checks on every actual graph.
    let mut segment = Seg { buf: &encoded, pos: 0 };
    let decoded = decode_circuit(&mut segment).expect("actual graph decodes");
    segment.done("circuit").unwrap();
    assert_eq!(decoded.graph.nodes, circuit.graph.nodes);
    assert_eq!(decoded.graph.degrees, circuit.graph.degrees);
    assert_eq!(decoded.graph.zeros, circuit.graph.zeros);
    assert_eq!(decoded.graph.lookups, circuit.graph.lookups);
    assert_eq!(
      decoded.graph.max_constraint_degree,
      circuit.graph.max_constraint_degree
    );
    assert!(decoded.graph.lookup_prefix_len <= circuit.graph.lookup_prefix_len);
    if decoded.graph.lookup_prefix_len < circuit.graph.lookup_prefix_len {
      shortened_prefixes += 1;
    }
    let mut reencoded = Vec::new();
    encode_circuit(&mut reencoded, &decoded);
    assert_eq!(reencoded, encoded);
    write_nat(&mut out, encoded.len());
    out.extend_from_slice(&encoded);
    write_nat(&mut out, 24);
    for pattern in 0..24 {
      let widths = [
        circuit.preprocessed_width,
        circuit.preprocessed_width,
        circuit.main_width,
        circuit.main_width,
        circuit.stage_2_width,
        circuit.stage_2_width,
      ];
      let rows: Vec<_> = widths
        .into_iter()
        .enumerate()
        .map(|(matrix, width)| assignment(width, matrix, pattern))
        .collect();
      let publics = assignment(circuit.num_publics, 6, pattern);
      for row in &rows {
        write_values(&mut out, row);
      }
      write_values(&mut out, &publics);
      let selectors = [
        Val::from_bool(pattern % 4 == 0),
        Val::from_bool(pattern % 4 == 1),
        Val::from_bool(pattern % 4 != 1),
      ];
      for value in selectors {
        out.extend_from_slice(&value.as_canonical_u64().to_le_bytes());
      }
      let values = VarValues {
        preprocessed: [&rows[0], &rows[1]],
        main: [&rows[2], &rows[3]],
        stage2: [&rows[4], &rows[5]],
        publics: &publics,
        is_first_row: selectors[0],
        is_last_row: selectors[1],
        is_transition: selectors[2],
      };
      let mut full = Vec::new();
      circuit.graph.sweep(&values, &mut full);
      let mut prefix = Vec::new();
      let mut compiled_prefix = Vec::new();
      circuit.graph.sweep_lookup_prefix(
        &VarValues { stage2: [&[], &[]], ..values },
        &mut compiled_prefix,
      );
      decoded.graph.sweep_lookup_prefix(
        &VarValues { stage2: [&[], &[]], ..values },
        &mut prefix,
      );
      assert_eq!(prefix, compiled_prefix[..prefix.len()]);
      assert_eq!(prefix, full[..prefix.len()]);
      write_values(&mut out, &full);
      write_values(&mut out, &prefix);
      write_values(&mut out, &circuit.graph.constraint_values(&full));
      let lookups = circuit.graph.lookup_values(&prefix);
      write_nat(&mut out, lookups.len());
      for lookup in lookups {
        out.extend_from_slice(
          &lookup.multiplicity.as_canonical_u64().to_le_bytes(),
        );
        write_values(&mut out, &lookup.args);
      }
      nodes_evaluated += full.len();
      checked += 1;
    }
  }
  assert_eq!(checked, 240);
  assert!(shortened_prefixes > 0, "include folded, unused lookup nodes");
  if let Some(path) = std::env::var_os("IX_EXPRESSION_GRAPH_SNAPSHOT") {
    File::create(path)?.write_all(&out)?;
  }
  eprintln!(
    "expression graphs: {checked} native assignments, {nodes_evaluated} node values"
  );
  Ok(())
}
