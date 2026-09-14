// Copyright (c) 2026 Argument Computer Corporation.
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Export complete native base graphs and rejected source specifications.

use super::*;
use multi_stark::{
  eval::{VarValues, eval_expr},
  expr::Expr,
  p3_matrix::dense::RowMajorMatrix,
  system::CircuitInputs,
};
use std::{fs, io, panic::catch_unwind};

#[derive(Clone)]
struct Spec {
  constraints: Vec<Expr<Val>>,
  lookups: Vec<Lookup<Expr<Val>>>,
}

impl Spec {
  fn inputs(&self) -> CircuitInputs<Val> {
    CircuitInputs {
      main_width: 4,
      preprocessed: Some(RowMajorMatrix::new(vec![Val::ZERO; 8], 4)),
      constraints: self.constraints.clone(),
      lookups: self.lookups.clone(),
      ..CircuitInputs::default()
    }
  }

  fn widths(&self) -> [usize; 4] {
    [4, 4, self.lookups.len().max(1) * 2, 8]
  }
}

fn binary(kind: usize, a: &Expr<Val>, b: &Expr<Val>) -> Expr<Val> {
  let a = Box::new(a.clone());
  let b = Box::new(b.clone());
  match kind {
    0 => Expr::Add(a, b),
    1 => Expr::Sub(a, b),
    _ => Expr::Mul(a, b),
  }
}

fn fixtures() -> Vec<Expr<Val>> {
  let x = Expr::main(0);
  let y = Expr::main(1);
  let zero = Expr::Const(Val::ZERO);
  let one = Expr::Const(Val::ONE);
  let mut result = vec![
    zero.clone(),
    one.clone(),
    Expr::Const(-Val::ONE),
    Expr::Const(Val::from_u64(17)),
  ];
  for source in [Source::Preprocessed, Source::Main] {
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
    Expr::Neg(Box::new(x.clone())),
    binary(0, &x, &y),
    binary(1, &zero, &x),
    binary(2, &zero, &y),
    Expr::Neg(Box::new(zero)),
    Expr::Neg(Box::new(one.clone())),
    Expr::Neg(Box::new(Expr::Neg(Box::new(x)))),
    Expr::Neg(Box::new(Expr::Neg(Box::new(one.clone())))),
    binary(0, &one, &one),
  ]);
  assert_eq!(result.len(), 22);
  result
}

fn accepted_specs() -> Vec<Spec> {
  let fixtures = fixtures();
  let zero = Expr::Const(Val::ZERO);
  let one = Expr::Const(Val::ONE);
  let anchor = Expr::main(3);
  let mut specs = vec![
    Spec { constraints: vec![], lookups: vec![] },
    Spec {
      constraints: vec![zero.clone()],
      lookups: vec![Lookup {
        multiplicity: one.clone(),
        args: fixtures.clone(),
      }],
    },
  ];
  for left in &fixtures {
    for right in &fixtures {
      for kind in 0..3 {
        let root = binary(kind, left, right);
        let reverse = binary(kind, right, left);
        let constraint = binary(1, &root, &anchor);
        specs.push(Spec {
          constraints: vec![
            constraint.clone(),
            constraint,
            binary(1, &reverse, &anchor),
            binary(1, &root, &root),
          ],
          lookups: vec![
            Lookup {
              multiplicity: left.clone(),
              args: vec![right.clone(), root.clone(), reverse, root],
            },
            // The final unused leaf extends the stored lookup prefix.
            Lookup {
              multiplicity: one.clone(),
              args: vec![binary(2, &zero, &anchor)],
            },
          ],
        });
      }
    }
    let negated = Expr::Neg(Box::new(left.clone()));
    specs.push(Spec {
      constraints: vec![binary(1, &negated, &anchor)],
      lookups: vec![Lookup {
        multiplicity: one.clone(),
        args: vec![left.clone(), negated],
      }],
    });
  }
  let x = Expr::main(0);
  let y = Expr::main(1);
  let mut ordered = vec![
    binary(0, &x, &y),
    binary(0, &y, &x),
    binary(2, &x, &y),
    binary(2, &y, &x),
    binary(1, &x, &y),
    binary(1, &y, &x),
    Expr::Neg(Box::new(x.clone())),
    Expr::Neg(Box::new(Expr::Neg(Box::new(x)))),
  ];
  for _ in 0..8 {
    specs.push(Spec { constraints: ordered.clone(), lookups: vec![] });
    ordered.rotate_left(1);
  }
  assert_eq!(specs.len(), 1484);
  specs
}

fn rejected_specs() -> Vec<(Spec, &'static str)> {
  let mut specs = Vec::new();
  let lookup_spec = |expr| Spec {
    constraints: vec![],
    lookups: vec![Lookup {
      multiplicity: Expr::Const(Val::ONE),
      args: vec![expr],
    }],
  };
  for source in [Source::Preprocessed, Source::Main, Source::Stage2] {
    let error = if source == Source::Stage2 {
      "Stage2InBaseContext"
    } else {
      "ColumnOutOfRange"
    };
    for offset in [RowOffset::Current, RowOffset::Next] {
      for index in [4, 7, u32::MAX] {
        specs.push((
          lookup_spec(Expr::Var(ColRef { source, offset, index })),
          error,
        ));
      }
      let index = if source == Source::Stage2 { 0 } else { 4 };
      let invalid = Expr::Var(ColRef { source, offset, index });
      // Raw folds still visit and reject their invalid children.
      specs.push((
        lookup_spec(binary(2, &Expr::Const(Val::ZERO), &invalid)),
        error,
      ));
      specs.push((lookup_spec(binary(1, &invalid, &invalid)), error));
    }
  }
  for index in [8, 9, u32::MAX] {
    specs.push((lookup_spec(Expr::Public(index)), "PublicOutOfRange"));
  }
  for constant in [Val::ONE, -Val::ONE, Val::from_u64(17)] {
    specs.push((
      Spec { constraints: vec![Expr::Const(constant)], lookups: vec![] },
      "UnsatisfiableConstant",
    ));
  }
  specs.push((
    Spec {
      constraints: vec![binary(
        0,
        &Expr::Const(Val::ONE),
        &Expr::Const(Val::ONE),
      )],
      lookups: vec![],
    },
    "UnsatisfiableConstant",
  ));
  specs.push((
    Spec {
      constraints: vec![Expr::main(0), Expr::Const(Val::ONE)],
      lookups: vec![],
    },
    "UnsatisfiableConstant",
  ));
  assert_eq!(specs.len(), 38);
  specs
}

fn write_nat(out: &mut Vec<u8>, value: usize) {
  out.extend_from_slice(&(value as u64).to_le_bytes());
}

fn write_field(out: &mut Vec<u8>, value: Val) {
  out.extend_from_slice(&value.as_canonical_u64().to_le_bytes());
}

fn write_values(out: &mut Vec<u8>, values: &[Val]) {
  write_nat(out, values.len());
  for &value in values {
    write_field(out, value);
  }
}

fn write_column(out: &mut Vec<u8>, column: ColRef) {
  out.push(match column.source {
    Source::Preprocessed => 0,
    Source::Main => 1,
    Source::Stage2 => 2,
  });
  out.push(match column.offset {
    RowOffset::Current => 0,
    RowOffset::Next => 1,
  });
  write_nat(out, column.index as usize);
}

fn write_expr(out: &mut Vec<u8>, expr: &Expr<Val>) {
  match expr {
    Expr::Const(value) => {
      out.push(0);
      write_field(out, *value);
    },
    Expr::Var(column) => {
      out.push(1);
      write_column(out, *column);
    },
    Expr::Public(index) => {
      out.push(2);
      write_nat(out, *index as usize);
    },
    Expr::IsFirstRow => out.push(3),
    Expr::IsLastRow => out.push(4),
    Expr::IsTransition => out.push(5),
    Expr::Add(a, b) | Expr::Sub(a, b) | Expr::Mul(a, b) => {
      out.push(match expr {
        Expr::Add(..) => 6,
        Expr::Sub(..) => 7,
        _ => 8,
      });
      write_expr(out, a);
      write_expr(out, b);
    },
    Expr::Neg(child) => {
      out.push(9);
      write_expr(out, child);
    },
  }
}

fn write_spec(out: &mut Vec<u8>, spec: &Spec) {
  for width in spec.widths() {
    write_nat(out, width);
  }
  write_nat(out, spec.lookups.len());
  for lookup in &spec.lookups {
    write_expr(out, &lookup.multiplicity);
    write_nat(out, lookup.args.len());
    for arg in &lookup.args {
      write_expr(out, arg);
    }
  }
  write_nat(out, spec.constraints.len());
  for expr in &spec.constraints {
    write_expr(out, expr);
  }
}

fn write_graph(out: &mut Vec<u8>, graph: &ConstraintGraph<Val>) {
  write_nat(out, graph.nodes.len());
  for node in &graph.nodes {
    match *node {
      Node::Const(value) => {
        out.push(0);
        write_field(out, value);
      },
      Node::Var(column) => {
        out.push(1);
        write_column(out, column);
      },
      Node::Public(index) => {
        out.push(2);
        write_nat(out, index as usize);
      },
      Node::IsFirstRow => out.push(3),
      Node::IsLastRow => out.push(4),
      Node::IsTransition => out.push(5),
      Node::Add(a, b) | Node::Sub(a, b) | Node::Mul(a, b) => {
        out.push(match node {
          Node::Add(..) => 6,
          Node::Sub(..) => 7,
          _ => 8,
        });
        write_nat(out, a.index());
        write_nat(out, b.index());
      },
      Node::Neg(child) => {
        out.push(9);
        write_nat(out, child.index());
      },
    }
  }
  for &degree in &graph.degrees {
    write_nat(out, degree as usize);
  }
  write_nat(out, graph.zeros.len());
  for root in &graph.zeros {
    write_nat(out, root.index());
  }
  write_nat(out, graph.lookups.len());
  for lookup in &graph.lookups {
    write_nat(out, lookup.multiplicity.index());
    write_nat(out, lookup.args.len());
    for arg in &lookup.args {
      write_nat(out, arg.index());
    }
  }
  write_nat(out, graph.lookup_prefix_len);
  write_nat(out, graph.max_constraint_degree as usize);
}

fn config() -> AiurConfig {
  AiurConfig::new(
    CommitmentParameters { log_blowup: 3, cap_height: 0 },
    FriParameters {
      log_final_poly_len: 0,
      max_log_arity: 1,
      num_queries: 64,
      commit_proof_of_work_bits: 0,
      query_proof_of_work_bits: 0,
    },
  )
}

fn assignment(width: usize, slot: usize, seed: usize) -> Vec<Val> {
  let choices = [
    Val::ZERO,
    Val::ONE,
    -Val::ONE,
    Val::from_u64(17),
    Val::from_u64(255),
    Val::from_u64(256),
    Val::from_u64(65536),
    Val::TWO,
  ];
  (0..width)
    .map(|index| {
      if seed < 3 {
        choices[seed]
      } else {
        choices[(3 * slot + 5 * seed + 7 * index) % choices.len()]
      }
    })
    .collect()
}

#[test]
fn graph_compilation_snapshot() -> io::Result<()> {
  let specs = accepted_specs();
  let (system, _) = System::new(config(), specs.iter().map(Spec::inputs));
  let mut out = b"Aiur graph compilation v1\n".to_vec();
  write_nat(&mut out, specs.len());
  let mut assignments = 0;
  let mut node_values = 0;
  for (spec, circuit) in specs.iter().zip(&system.circuits) {
    assert_eq!(
      spec.widths(),
      [
        circuit.preprocessed_width,
        circuit.main_width,
        circuit.stage_2_width,
        circuit.num_publics
      ]
    );
    write_spec(&mut out, spec);
    write_graph(&mut out, &circuit.graph);
    for seed in 0..8 {
      let [pre, main, stage, publics] = spec.widths();
      let rows: Vec<_> = [pre, pre, main, main, stage, stage, publics, 3]
        .into_iter()
        .enumerate()
        .map(|(slot, width)| assignment(width, slot, seed))
        .collect();
      for row in &rows {
        write_values(&mut out, row);
      }
      let values = VarValues {
        preprocessed: [&rows[0], &rows[1]],
        main: [&rows[2], &rows[3]],
        stage2: [&rows[4], &rows[5]],
        publics: &rows[6],
        is_first_row: rows[7][0],
        is_last_row: rows[7][1],
        is_transition: rows[7][2],
      };
      let mut buffer = Vec::new();
      circuit.graph.sweep(&values, &mut buffer);
      write_values(&mut out, &buffer);
      let mut prefix = Vec::new();
      circuit.graph.sweep_lookup_prefix(
        &VarValues { stage2: [&[], &[]], ..values },
        &mut prefix,
      );
      assert_eq!(prefix, buffer[..circuit.graph.lookup_prefix_len]);
      write_values(&mut out, &prefix);
      let original: Vec<_> =
        spec.constraints.iter().map(|expr| eval_expr(expr, &values)).collect();
      write_values(&mut out, &original);
      assert_eq!(
        original.iter().all(|v| *v == Val::ZERO),
        circuit
          .graph
          .constraint_values(&buffer)
          .iter()
          .all(|v| *v == Val::ZERO)
      );
      let lookups: Vec<_> = spec
        .lookups
        .iter()
        .map(|lookup| Lookup {
          multiplicity: eval_expr(&lookup.multiplicity, &values),
          args: lookup
            .args
            .iter()
            .map(|expr| eval_expr(expr, &values))
            .collect(),
        })
        .collect();
      assert_eq!(lookups, circuit.graph.lookup_values(&prefix));
      for lookup in lookups {
        write_field(&mut out, lookup.multiplicity);
        write_values(&mut out, &lookup.args);
      }
      assignments += 1;
      node_values += buffer.len();
    }
  }
  let rejected = rejected_specs();
  write_nat(&mut out, rejected.len());
  for (spec, expected_error) in &rejected {
    let failed = catch_unwind(|| System::new(config(), [spec.inputs()]));
    let Err(error) = failed else {
      panic!("invalid graph unexpectedly compiled")
    };
    let message = error
      .downcast_ref::<String>()
      .map(String::as_str)
      .or_else(|| error.downcast_ref::<&str>().copied())
      .expect("string compilation error");
    assert!(message.contains("constraint compilation failed:"), "{message}");
    assert!(message.contains(expected_error), "{message}");
    write_spec(&mut out, spec);
  }
  if let Some(path) = std::env::var_os("IX_GRAPH_COMPILATION_SNAPSHOT") {
    fs::write(path, out)?;
  }
  eprintln!(
    "graph compilation: {} complete graphs, {} rejected specifications, {assignments} assignments, {node_values} node values",
    specs.len(),
    rejected.len()
  );
  Ok(())
}
