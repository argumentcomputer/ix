use super::*;
use aiur::trace::{FunctionCircuit, Polynomial};
use multi_stark::{
  expr::Expr,
  graph::ConstraintGraph,
  lookup::{Lookup, MAX_LOOKUP_GROUP, stage2_width},
  traits::Algebra,
};
use p3_matrix::dense::RowMajorMatrix;

const CALL: u64 = 1;
const ROM: u64 = 2;

pub(super) struct FixedTable {
  pub(super) maps: Vec<usize>,
  pub(super) height: usize,
}

pub(super) struct Lowered<C: KzgCurve = crate::kzg::Bn254> {
  pub(super) inputs: Vec<CircuitInputs<CurveScalar<C>>>,
  pub(super) names: Vec<String>,
  pub(super) placements: Vec<Placement<FieldWord>>,
  pub(super) function_circuits: usize,
  pub(super) tables: Vec<FixedTable>,
  pub(super) memory_widths: Vec<usize>,
}

fn constant<F: AiurField>(value: u64) -> Expr<CurveScalar<F::Curve>> {
  Expr::constant(F::default().from_u64(value))
}

fn main_var<C: KzgCurve>(column: usize) -> Expr<CurveScalar<C>> {
  Expr::main(u32::try_from(column).expect("validated compiler column"))
}

fn quotient_degree<C: KzgCurve>(
  graph: &ConstraintGraph<CurveScalar<C>>,
  group_size: usize,
) -> Result<usize, String> {
  let degree = graph
    .max_constraint_degree
    .max(logup_max_degree(graph, group_size)) as usize;
  (degree.max(2) - 1)
    .checked_next_power_of_two()
    .ok_or_else(|| "quotient degree overflow".into())
}

/// Opt-in quotient-degree budget for lookup grouping. When set to a power of
/// two `B`, each circuit's group size minimizes its committed column count
/// (stage-2 columns plus quotient chunks) with quotient degree at most
/// `max(B, degree at group size 1)`. Unset keeps every circuit's quotient
/// degree at its group-size-1 value. Grouping is part of the verifying key, so
/// prover and verifier must build their systems under the same setting.
/// Callers that do not pass a budget explicitly read this variable.
const LOOKUP_QUOTIENT_BUDGET_ENV: &str = "IX_AIUR_KZG_LOOKUP_QUOTIENT_BUDGET";

pub(super) fn lookup_quotient_budget_from_env() -> Result<Option<usize>, String>
{
  let Ok(value) = std::env::var(LOOKUP_QUOTIENT_BUDGET_ENV) else {
    return Ok(None);
  };
  match value.parse::<usize>() {
    Ok(budget) if budget.is_power_of_two() => Ok(Some(budget)),
    _ => Err(format!(
      "{LOOKUP_QUOTIENT_BUDGET_ENV} must be a power of two, got {value:?}"
    )),
  }
}

pub(super) fn lookup_group_size<C: KzgCurve>(
  graph: &ConstraintGraph<CurveScalar<C>>,
  budget: Option<usize>,
) -> Result<usize, String> {
  let lookups = graph.lookups.len();
  let base = quotient_degree(graph, 1)?;
  let Some(budget) = budget else {
    let mut best = (stage2_width(lookups, 1, 1), 1);
    // Chunk boundaries can make a larger group cheaper in degree than a
    // smaller one. Every supported size is checked against the circuit's own
    // group-size-1 degree.
    for size in 2..=MAX_LOOKUP_GROUP {
      if quotient_degree(graph, size)? == base {
        best = best.min((stage2_width(lookups, size, 1), size));
      }
    }
    return Ok(best.1);
  };
  let budget = budget.max(base);
  let mut best = (stage2_width(lookups, 1, 1) + base, base, 1);
  for size in 2..=MAX_LOOKUP_GROUP {
    let quotient = quotient_degree(graph, size)?;
    if quotient <= budget {
      best =
        best.min((stage2_width(lookups, size, 1) + quotient, quotient, size));
    }
  }
  Ok(best.2)
}

fn lower<F: AiurField>(
  polynomial: &Polynomial<FieldWord>,
) -> Expr<CurveScalar<F::Curve>> {
  match polynomial {
    Polynomial::Const(value) => Expr::constant(F::default().from_word(*value)),
    Polynomial::Var(column) => main_var(*column),
    Polynomial::Add(terms) => lower::<F>(&terms[0]) + lower::<F>(&terms[1]),
    Polynomial::Sub(terms) => lower::<F>(&terms[0]) - lower::<F>(&terms[1]),
    Polynomial::Mul(terms) => lower::<F>(&terms[0]) * lower::<F>(&terms[1]),
  }
}

pub(super) fn evaluate<F: AiurField>(
  polynomial: &Polynomial<FieldWord>,
  row: &[CurveScalar<F::Curve>],
) -> CurveScalar<F::Curve> {
  match polynomial {
    Polynomial::Const(value) => F::default().from_word(*value),
    Polynomial::Var(column) => row[*column],
    Polynomial::Add(terms) => {
      evaluate::<F>(&terms[0], row) + evaluate::<F>(&terms[1], row)
    },
    Polynomial::Sub(terms) => {
      evaluate::<F>(&terms[0], row) - evaluate::<F>(&terms[1], row)
    },
    Polynomial::Mul(terms) => {
      evaluate::<F>(&terms[0], row) * evaluate::<F>(&terms[1], row)
    },
  }
}

pub(super) fn build<F: AiurField>(
  plan: &TracePlan<'_, F>,
) -> Result<Lowered<F::Curve>, String> {
  build_with(plan, lookup_quotient_budget_from_env()?)
}

pub(super) fn build_with<F: AiurField>(
  plan: &TracePlan<'_, F>,
  budget: Option<usize>,
) -> Result<Lowered<F::Curve>, String> {
  if budget.is_some_and(|budget| !budget.is_power_of_two()) {
    return Err("lookup quotient budget must be a power of two".into());
  }
  let layout = plan.layout()?;
  let artifact = plan.artifact();
  let callable = |name: &str| {
    plan
      .callable_id(name)
      .and_then(|id| u64::try_from(id).ok())
      .ok_or_else(|| format!("unknown callable {name}"))
  };
  let mut inputs = vec![];
  let mut names = vec![];
  let mut memory_widths: Vec<_> = artifact
    .chips
    .iter()
    .flat_map(|chip| chip.memory.iter().map(|cell| cell.values.len()))
    .collect();
  memory_widths.sort_unstable();
  memory_widths.dedup();

  for circuit in &layout.circuits {
    match *circuit {
      FunctionCircuit::Group(index) => {
        let group = &artifact.groups[index];
        for polynomial in group
          .constraints
          .iter()
          .chain(&group.receive)
          .chain(std::iter::once(&group.activation))
          .chain(
            group
              .sends
              .iter()
              .flat_map(|send| std::iter::once(&send.enable).chain(&send.args)),
          )
        {
          polynomial.validate(group.width, F::default())?;
        }
        let mut constraints: Vec<_> =
          group.constraints.iter().map(lower::<F>).collect();
        constraints.push(
          (constant::<F>(1) - lower::<F>(&group.activation))
            * main_var(group.width),
        );
        let mut lookups = vec![Lookup::pull(
          main_var(group.width),
          group.receive.iter().map(lower::<F>).collect(),
        )];
        lookups.extend(group.sends.iter().map(|send| {
          Lookup::push(
            lower::<F>(&send.enable),
            send.args.iter().map(lower::<F>).collect(),
          )
        }));
        inputs.push(CircuitInputs {
          main_width: group.width + 1,
          constraints,
          lookups,
          ..Default::default()
        });
        names.push(group.name.clone());
      },
      FunctionCircuit::Chip(index) => {
        let chip = &artifact.chips[index];
        let mut args =
          vec![constant::<F>(CALL), constant::<F>(callable(&chip.name)?)];
        args.extend(chip.inputs.iter().map(|&column| main_var(column)));
        args.extend(chip.output.iter().map(lower::<F>));
        let mut lookups = vec![Lookup::pull(main_var(chip.width), args)];
        for send in &chip.sends {
          let mut args =
            vec![constant::<F>(CALL), constant::<F>(callable(&send.channel)?)];
          args.extend(send.args.iter().map(lower::<F>));
          args.extend(send.result.iter().map(|&column| main_var(column)));
          lookups.push(Lookup::push(lower::<F>(&send.enable), args));
        }
        for cell in &chip.memory {
          let payload = u64::try_from(cell.values.len())
            .map_err(|_error| "ROM width overflow")?;
          let mut args = vec![
            constant::<F>(ROM),
            constant::<F>(payload),
            lower::<F>(&cell.address),
          ];
          args.extend(cell.values.iter().map(lower::<F>));
          lookups.push(Lookup::push(lower::<F>(&cell.enable), args));
        }
        let inactive_zero =
          (constant::<F>(1) - main_var(chip.activation)) * main_var(chip.width);
        inputs.push(CircuitInputs {
          main_width: chip.width + 1,
          constraints: chip
            .constraints
            .iter()
            .map(lower::<F>)
            .chain([inactive_zero])
            .collect(),
          lookups,
          ..Default::default()
        });
        names.push(chip.name.clone());
      },
    }
  }
  let function_circuits = inputs.len();
  let tables = fixed_tables(plan, &mut inputs, &mut names)?;
  for &payload in &memory_widths {
    let width = payload
      .checked_add(3)
      .filter(|&width| u32::try_from(width).is_ok())
      .ok_or("ROM width overflow")?;
    let count = main_var(0);
    let active = main_var(1);
    let address = main_var(2);
    let mut args = vec![
      constant::<F>(ROM),
      constant::<F>(
        u64::try_from(payload).map_err(|_error| "ROM width overflow")?,
      ),
      address.clone(),
    ];
    args.extend((3..width).map(main_var));
    let transition = Expr::IsTransition * Expr::main_next(1);
    inputs.push(CircuitInputs {
      main_width: width,
      constraints: vec![
        active.clone() * (active.clone() - constant::<F>(1)),
        count.clone() * (constant::<F>(1) - active.clone()),
        transition.clone() * (active - constant::<F>(1)),
        transition * (Expr::main_next(2) - address.clone() - constant::<F>(1)),
        Expr::IsFirstRow * address,
      ],
      lookups: vec![Lookup::pull(count, args)],
      ..Default::default()
    });
    names.push(format!("<ROM:{payload}>"));
  }
  let params = extension_params::<KzgConfig<F::Curve>>();
  for (input, name) in inputs.iter_mut().zip(&names) {
    let graph = input.compile_graph(&params).map_err(|error| {
      format!("{name}: invalid compiler circuit: {error:?}")
    })?;
    input.lookup_group_size = lookup_group_size(&graph, budget)?;
  }
  Ok(Lowered {
    inputs,
    names,
    placements: layout.placements,
    function_circuits,
    tables,
    memory_widths,
  })
}

fn fixed_tables<F: AiurField>(
  plan: &TracePlan<'_, F>,
  inputs: &mut Vec<CircuitInputs<CurveScalar<F::Curve>>>,
  names: &mut Vec<String>,
) -> Result<Vec<FixedTable>, String> {
  let checked = plan.program();
  let program = checked.program();
  let mut groups: Vec<(usize, Vec<usize>)> = vec![];
  for (map, definition) in program.maps.iter().enumerate() {
    let height = program.tables[definition.input].rows.len();
    if let Some((_, maps)) = groups.iter_mut().find(|(rows, _)| *rows == height)
    {
      maps.push(map);
    } else {
      groups.push((height, vec![map]));
    }
  }
  let mut tables = vec![];
  for (real_height, maps) in groups {
    let height = if real_height == 0 {
      0
    } else {
      real_height
        .checked_next_power_of_two()
        .ok_or("fixed table height overflow")?
    };
    // The leading fixed column authenticates even unit-to-unit tables.
    let mut width = 1usize;
    let mut columns: Vec<(usize, usize, usize)> = vec![];
    let mut constraints = vec![];
    let mut lookups = vec![];
    for (column, &map) in maps.iter().enumerate() {
      let definition = &program.maps[map];
      let callable =
        program.functions.len().checked_add(map).ok_or("callable overflow")?;
      let input_width =
        checked.input_width(callable).ok_or("unknown map input layout")?;
      let output_width =
        checked.output_width(callable).ok_or("unknown map output layout")?;
      let mut offsets = [0; 2];
      for ((table, size), offset) in
        [(definition.input, input_width), (definition.output, output_width)]
          .into_iter()
          .zip(&mut offsets)
      {
        *offset = if let Some((_, start, _)) =
          columns.iter().find(|(id, _, _)| *id == table)
        {
          *start
        } else {
          let start = width;
          width = width
            .checked_add(size)
            .filter(|&width| u32::try_from(width).is_ok())
            .ok_or("fixed table width overflow")?;
          columns.push((table, start, size));
          start
        };
      }
      let mut args = vec![
        constant::<F>(CALL),
        constant::<F>(
          u64::try_from(callable).map_err(|_error| "callable overflow")?,
        ),
      ];
      if height == 0 {
        args.resize(2 + input_width + output_width, constant::<F>(0));
        constraints.push(main_var(column));
      } else {
        for (start, len) in
          [(offsets[0], input_width), (offsets[1], output_width)]
        {
          args.extend((start..start + len).map(|column| {
            Expr::preprocessed(
              u32::try_from(column).expect("checked fixed width"),
            )
          }));
        }
      }
      lookups.push(Lookup::pull(main_var(column), args));
    }
    let preprocessed = if height == 0 {
      None
    } else {
      let mut values = Vec::with_capacity(
        height.checked_mul(width).ok_or("fixed table size overflow")?,
      );
      for row in 0..height {
        // Padding repeats a valid table member but has zero honest multiplicity.
        let row = if row < real_height { row } else { 0 };
        values.push(CurveScalar::<F::Curve>::ONE);
        for &(table, _, _) in &columns {
          values.extend(
            program.tables[table].rows[row]
              .iter()
              .map(|&word| F::default().from_word(word)),
          );
        }
      }
      Some(RowMajorMatrix::new(values, width))
    };
    inputs.push(CircuitInputs {
      main_width: maps.len(),
      preprocessed,
      constraints,
      lookups,
      ..Default::default()
    });
    names.push(format!(
      "<table:{}>",
      program.tables[program.maps[maps[0]].input].name
    ));
    tables.push(FixedTable { maps, height });
  }
  Ok(tables)
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::kzg::Scalar;

  fn graph(degrees: &[usize]) -> ConstraintGraph<Scalar> {
    let input = CircuitInputs {
      main_width: 1,
      lookups: degrees
        .iter()
        .map(|&degree| {
          let argument = (0..degree)
            .fold(constant::<Bn254>(1), |value, _| value * main_var(0));
          Lookup::pull(constant::<Bn254>(1), vec![argument])
        })
        .collect(),
      ..Default::default()
    };
    input.compile_graph(&extension_params::<KzgConfig>()).unwrap()
  }

  #[test]
  fn lookup_selection_preserves_actual_degree_and_finds_nonmonotonic_choice() {
    let graph = graph(&[0, 0, 0, 0, 2, 2, 0, 0, 0, 0]);
    assert_eq!(quotient_degree(&graph, 1).unwrap(), 2);
    for size in 2..=4 {
      assert_eq!(quotient_degree(&graph, size).unwrap(), 4);
    }
    assert_eq!(quotient_degree(&graph, 5).unwrap(), 2);
    assert_eq!(lookup_group_size(&graph, None).unwrap(), 5);
  }

  #[test]
  fn linear_lookup_circuit_cannot_spend_a_larger_global_budget() {
    let graph = graph(&[1; 6]);
    assert_eq!(quotient_degree(&graph, 1).unwrap(), 1);
    assert_eq!(quotient_degree(&graph, 2).unwrap(), 2);
    assert_eq!(lookup_group_size(&graph, None).unwrap(), 1);
  }

  #[test]
  fn equal_width_choices_use_the_smallest_group() {
    let graph = graph(&[0; 6]);
    assert_eq!(lookup_group_size(&graph, None).unwrap(), 6);
    assert_eq!(lookup_group_size(&self::graph(&[]), None).unwrap(), 1);
  }

  #[test]
  fn quotient_budget_trades_lookup_columns_for_quotient_chunks() {
    let graph = graph(&[1; 6]);
    assert_eq!(lookup_group_size(&graph, Some(1)).unwrap(), 1);
    assert_eq!(lookup_group_size(&graph, Some(2)).unwrap(), 2);
    assert_eq!(lookup_group_size(&graph, Some(4)).unwrap(), 2);
    let graph = self::graph(&[0; 6]);
    assert_eq!(lookup_group_size(&graph, Some(2)).unwrap(), 6);
  }

  fn eval_constraint_graph<F>(
    graph: &ConstraintGraph<F>,
    cur_main: &[F],
    next_main: &[F],
    prep: &[F],
    is_first: bool,
    is_last: bool,
    is_transition: bool,
  ) -> (Vec<F>, Vec<(F, Vec<F>)>)
  where
    F: multi_stark::traits::Field,
  {
    use multi_stark::{
      expr::{RowOffset, Source},
      graph::Node,
    };
    let mut vals: Vec<F> = Vec::with_capacity(graph.nodes.len());
    for node in &graph.nodes {
      let v = match node {
        Node::Const(c) => *c,
        Node::Var(col) => {
          let idx = usize::try_from(col.index).unwrap();
          match (col.source, col.offset) {
            (Source::Main, RowOffset::Current) => cur_main[idx],
            (Source::Main, RowOffset::Next) => next_main[idx],
            (Source::Preprocessed, RowOffset::Current) => prep[idx],
            other => panic!("unexpected column reference {other:?}"),
          }
        },
        Node::Public(_) => panic!("unexpected public value in Aiur circuit"),
        Node::IsFirstRow => {
          if is_first {
            F::ONE
          } else {
            F::ZERO
          }
        },
        Node::IsLastRow => {
          if is_last {
            F::ONE
          } else {
            F::ZERO
          }
        },
        Node::IsTransition => {
          if is_transition {
            F::ONE
          } else {
            F::ZERO
          }
        },
        Node::Add(a, b) => vals[a.index()] + vals[b.index()],
        Node::Sub(a, b) => vals[a.index()] - vals[b.index()],
        Node::Mul(a, b) => vals[a.index()] * vals[b.index()],
        Node::Neg(a) => -vals[a.index()],
      };
      vals.push(v);
    }
    let zeros = graph.zeros.iter().map(|id| vals[id.index()]).collect();
    let lookups = graph
      .lookups
      .iter()
      .map(|l| {
        let mult = vals[l.multiplicity.index()];
        let args = l.args.iter().map(|id| vals[id.index()]).collect();
        (mult, args)
      })
      .collect();
    (zeros, lookups)
  }

  fn gl_to_small_i128(v: multi_stark::types::Val) -> i128 {
    use multi_stark::p3_field::PrimeField64;
    let u = v.as_canonical_u64();
    let p = multi_stark::types::Val::ORDER_U64;
    if u <= 1_000_000_000 {
      i128::from(u)
    } else {
      assert!(p - u <= 1_000_000_000, "unexpected large Goldilocks value {u}");
      -i128::from(p - u)
    }
  }

  fn bn_to_small_i128(v: Scalar) -> i128 {
    use aiur::field::FieldBackend;
    if let Ok(u) = Bn254.try_to_u64(v)
      && u <= 1_000_000_000
    {
      return i128::from(u);
    }
    if let Ok(u) = Bn254.try_to_u64(-v)
      && u <= 1_000_000_000
    {
      return -i128::from(u);
    }
    panic!("unexpected large BN254 scalar value {v:?}");
  }

  fn build_shared_differential_program_json(
    modulus: &serde_json::Value,
    word: impl Fn(u64) -> serde_json::Value,
  ) -> (serde_json::Value, serde_json::Value) {
    use serde_json::json;
    let field = json!({"kind": "field"});
    let tuple1 = json!({"kind": "tuple", "items": [field]});
    let pair = json!({"kind": "tuple", "items": [field, field]});
    let ptr_f = json!({"kind": "pointer", "target": field});
    let ptr_p = json!({"kind": "pointer", "target": pair});
    let program = json!({
      "version": 1,
      "modulus": modulus,
      "enums": [],
      "tables": [
        {"name": "in_bits", "type": tuple1, "rows": [[word(0)], [word(1)]]},
        {"name": "out_flip", "type": field, "rows": [[word(1)], [word(0)]]},
        {"name": "out_dbl", "type": field, "rows": [[word(0)], [word(2)]]},
        {"name": "empty_in", "type": tuple1, "rows": []},
        {"name": "empty_out", "type": field, "rows": []}
      ],
      "maps": [
        {"name": "flip", "params": [field], "result": field, "input": 0, "output": 1},
        {"name": "dbl", "params": [field], "result": field, "input": 0, "output": 2},
        {"name": "empty_map", "params": [field], "result": field, "input": 3, "output": 4}
      ],
      "functions": [
        {
          "name": "main",
          "params": [field],
          "result": field,
          "registers": 5,
          "code": [
            {"op": "store", "type": field, "value": [0], "dest": 1},
            {"op": "store", "type": pair, "value": [0, 0], "dest": 2},
            {"op": "load", "type": field, "pointer": 1, "dest": [3]},
            {"op": "call", "function": 1, "args": [3], "dest": [4]},
            {"op": "ret", "value": [4]}
          ]
        },
        {
          "name": "left",
          "params": [field],
          "result": field,
          "registers": 2,
          "code": [
            {"op": "call", "function": 3, "args": [0], "dest": [1]},
            {"op": "ret", "value": [1]}
          ]
        },
        {
          "name": "right",
          "params": [field],
          "result": field,
          "registers": 2,
          "code": [
            {"op": "call", "function": 4, "args": [0], "dest": [1]},
            {"op": "ret", "value": [1]}
          ]
        }
      ],
      "entries": [
        {"name": "main", "function": 0, "inputs": [field], "output": field}
      ]
    });
    let _ = (ptr_f, ptr_p);
    let trace = json!({
      "version": 3,
      "modulus": modulus,
      "functions": [
        {
          "name": "main", "chip": "main", "witnesses": 5,
          "inputs": [0], "output": [4], "steps": [],
          "writes": [{"column": 0, "source": 0, "guard": {"const": word(1)}}]
        },
        {
          "name": "left", "chip": "left", "witnesses": 2,
          "inputs": [0], "output": [1], "steps": [],
          "writes": [{"column": 0, "source": 0, "guard": {"const": word(1)}}]
        },
        {
          "name": "right", "chip": "right", "witnesses": 2,
          "inputs": [0], "output": [1], "steps": [],
          "writes": [{"column": 0, "source": 0, "guard": {"const": word(1)}}]
        }
      ],
      "chips": [
        {
          "name": "main",
          "width": 6,
          "activation": 5,
          "inputs": [0],
          "output": [{"add": [{"var": 1}, {"var": 2}]}],
          "constraints": [
            {"mul": [{"var": 5}, {"sub": [{"var": 5}, {"const": word(1)}]}]},
            {"sub": [{"var": 1}, {"mul": [{"var": 0}, {"var": 0}]}]},
            {"sub": [{"var": 2}, {"add": [{"var": 0}, {"var": 3}]}]}
          ],
          "sends": [
            {
              "channel": "left",
              "args": [{"var": 0}],
              "result": [1],
              "enable": {"var": 5}
            },
            {
              "channel": "right",
              "args": [{"add": [{"var": 0}, {"const": word(1)}]}],
              "result": [2],
              "enable": {"var": 5}
            }
          ],
          "memory": [
            {
              "type": field,
              "address": {"var": 3},
              "values": [{"var": 0}],
              "enable": {"var": 5}
            },
            {
              "type": pair,
              "address": {"var": 4},
              "values": [{"var": 0}, {"var": 1}],
              "enable": {"var": 5}
            }
          ]
        },
        {
          "name": "left",
          "width": 3,
          "activation": 2,
          "inputs": [0],
          "output": [{"var": 1}],
          "constraints": [
            {"mul": [{"var": 2}, {"sub": [{"var": 2}, {"const": word(1)}]}]}
          ],
          "sends": [
            {
              "channel": "flip",
              "args": [{"var": 0}],
              "result": [1],
              "enable": {"var": 2}
            }
          ],
          "memory": []
        },
        {
          "name": "right",
          "width": 3,
          "activation": 2,
          "inputs": [0],
          "output": [{"var": 1}],
          "constraints": [
            {"mul": [{"var": 2}, {"sub": [{"var": 2}, {"const": word(1)}]}]}
          ],
          "sends": [
            {
              "channel": "dbl",
              "args": [{"var": 0}],
              "result": [1],
              "enable": {"var": 2}
            }
          ],
          "memory": []
        }
      ],
      "groups": [
        {
          "name": "grp_left_right",
          "width": 4,
          "activation": {"add": [{"var": 2}, {"var": 3}]},
          "constraints": [
            {"mul": [{"var": 2}, {"sub": [{"var": 2}, {"const": word(1)}]}]},
            {"mul": [{"var": 3}, {"sub": [{"var": 3}, {"const": word(1)}]}]},
            {"mul": [{"var": 2}, {"var": 3}]}
          ],
          "receive": [
            {"add": [{"var": 2}, {"var": 3}]},
            {"add": [{"var": 2}, {"mul": [{"const": word(2)}, {"var": 3}]}]},
            {"var": 0},
            {"var": 1}
          ],
          "sends": [
            {
              "enable": {"add": [{"var": 2}, {"var": 3}]},
              "args": [
                {"add": [{"var": 2}, {"var": 3}]},
                {"add": [
                  {"mul": [{"const": word(3)}, {"var": 2}]},
                  {"mul": [{"const": word(4)}, {"var": 3}]}
                ]},
                {"var": 0},
                {"var": 1}
              ]
            }
          ],
          "members": [
            {"name": "left", "columns": [0, 1, 2], "selector": 2, "writes": []},
            {"name": "right", "columns": [0, 1, 3], "selector": 3, "writes": []}
          ]
        }
      ]
    });
    (program, trace)
  }

  fn assert_bn254_matches_goldilocks_lowering(
    gl_plan: &TracePlan<'_, aiur::field::PrimeField>,
    bn_plan: &TracePlan<'_, Bn254>,
  ) {
    use aiur::{
      field::FieldBackend,
      trace::stark::{Backend as GlBackend, Parameters, RomLayout},
    };
    use multi_stark::{p3_field::PrimeCharacteristicRing, types::Val};

    let gl_params = Parameters {
      num_queries: 2,
      commit_proof_of_work_bits: 0,
      query_proof_of_work_bits: 0,
      ..Parameters::default()
    };
    let gl_backend = GlBackend::new_below_floor_with_rom_layout(
      gl_plan,
      gl_params,
      RomLayout::Scalar,
    )
    .unwrap();
    let gl_stats = gl_backend.statistics();
    let gl_sys = gl_backend.system();

    let bn_lowered = build_with::<Bn254>(bn_plan, None).unwrap();
    let bn_ext = extension_params::<KzgConfig<crate::kzg::Bn254>>();

    assert_eq!(gl_sys.circuits.len(), bn_lowered.inputs.len());
    assert_eq!(gl_stats.len(), bn_lowered.names.len());

    for (idx, ((gl_circuit, bn_input), (gl_stat, name))) in gl_sys
      .circuits
      .iter()
      .zip(&bn_lowered.inputs)
      .zip(gl_stats.iter().zip(&bn_lowered.names))
      .enumerate()
    {
      assert_eq!(&gl_stat.name, name, "circuit name mismatch at {idx}");

      let bn_graph = bn_input.compile_graph(&bn_ext).unwrap();

      assert_eq!(
        gl_circuit.main_width, bn_input.main_width,
        "{name}: main_width mismatch"
      );
      let (bn_prep_width, bn_prep_height) = match &bn_input.preprocessed {
        Some(m) => (m.width, m.values.len() / m.width),
        None => (0, 0),
      };
      assert_eq!(
        gl_circuit.preprocessed_width, bn_prep_width,
        "{name}: preprocessed_width mismatch"
      );
      assert_eq!(
        gl_circuit.preprocessed_height, bn_prep_height,
        "{name}: preprocessed_height mismatch"
      );

      let gl_graph = &gl_circuit.graph;
      assert_eq!(
        gl_graph.zeros.len(),
        bn_graph.zeros.len(),
        "{name}: constraint count mismatch"
      );
      assert_eq!(
        gl_graph.max_constraint_degree, bn_graph.max_constraint_degree,
        "{name}: max_constraint_degree mismatch"
      );
      for (ci, (&gz, &bz)) in
        gl_graph.zeros.iter().zip(&bn_graph.zeros).enumerate()
      {
        assert_eq!(
          gl_graph.degrees[gz.index()],
          bn_graph.degrees[bz.index()],
          "{name}: constraint {ci} degree mismatch"
        );
      }

      assert_eq!(
        gl_graph.lookups.len(),
        bn_graph.lookups.len(),
        "{name}: lookup count mismatch"
      );
      for (li, (gl_l, bn_l)) in
        gl_graph.lookups.iter().zip(&bn_graph.lookups).enumerate()
      {
        assert_eq!(
          gl_l.args.len(),
          bn_l.args.len(),
          "{name}: lookup {li} arity mismatch"
        );
        assert_eq!(
          gl_graph.degrees[gl_l.multiplicity.index()],
          bn_graph.degrees[bn_l.multiplicity.index()],
          "{name}: lookup {li} multiplicity degree mismatch"
        );
        for (ai, (&ga, &ba)) in gl_l.args.iter().zip(&bn_l.args).enumerate() {
          assert_eq!(
            gl_graph.degrees[ga.index()],
            bn_graph.degrees[ba.index()],
            "{name}: lookup {li} arg {ai} degree mismatch"
          );
        }
      }

      // Behavioral differential evaluation on shared small-integer rows:
      // all-zero padding row, active/nonzero rows, and transition/first-row flags.
      let mw = gl_circuit.main_width;
      let pw = gl_circuit.preprocessed_width;
      let test_rows: Vec<(Vec<u64>, Vec<u64>, Vec<u64>, bool, bool, bool)> = vec![
        (vec![0; mw], vec![0; mw], vec![0; pw], true, false, true),
        (
          (0..mw).map(|j| u64::try_from((j + 1) % 5).unwrap()).collect(),
          (0..mw).map(|j| u64::try_from((j + 2) % 5).unwrap()).collect(),
          (0..pw).map(|j| u64::try_from((j + 3) % 5).unwrap()).collect(),
          true,
          false,
          true,
        ),
        (
          (0..mw)
            .map(
              |j| {
                if j + 1 == mw { 3 } else { u64::try_from(j % 2).unwrap() }
              },
            )
            .collect(),
          (0..mw).map(|j| u64::try_from((j * 2 + 1) % 7).unwrap()).collect(),
          (0..pw).map(|j| u64::try_from(j + 1).unwrap()).collect(),
          false,
          false,
          true,
        ),
        (
          (0..mw).map(|j| u64::try_from((j * 3 + 2) % 11).unwrap()).collect(),
          vec![0; mw],
          (0..pw).map(|j| u64::try_from((j * 5 + 1) % 7).unwrap()).collect(),
          false,
          true,
          false,
        ),
      ];
      for (row_idx, (cur, next, prep, first, last, trans)) in
        test_rows.iter().enumerate()
      {
        let gl_cur: Vec<Val> = cur.iter().copied().map(Val::from_u64).collect();
        let gl_next: Vec<Val> =
          next.iter().copied().map(Val::from_u64).collect();
        let gl_prep: Vec<Val> =
          prep.iter().copied().map(Val::from_u64).collect();
        let (gl_zeros, gl_lookups) = eval_constraint_graph(
          gl_graph, &gl_cur, &gl_next, &gl_prep, *first, *last, *trans,
        );

        let bn_cur: Vec<Scalar> =
          cur.iter().copied().map(|v| Bn254.from_u64(v)).collect();
        let bn_next: Vec<Scalar> =
          next.iter().copied().map(|v| Bn254.from_u64(v)).collect();
        let bn_prep: Vec<Scalar> =
          prep.iter().copied().map(|v| Bn254.from_u64(v)).collect();
        let (bn_zeros, bn_lookups) = eval_constraint_graph(
          &bn_graph, &bn_cur, &bn_next, &bn_prep, *first, *last, *trans,
        );

        let gl_z_i128: Vec<i128> =
          gl_zeros.into_iter().map(gl_to_small_i128).collect();
        let bn_z_i128: Vec<i128> =
          bn_zeros.into_iter().map(bn_to_small_i128).collect();
        assert_eq!(
          gl_z_i128, bn_z_i128,
          "{name}: constraint values differ on row {row_idx}"
        );

        for (li, ((gm, ga), (bm, ba))) in
          gl_lookups.into_iter().zip(bn_lookups).enumerate()
        {
          assert_eq!(
            gl_to_small_i128(gm),
            bn_to_small_i128(bm),
            "{name}: lookup {li} multiplicity differs on row {row_idx}"
          );
          let ga_i128: Vec<i128> =
            ga.into_iter().map(gl_to_small_i128).collect();
          let ba_i128: Vec<i128> =
            ba.into_iter().map(bn_to_small_i128).collect();
          assert_eq!(
            ga_i128, ba_i128,
            "{name}: lookup {li} args differ on row {row_idx}"
          );
        }
      }
    }
  }

  #[test]
  fn bn254_lowering_matches_goldilocks_on_chips_groups_tables_and_rom() {
    use aiur::{Program, field::FieldBackend, trace::TraceArtifact};
    use multi_stark::{p3_field::PrimeField64, types::Val};

    // 1. Shared circuit with ungrouped chip, function group, shared/empty
    // fixed tables, and multiple ROM widths.
    let gl_mod = serde_json::json!(Val::ORDER_U64);
    let (gl_prog_json, gl_trace_json) =
      build_shared_differential_program_json(&gl_mod, |v| serde_json::json!(v));
    let gl_prog: Program<u64> = serde_json::from_value(gl_prog_json).unwrap();
    let gl_trace: TraceArtifact<u64> =
      serde_json::from_value(gl_trace_json).unwrap();
    let gl_checked = gl_prog.check().unwrap();
    let gl_plan = TracePlan::new(&gl_checked, gl_trace).unwrap();

    let bn_mod = serde_json::to_value(Bn254.modulus()).unwrap();
    let (bn_prog_json, bn_trace_json) =
      build_shared_differential_program_json(&bn_mod, |v| {
        serde_json::to_value(FieldWord::from(v)).unwrap()
      });
    let bn_prog: Program<FieldWord> =
      serde_json::from_value(bn_prog_json).unwrap();
    let bn_trace: TraceArtifact<FieldWord> =
      serde_json::from_value(bn_trace_json).unwrap();
    let bn_checked = bn_prog.check_with(Bn254).unwrap();
    let bn_plan = TracePlan::new(&bn_checked, bn_trace).unwrap();

    assert_bn254_matches_goldilocks_lowering(&gl_plan, &bn_plan);

    // 2. Also verify exact parity when the group is cleared (all singleton chips).
    let mut gl_trace_ungrouped = gl_plan.artifact().clone();
    gl_trace_ungrouped.groups.clear();
    let gl_plan_ungrouped =
      TracePlan::new(&gl_checked, gl_trace_ungrouped).unwrap();

    let mut bn_trace_ungrouped = bn_plan.artifact().clone();
    bn_trace_ungrouped.groups.clear();
    let bn_plan_ungrouped =
      TracePlan::new(&bn_checked, bn_trace_ungrouped).unwrap();

    assert_bn254_matches_goldilocks_lowering(
      &gl_plan_ungrouped,
      &bn_plan_ungrouped,
    );
  }
}
