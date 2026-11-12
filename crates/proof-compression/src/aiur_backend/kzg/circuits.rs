use super::*;
use aiur::{
  field::FieldBackend,
  trace::{FunctionCircuit, Polynomial},
};
use multi_stark::{expr::Expr, lookup::Lookup, traits::Algebra};
use p3_matrix::dense::RowMajorMatrix;

const CALL: u64 = 1;
const ROM: u64 = 2;

pub(super) struct FixedTable {
  pub(super) maps: Vec<usize>,
  pub(super) height: usize,
}

pub(super) struct Lowered {
  pub(super) inputs: Vec<CircuitInputs<Scalar>>,
  pub(super) names: Vec<String>,
  pub(super) placements: Vec<Placement<FieldWord>>,
  pub(super) function_circuits: usize,
  pub(super) tables: Vec<FixedTable>,
  pub(super) memory_widths: Vec<usize>,
}

fn constant(value: u64) -> Expr<Scalar> {
  Expr::constant(Bn254.from_u64(value))
}

fn main_var(column: usize) -> Expr<Scalar> {
  Expr::main(u32::try_from(column).expect("validated compiler column"))
}

fn lower(polynomial: &Polynomial<FieldWord>) -> Expr<Scalar> {
  match polynomial {
    Polynomial::Const(value) => Expr::constant(Bn254.from_word(*value)),
    Polynomial::Var(column) => main_var(*column),
    Polynomial::Add(terms) => lower(&terms[0]) + lower(&terms[1]),
    Polynomial::Sub(terms) => lower(&terms[0]) - lower(&terms[1]),
    Polynomial::Mul(terms) => lower(&terms[0]) * lower(&terms[1]),
  }
}

pub(super) fn evaluate(
  polynomial: &Polynomial<FieldWord>,
  row: &[Scalar],
) -> Scalar {
  match polynomial {
    Polynomial::Const(value) => Bn254.from_word(*value),
    Polynomial::Var(column) => row[*column],
    Polynomial::Add(terms) => {
      evaluate(&terms[0], row) + evaluate(&terms[1], row)
    },
    Polynomial::Sub(terms) => {
      evaluate(&terms[0], row) - evaluate(&terms[1], row)
    },
    Polynomial::Mul(terms) => {
      evaluate(&terms[0], row) * evaluate(&terms[1], row)
    },
  }
}

pub(super) fn build(plan: &TracePlan<'_, Bn254>) -> Result<Lowered, String> {
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
          polynomial.validate(group.width, Bn254)?;
        }
        let mut constraints: Vec<_> =
          group.constraints.iter().map(lower).collect();
        constraints.push(
          (constant(1) - lower(&group.activation)) * main_var(group.width),
        );
        let mut lookups = vec![Lookup::pull(
          main_var(group.width),
          group.receive.iter().map(lower).collect(),
        )];
        lookups.extend(group.sends.iter().map(|send| {
          Lookup::push(
            lower(&send.enable),
            send.args.iter().map(lower).collect(),
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
        let mut args = vec![constant(CALL), constant(callable(&chip.name)?)];
        args.extend(chip.inputs.iter().map(|&column| main_var(column)));
        args.extend(chip.output.iter().map(lower));
        let mut lookups = vec![Lookup::pull(main_var(chip.width), args)];
        for send in &chip.sends {
          let mut args =
            vec![constant(CALL), constant(callable(&send.channel)?)];
          args.extend(send.args.iter().map(lower));
          args.extend(send.result.iter().map(|&column| main_var(column)));
          lookups.push(Lookup::push(lower(&send.enable), args));
        }
        for cell in &chip.memory {
          let payload = u64::try_from(cell.values.len())
            .map_err(|_error| "ROM width overflow")?;
          let mut args =
            vec![constant(ROM), constant(payload), lower(&cell.address)];
          args.extend(cell.values.iter().map(lower));
          lookups.push(Lookup::push(lower(&cell.enable), args));
        }
        inputs.push(CircuitInputs {
          main_width: chip.width + 1,
          constraints: chip
            .constraints
            .iter()
            .map(lower)
            .chain([
              (constant(1) - main_var(chip.activation)) * main_var(chip.width)
            ])
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
      constant(ROM),
      constant(u64::try_from(payload).map_err(|_error| "ROM width overflow")?),
      address.clone(),
    ];
    args.extend((3..width).map(main_var));
    let transition = Expr::IsTransition * Expr::main_next(1);
    inputs.push(CircuitInputs {
      main_width: width,
      constraints: vec![
        active.clone() * (active.clone() - constant(1)),
        count.clone() * (constant(1) - active.clone()),
        transition.clone() * (active - constant(1)),
        transition * (Expr::main_next(2) - address.clone() - constant(1)),
        Expr::IsFirstRow * address,
      ],
      lookups: vec![Lookup::pull(count, args)],
      ..Default::default()
    });
    names.push(format!("<ROM:{payload}>"));
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

fn fixed_tables(
  plan: &TracePlan<'_, Bn254>,
  inputs: &mut Vec<CircuitInputs<Scalar>>,
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
        constant(CALL),
        constant(
          u64::try_from(callable).map_err(|_error| "callable overflow")?,
        ),
      ];
      if height == 0 {
        args.resize(2 + input_width + output_width, constant(0));
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
        values.push(Scalar::ONE);
        for &(table, _, _) in &columns {
          values.extend(
            program.tables[table].rows[row]
              .iter()
              .map(|&word| Bn254.from_word(word)),
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
