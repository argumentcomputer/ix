//! Witness population plans for the final, certified circuit layout.
//!
//! This is an untrusted witness generator. Plans are exported by Lean alongside
//! the certified circuits. Population never executes a callee or obtains fresh
//! hints. Constraints and exact integer message balance can be checked separately.
use crate::bytecode::{CheckedProgram, Instruction, Type};
use crate::execute::Execution;
use crate::field::{FieldBackend, PrimeField};
#[cfg(feature = "parallel")]
use rayon::prelude::*;
use rustc_hash::{FxHashMap, FxHashSet};
use serde::{Deserialize, Serialize};

mod plan;
#[cfg(feature = "stark")]
pub mod stark;
#[cfg(test)]
mod tests;

#[derive(Clone, Debug, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Polynomial {
  Const(u64),
  Var(usize),
  Add(Box<[Polynomial; 2]>),
  Sub(Box<[Polynomial; 2]>),
  Mul(Box<[Polynomial; 2]>),
}

impl Polynomial {
  fn visit(&self, f: &mut impl FnMut(usize)) {
    match self {
      Self::Var(v) => f(*v),
      Self::Const(_) => (),
      Self::Add(xs) | Self::Sub(xs) | Self::Mul(xs) => {
        xs[0].visit(f);
        xs[1].visit(f);
      },
    }
  }
  fn validate<B: FieldBackend>(
    &self,
    width: usize,
    field: B,
  ) -> Result<(), String> {
    match self {
      Self::Var(v) if *v >= width => {
        Err(format!("out-of-bounds witness {v}/{width}"))
      },
      Self::Const(v) if !field.contains(*v) => {
        Err("noncanonical plan constant".into())
      },
      Self::Add(xs) | Self::Sub(xs) | Self::Mul(xs) => {
        xs[0].validate(width, field)?;
        xs[1].validate(width, field)
      },
      _ => Ok(()),
    }
  }
  fn eval<B: FieldBackend>(&self, row: &[B::Element], field: B) -> B::Element {
    match self {
      Self::Const(v) => field.from_u64(*v),
      Self::Var(v) => row[*v],
      Self::Add(xs) => {
        field.add(xs[0].eval(row, field), xs[1].eval(row, field))
      },
      Self::Sub(xs) => {
        field.sub(xs[0].eval(row, field), xs[1].eval(row, field))
      },
      Self::Mul(xs) => {
        field.mul(xs[0].eval(row, field), xs[1].eval(row, field))
      },
    }
  }
}

#[derive(Clone, Debug, Deserialize)]
#[serde(tag = "op", rename_all = "snake_case")]
pub enum Action {
  Assign {
    dest: Vec<usize>,
    values: Vec<Polynomial>,
  },
  Inverse {
    dest: usize,
    value: Polynomial,
  },
  Choose {
    dest: Vec<usize>,
    tests: Vec<Vec<Polynomial>>,
  },
  Failure {
    dest: Vec<usize>,
    differences: Vec<Polynomial>,
  },
  Call {
    name: String,
    args: Vec<Polynomial>,
    dest: Vec<usize>,
  },
  Store {
    r#type: Type,
    values: Vec<Polynomial>,
    dest: usize,
  },
  Load {
    r#type: Type,
    address: Polynomial,
    dest: Vec<usize>,
  },
  Hint {
    #[serde(default)]
    channel: String,
    instruction: usize,
    r#type: Type,
    key_type: Type,
    key: Vec<Polynomial>,
    dest: Vec<usize>,
  },
}

impl Action {
  fn dest(&self) -> &[usize] {
    match self {
      Self::Assign { dest, .. }
      | Self::Choose { dest, .. }
      | Self::Failure { dest, .. }
      | Self::Call { dest, .. }
      | Self::Load { dest, .. }
      | Self::Hint { dest, .. } => dest,
      Self::Inverse { dest, .. } | Self::Store { dest, .. } => {
        std::slice::from_ref(dest)
      },
    }
  }
  fn expressions(&self) -> Vec<&Polynomial> {
    match self {
      Self::Assign { values, .. } | Self::Store { values, .. } => {
        values.iter().collect()
      },
      Self::Inverse { value, .. } => vec![value],
      Self::Choose { tests, .. } => tests.iter().flatten().collect(),
      Self::Failure { differences, .. } => differences.iter().collect(),
      Self::Call { args, .. } => args.iter().collect(),
      Self::Load { address, .. } => vec![address],
      Self::Hint { key, .. } => key.iter().collect(),
    }
  }
}

#[derive(Clone, Debug, Deserialize)]
pub struct PopulationStep {
  pub guard: Polynomial,
  pub action: Action,
}
#[derive(Clone, Debug, Deserialize)]
pub struct ColumnWrite {
  pub column: usize,
  pub source: usize,
  pub guard: Polynomial,
}
#[derive(Clone, Debug, Deserialize)]
pub struct FunctionPlan {
  pub name: String,
  pub chip: String,
  pub witnesses: usize,
  pub inputs: Vec<usize>,
  pub output: Vec<usize>,
  pub steps: Vec<PopulationStep>,
  pub writes: Vec<ColumnWrite>,
}
#[derive(Clone, Debug, Deserialize)]
pub struct Send {
  pub channel: String,
  pub args: Vec<Polynomial>,
  pub result: Vec<usize>,
  pub enable: Polynomial,
}
#[derive(Clone, Debug, Deserialize)]
pub struct MemoryLookup {
  pub r#type: Type,
  pub address: Polynomial,
  pub values: Vec<Polynomial>,
  pub enable: Polynomial,
}
#[derive(Clone, Debug, Deserialize)]
pub struct Chip {
  pub name: String,
  pub width: usize,
  /// The last physical column is the proved row-activation selector.
  pub activation: usize,
  pub inputs: Vec<usize>,
  pub output: Vec<Polynomial>,
  pub constraints: Vec<Polynomial>,
  pub sends: Vec<Send>,
  pub memory: Vec<MemoryLookup>,
}
#[derive(Clone, Debug, Deserialize)]
pub struct TraceArtifact {
  pub version: u32,
  pub modulus: u64,
  pub functions: Vec<FunctionPlan>,
  pub chips: Vec<Chip>,
}

/// Height is explicit: a zero-column circuit can still provide a claim.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Matrix<F = u64> {
  pub chip: String,
  pub width: usize,
  pub height: usize,
  pub unpadded_height: usize,
  pub values: Vec<F>,
  pub multiplicities: Vec<u64>,
}
impl<F> Matrix<F> {
  pub fn row(&self, index: usize) -> &[F] {
    &self.values[index * self.width..(index + 1) * self.width]
  }
}
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Trace<F = u64> {
  pub matrices: Vec<Matrix<F>>,
}

#[derive(Clone, Debug, Default, Serialize)]
pub struct PopulationTimings {
  pub validate_seconds: f64,
  pub bind_seconds: f64,
  pub fill_seconds: f64,
  pub padding_seconds: f64,
  pub count_seconds: f64,
}

/// A checked plan is tied to the immutable checked execution program.
pub struct TracePlan<'a, B: FieldBackend = PrimeField> {
  program: &'a CheckedProgram<B>,
  artifact: TraceArtifact,
  callables: FxHashMap<String, usize>,
  members: Vec<usize>,
  fills: Vec<plan::FillPlan<B>>,
}

fn indices(xs: &[usize], width: usize) -> Result<(), String> {
  if xs.iter().any(|x| *x >= width) {
    Err("plan index out of bounds".into())
  } else {
    Ok(())
  }
}

impl<'a, B: FieldBackend> TracePlan<'a, B> {
  pub fn new(
    program: &'a CheckedProgram<B>,
    mut artifact: TraceArtifact,
  ) -> Result<Self, String> {
    if artifact.version != 2 || artifact.modulus != program.field.modulus() {
      return Err("trace version or field mismatch".into());
    }
    if artifact.functions.len() != program.program.functions.len() {
      return Err("trace function count mismatch".into());
    }
    let mut chips = FxHashMap::default();
    for (i, chip) in artifact.chips.iter().enumerate() {
      if chips.insert(chip.name.clone(), i).is_some() {
        return Err("duplicate trace chip".into());
      }
    }
    let callables: FxHashMap<_, _> = (0..program.inputs.len())
      .map(|id| (program.callable_name(id).unwrap().to_owned(), id))
      .collect();
    let field = program.field;
    let mut members = vec![];
    for (id, function) in artifact.functions.iter_mut().enumerate() {
      if function.name != program.program.functions[id].name {
        return Err("trace function order mismatch".into());
      }
      let chip =
        *chips.get(&function.chip).ok_or("unknown representative chip")?;
      members.push(chip);
      if function.inputs.len() != program.inputs[id].width()
        || function.output.len() != program.outputs[id].width()
      {
        return Err("trace function interface width mismatch".into());
      }
      indices(&function.inputs, function.witnesses)?;
      indices(&function.output, function.witnesses)?;
      for step in &function.steps {
        step.guard.validate(function.witnesses, field)?;
        indices(step.action.dest(), function.witnesses)?;
        for expr in step.action.expressions() {
          expr.validate(function.witnesses, field)?;
        }
        match &step.action {
          Action::Assign { dest, values } if dest.len() != values.len() => {
            return Err("assignment shape mismatch".into());
          },
          Action::Choose { dest, tests } if dest.len() != tests.len() => {
            return Err("choice shape mismatch".into());
          },
          Action::Failure { dest, differences }
            if dest.len() != differences.len() =>
          {
            return Err("failure shape mismatch".into());
          },
          Action::Call { name, args, dest } => {
            let id = *callables.get(name).ok_or("unknown trace callable")?;
            if args.len() != program.inputs[id].width()
              || dest.len() != program.outputs[id].width()
            {
              return Err("trace call shape mismatch".into());
            }
          },
          Action::Store { r#type, values, .. } => {
            if r#type.layout(&program.program.enums, &mut vec![])?.width()
              != values.len()
            {
              return Err("trace store shape mismatch".into());
            }
          },
          Action::Load { r#type, dest, .. } => {
            if r#type.layout(&program.program.enums, &mut vec![])?.width()
              != dest.len()
            {
              return Err("trace load shape mismatch".into());
            }
          },
          Action::Hint {
            channel,
            instruction,
            r#type,
            key_type,
            key,
            dest,
          } => match program.program.functions[id].code.get(*instruction) {
            Some(Instruction::Hint {
              channel: c,
              r#type: t,
              key_type: k,
              key: ks,
              dest: ds,
            }) if c == channel
              && t == r#type
              && k == key_type
              && ks.len() == key.len()
              && ds.len() == dest.len() => {},
            _ => return Err("trace hint site mismatch".into()),
          },
          _ => (),
        }
      }
      for write in &function.writes {
        indices(&[write.source], function.witnesses)?;
        // The row writer owns the activation column, never a recipe.
        indices(&[write.column], artifact.chips[chip].activation)?;
        write.guard.validate(function.witnesses, field)?;
      }
      // Conservative dependency closure. Guarded assignments do not kill
      // alternative branch definitions of the same logical destination.
      let mut live = FxHashSet::default();
      for write in &function.writes {
        live.insert(write.source);
        write.guard.visit(&mut |v| {
          live.insert(v);
        });
      }
      loop {
        let before = live.len();
        for step in function.steps.iter().rev() {
          if step.action.dest().iter().any(|v| live.contains(v)) {
            step.guard.visit(&mut |v| {
              live.insert(v);
            });
            for p in step.action.expressions() {
              p.visit(&mut |v| {
                live.insert(v);
              });
            }
          }
        }
        if live.len() == before {
          break;
        }
      }
      function
        .steps
        .retain(|s| s.action.dest().iter().any(|v| live.contains(v)));
    }
    for chip in &artifact.chips {
      if chip.activation.checked_add(1) != Some(chip.width) {
        return Err("invalid activation column".into());
      }
      let callable =
        *callables.get(&chip.name).ok_or("unknown chip callable")?;
      if chip.inputs.len() != program.inputs[callable].width()
        || chip.output.len() != program.outputs[callable].width()
      {
        return Err("circuit interface width mismatch".into());
      }
      indices(&chip.inputs, chip.width)?;
      for p in chip.constraints.iter().chain(&chip.output) {
        p.validate(chip.width, field)?;
      }
      for send in &chip.sends {
        send.enable.validate(chip.width, field)?;
        for p in &send.args {
          p.validate(chip.width, field)?;
        }
        indices(&send.result, chip.width)?;
        let id =
          *callables.get(&send.channel).ok_or("unknown circuit channel")?;
        if send.args.len() != program.inputs[id].width()
          || send.result.len() != program.outputs[id].width()
        {
          return Err("circuit send shape mismatch".into());
        }
      }
      for cell in &chip.memory {
        cell.enable.validate(chip.width, field)?;
        cell.address.validate(chip.width, field)?;
        for p in &cell.values {
          p.validate(chip.width, field)?;
        }
        if cell.r#type.layout(&program.program.enums, &mut vec![])?.width()
          != cell.values.len()
        {
          return Err("circuit memory shape mismatch".into());
        }
      }
    }
    let fills = artifact
      .functions
      .iter()
      .map(|f| plan::FillPlan::compile(f, &callables, program))
      .collect();
    Ok(Self { program, artifact, callables, members, fills })
  }

  /// Populate each original query once. Power-of-two padding remains all
  /// zero, with no activation, provides, or outgoing requirements.
  pub fn generate(
    &self,
    record: &Execution<B>,
    entry: &str,
    args: &[B::Element],
    pad: bool,
  ) -> Result<Trace<B::Element>, String> {
    self.generate_impl(
      record,
      entry,
      args,
      pad,
      false,
      &mut PopulationTimings::default(),
    )
  }

  /// Slow logical recipe interpreter for differential checks and benchmarks.
  pub fn generate_reference(
    &self,
    record: &Execution<B>,
    entry: &str,
    args: &[B::Element],
    pad: bool,
  ) -> Result<Trace<B::Element>, String> {
    self.generate_impl(
      record,
      entry,
      args,
      pad,
      true,
      &mut PopulationTimings::default(),
    )
  }

  pub fn generate_profiled(
    &self,
    record: &Execution<B>,
    entry: &str,
    args: &[B::Element],
    pad: bool,
    reference: bool,
  ) -> Result<(Trace<B::Element>, PopulationTimings), String> {
    let mut timings = PopulationTimings::default();
    let trace =
      self.generate_impl(record, entry, args, pad, reference, &mut timings)?;
    Ok((trace, timings))
  }

  fn generate_impl(
    &self,
    record: &Execution<B>,
    entry: &str,
    args: &[B::Element],
    pad: bool,
    reference: bool,
    timings: &mut PopulationTimings,
  ) -> Result<Trace<B::Element>, String> {
    let start = std::time::Instant::now();
    self.validate_record(record)?;
    self.root(record, entry, args)?;
    timings.validate_seconds = start.elapsed().as_secs_f64();
    let start = std::time::Instant::now();
    let mut matrices: Vec<_> = self
      .artifact
      .chips
      .iter()
      .map(|chip| Matrix {
        chip: chip.name.clone(),
        width: chip.width,
        height: 0,
        unpadded_height: 0,
        values: vec![],
        multiplicities: vec![],
      })
      .collect();
    for (function, &chip) in self.members.iter().enumerate() {
      matrices[chip].unpadded_height = matrices[chip]
        .unpadded_height
        .checked_add(record.queries.tables[function].len())
        .ok_or("trace height overflow")?;
    }
    for matrix in &mut matrices {
      matrix.height = if pad && matrix.unpadded_height > 0 {
        matrix
          .unpadded_height
          .checked_next_power_of_two()
          .ok_or("padded height overflow")?
      } else {
        matrix.unpadded_height
      };
      let size =
        matrix.height.checked_mul(matrix.width).ok_or("trace size overflow")?;
      matrix.values.try_reserve_exact(size).map_err(|e| e.to_string())?;
      matrix.values.resize(size, self.program.field.zero());
      matrix.multiplicities.resize(matrix.height, 0);
    }
    let memory: FxHashMap<&[B::Element], usize> =
      record.memory.iter().map(|m| (m.cell.value, m.address)).collect();
    if memory.len() != record.memory.len() {
      return Err("duplicate interned ROM payload".into());
    }
    let mut offsets = vec![0usize; matrices.len()];
    let mut scratch = vec![];
    let mut buffer = vec![];
    let mut hint_output = vec![];
    let field = self.program.field;
    timings.bind_seconds = start.elapsed().as_secs_f64();
    let start = std::time::Instant::now();
    for (function, plan) in self.artifact.functions.iter().enumerate() {
      let table = &record.queries.tables[function];
      let matrix = &mut matrices[self.members[function]];
      scratch.resize(plan.witnesses, field.zero());
      for query in 0..table.len() {
        let offset = offsets[self.members[function]];
        matrix.values[offset * matrix.width
          + self.artifact.chips[self.members[function]].activation] =
          field.one();
        matrix.multiplicities[offset] = table.output(query).multiplicity;
        if !reference {
          let row = &mut matrix.values
            [offset * matrix.width..(offset + 1) * matrix.width];
          self.fills[function]
            .fill(
              record,
              (table.input(query), table.output(query)),
              &memory,
              &mut scratch,
              &mut buffer,
              row,
            )
            .map_err(|e| format!("{} query {query}: {e}", plan.name))?;
          offsets[self.members[function]] += 1;
          continue;
        }
        scratch.fill(field.zero());
        let input = table.input(query);
        let output = table.output(query);
        for (&dest, &v) in plan.inputs.iter().zip(input) {
          scratch[dest] = v;
        }
        for (&dest, &v) in plan.output.iter().zip(output.output) {
          scratch[dest] = v;
        }
        for (step_id, step) in plan.steps.iter().enumerate() {
          if step.guard.eval(&scratch, field) != field.one() {
            continue;
          }
          let mut fill = || -> Result<(), String> {
            match &step.action {
              Action::Assign { dest, values } => {
                buffer.clear();
                buffer.extend(values.iter().map(|p| p.eval(&scratch, field)));
                for (&d, &v) in dest.iter().zip(&buffer) {
                  scratch[d] = v;
                }
              },
              Action::Inverse { dest, value } => {
                scratch[*dest] = field
                  .inverse(value.eval(&scratch, field))
                  .ok_or("active zero denominator")?;
              },
              Action::Choose { dest, tests } => {
                let selected = tests
                  .iter()
                  .position(|xs| {
                    xs.iter().all(|p| p.eval(&scratch, field) == field.zero())
                  })
                  .ok_or("no matching trace arm")?;
                for (i, &d) in dest.iter().enumerate() {
                  scratch[d] = field.from_u64(u64::from(i == selected));
                }
              },
              Action::Failure { dest, differences } => {
                let (selected, v) = differences
                  .iter()
                  .enumerate()
                  .find_map(|(i, p)| {
                    let v = p.eval(&scratch, field);
                    (v != field.zero()).then_some((i, v))
                  })
                  .ok_or("rejected pattern actually matches")?;
                for &d in dest {
                  scratch[d] = field.zero();
                }
                scratch[dest[selected]] =
                  field.inverse(v).ok_or("zero failure witness")?;
              },
              Action::Call { name, args, dest } => {
                buffer.clear();
                buffer.extend(args.iter().map(|p| p.eval(&scratch, field)));
                let table = &record.queries.tables[self.callables[name]];
                // Independent reference population always uses
                // the original table, never a host override.
                let values = if let Some(map) = &table.static_map {
                  map.binding.output(map.binding.row(&buffer)?)
                } else {
                  let id =
                    table.lookup(&buffer).1.ok_or("missing recorded callee")?;
                  let answer = table.output(id);
                  if answer.multiplicity == 0 {
                    return Err("pending recorded callee".into());
                  }
                  answer.output
                };
                for (&d, &v) in dest.iter().zip(values) {
                  scratch[d] = v;
                }
              },
              Action::Store { values, dest, .. } => {
                buffer.clear();
                buffer.extend(values.iter().map(|p| p.eval(&scratch, field)));
                let address = *memory
                  .get(buffer.as_slice())
                  .ok_or("missing recorded store")?;
                scratch[*dest] = field.from_u64(
                  u64::try_from(address).map_err(|_| "ROM address overflow")?,
                );
              },
              Action::Load { address, dest, .. } => {
                let address =
                  usize::try_from(field.to_u64(address.eval(&scratch, field)))
                    .map_err(|_| "ROM address overflow")?;
                let cell = &record
                  .memory
                  .get_by_width(dest.len(), address)
                  .ok_or("missing recorded load")?
                  .cell;
                if cell.value.len() != dest.len() {
                  return Err("ROM load shape mismatch".into());
                }
                for (&d, &v) in dest.iter().zip(cell.value) {
                  scratch[d] = v;
                }
              },
              Action::Hint { instruction, key, dest, .. } => {
                buffer.clear();
                buffer.extend(key.iter().map(|p| p.eval(&scratch, field)));
                hint_output.resize(dest.len(), field.zero());
                record.hints.sites[function][*instruction]
                  .as_ref()
                  .ok_or("missing hint site")?
                  .evaluate(&buffer, &mut hint_output, field)?;
                for (&d, &v) in dest.iter().zip(&hint_output) {
                  scratch[d] = v;
                }
              },
            }
            Ok(())
          };
          fill().map_err(|e| {
            format!(
              "{} query {query}, population step {step_id}: {e}",
              plan.name
            )
          })?;
        }
        let offset = offsets[self.members[function]];
        let row = &mut matrix.values
          [offset * matrix.width..(offset + 1) * matrix.width];
        for write in &plan.writes {
          if write.guard.eval(&scratch, field) == field.one() {
            row[write.column] = scratch[write.source];
          }
        }
        offsets[self.members[function]] += 1;
      }
    }
    timings.fill_seconds = start.elapsed().as_secs_f64();
    // Allocation already zeroed the inactive padding rows. Their lookup
    // multiplicities are zero, so execution counts require no repair.
    Ok(Trace { matrices })
  }

  fn validate_record(&self, record: &Execution<B>) -> Result<(), String> {
    if !std::sync::Arc::ptr_eq(&record.hints.program, &self.program.program) {
      return Err("hint providers belong to another program".into());
    }
    if record.queries.tables.len() != self.program.inputs.len() {
      return Err("query record callable count mismatch".into());
    }
    let validate_table = |(i, table): (usize, &crate::query::QueryTable<B>)| {
      if table.widths()
        != (self.program.inputs[i].width(), self.program.outputs[i].width())
      {
        return Err("query record width mismatch".into());
      }
      if i >= self.program.program.functions.len() {
        let map =
          table.static_map.as_ref().ok_or("missing static map record")?;
        if !std::sync::Arc::ptr_eq(&map.binding.program, &self.program.program)
          || map.binding.id != i - self.program.program.functions.len()
        {
          return Err(
            "static map record belongs to another program/map".into(),
          );
        }
        if map.counts.len() != map.binding.rows() {
          return Err("malformed static map counts".into());
        }
        // Inputs/results are borrowed from already validated tables.
        return Ok(());
      }
      if table.static_map.is_some() {
        return Err("function record contains a static map".into());
      }
      for row in 0..table.len() {
        let output = table.output(row);
        if output.multiplicity == 0 {
          return Err("incomplete query record".into());
        }
        self.program.inputs[i]
          .validate(table.input(row), self.program.field)?;
        self.program.outputs[i].validate(output.output, self.program.field)?;
      }
      Ok::<_, String>(())
    };
    #[cfg(feature = "parallel")]
    record
      .queries
      .tables
      .par_iter()
      .enumerate()
      .try_for_each(validate_table)?;
    #[cfg(not(feature = "parallel"))]
    record.queries.tables.iter().enumerate().try_for_each(validate_table)?;
    if record
      .memory
      .iter()
      .any(|m| m.address as u128 >= self.program.field.modulus() as u128)
    {
      return Err("ROM exceeds field capacity".into());
    }
    let validate_memory = |m: crate::memory::MemoryEntryRef<'_, B::Element>| {
      self
        .program
        .memory_layouts
        .get(m.cell.r#type)
        .ok_or("unknown recorded ROM type")?
        .validate(m.cell.value, self.program.field)
    };
    #[cfg(feature = "parallel")]
    record.memory.par_iter().try_for_each(validate_memory)?;
    #[cfg(not(feature = "parallel"))]
    record.memory.iter().try_for_each(validate_memory)?;
    Ok(())
  }

  fn root(
    &self,
    record: &Execution<B>,
    entry: &str,
    args: &[B::Element],
  ) -> Result<Claim<B::Element>, String> {
    let id = self.program.entry(entry)?.function;
    self.program.inputs[id].validate(args, self.program.field)?;
    let query =
      record.queries.tables[id].lookup(args).1.ok_or("missing entry query")?;
    if record.queries.tables[id].output(query).output != record.output {
      return Err("root output mismatch".into());
    }
    let chip = self.members[id];
    Ok(Claim {
      channel: self.callables[&self.artifact.chips[chip].name],
      args: args.to_vec(),
      output: record.output.clone(),
    })
  }

  fn claim(&self, chip: &Chip, row: &[B::Element]) -> Claim<B::Element> {
    Claim {
      channel: self.callables[&chip.name],
      args: chip.inputs.iter().map(|&i| row[i]).collect(),
      output: chip
        .output
        .iter()
        .map(|p| p.eval(row, self.program.field))
        .collect(),
    }
  }
  fn send_claim(&self, send: &Send, row: &[B::Element]) -> Claim<B::Element> {
    Claim {
      channel: self.callables[&send.channel],
      args: send.args.iter().map(|p| p.eval(row, self.program.field)).collect(),
      output: send.result.iter().map(|&i| row[i]).collect(),
    }
  }
  fn static_claim(&self, claim: &Claim<B::Element>) -> Result<bool, String> {
    let Some(map) = self
      .program
      .program
      .maps
      .get(claim.channel.wrapping_sub(self.program.program.functions.len()))
    else {
      return Ok(false);
    };
    let index = self.program.map_indexes[map.input]
      .as_ref()
      .ok_or("missing static map index")?;
    let row = index.get(&claim.args).ok_or("unavailable static map claim")?;
    if self.program.tables[map.output][row] != claim.output {
      return Err("wrong static map result".into());
    }
    Ok(true)
  }

  /// Independent diagnostic validation of every physical row, typed ROM
  /// lookup, static map membership and exact integer message balance.
  pub fn check(
    &self,
    record: &Execution<B>,
    trace: &Trace<B::Element>,
    entry: &str,
    args: &[B::Element],
  ) -> Result<(), String> {
    self.validate_record(record)?;
    if trace.matrices.len() != self.artifact.chips.len() {
      return Err("trace matrix count mismatch".into());
    }
    let field = self.program.field;
    let mut ledger: FxHashMap<Claim<B::Element>, i128> = FxHashMap::default();
    ledger.insert(self.root(record, entry, args)?, -1);
    for (chip, matrix) in self.artifact.chips.iter().zip(&trace.matrices) {
      if matrix.chip != chip.name
        || matrix.width != chip.width
        || matrix.unpadded_height > matrix.height
        || matrix.height.checked_mul(matrix.width) != Some(matrix.values.len())
        || matrix.multiplicities.len() != matrix.height
        || matrix.values.iter().any(|v| !field.valid(*v))
      {
        return Err("malformed trace matrix".into());
      }
      for row_id in 0..matrix.height {
        let row = matrix.row(row_id);
        if (row[chip.activation] != field.zero()
          && row[chip.activation] != field.one())
          || (row[chip.activation] == field.zero()
            && matrix.multiplicities[row_id] != 0)
        {
          return Err("invalid inactive row multiplicity or activation".into());
        }
        for (i, p) in chip.constraints.iter().enumerate() {
          if p.eval(row, field) != field.zero() {
            return Err(format!(
              "{} row {row_id}: constraint {i} is nonzero",
              chip.name
            ));
          }
        }
        for (i, cell) in chip.memory.iter().enumerate() {
          if cell.enable.eval(row, field) != field.one() {
            continue;
          }
          let address =
            usize::try_from(field.to_u64(cell.address.eval(row, field)))
              .map_err(|_| "ROM address overflow")?;
          let value = &record
            .memory
            .get_by_width(cell.values.len(), address)
            .ok_or("missing circuit ROM cell")?
            .cell;
          if value.value.len() != cell.values.len()
            || value
              .value
              .iter()
              .zip(&cell.values)
              .any(|(&v, p)| v != p.eval(row, field))
          {
            return Err(format!(
              "{} row {row_id}: memory lookup {i} mismatch",
              chip.name
            ));
          }
        }
        let balance = ledger.entry(self.claim(chip, row)).or_default();
        *balance = balance
          .checked_add(i128::from(matrix.multiplicities[row_id]))
          .ok_or("ledger overflow")?;
        for send in &chip.sends {
          if send.enable.eval(row, field) == field.one() {
            let claim = self.send_claim(send, row);
            if !self.static_claim(&claim)? {
              let balance = ledger.entry(claim).or_default();
              *balance = balance.checked_sub(1).ok_or("ledger overflow")?;
            }
          }
        }
      }
    }
    if ledger.values().any(|&count| count != 0) {
      return Err("unbalanced trace messages".into());
    }
    Ok(())
  }
}

#[derive(Debug, PartialEq, Eq, Hash)]
struct Claim<F> {
  channel: usize,
  args: Vec<F>,
  output: Vec<F>,
}
