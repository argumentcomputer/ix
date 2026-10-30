//! Populate main rows and lookup messages together, directly in backend storage.
//! The lookup writer is compiled from the backend's actual constraint graph;
//! it introduces no alternate message encoding or changes to the circuits.
use super::*;
use multi_stark::{
  expr::{RowOffset, Source},
  graph::{ConstraintGraph, Node},
  lookup::{LookupRowMut, LookupValues},
};
#[derive(Clone, Copy)]
enum Value {
  Constant(Val),
  Main(usize),
  Preprocessed(usize),
  Scratch(usize),
}
impl Value {
  #[inline]
  fn get(self, row: &[Val], fixed: &[Val], scratch: &[Val]) -> Val {
    match self {
      Self::Constant(value) => value,
      Self::Main(i) => row[i],
      Self::Preprocessed(i) => fixed[i],
      Self::Scratch(i) => scratch[i],
    }
  }
}

enum Arithmetic {
  Add(Value, Value),
  Sub(Value, Value),
  Mul(Value, Value),
  Neg(Value),
}
struct Slot {
  multiplicity: Value,
  args: Arguments,
}

struct CopySpan {
  source: usize,
  destination: usize,
  len: usize,
}

#[derive(Default)]
/// Partition argument sources once and coalesce adjacent copies. Filling a
/// lookup then needs no per-argument source dispatch or temporary argument Vec.
struct Arguments {
  width: usize,
  constants: Vec<(usize, Val)>,
  main: Vec<CopySpan>,
  fixed: Vec<CopySpan>,
  scratch: Vec<CopySpan>,
}

impl Arguments {
  fn compile(values: &[Value]) -> Self {
    let mut plan = Self { width: values.len(), ..Self::default() };
    for (destination, value) in values.iter().copied().enumerate() {
      let (spans, source) = match value {
        Value::Constant(v) => {
          // Lookup builder storage starts at zero.
          if v != Val::ZERO {
            plan.constants.push((destination, v));
          }
          continue;
        },
        Value::Main(i) => (&mut plan.main, i),
        Value::Preprocessed(i) => (&mut plan.fixed, i),
        Value::Scratch(i) => (&mut plan.scratch, i),
      };
      if let Some(last) = spans.last_mut()
        && last.source + last.len == source
        && last.destination + last.len == destination
      {
        last.len += 1;
      } else {
        spans.push(CopySpan { source, destination, len: 1 });
      }
    }
    plan
  }

  /// Populate a fresh, zeroed slot exactly once. Constant-zero arguments are
  /// intentionally left untouched, as are all inactive lookup slots.
  #[inline]
  fn fill(
    &self,
    row: &[Val],
    fixed: &[Val],
    scratch: &[Val],
    args: &mut [Val],
  ) {
    for &(destination, value) in &self.constants {
      args[destination] = value;
    }
    for (spans, source) in
      [(&self.main, row), (&self.fixed, fixed), (&self.scratch, scratch)]
    {
      for span in spans {
        if span.len == 1 {
          args[span.destination] = source[span.source];
        } else {
          args[span.destination..span.destination + span.len]
            .copy_from_slice(&source[span.source..span.source + span.len]);
        }
      }
    }
  }
}

/// Leaf references read directly from the completed row. Only arithmetic needs
/// scratch slots; constants and column copies require no graph instructions.
pub(super) struct LookupPlan {
  arithmetic: Vec<Arithmetic>,
  slots: Vec<Slot>,
  widths: Vec<usize>,
}
impl LookupPlan {
  pub(super) fn compile(graph: &ConstraintGraph<Val>) -> Result<Self, String> {
    let mut values = Vec::with_capacity(graph.lookup_prefix_len);
    let mut arithmetic = vec![];
    for node in &graph.nodes[..graph.lookup_prefix_len] {
      let op = match *node {
        Node::Const(value) => {
          values.push(Value::Constant(value));
          continue;
        },
        Node::Var(col) if col.offset == RowOffset::Current => {
          values.push(match col.source {
            Source::Main => Value::Main(col.index as usize),
            Source::Preprocessed => Value::Preprocessed(col.index as usize),
            Source::Stage2 => return Err("stage-two lookup input".into()),
          });
          continue;
        },
        Node::Add(a, b) => {
          Arithmetic::Add(values[a.index()], values[b.index()])
        },
        Node::Sub(a, b) => {
          Arithmetic::Sub(values[a.index()], values[b.index()])
        },
        Node::Mul(a, b) => {
          Arithmetic::Mul(values[a.index()], values[b.index()])
        },
        Node::Neg(a) => Arithmetic::Neg(values[a.index()]),
        _ => return Err("lookup requires a nonlocal row input".into()),
      };
      values.push(Value::Scratch(arithmetic.len()));
      arithmetic.push(op);
    }
    let slots: Vec<_> = graph
      .lookups
      .iter()
      .map(|lookup| {
        let mut args: Vec<_> =
          lookup.args.iter().map(|id| values[id.index()]).collect();
        // The protocol fingerprints sum(args[i] * gamma^i), so a
        // suffix of compile-time zeros contributes nothing. Message
        // namespaces and callable/type/width IDs still fix its shape.
        while matches!(args.last(), Some(Value::Constant(v)) if *v == Val::ZERO)
        {
          args.pop();
        }
        Slot {
          multiplicity: values[lookup.multiplicity.index()],
          args: Arguments::compile(&args),
        }
      })
      .collect();
    let widths = slots.iter().map(|slot| slot.args.width).collect();
    Ok(Self { arithmetic, slots, widths })
  }

  fn fill<F>(
    &self,
    row: &[Val],
    fixed: &[Val],
    worker: &mut Worker<F>,
    lookup: &mut LookupRowMut<'_, Val>,
  ) {
    let scratch = &mut worker.lookup_scratch;
    scratch.clear();
    for op in &self.arithmetic {
      let get = |value: Value| value.get(row, fixed, scratch);
      let value = match *op {
        Arithmetic::Add(a, b) => get(a) + get(b),
        Arithmetic::Sub(a, b) => get(a) - get(b),
        Arithmetic::Mul(a, b) => get(a) * get(b),
        Arithmetic::Neg(a) => -get(a),
      };
      scratch.push(value);
    }
    for (slot, plan) in self.slots.iter().enumerate() {
      let multiplicity = plan.multiplicity.get(row, fixed, scratch);
      // Zero-multiplicity messages do not affect the lookup argument.
      // Fresh builder storage already contains the empty lookup.
      if multiplicity == Val::ZERO {
        continue;
      }
      let (count, args) = lookup.slot_mut(slot);
      *count = multiplicity;
      debug_assert_eq!(args.len(), plan.args.width);
      plan.args.fill(row, fixed, scratch, args);
    }
  }

  /// Exercise the production writer and expose its stored messages to the
  /// independent constraint-graph evaluator in tests.
  #[cfg(test)]
  pub(super) fn evaluate(
    &self,
    row: &[Val],
    fixed: &[Val],
    mut emit: impl FnMut(usize, Val, &[Val]),
  ) {
    let mut builder = LookupValues::builder(1, &self.widths);
    let mut rows = builder.rows_mut();
    let lookup = &mut rows[0];
    self.fill(row, fixed, &mut Worker::<Val>::default(), lookup);
    for slot in 0..self.slots.len() {
      let (count, args) = lookup.slot_mut(slot);
      if *count != Val::ZERO {
        emit(slot, *count, args);
      }
    }
  }
}

struct Worker<F> {
  scratch: Vec<F>,
  buffer: Vec<F>,
  lookup_scratch: Vec<Val>,
}

impl<F> Default for Worker<F> {
  fn default() -> Self {
    Self {
      scratch: Default::default(),
      buffer: Default::default(),
      lookup_scratch: Default::default(),
    }
  }
}

/// A few rows per task amortize scheduling and scratch allocation while letting
/// a large circuit use the whole pool alongside the many small circuits.
const ROW_BATCH: usize = 32;

impl<B: WitnessField> Backend<'_, '_, B> {
  /// Generate a complete stage-one witness from the immutable query record.
  /// Main rows and their lookup messages are populated together. With the
  /// `parallel` feature, circuits and real-row batches share the Rayon pool.
  pub fn generate(
    &self,
    record: &Execution<B>,
    entry: &str,
    args: &[B::Element],
  ) -> Result<SystemWitness<Val>, String> {
    if self.gpu_lookup_only {
      Ok(self.witness_from_main(self.generate_stage_1(record, entry, args)?))
    } else {
      self.generate_with::<true>(record, Some((entry, args)))
    }
  }

  /// Batch proving creates lookup buffers per shard. Avoid allocating their
  /// whole-trace counterparts during the initial row population.
  pub fn generate_stage_1(
    &self,
    record: &Execution<B>,
    entry: &str,
    args: &[B::Element],
  ) -> Result<Vec<RowMajorMatrix<Val>>, String> {
    Ok(self.generate_with::<false>(record, Some((entry, args)))?.traces)
  }

  /// A worker record may have no public entrypoint of its own. Its unresolved
  /// calls are checked by the combined batch, never by a separate claim.
  pub fn generate_record_stage_1(
    &self,
    record: &Execution<B>,
  ) -> Result<Vec<RowMajorMatrix<Val>>, String> {
    Ok(self.generate_with::<false>(record, None)?.traces)
  }

  fn generate_with<const LOOKUPS: bool>(
    &self,
    record: &Execution<B>,
    root: Option<(&str, &[B::Element])>,
  ) -> Result<SystemWitness<Val>, String> {
    #[cfg(feature = "trace-profile")]
    let mut profile = super::profile::Phases::new();
    self.plan.validate_record(record)?;
    if let Some((entry, args)) = root {
      self.plan.root(record, entry, args)?;
    }
    #[cfg(feature = "trace-profile")]
    profile.mark("validate_and_root");
    let table_counts = self.auxiliary_counts(record)?;
    #[cfg(feature = "trace-profile")]
    profile.mark("auxiliary_counts");
    let generate = |ci: usize| {
      #[cfg(feature = "trace-profile")]
      let start = std::time::Instant::now();
      let result = if ci < self.members.len() {
        self.function_witness::<LOOKUPS>(ci, record)
      } else {
        let table = ci - self.members.len();
        let trace = if let Some(table) = self.tables.get(table) {
          table.witness(&table_counts)
        } else {
          self.rom.witness(record, table - self.tables.len())?
        };
        let lookups = if LOOKUPS {
          self.auxiliary_lookups(ci, &trace)
        } else {
          LookupValues::builder(0, &self.lookup_plans[ci].widths).finish()
        };
        Ok((trace, lookups))
      };
      #[cfg(feature = "trace-profile")]
      profile.circuit(ci, start.elapsed());
      result
    };
    #[cfg(feature = "parallel")]
    let results = (0..self.system.circuits.len())
      .into_par_iter()
      .map(generate)
      .collect::<Result<Vec<_>, String>>()?;
    #[cfg(not(feature = "parallel"))]
    let results = (0..self.system.circuits.len())
      .map(generate)
      .collect::<Result<Vec<_>, String>>()?;
    let (traces, lookups): (Vec<_>, Vec<_>) = results.into_iter().unzip();
    #[cfg(feature = "trace-profile")]
    profile.mark("populate_circuits");
    let (active, degrees) = self.trace_shape(&traces)?;
    self.check_shape(&active, &degrees)?;
    #[cfg(feature = "trace-profile")]
    {
      profile.mark("check_shape");
      drop(table_counts);
      profile.mark("cleanup");
      profile.finish(&self.names, LOOKUPS);
    }
    Ok(SystemWitness { traces, lookups })
  }

  fn function_witness<const LOOKUPS: bool>(
    &self,
    ci: usize,
    record: &Execution<B>,
  ) -> Result<(RowMajorMatrix<Val>, LookupValues<Val>), String> {
    let mut rows = vec![];
    for &function in &self.members[ci] {
      rows.extend(
        (0..record.queries.tables[function].len())
          .map(|query| (function, query)),
      );
    }
    let height = if rows.is_empty() {
      0
    } else {
      rows.len().checked_next_power_of_two().ok_or("trace height overflow")?
    };
    let width = self.system.circuits[ci].main_width;
    let mut values =
      Val::zero_vec(height.checked_mul(width).ok_or("trace size overflow")?);
    let lookup_plan = &self.lookup_plans[ci];
    let mut builder = LookupValues::builder(
      if LOOKUPS { height } else { 0 },
      &lookup_plan.widths,
    );
    let mut writers = builder.rows_mut();
    let populate = |worker: &mut Worker<B::Element>,
                    batch: usize,
                    cells: &mut [Val],
                    lookups: &mut [LookupRowMut<'_, Val>]| {
      for (i, row) in cells.chunks_mut(width).enumerate() {
        let (function, query) = rows[batch * ROW_BATCH + i];
        let table = &record.queries.tables[function];
        let output = table.output(query);
        if output.multiplicity >= Val::ORDER_U64 {
          return Err("function count reaches field characteristic".into());
        }
        let placement = &self.placements[self.plan.members[function]];
        self.plan.fills[function]
          .fill_into(
            record,
            (table.input(query), output),
            &mut worker.scratch,
            &mut worker.buffer,
            |column, value| {
              row[placement.columns[column]] = B::into_stark(value)
            },
          )
          .map_err(|e| {
            format!(
              "{} query {query}: {e}",
              self.plan.artifact.functions[function].name
            )
          })?;
        placement.finish(row, output.multiplicity);
        if LOOKUPS {
          lookup_plan.fill(row, &[], worker, &mut lookups[i]);
        }
      }
      Ok::<_, String>(())
    };
    let real_values = &mut values[..rows.len() * width];
    let real_writers =
      if LOOKUPS { &mut writers[..rows.len()] } else { &mut [] };
    #[cfg(feature = "parallel")]
    if LOOKUPS {
      real_values
        .par_chunks_mut(width * ROW_BATCH)
        .zip(real_writers.par_chunks_mut(ROW_BATCH))
        .enumerate()
        .try_for_each_init(
          Worker::<B::Element>::default,
          |worker, (batch, (cells, lookups))| {
            populate(worker, batch, cells, lookups)
          },
        )?;
    } else {
      real_values
        .par_chunks_mut(width * ROW_BATCH)
        .enumerate()
        .try_for_each_init(
          Worker::<B::Element>::default,
          |worker, (batch, cells)| populate(worker, batch, cells, &mut []),
        )?;
    }
    #[cfg(not(feature = "parallel"))]
    {
      let mut worker = Worker::<B::Element>::default();
      if LOOKUPS {
        for (batch, (cells, lookups)) in real_values
          .chunks_mut(width * ROW_BATCH)
          .zip(real_writers.chunks_mut(ROW_BATCH))
          .enumerate()
        {
          populate(&mut worker, batch, cells, lookups)?;
        }
      } else {
        for (batch, cells) in
          real_values.chunks_mut(width * ROW_BATCH).enumerate()
        {
          populate(&mut worker, batch, cells, &mut [])?;
        }
      }
    }
    drop(writers);
    Ok((RowMajorMatrix::new(values, width), builder.finish()))
  }

  pub(super) fn auxiliary_lookups(
    &self,
    ci: usize,
    trace: &RowMajorMatrix<Val>,
  ) -> LookupValues<Val> {
    let plan = &self.lookup_plans[ci];
    let mut builder = LookupValues::builder(trace.height(), &plan.widths);
    let mut writers = builder.rows_mut();
    let fixed = self.system.circuits[ci].preprocessed.as_ref();
    let populate = |worker: &mut Worker<B::Element>,
                    batch: usize,
                    lookups: &mut [LookupRowMut<'_, Val>]| {
      for (i, lookup) in lookups.iter_mut().enumerate() {
        let r = batch * ROW_BATCH + i;
        let row = &trace.values[r * trace.width..(r + 1) * trace.width];
        let fixed_row =
          fixed.map_or(&[][..], |f| &f.values[r * f.width..(r + 1) * f.width]);
        plan.fill(row, fixed_row, worker, lookup);
      }
    };
    #[cfg(feature = "parallel")]
    writers.par_chunks_mut(ROW_BATCH).enumerate().for_each_init(
      Worker::<B::Element>::default,
      |worker, (batch, lookups)| populate(worker, batch, lookups),
    );
    #[cfg(not(feature = "parallel"))]
    {
      let mut worker = Worker::<B::Element>::default();
      for (batch, lookups) in writers.chunks_mut(ROW_BATCH).enumerate() {
        populate(&mut worker, batch, lookups);
      }
    }
    drop(writers);
    builder.finish()
  }
}
