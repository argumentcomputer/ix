//! Populate main rows and lookup messages together, directly in backend storage.
//! The lookup writer is compiled from the backend's actual constraint graph;
//! it introduces no alternate message encoding or changes to the circuits.
use super::*;
use multi_stark::{
  expr::{RowOffset, Source},
  graph::{ConstraintGraph, Node},
  lookup::{LookupRowMut, LookupValues},
};
#[derive(Clone, Copy, PartialEq, Eq)]
enum Value {
  Constant(Val),
  Main(usize),
  Preprocessed(usize),
  Scratch(usize),
}
impl Value {
  #[inline]
  fn key(self) -> (u8, u64) {
    match self {
      Self::Constant(value) => (0, value.as_canonical_u64()),
      Self::Main(i) => (1, i as u64),
      Self::Preprocessed(i) => (2, i as u64),
      Self::Scratch(i) => (3, i as u64),
    }
  }
  #[inline]
  fn remap_scratch(self, remap: &[usize]) -> Self {
    match self {
      Self::Scratch(i) => Self::Scratch(remap[i]),
      other => other,
    }
  }
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

#[derive(Clone, Copy, PartialEq, Eq)]
enum Arithmetic {
  Add(Value, Value),
  Sub(Value, Value),
  Mul(Value, Value),
  Neg(Value),
}
impl Arithmetic {
  #[inline]
  fn key(self) -> (u8, (u8, u64), (u8, u64)) {
    match self {
      Self::Add(a, b) => (0, a.key(), b.key()),
      Self::Sub(a, b) => (1, a.key(), b.key()),
      Self::Mul(a, b) => (2, a.key(), b.key()),
      Self::Neg(a) => (3, a.key(), (0, 0)),
    }
  }
  #[inline]
  fn mark_live(self, live: &mut [bool]) {
    let mut mark = |v: Value| {
      if let Value::Scratch(i) = v {
        live[i] = true;
      }
    };
    match self {
      Self::Add(a, b) | Self::Sub(a, b) | Self::Mul(a, b) => {
        mark(a);
        mark(b);
      },
      Self::Neg(a) => mark(a),
    }
  }
  #[inline]
  fn remap_scratch(self, remap: &[usize]) -> Self {
    match self {
      Self::Add(a, b) => {
        Self::Add(a.remap_scratch(remap), b.remap_scratch(remap))
      },
      Self::Sub(a, b) => {
        Self::Sub(a.remap_scratch(remap), b.remap_scratch(remap))
      },
      Self::Mul(a, b) => {
        Self::Mul(a.remap_scratch(remap), b.remap_scratch(remap))
      },
      Self::Neg(a) => Self::Neg(a.remap_scratch(remap)),
    }
  }
}
struct Slot {
  slot: usize,
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
  zero_row_empty: bool,
}

/// A member-specialized lookup writer for one chip in a function circuit.
/// Constant-folds the member's active selector (`= 1`) and inactive members'
/// private/write columns (`= 0`), pruning zero-multiplicity slots and dead
/// arithmetic nodes. `zero_cols` records the main columns assumed to be `0`
/// that are actually read by the circuit's lookup prefix, allowing
/// `auxiliary_lookups` to dispatch safely even on arbitrary traces.
pub(super) struct MemberLookupPlan {
  pub(super) plan: LookupPlan,
  pub(super) selector: usize,
  pub(super) zero_cols: Vec<usize>,
}

impl LookupPlan {
  pub(super) fn compile(graph: &ConstraintGraph<Val>) -> Result<Self, String> {
    Self::compile_specialized(graph, |_| None)
  }

  pub(super) fn compile_specialized(
    graph: &ConstraintGraph<Val>,
    known: impl Fn(usize) -> Option<Val>,
  ) -> Result<Self, String> {
    let mut values = Vec::with_capacity(graph.lookup_prefix_len);
    let mut arithmetic = Vec::new();
    let mut cse: FxHashMap<(u8, (u8, u64), (u8, u64)), Value> =
      FxHashMap::default();
    let emit = |op: Arithmetic,
                arithmetic: &mut Vec<Arithmetic>,
                cse: &mut FxHashMap<(u8, (u8, u64), (u8, u64)), Value>|
     -> Value {
      let key = op.key();
      if let Some(&existing) = cse.get(&key) {
        return existing;
      }
      let val = Value::Scratch(arithmetic.len());
      arithmetic.push(op);
      cse.insert(key, val);
      val
    };
    let mut uses_preprocessed = false;
    for node in &graph.nodes[..graph.lookup_prefix_len] {
      let value = match *node {
        Node::Const(value) => Value::Constant(value),
        Node::Var(col) if col.offset == RowOffset::Current => {
          match col.source {
            Source::Main => {
              let index = col.index as usize;
              known(index).map_or(Value::Main(index), Value::Constant)
            },
            Source::Preprocessed => {
              uses_preprocessed = true;
              Value::Preprocessed(col.index as usize)
            },
            Source::Stage2 => return Err("stage-two lookup input".into()),
          }
        },
        Node::Add(a, b) => match (values[a.index()], values[b.index()]) {
          (Value::Constant(x), Value::Constant(y)) => Value::Constant(x + y),
          (Value::Constant(x), y) if x == Val::ZERO => y,
          (x, Value::Constant(y)) if y == Val::ZERO => x,
          (va, vb) => emit(Arithmetic::Add(va, vb), &mut arithmetic, &mut cse),
        },
        Node::Sub(a, b) => match (values[a.index()], values[b.index()]) {
          (Value::Constant(x), Value::Constant(y)) => Value::Constant(x - y),
          (x, Value::Constant(y)) if y == Val::ZERO => x,
          (x, y) if x == y => Value::Constant(Val::ZERO),
          (Value::Constant(x), y) if x == Val::ZERO => match y {
            Value::Scratch(s)
              if matches!(arithmetic[s], Arithmetic::Neg(_)) =>
            {
              let Arithmetic::Neg(inner) = arithmetic[s] else {
                unreachable!();
              };
              inner
            },
            _ => emit(Arithmetic::Neg(y), &mut arithmetic, &mut cse),
          },
          (va, vb) => emit(Arithmetic::Sub(va, vb), &mut arithmetic, &mut cse),
        },
        Node::Mul(a, b) => match (values[a.index()], values[b.index()]) {
          (Value::Constant(x), Value::Constant(y)) => Value::Constant(x * y),
          (Value::Constant(x), _) | (_, Value::Constant(x))
            if x == Val::ZERO =>
          {
            Value::Constant(Val::ZERO)
          },
          (Value::Constant(x), y) if x == Val::ONE => y,
          (x, Value::Constant(y)) if y == Val::ONE => x,
          (Value::Constant(x), y) | (y, Value::Constant(x))
            if x == Val::NEG_ONE =>
          {
            match y {
              Value::Scratch(s)
                if matches!(arithmetic[s], Arithmetic::Neg(_)) =>
              {
                let Arithmetic::Neg(inner) = arithmetic[s] else {
                  unreachable!();
                };
                inner
              },
              _ => emit(Arithmetic::Neg(y), &mut arithmetic, &mut cse),
            }
          },
          (va, vb) => emit(Arithmetic::Mul(va, vb), &mut arithmetic, &mut cse),
        },
        Node::Neg(a) => match values[a.index()] {
          Value::Constant(x) => Value::Constant(-x),
          Value::Scratch(s) if matches!(arithmetic[s], Arithmetic::Neg(_)) => {
            let Arithmetic::Neg(inner) = arithmetic[s] else {
              unreachable!();
            };
            inner
          },
          va => emit(Arithmetic::Neg(va), &mut arithmetic, &mut cse),
        },
        _ => return Err("lookup requires a nonlocal row input".into()),
      };
      values.push(value);
    }

    let mut raw_slots = Vec::with_capacity(graph.lookups.len());
    let mut widths = Vec::with_capacity(graph.lookups.len());
    for (slot_idx, lookup) in graph.lookups.iter().enumerate() {
      let mut args: Vec<_> =
        lookup.args.iter().map(|id| values[id.index()]).collect();
      // The protocol fingerprints sum(args[i] * gamma^i), so a
      // suffix of compile-time zeros contributes nothing. Message
      // namespaces and callable/type/width IDs still fix its shape.
      while matches!(args.last(), Some(Value::Constant(v)) if *v == Val::ZERO) {
        args.pop();
      }
      widths.push(args.len());
      let multiplicity = values[lookup.multiplicity.index()];
      if multiplicity == Value::Constant(Val::ZERO) {
        continue;
      }
      raw_slots.push((slot_idx, multiplicity, args));
    }

    // Prune dead arithmetic nodes unreachable from surviving lookup slots.
    let mut live = vec![false; arithmetic.len()];
    for &(_, mult, ref args) in &raw_slots {
      if let Value::Scratch(i) = mult {
        live[i] = true;
      }
      for &v in args {
        if let Value::Scratch(i) = v {
          live[i] = true;
        }
      }
    }
    for i in (0..arithmetic.len()).rev() {
      if live[i] {
        arithmetic[i].mark_live(&mut live);
      }
    }
    let mut remap = vec![0usize; arithmetic.len()];
    let mut compact_arith = Vec::new();
    for (i, &op) in arithmetic.iter().enumerate() {
      if live[i] {
        remap[i] = compact_arith.len();
        compact_arith.push(op.remap_scratch(&remap));
      }
    }
    let slots: Vec<_> = raw_slots
      .into_iter()
      .map(|(slot, multiplicity, args)| {
        let remapped_args: Vec<_> =
          args.into_iter().map(|v| v.remap_scratch(&remap)).collect();
        Slot {
          slot,
          multiplicity: multiplicity.remap_scratch(&remap),
          args: Arguments::compile(&remapped_args),
        }
      })
      .collect();

    // Precompute whether an all-zero main row (with no preprocessed columns)
    // produces exclusively zero multiplicities.
    let zero_row_empty = if uses_preprocessed {
      false
    } else {
      let mut zero_scratch = Vec::with_capacity(compact_arith.len());
      let eval_zero = |v: Value, scratch: &[Val]| match v {
        Value::Constant(c) => c,
        Value::Main(_) | Value::Preprocessed(_) => Val::ZERO,
        Value::Scratch(i) => scratch[i],
      };
      for &op in &compact_arith {
        let v = match op {
          Arithmetic::Add(a, b) => {
            eval_zero(a, &zero_scratch) + eval_zero(b, &zero_scratch)
          },
          Arithmetic::Sub(a, b) => {
            eval_zero(a, &zero_scratch) - eval_zero(b, &zero_scratch)
          },
          Arithmetic::Mul(a, b) => {
            eval_zero(a, &zero_scratch) * eval_zero(b, &zero_scratch)
          },
          Arithmetic::Neg(a) => -eval_zero(a, &zero_scratch),
        };
        zero_scratch.push(v);
      }
      slots
        .iter()
        .all(|slot| eval_zero(slot.multiplicity, &zero_scratch) == Val::ZERO)
    };

    Ok(Self { arithmetic: compact_arith, slots, widths, zero_row_empty })
  }

  #[cfg(test)]
  pub(super) fn stats(&self) -> (usize, usize) {
    (self.arithmetic.len(), self.slots.len())
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
    for plan in &self.slots {
      let multiplicity = plan.multiplicity.get(row, fixed, scratch);
      // Zero-multiplicity messages do not affect the lookup argument.
      // Fresh builder storage already contains the empty lookup.
      if multiplicity == Val::ZERO {
        continue;
      }
      worker.lookup_args.clear();
      worker.lookup_args.resize(plan.args.width, Val::ZERO);
      plan.args.fill(row, fixed, scratch, &mut worker.lookup_args);
      lookup.push(plan.slot, multiplicity, &worker.lookup_args);
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
    let mut scratch = Vec::with_capacity(self.arithmetic.len());
    for op in &self.arithmetic {
      let get = |value: Value| value.get(row, fixed, &scratch);
      let value = match *op {
        Arithmetic::Add(a, b) => get(a) + get(b),
        Arithmetic::Sub(a, b) => get(a) - get(b),
        Arithmetic::Mul(a, b) => get(a) * get(b),
        Arithmetic::Neg(a) => -get(a),
      };
      scratch.push(value);
    }
    let mut args = Vec::new();
    for plan in &self.slots {
      let multiplicity = plan.multiplicity.get(row, fixed, &scratch);
      if multiplicity != Val::ZERO {
        args.clear();
        args.resize(plan.args.width, Val::ZERO);
        plan.args.fill(row, fixed, &scratch, &mut args);
        emit(plan.slot, multiplicity, &args);
      }
    }
  }
}

pub(super) fn compile_member_lookup_plans(
  placements: &[grouping::Placement],
  circuits: &[multi_stark::system::Circuit<Val>],
) -> Result<Vec<MemberLookupPlan>, String> {
  placements
    .iter()
    .map(|placement| {
      let circuit = &circuits[placement.circuit];
      let main_width = circuit.main_width;
      let mut written = vec![false; main_width];
      for &col in &placement.columns {
        written[col] = true;
      }
      for write in &placement.writes {
        written[write.column] = true;
      }
      written[placement.selector] = true;
      if let Some(last) = written.last_mut() {
        *last = true;
      }
      let mut used_main = vec![false; main_width];
      for node in &circuit.graph.nodes[..circuit.graph.lookup_prefix_len] {
        if let Node::Var(col) = *node
          && col.offset == RowOffset::Current
          && matches!(col.source, Source::Main)
          && let Some(slot) = used_main.get_mut(col.index as usize)
        {
          *slot = true;
        }
      }
      let zero_cols: Vec<usize> = (0..main_width.saturating_sub(1))
        .filter(|&col| !written[col] && used_main[col])
        .collect();
      let plan = LookupPlan::compile_specialized(&circuit.graph, |col| {
        if col == placement.selector {
          Some(Val::ONE)
        } else if col + 1 < main_width && !written[col] {
          Some(Val::ZERO)
        } else {
          None
        }
      })?;
      Ok(MemberLookupPlan { plan, selector: placement.selector, zero_cols })
    })
    .collect()
}

struct Worker<F> {
  scratch: Vec<F>,
  buffer: Vec<F>,
  // A depth circuit's row, before placement.
  row: Vec<F>,
  lookup_scratch: Vec<Val>,
  lookup_args: Vec<Val>,
}

impl<F> Default for Worker<F> {
  fn default() -> Self {
    Self {
      scratch: Default::default(),
      buffer: Default::default(),
      row: Default::default(),
      lookup_scratch: Default::default(),
      lookup_args: Default::default(),
    }
  }
}

/// A few rows per task amortize scheduling and scratch allocation while letting
/// a large circuit use the whole pool alongside the many small circuits.
const ROW_BATCH: usize = 32;

/// An immutable reference to an [`Execution`] already validated against a
/// specific [`Backend`] instance, allowing repeated witness generation without
/// rescanning every query row, depth word, and ROM cell.
pub struct ValidatedRecord<'r, B: WitnessField = PrimeField> {
  backend_id: u64,
  record: &'r Execution<B>,
}

impl<'r, B: WitnessField> ValidatedRecord<'r, B> {
  pub const fn record(&self) -> &'r Execution<B> {
    self.record
  }
}

impl<B: WitnessField> Backend<'_, '_, B> {
  /// Validate `record` once for this backend so subsequent witness calls can
  /// skip whole-record validation scans.
  pub fn validate_record<'r>(
    &self,
    record: &'r Execution<B>,
  ) -> Result<ValidatedRecord<'r, B>, String> {
    self.plan.validate_record(record)?;
    Ok(ValidatedRecord { backend_id: self.id, record })
  }

  /// Generate a complete stage-one witness from an already-validated record.
  pub fn generate_validated(
    &self,
    validated: &ValidatedRecord<'_, B>,
    entry: &str,
    args: &[B::Element],
  ) -> Result<SystemWitness<Val>, String> {
    if validated.backend_id != self.id {
      return Err("record was validated for a different backend".into());
    }
    if self.gpu_lookup_only {
      Ok(self.witness_from_main(
        self.generate_stage_1_validated(validated, entry, args)?,
      ))
    } else {
      self.generate_with_validated::<true>(
        validated.record,
        Some((entry, args)),
        &[],
        &RangeCounts::default(),
        None,
      )
    }
  }

  /// Generate stage-one main traces from an already-validated record.
  pub fn generate_stage_1_validated(
    &self,
    validated: &ValidatedRecord<'_, B>,
    entry: &str,
    args: &[B::Element],
  ) -> Result<Vec<RowMajorMatrix<Val>>, String> {
    if validated.backend_id != self.id {
      return Err("record was validated for a different backend".into());
    }
    Ok(
      self
        .generate_with_validated::<false>(
          validated.record,
          Some((entry, args)),
          &[],
          &RangeCounts::default(),
          None,
        )?
        .traces,
    )
  }

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
      self.generate_with::<true>(
        record,
        Some((entry, args)),
        &[],
        &RangeCounts::default(),
        None,
      )
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
    Ok(
      self
        .generate_with::<false>(
          record,
          Some((entry, args)),
          &[],
          &RangeCounts::default(),
          None,
        )?
        .traces,
    )
  }

  /// Populate stage-one traces directly at pre-padded normalized heights so
  /// callers do not allocate at natural height and resize afterward.
  pub(super) fn generate_stage_1_with_heights(
    &self,
    record: &Execution<B>,
    entry: &str,
    args: &[B::Element],
    min_heights: &[usize],
  ) -> Result<Vec<RowMajorMatrix<Val>>, String> {
    Ok(
      self
        .generate_with::<false>(
          record,
          Some((entry, args)),
          &[],
          &RangeCounts::default(),
          Some(min_heights),
        )?
        .traces,
    )
  }

  /// A worker record may have no public entrypoint of its own. Its unresolved
  /// calls are checked by the combined batch, never by a separate claim.
  #[cfg(test)]
  pub fn generate_record_stage_1(
    &self,
    record: &Execution<B>,
  ) -> Result<Vec<RowMajorMatrix<Val>>, String> {
    Ok(
      self
        .generate_with::<false>(
          record,
          None,
          &[],
          &RangeCounts::default(),
          None,
        )?
        .traces,
    )
  }

  /// Circuits with a `device` height are populated on the GPU; their host
  /// matrices are left empty. `device_ranges` counts the depth range-table
  /// uses of those device rows.
  pub(super) fn generate_with<const LOOKUPS: bool>(
    &self,
    record: &Execution<B>,
    root: Option<(&str, &[B::Element])>,
    device: &[Option<usize>],
    device_ranges: &RangeCounts,
    min_heights: Option<&[usize]>,
  ) -> Result<SystemWitness<Val>, String> {
    self.require_committed()?;
    self.plan.validate_record(record)?;
    self.generate_with_validated::<LOOKUPS>(
      record,
      root,
      device,
      device_ranges,
      min_heights,
    )
  }

  /// Same as [`Self::generate_with`], skipping `validate_record` because the
  /// caller already validated `record` against this backend's plan.
  pub(super) fn generate_with_validated<const LOOKUPS: bool>(
    &self,
    record: &Execution<B>,
    root: Option<(&str, &[B::Element])>,
    device: &[Option<usize>],
    device_ranges: &RangeCounts,
    min_heights: Option<&[usize]>,
  ) -> Result<SystemWitness<Val>, String> {
    self.require_committed()?;
    #[cfg(feature = "trace-profile")]
    let mut profile = super::profile::Phases::new();
    if let Some((entry, args)) = root {
      self.plan.root(record, entry, args)?;
    }
    #[cfg(feature = "trace-profile")]
    profile.mark("validate_and_root");
    let functions = self.members.len();
    let fixed = functions..functions + self.tables.len();
    let empty = |ci: usize| {
      (
        RowMajorMatrix::new(vec![], self.system.circuits[ci].main_width),
        LookupValues::builder(0, &self.lookup_plans[ci].widths).finish(),
      )
    };
    // Fixed tables come last: function population counts the uses of the
    // depth pass's range tables, which execution never calls.
    let generate = |ci: usize| {
      #[cfg(feature = "trace-profile")]
      let start = std::time::Instant::now();
      let min_height = min_heights.map(|heights| heights[ci]);
      let result =
        if device.get(ci).copied().flatten().is_some() || fixed.contains(&ci) {
          let (trace, lookups) = empty(ci);
          Ok((trace, lookups, RangeCounts::default()))
        } else if ci < functions {
          self.function_witness::<LOOKUPS>(ci, record, min_height)
        } else {
          let (trace, active_rows) =
            self.rom.witness_with_active(record, ci - fixed.end, min_height)?;
          let lookups = if LOOKUPS {
            debug_assert!(self.lookup_plans[ci].zero_row_empty);
            self.auxiliary_lookups_rows(ci, &trace, active_rows)
          } else {
            empty(ci).1
          };
          Ok((trace, lookups, RangeCounts::default()))
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
    let mut ranges = device_ranges.clone();
    let mut traces = Vec::with_capacity(results.len());
    let mut lookups = Vec::with_capacity(results.len());
    for (trace, lookup, counts) in results {
      traces.push(trace);
      lookups.push(lookup);
      ranges = ranges.merge(counts);
    }
    #[cfg(feature = "trace-profile")]
    profile.mark("populate_circuits");
    let table_counts = self.auxiliary_counts(record, &ranges)?;
    #[cfg(feature = "trace-profile")]
    profile.mark("auxiliary_counts");
    let table = |ci: usize| {
      let trace = self.tables[ci - functions].witness(&table_counts);
      let lookup =
        if LOOKUPS { self.auxiliary_lookups(ci, &trace) } else { empty(ci).1 };
      (ci, trace, lookup)
    };
    #[cfg(feature = "parallel")]
    let tables: Vec<_> = fixed.clone().into_par_iter().map(table).collect();
    #[cfg(not(feature = "parallel"))]
    let tables: Vec<_> = fixed.clone().map(table).collect();
    for (ci, trace, lookup) in tables {
      traces[ci] = trace;
      lookups[ci] = lookup;
    }
    #[cfg(feature = "trace-profile")]
    profile.mark("fixed_tables");
    let (active, degrees) = self.trace_shape_with(&traces, device)?;
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
    min_height: Option<usize>,
  ) -> Result<(RowMajorMatrix<Val>, LookupValues<Val>, RangeCounts), String> {
    let mut rows = vec![];
    for &function in &self.members[ci] {
      rows.extend(
        (0..record.queries.tables[function].len())
          .map(|query| (function, query)),
      );
    }
    let natural_height = if rows.is_empty() {
      0
    } else {
      rows.len().checked_next_power_of_two().ok_or("trace height overflow")?
    };
    let height = match min_height {
      Some(target) => {
        if natural_height > target {
          return Err(format!(
            "circuit {ci} trace height {natural_height} exceeds normalized height {target}"
          ));
        }
        target
      },
      None => natural_height,
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
    let field = self.plan.program.field;
    let populate = |worker: &mut Worker<B::Element>,
                    ranges: &mut RangeCounts,
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
        let chip = self.plan.members[function];
        let placement = &self.placements[chip];
        let name = &self.plan.artifact.functions[function].name;
        if self.plan.depth.fills[chip].is_empty() {
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
            .map_err(|e| format!("{name} query {query}: {e}"))?;
        } else {
          // Depth columns are computed from the circuit's own columns: fill
          // the depth circuit's row, then place it.
          let source = &mut worker.row;
          let activation = self.plan.artifact.chips[chip].activation;
          source.clear();
          source.resize(activation + 1, field.zero());
          source[activation] = field.one();
          self.plan.fills[function]
            .fill(
              record,
              (table.input(query), output),
              &mut worker.scratch,
              &mut worker.buffer,
              source,
            )
            .and_then(|()| {
              self.plan.depth.fill(
                chip,
                record,
                table.depth(query),
                source,
                field,
                &mut worker.buffer,
                ranges,
              )
            })
            .map_err(|e| format!("{name} query {query}: {e}"))?;
          for (&column, &value) in placement.columns.iter().zip(source.iter()) {
            row[column] = B::into_stark(value);
          }
        }
        placement.finish(row, output.multiplicity);
        if LOOKUPS {
          self.member_lookup_plans[chip].plan.fill(
            row,
            &[],
            worker,
            &mut lookups[i],
          );
        }
      }
      Ok::<_, String>(())
    };
    let real_values = &mut values[..rows.len() * width];
    let real_writers =
      if LOOKUPS { &mut writers[..rows.len()] } else { &mut [] };
    #[cfg(feature = "parallel")]
    let ranges = {
      let start = || (Worker::<B::Element>::default(), RangeCounts::default());
      let merge = |a: RangeCounts, b| Ok::<_, String>(a.merge(b));
      if LOOKUPS {
        real_values
          .par_chunks_mut(width * ROW_BATCH)
          .zip(real_writers.par_chunks_mut(ROW_BATCH))
          .enumerate()
          .try_fold(
            start,
            |(mut worker, mut ranges), (batch, (cells, lookups))| {
              populate(&mut worker, &mut ranges, batch, cells, lookups)?;
              Ok::<_, String>((worker, ranges))
            },
          )
          .map(|state| state.map(|(_, ranges)| ranges))
          .try_reduce(RangeCounts::default, merge)?
      } else {
        real_values
          .par_chunks_mut(width * ROW_BATCH)
          .enumerate()
          .try_fold(start, |(mut worker, mut ranges), (batch, cells)| {
            populate(&mut worker, &mut ranges, batch, cells, &mut [])?;
            Ok::<_, String>((worker, ranges))
          })
          .map(|state| state.map(|(_, ranges)| ranges))
          .try_reduce(RangeCounts::default, merge)?
      }
    };
    #[cfg(not(feature = "parallel"))]
    let ranges = {
      let mut worker = Worker::<B::Element>::default();
      let mut ranges = RangeCounts::default();
      if LOOKUPS {
        for (batch, (cells, lookups)) in real_values
          .chunks_mut(width * ROW_BATCH)
          .zip(real_writers.chunks_mut(ROW_BATCH))
          .enumerate()
        {
          populate(&mut worker, &mut ranges, batch, cells, lookups)?;
        }
      } else {
        for (batch, cells) in
          real_values.chunks_mut(width * ROW_BATCH).enumerate()
        {
          populate(&mut worker, &mut ranges, batch, cells, &mut [])?;
        }
      }
      ranges
    };
    drop(writers);
    Ok((RowMajorMatrix::new(values, width), builder.finish(), ranges))
  }

  pub(super) fn auxiliary_lookups(
    &self,
    ci: usize,
    trace: &RowMajorMatrix<Val>,
  ) -> LookupValues<Val> {
    self.auxiliary_lookups_rows(ci, trace, trace.height())
  }

  fn auxiliary_lookups_rows(
    &self,
    ci: usize,
    trace: &RowMajorMatrix<Val>,
    active_rows: usize,
  ) -> LookupValues<Val> {
    let plan = &self.lookup_plans[ci];
    let mut builder = LookupValues::builder(trace.height(), &plan.widths);
    let mut writers = builder.rows_mut();
    let active_writers = &mut writers[..active_rows];
    let fixed = self.system.circuits[ci].preprocessed.as_ref();
    let chips = self.circuit_chips.get(ci).map(Vec::as_slice);
    let populate = |worker: &mut Worker<B::Element>,
                    batch: usize,
                    lookups: &mut [LookupRowMut<'_, Val>]| {
      for (i, lookup) in lookups.iter_mut().enumerate() {
        let r = batch * ROW_BATCH + i;
        let row = &trace.values[r * trace.width..(r + 1) * trace.width];
        if plan.zero_row_empty && row.iter().all(|&v| v == Val::ZERO) {
          continue;
        }
        let fixed_row =
          fixed.map_or(&[][..], |f| &f.values[r * f.width..(r + 1) * f.width]);
        if let Some(chips) = chips
          && let Some(&chip) = chips.iter().find(|&&chip| {
            let mlp = &self.member_lookup_plans[chip];
            row[mlp.selector] == Val::ONE
              && mlp.zero_cols.iter().all(|&col| row[col] == Val::ZERO)
          })
        {
          self.member_lookup_plans[chip]
            .plan
            .fill(row, fixed_row, worker, lookup);
        } else {
          plan.fill(row, fixed_row, worker, lookup);
        }
      }
    };
    #[cfg(feature = "parallel")]
    active_writers.par_chunks_mut(ROW_BATCH).enumerate().for_each_init(
      Worker::<B::Element>::default,
      |worker, (batch, lookups)| populate(worker, batch, lookups),
    );
    #[cfg(not(feature = "parallel"))]
    {
      let mut worker = Worker::<B::Element>::default();
      for (batch, lookups) in active_writers.chunks_mut(ROW_BATCH).enumerate() {
        populate(&mut worker, batch, lookups);
      }
    }
    drop(writers);
    builder.finish()
  }
}
