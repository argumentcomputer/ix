//! Memoized evaluation. A query is (callable ID, flat arguments); its first
//! completed output is reused. Counts are integers, never field elements.
use crate::bytecode::{Binary as BinOp, CheckedProgram, Instruction, Type};
use crate::field::{FieldBackend, PrimeField};
use crate::hints::{BoundHints, HintEntry, HintSite, PreparedHints};
use crate::memory::Memory;
use crate::query::QueryMap;
use crate::value::Value;
use serde::Serialize;
use std::fmt;

pub(crate) mod dispatch;

#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize)]
pub struct QueryInput<F = u64> {
  pub function: usize,
  pub args: Vec<F>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct QueryOutput<F = u64> {
  pub output: Vec<F>,
  pub multiplicity: u64,
}
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize)]
pub struct Cell<F = u64> {
  pub r#type: Type,
  pub value: Vec<F>,
}
#[derive(Clone, Debug, Serialize)]
pub struct MemoryEntry<F = u64> {
  pub address: usize,
  pub cell: Cell<F>,
  pub multiplicity: u64,
}
#[derive(Clone, Debug)]
pub struct Execution<B: FieldBackend = PrimeField> {
  pub output: Vec<B::Element>,
  pub queries: QueryMap<B>,
  /// Pointers are local to each payload width; record indices are separate.
  pub memory: Memory<B::Element>,
  pub instructions: u64,
  pub(crate) hints: std::sync::Arc<BoundHints<B::Element>>,
  pub(crate) deferred: Option<Deferred<B::Element>>,
}

/// Unit calls owned by another record remain lookup demands in the circuit.
/// The host may defer only this callable; no result or pointer is fabricated.
#[derive(Clone, Debug)]
pub struct Partition<F> {
  pub function: usize,
  pub owned: Vec<Vec<F>>,
  pub memory_start: u64,
  pub memory_end: u64,
  /// The honest heights of the deferred calls, from [`owned_heights`]
  /// over every record's first execution (depth pass, design §9). `None`
  /// in that first execution, which leaves them out of its heights.
  pub heights: Option<rustc_hash::FxHashMap<Vec<F>, u64>>,
}
#[derive(Clone, Debug)]
pub(crate) struct Deferred<F: Eq + std::hash::Hash> {
  function: usize,
  calls: rustc_hash::FxHashMap<Vec<F>, u64>,
  // Owned call to the first calls of `function` it reaches, each with the
  // longest call path to it (its offset, in calls).
  edges: rustc_hash::FxHashMap<(Vec<F>, Vec<F>), u64>,
  // First owned calls reachable through a non-owned query, with offsets.
  // Cache hits must replay these dependencies even though they do not
  // execute the query.
  dependencies: rustc_hash::FxHashMap<
    (usize, usize),
    rustc_hash::FxHashMap<Vec<F>, u64>,
  >,
  heights: Option<rustc_hash::FxHashMap<Vec<F>, u64>>,
}
impl<F: Copy + Eq + std::hash::Hash> Deferred<F> {
  /// Record that the open query `(function, row)` (arguments `source`)
  /// reaches the call `target` of the deferrable function through `offset`
  /// calls. Owned queries keep the longest offset per target as a
  /// cross-record edge; others keep it until they return to their caller.
  fn dependency(
    &mut self,
    function: usize,
    row: usize,
    source: &[F],
    target: &[F],
    offset: u64,
    budget: &crate::budget::Budget,
  ) -> Result<(), crate::budget::BudgetError> {
    if function == self.function {
      let edge = (source.to_vec(), target.to_vec());
      if let Some(known) = self.edges.get_mut(&edge) {
        *known = (*known).max(offset);
      } else {
        budget.reserve(
          (source.len() + target.len()).saturating_mul(size_of::<F>()) + 200,
        )?;
        self.edges.insert(edge, offset);
      }
    } else {
      if !self.dependencies.contains_key(&(function, row)) {
        budget.reserve(256)?;
      }
      let map = self.dependencies.entry((function, row)).or_default();
      if let Some(known) = map.get_mut(target) {
        *known = (*known).max(offset);
      } else {
        budget.reserve(target.len().saturating_mul(size_of::<F>()) + 104)?;
        map.insert(target.to_vec(), offset);
      }
    }
    Ok(())
  }
}

/// Every owned call's honest height across records (design §9). Each
/// record's first execution gives `base`, an owned call's height ignoring
/// the calls deferred to other records, and `edges`: an owned call `a`
/// reaches the call `b` of the deferrable function, first on its path,
/// through at most `offset` calls, all within one SCC. Heights then satisfy
/// `height(a) = max(base(a), max height(b) + offset)` over `a`'s edges, which
/// is the longest path in the owned-call graph. That graph must be acyclic;
/// a cycle, like an edge to a call that no record owns, is an error.
pub fn owned_heights<K: Clone + Eq + std::hash::Hash>(
  base: &rustc_hash::FxHashMap<K, u64>,
  edges: &[(K, K, u64)],
) -> Result<rustc_hash::FxHashMap<K, u64>, String> {
  let index: rustc_hash::FxHashMap<&K, usize> =
    base.keys().enumerate().map(|(i, k)| (k, i)).collect();
  let keys: Vec<&K> = base.keys().collect();
  let mut callees = vec![vec![]; keys.len()];
  let mut callers = vec![vec![]; keys.len()];
  let mut pending = vec![0usize; keys.len()];
  for (a, b, offset) in edges {
    let (Some(&a), Some(&b)) = (index.get(a), index.get(b)) else {
      return Err("owned-call edge to a call no record owns".into());
    };
    callees[a].push((b, *offset));
    callers[b].push(a);
    pending[a] += 1;
  }
  let mut heights: Vec<u64> = keys.iter().map(|k| base[*k]).collect();
  let mut ready: Vec<usize> = (0..keys.len()).filter(|&i| pending[i] == 0).collect();
  let mut done = 0;
  while let Some(b) = ready.pop() {
    done += 1;
    for &(c, offset) in &callees[b] {
      let height = heights[c].checked_add(offset).ok_or("height overflow")?;
      heights[b] = heights[b].max(height);
    }
    for &a in &callers[b] {
      pending[a] -= 1;
      if pending[a] == 0 {
        ready.push(a);
      }
    }
  }
  if done != keys.len() {
    return Err("recursive owned-call cycle crosses worker records".into());
  }
  Ok(keys.into_iter().cloned().zip(heights).collect())
}

impl<B: FieldBackend> Execution<B> {
  pub fn deferred_calls(&self) -> impl Iterator<Item = (&[B::Element], u64)> {
    self
      .deferred
      .iter()
      .flat_map(|d| d.calls.iter().map(|(k, &n)| (k.as_slice(), n)))
  }
  pub fn partition_edges(
    &self,
  ) -> impl Iterator<Item = (&[B::Element], &[B::Element])> {
    self.partition_offsets().map(|(a, b, _)| (a, b))
  }
  /// The cross-record edges with their offsets, for [`owned_heights`].
  pub fn partition_offsets(
    &self,
  ) -> impl Iterator<Item = (&[B::Element], &[B::Element], u64)> {
    self.deferred.iter().flat_map(|d| {
      d.edges.iter().map(|((a, b), &w)| (a.as_slice(), b.as_slice(), w))
    })
  }
  /// The recorded height of a completed query of `function`: the longest
  /// call path below it within its SCC (zero without a depth word).
  pub fn query_depth(&self, function: usize, args: &[B::Element]) -> Option<u64> {
    let table = self.queries.tables.get(function)?;
    if table.static_map.is_some() {
      return None;
    }
    let row = table.lookup(args).1?;
    (table.count(row) != 0).then(|| table.depth(row))
  }
  /// A deferred call's height, as the coordinator supplied it.
  pub(crate) fn deferred_height(
    &self,
    function: usize,
    args: &[B::Element],
  ) -> Option<u64> {
    let deferred = self.deferred.as_ref()?;
    if deferred.function != function || !deferred.calls.contains_key(args) {
      return None;
    }
    deferred.heights.as_ref()?.get(args).copied()
  }
  /// The function whose calls this record defers to other records, if any.
  #[cfg(feature = "cuda")]
  pub(crate) fn deferred_function(&self) -> Option<usize> {
    self.deferred.as_ref().filter(|d| !d.calls.is_empty()).map(|d| d.function)
  }
  pub(crate) fn is_deferred(
    &self,
    function: usize,
    args: &[B::Element],
  ) -> bool {
    self
      .deferred
      .as_ref()
      .is_some_and(|d| d.function == function && d.calls.contains_key(args))
  }
  /// Absorb callers' counts only after all owned calls have completed. Missing
  /// owners, overflow and a deferred answer cannot become a completed query.
  pub fn absorb_deferred(
    &mut self,
    function: usize,
    args: &[B::Element],
    count: u64,
  ) -> Result<(), String> {
    if self.is_deferred(function, args) {
      return Err("owner deferred its own call".into());
    }
    let table =
      self.queries.tables.get_mut(function).ok_or("unknown owner function")?;
    if table.widths().1 != 0 {
      return Err("deferred call has a non-unit result".into());
    }
    let row = table.lookup(args).1.ok_or("deferred call has no owning row")?;
    table
      .adjust_count(row, count, true)
      .ok_or("deferred multiplicity overflow")?;
    Ok(())
  }
}
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ExecutionError {
  pub function: String,
  pub instruction: usize,
  pub message: String,
  #[serde(skip)]
  pub resource: Option<crate::budget::BudgetError>,
}
impl fmt::Display for ExecutionError {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(
      f,
      "{} at instruction {}: {}",
      self.function, self.instruction, self.message
    )
  }
}
impl std::error::Error for ExecutionError {}
impl From<crate::budget::BudgetError> for ExecutionError {
  fn from(error: crate::budget::BudgetError) -> Self {
    Self {
      function: "<storage>".into(),
      instruction: 0,
      message: error.to_string(),
      resource: Some(error),
    }
  }
}

struct Frame<'a, F> {
  function: usize,
  query: usize,
  registers: Vec<F>,
  pc: usize,
  cursor: usize,
  destination: &'a [usize],
  // The query's height so far: one more than its highest callee in its SCC.
  depth: u64,
}
struct Machine<'a, 'p, B: FieldBackend> {
  #[cfg(feature = "function-profile")]
  profile: Option<&'p mut crate::function_profile::FunctionProfiler>,
  _profile_lifetime: std::marker::PhantomData<&'p ()>,
  program: &'a CheckedProgram<B>,
  frames: Vec<Frame<'a, B::Element>>,
  spare_registers: Vec<Vec<B::Element>>,
  arguments: Vec<B::Element>,
  output_buffer: Vec<B::Element>,
  record: Execution<B>,
  hints: &'a [Vec<Option<HintSite<B::Element>>>],
  dispatch: &'a [Vec<dispatch::Dispatch<B::Element>>],
  ownership: Option<(usize, rustc_hash::FxHashSet<Vec<B::Element>>)>,
  // Function SCCs of the depth circuits, when heights are recorded.
  sccs: Option<&'a [u32]>,
}

enum Request {
  Started,
  Cached(usize),
  Deferred,
}
impl<F: Copy> Frame<'_, F> {
  #[inline]
  fn write(&mut self, dest: &[usize], values: &[F]) {
    debug_assert_eq!(dest.len(), values.len());
    if let ([reg], [value]) = (dest, values) {
      self.registers[*reg] = *value;
      return;
    }
    for (reg, value) in dest.iter().zip(values) {
      self.registers[*reg] = *value;
    }
  }
}
impl<B: FieldBackend> CheckedProgram<B> {
  /// A fresh execution session. No cache or pointer can leak across sessions.
  pub fn execute(
    &self,
    entry: &str,
    args: Vec<B::Element>,
  ) -> Result<Execution<B>, ExecutionError> {
    self.execute_with_hints(entry, args, &[])
  }

  /// Witness data and query caches belong to this invocation alone. Supplied
  /// data is validated before execution, including unused rows and conflicts.
  pub fn execute_with_hints(
    &self,
    entry: &str,
    args: Vec<B::Element>,
    hints: &[HintEntry],
  ) -> Result<Execution<B>, ExecutionError> {
    let error = |message| ExecutionError {
      function: entry.into(),
      instruction: 0,
      resource: None,
      message,
    };
    let selected = self.entry(entry).map_err(error)?;
    self.inputs[selected.function]
      .validate(&args, self.field)
      .map_err(error)?;
    let hints = self.prepare_hints(hints).map_err(error)?;
    hints.execute(entry, args)
  }

  pub fn execute_values(
    &self,
    entry: &str,
    args: &[Value],
  ) -> Result<Execution<B>, ExecutionError> {
    self.execute_values_with_hints(entry, args, &[])
  }

  pub fn execute_values_with_hints(
    &self,
    entry: &str,
    args: &[Value],
    hints: &[HintEntry],
  ) -> Result<Execution<B>, ExecutionError> {
    let error = |message| ExecutionError {
      function: entry.into(),
      instruction: 0,
      resource: None,
      message,
    };
    let selected = self.entry(entry).map_err(error)?;
    if args.len() != selected.inputs.len() {
      return Err(error("entry argument count mismatch".into()));
    }
    let mut flat = vec![];
    for (value, ty) in args.iter().zip(&selected.inputs) {
      flat.extend(ty.flatten(value, self.field).map_err(error)?);
    }
    self.execute_with_hints(entry, flat, hints)
  }

  pub fn output_value(
    &self,
    entry: &str,
    result: &Execution<B>,
  ) -> Result<Value, String> {
    let ty = self
      .entry(entry)?
      .output
      .as_ref()
      .ok_or("entry result contains opaque types or pointers")?;
    ty.unflatten(&result.output, self.field)
  }
}

impl<B: FieldBackend> PreparedHints<'_, B> {
  /// Execute with previously validated hints and a fresh query record/ROM.
  pub fn execute(
    &self,
    entry: &str,
    args: Vec<B::Element>,
  ) -> Result<Execution<B>, ExecutionError> {
    self.execute_inner(
      entry,
      args,
      None,
      None,
      #[cfg(feature = "function-profile")]
      None,
    )
  }

  /// Execute under a shared record reservation. Its storage keeps the charge
  /// alive after the worker hands the record to a prover on another thread.
  pub fn execute_reserved(
    &self,
    entry: &str,
    args: Vec<B::Element>,
    reservation: &crate::budget::RecordReservation,
  ) -> Result<Execution<B>, ExecutionError> {
    self.execute_inner(
      entry,
      args,
      Some(reservation),
      None,
      #[cfg(feature = "function-profile")]
      None,
    )
  }

  pub fn execute_partition(
    &self,
    entry: Option<(&str, Vec<B::Element>)>,
    partition: Partition<B::Element>,
    reservation: Option<&crate::budget::RecordReservation>,
  ) -> Result<Execution<B>, ExecutionError> {
    let (name, args) = entry.unwrap_or(("", vec![]));
    self.execute_inner(
      name,
      args,
      reservation,
      Some(partition),
      #[cfg(feature = "function-profile")]
      None,
    )
  }

  #[cfg(feature = "function-profile")]
  pub fn execute_profiled(
    &self,
    entry: &str,
    args: Vec<B::Element>,
    profile: &mut crate::function_profile::FunctionProfiler,
  ) -> Result<Execution<B>, ExecutionError> {
    self.execute_inner(entry, args, None, None, Some(profile))
  }

  fn execute_inner(
    &self,
    entry: &str,
    args: Vec<B::Element>,
    reservation: Option<&crate::budget::RecordReservation>,
    partition: Option<Partition<B::Element>>,
    #[cfg(feature = "function-profile")] profile: Option<
      &mut crate::function_profile::FunctionProfiler,
    >,
  ) -> Result<Execution<B>, ExecutionError> {
    let error = |message| ExecutionError {
      function: entry.into(),
      instruction: 0,
      resource: None,
      message,
    };
    let root = if partition.is_some() && entry.is_empty() {
      None
    } else {
      let selected = self.program.entry(entry).map_err(error)?;
      self.program.inputs[selected.function]
        .validate(&args, self.program.field)
        .map_err(error)?;
      Some(QueryInput { function: selected.function, args })
    };
    if let Some(p) = &partition {
      if p.function >= self.program.program.functions.len()
        || self.program.outputs[p.function].width() != 0
      {
        return Err(error(
          "partition requires an ordinary unit-returning function".into(),
        ));
      }
      if p.memory_end > self.program.field.modulus() {
        return Err(error("partition exceeds field".into()));
      }
      for args in &p.owned {
        self.program.inputs[p.function]
          .validate(args, self.program.field)
          .map_err(error)?;
      }
    }
    let mut queries = QueryMap::new(
      self
        .program
        .inputs
        .iter()
        .zip(&self.program.outputs)
        .map(|(a, b)| (a.width(), b.width())),
      self.program.field,
    );
    queries.reserve_with(reservation);
    if let Some(sccs) = &self.program.depth {
      queries.track_depth(sccs);
    }
    for map in &self.maps {
      queries.budget.reserve(map.rows().saturating_mul(size_of::<u64>()))?;
    }
    queries.bind_maps(&self.maps);
    let mut memory = Memory::new(
      self
        .program
        .memory_types
        .iter()
        .map(|(ty, layout)| (ty.clone(), layout.width())),
    );
    memory.budget = queries.budget.clone();
    if let Some(p) = &partition {
      memory
        .set_range(p.memory_start, p.memory_end)
        .map_err(|e| error(e.into()))?;
    }
    let mut machine = Machine {
      #[cfg(feature = "function-profile")]
      profile,
      _profile_lifetime: std::marker::PhantomData,
      program: self.program,
      frames: vec![],
      spare_registers: vec![],
      arguments: vec![],
      output_buffer: vec![],
      hints: &self.bindings.sites,
      dispatch: &self.dispatch,
      ownership: partition
        .as_ref()
        .map(|p| (p.function, p.owned.iter().cloned().collect())),
      sccs: self.program.depth.as_deref(),
      record: Execution {
        hints: self.bindings.clone(),
        output: vec![],
        queries,
        memory,
        instructions: 0,
        deferred: partition.as_ref().map(|p| Deferred {
          function: p.function,
          calls: Default::default(),
          edges: Default::default(),
          dependencies: Default::default(),
          heights: p.heights.clone(),
        }),
      },
    };
    if let Some(root) = root {
      machine.run_query(root)?;
    }
    if let Some(partition) = partition {
      let output = std::mem::take(&mut machine.record.output);
      let mut artificial = Vec::new();
      for args in partition.owned {
        if machine.record.queries.tables[partition.function]
          .lookup(&args)
          .1
          .is_some()
        {
          continue;
        }
        machine.run_query(QueryInput {
          function: partition.function,
          args: args.clone(),
        })?;
        artificial.push(args);
      }
      let table = &mut machine.record.queries.tables[partition.function];
      for args in artificial {
        let row = table.lookup(&args).1.unwrap();
        table
          .adjust_count(row, 1, false)
          .ok_or_else(|| error("missing artificial root count".into()))?;
      }
      machine.record.output = output;
    }
    Ok(machine.record)
  }
}
impl<'a, B: FieldBackend> Machine<'a, '_, B> {
  #[inline(always)]
  fn finish_return(&mut self) -> Result<(), ExecutionError> {
    let frame = self.frames.last().unwrap();
    self.program.outputs[frame.function]
      .validate_registers(&self.arguments, self.program.field)
      .map_err(|e| self.error(e))?;
    let frame = self.frames.pop().unwrap();
    if self.record.deferred.is_some() {
      self.propagate_dependencies(frame.function, frame.query)?;
    }
    let intra = self
      .frames
      .last()
      .is_some_and(|parent| self.intra(parent.function, frame.function));
    if let Some(parent) = self.frames.last_mut() {
      parent.write(frame.destination, &self.arguments);
      if intra {
        parent.depth = parent.depth.max(frame.depth.saturating_add(1));
      }
    } else {
      self.record.output = self.arguments.clone();
    }
    let table = &mut self.record.queries.tables[frame.function];
    table.finish(frame.query, &self.arguments);
    table.set_depth(frame.query, frame.depth);
    self.spare_registers.push(frame.registers);
    #[cfg(feature = "function-profile")]
    if let Some(profile) = &mut self.profile {
      profile.exit(false);
    }
    Ok(())
  }

  fn error(&self, message: impl Into<String>) -> ExecutionError {
    let (function, instruction) =
      self.frames.last().map_or(("<entry>".into(), 0), |f| {
        (
          self
            .program
            .callable_name(f.function)
            .unwrap_or("<unknown>")
            .to_owned(),
          f.pc,
        )
      });
    ExecutionError {
      function,
      instruction,
      message: message.into(),
      resource: None,
    }
  }

  /// Whether a call from `caller` to `callee` stays within an SCC of the
  /// depth circuits, so that the callee's height bounds the caller's.
  #[inline(always)]
  fn intra(&self, caller: usize, callee: usize) -> bool {
    self.sccs.is_some_and(|s| {
      let scc = s.get(callee).copied().unwrap_or(crate::trace::depth::NO_SCC);
      scc != crate::trace::depth::NO_SCC && s.get(caller) == Some(&scc)
    })
  }

  fn propagate_dependencies(
    &mut self,
    function: usize,
    row: usize,
  ) -> Result<(), ExecutionError> {
    let Some(deferred) = &mut self.record.deferred else { return Ok(()) };
    if function != deferred.function
      && let Some(dependencies) = deferred.dependencies.remove(&(function, row))
    {
      if let Some(parent) = self.frames.last() {
        let source =
          self.record.queries.tables[parent.function].input(parent.query);
        for (target, &offset) in &dependencies {
          deferred.dependency(
            parent.function,
            parent.query,
            source,
            target,
            offset.saturating_add(1),
            &self.record.queries.budget,
          )?;
        }
      }
      deferred.dependencies.insert((function, row), dependencies);
    }
    Ok(())
  }

  /// Hit: return the existing output and increment only this query's count.
  /// Miss: reserve a stable query ID, then start a function frame.
  /// Multiplicity zero marks an in-progress query, whose output cannot be used.
  #[inline(always)]
  fn request(
    &mut self,
    function_id: usize,
    destination: &'a [usize],
  ) -> Result<Request, ExecutionError> {
    debug_assert!(function_id < self.program.program.functions.len());
    #[cfg(feature = "function-profile")]
    if let Some(profile) = &mut self.profile {
      profile.enter(function_id);
    }
    if let Some(deferred) = &mut self.record.deferred
      && deferred.function == function_id
      && let Some(parent) = self.frames.last()
    {
      let source =
        self.record.queries.tables[parent.function].input(parent.query);
      deferred.dependency(
        parent.function,
        parent.query,
        source,
        &self.arguments,
        1,
        &self.record.queries.budget,
      )?;
    }
    let intra = self
      .frames
      .last()
      .is_some_and(|parent| self.intra(parent.function, function_id));
    if let Some((callee, owned)) = &self.ownership
      && *callee == function_id
      && !owned.contains(&self.arguments)
    {
      let calls = &mut self.record.deferred.as_mut().unwrap().calls;
      if !calls.contains_key(&self.arguments) {
        self.record.queries.budget.reserve(
          self.arguments.len().saturating_mul(size_of::<B::Element>()) + 96,
        )?;
      }
      let count = calls.entry(self.arguments.clone()).or_default();
      *count = count.checked_add(1).ok_or_else(|| ExecutionError {
        function: "<deferred>".into(),
        instruction: 0,
        resource: None,
        message: "deferred count overflow".into(),
      })?;
      // The owner's height bounds the caller's once the coordinator has
      // supplied it; the first execution leaves deferred calls out.
      if intra
        && let Some(heights) = &self.record.deferred.as_ref().unwrap().heights
      {
        let height = *heights
          .get(&self.arguments)
          .ok_or_else(|| self.error("deferred call has no supplied height"))?;
        let parent = self.frames.last_mut().unwrap();
        parent.depth = parent.depth.max(height.saturating_add(1));
      }
      return Ok(Request::Deferred);
    }
    let budget = &self.record.queries.budget;
    let table = &mut self.record.queries.tables[function_id];
    let (hash, found) = table.lookup(&self.arguments);
    if let Some(id) = found {
      if table.count(id) == 0 {
        return Err(self.error("recursive query is already being evaluated"));
      }
      table.bump(id).ok_or_else(|| ExecutionError {
        function: "<query>".into(),
        instruction: 0,
        resource: None,
        message: "query multiplicity overflow".into(),
      })?;
      if intra {
        let height = table.depth(id);
        let parent = self.frames.last_mut().unwrap();
        parent.depth = parent.depth.max(height.saturating_add(1));
      }
      if self.record.deferred.is_some() {
        self.propagate_dependencies(function_id, id)?;
      }
      return Ok(Request::Cached(id));
    }
    let function = &self.program.program.functions[function_id];
    let mut registers = self.spare_registers.pop().unwrap_or_default();
    // The checked bytecode initializes every register before reading it.
    // Keep already initialized spare slots when reusing a larger buffer.
    // Static definite-assignment checking prevents stale slots being read.
    if registers.len() < function.registers {
      budget.vector(&registers, function.registers - registers.len())?;
      registers.resize(function.registers, self.program.field.zero());
    }
    for &(reg, value) in &self.program.initial_registers[function_id] {
      registers[reg] = value;
    }
    registers[..self.arguments.len()].copy_from_slice(&self.arguments);
    let query = table.start(&self.arguments, hash)?;
    budget.vector(&self.frames, 1)?;
    self.frames.push(Frame {
      function: function_id,
      query,
      registers,
      pc: 0,
      cursor: 0,
      destination,
      depth: 0,
    });
    Ok(Request::Started)
  }

  fn run_query(
    &mut self,
    root: QueryInput<B::Element>,
  ) -> Result<(), ExecutionError> {
    if root.function >= self.program.program.functions.len() {
      #[cfg(feature = "function-profile")]
      if let Some(profile) = &mut self.profile {
        profile.enter(root.function);
      }
      self.record.output.resize(
        self.program.outputs[root.function].width(),
        self.program.field.zero(),
      );
      self.record.queries.tables[root.function]
        .static_map
        .as_mut()
        .unwrap()
        .call(&root.args, &mut self.record.output)
        .map_err(|e| self.error(e))?;
      #[cfg(feature = "function-profile")]
      if let Some(profile) = &mut self.profile {
        profile.exit(false);
      }
      return Ok(());
    }
    self.arguments = root.args;
    let request = self.request(root.function, &[])?;
    if !matches!(request, Request::Started) {
      self.record.output = if let Request::Cached(id) = request {
        self.record.queries.tables[root.function].output(id).output.to_vec()
      } else {
        vec![]
      };
      #[cfg(feature = "function-profile")]
      if let Some(profile) = &mut self.profile {
        profile.exit(true);
      }
      return Ok(());
    }
    while !self.frames.is_empty() {
      let frame = self.frames.last().unwrap();
      let step = &self.dispatch[frame.function][frame.cursor];
      self.record.instructions = self
        .record
        .instructions
        .checked_add(step.instructions)
        .ok_or_else(|| self.error("instruction counter overflow"))?;
      let frame = self.frames.last_mut().unwrap();
      frame.pc = step.pc;
      let program = self.program;
      let (memory_type, branch) = match &step.action {
        dispatch::Action::Return { plan } => {
          #[cfg(feature = "function-profile-ops")]
          if let Some(profile) = &mut self.profile {
            profile.operation("return");
          }
          let ret = program.returns[frame.function][*plan].as_ref().unwrap();
          self.arguments.clear();
          self.arguments.extend(ret.values.iter().map(|r| frame.registers[*r]));
          self.finish_return()?;
          continue;
        },
        dispatch::Action::Map { function, call } => {
          #[cfg(feature = "function-profile-ops")]
          if let Some(profile) = &mut self.profile {
            profile.operation("table");
          }
          let map =
            self.record.queries.tables[*function].static_map.as_mut().unwrap();
          call(&mut frame.registers, &mut map.counts).map_err(|message| {
            ExecutionError {
              function: program.callable_name(frame.function).unwrap().into(),
              instruction: frame.pc,
              resource: None,
              message,
            }
          })?;
          frame.pc += 1;
          frame.cursor = step.next;
          continue;
        },
        dispatch::Action::Hint { call } => {
          #[cfg(feature = "function-profile-ops")]
          if let Some(profile) = &mut self.profile {
            profile.operation("hint");
          }
          call(&mut frame.registers).map_err(|message| ExecutionError {
            function: program.callable_name(frame.function).unwrap().into(),
            instruction: frame.pc,
            resource: None,
            message,
          })?;
          frame.pc += 1;
          frame.cursor = step.next;
          continue;
        },
        dispatch::Action::Bytecode { memory_type, branch } => {
          (*memory_type, *branch)
        },
      };
      let instruction =
        &program.execution_functions[frame.function].code[frame.pc];
      use Instruction::{
        AssertEq, Binary, Branch, Call, Copy, Fail, Guard, Hint, Jump, Literal,
        Load, Neg, Ret, Store,
      };
      #[cfg(feature = "function-profile-ops")]
      if let Some(profile) = &mut self.profile {
        profile.operation(match instruction {
          Literal { .. } => "literal",
          Copy { .. } => "copy",
          Neg { .. } => "neg",
          Binary { operator, .. } => match operator {
            BinOp::Add => "add",
            BinOp::Sub => "sub",
            BinOp::Mul => "mul",
            BinOp::Div => "div",
          },
          Guard { .. } => "guard",
          Branch { .. } => "branch",
          Jump { .. } => "jump",
          Call { function, .. }
            if *function >= program.program.functions.len() =>
          {
            "table"
          },
          Call { .. } => "call",
          Store { .. } => "store",
          Load { .. } => "load",
          Hint { .. } => "hint",
          AssertEq { .. } => "assert_eq",
          Ret { .. } => "return",
          Fail { .. } => "fail",
        });
      }
      match instruction {
        Literal { dest, value } => frame.registers[*dest] = *value,
        Copy { dest, source } => {
          self.arguments.clear();
          self.arguments.extend(source.iter().map(|r| frame.registers[*r]));
          frame.write(dest, &self.arguments);
        },
        Neg { dest, source } => {
          frame.registers[*dest] = program.field.neg(frame.registers[*source])
        },
        Binary { dest, operator, left, right } => {
          let (a, b) = (frame.registers[*left], frame.registers[*right]);
          let result = match operator {
            BinOp::Add => program.field.add(a, b),
            BinOp::Sub => program.field.sub(a, b),
            BinOp::Mul => program.field.mul(a, b),
            BinOp::Div => match program.division_inverses[frame.function]
              [frame.pc]
              .or_else(|| program.field.inverse(b))
            {
              Some(inv) => program.field.mul(a, inv),
              None => return Err(self.error("division by zero")),
            },
          };
          frame.registers[*dest] = result;
        },
        Guard { tests, message } => {
          if !tests.iter().all(|(reg, value)| frame.registers[*reg] == *value) {
            return Err(self.error(message));
          }
        },
        Branch { tests, otherwise } => {
          if !tests.iter().all(|(reg, value)| frame.registers[*reg] == *value) {
            frame.pc = *otherwise;
            frame.cursor = branch;
            continue;
          }
        },
        Jump { target } => {
          frame.pc = *target;
          frame.cursor = branch;
          continue;
        },
        Call { function, args, dest } => {
          if let Some(map) =
            &mut self.record.queries.tables[*function].static_map
          {
            self.arguments.clear();
            self.arguments.extend(args.iter().map(|r| frame.registers[*r]));
            self.output_buffer.resize(dest.len(), program.field.zero());
            let result =
              map.call(&self.arguments, &mut self.output_buffer).map(|()| {
                frame.write(dest, &self.output_buffer);
              });
            result.map_err(|message| ExecutionError {
              function: program.callable_name(frame.function).unwrap().into(),
              instruction: frame.pc,
              resource: None,
              message,
            })?;
            frame.pc += 1;
            frame.cursor = step.next;
            continue;
          }
          self.arguments.clear();
          self.arguments.extend(args.iter().map(|r| frame.registers[*r]));
          let parent = self.frames.len() - 1;
          let output = self.request(*function, dest)?;
          self.frames[parent].pc += 1;
          self.frames[parent].cursor = step.next;
          if !matches!(output, Request::Started) {
            if let Request::Cached(id) = output {
              let output =
                self.record.queries.tables[*function].output(id).output;
              self.frames[parent].write(dest, output);
            }
            #[cfg(feature = "function-profile")]
            if let Some(profile) = &mut self.profile {
              profile.exit(true);
            }
          }
          continue;
        },
        Store { value, dest, .. } => {
          self.arguments.clear();
          self.arguments.extend(value.iter().map(|r| frame.registers[*r]));
          program.memory_types[memory_type]
            .1
            .validate_registers(&self.arguments, program.field)
            .map_err(|e| self.error(e))?;
          let index = self
            .record
            .memory
            .intern(memory_type, &self.arguments, program.field.modulus())
            .map_err(|e| match e {
              crate::budget::StorageError::Resource(e) => {
                ExecutionError::from(e)
              },
              crate::budget::StorageError::Invalid(e) => self.error(e),
            })?;
          let address = self.record.memory.address(index) as u64;
          let count = self.record.memory.multiplicity_mut(index);
          *count = count.checked_add(1).ok_or_else(|| ExecutionError {
            function: "<ROM>".into(),
            instruction: 0,
            resource: None,
            message: "ROM multiplicity overflow".into(),
          })?;
          self.frames.last_mut().unwrap().registers[*dest] =
            program.field.from_u64(address);
        },
        Load { pointer, dest, .. } => {
          let address =
            usize::try_from(program.field.to_u64(frame.registers[*pointer]))
              .ok()
              .ok_or_else(|| self.error("ROM address overflow"))?;
          let Some(index) =
            self.record.memory.index_for_type(memory_type, address)
          else {
            return Err(self.error("dangling pointer"));
          };
          let count = self.record.memory.multiplicity_mut(index);
          *count = count.checked_add(1).ok_or_else(|| ExecutionError {
            function: "<ROM>".into(),
            instruction: 0,
            resource: None,
            message: "ROM multiplicity overflow".into(),
          })?;
          let entry = self.record.memory.get(index).unwrap();
          self.frames.last_mut().unwrap().write(dest, entry.cell.value);
        },
        Hint { key, dest, .. } => {
          let site = self.hints[frame.function][frame.pc].as_ref().unwrap();
          self.arguments.clear();
          self.arguments.extend(key.iter().map(|r| frame.registers[*r]));
          self.output_buffer.resize(dest.len(), program.field.zero());
          let result = site
            .evaluate(&self.arguments, &mut self.output_buffer, program.field)
            .map(|()| {
              frame.write(dest, &self.output_buffer);
            });
          result.map_err(|message| ExecutionError {
            function: self.program.program.functions[frame.function]
              .name
              .clone(),
            instruction: frame.pc,
            resource: None,
            message,
          })?;
        },
        AssertEq { left, right, message, runtime_check } => {
          if *runtime_check
            && left
              .iter()
              .zip(right)
              .any(|(a, b)| frame.registers[*a] != frame.registers[*b])
          {
            return Err(self.error(
              message.as_deref().unwrap_or("equality assertion failed"),
            ));
          }
        },
        Ret { value } => {
          self.arguments.clear();
          self.arguments.extend(value.iter().map(|r| frame.registers[*r]));
          self.finish_return()?;
          continue;
        },
        Fail { message } => return Err(self.error(message)),
      }
      let frame = self.frames.last_mut().unwrap();
      frame.pc += 1;
      frame.cursor = step.next;
    }
    Ok(())
  }
}
