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
  pub(crate) hints: std::sync::Arc<BoundHints<B::Element>>,
  pub queries: QueryMap<B>,
  /// Pointers are local to each payload width; record indices are separate.
  pub memory: Memory<B::Element>,
  pub instructions: u64,
  /// Stack a generated native executor touched on its execution thread,
  /// including any heap segments at their full size; zero for the
  /// interpreter, whose frames are heap allocations charged to the record.
  pub native_stack_bytes: usize,
  /// Set by the planner when this record's trace stays on the host although
  /// device population is enabled, or when only some device circuits fit.
  /// Only CUDA builds populate on the device.
  #[cfg_attr(not(feature = "cuda"), allow(dead_code))]
  pub(crate) host_population: HostPopulation,
}

/// A record's population override, kept by value through clones: whether
/// the whole trace stays on the host, and otherwise, when set, which
/// function circuits the device may populate.
#[derive(Debug, Default)]
pub(crate) struct HostPopulation {
  host: std::sync::atomic::AtomicBool,
  circuits: std::sync::RwLock<Option<std::sync::Arc<Vec<bool>>>>,
  /// The device circuits a planner's search admitted, with the identity of
  /// the planning inputs it searched under, so that planning the record
  /// again under the same inputs reuses it.
  admitted: std::sync::Mutex<Option<(String, std::sync::Arc<Admission>)>>,
  /// Whether the device record is uploaded one shard image at a time,
  /// which the planner chooses only when the whole record does not fit.
  sharded: std::sync::atomic::AtomicBool,
}

/// What a planner's population search decided.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct Admission {
  /// The device circuits admitted.
  pub(crate) circuits: Vec<bool>,
}

#[cfg_attr(not(feature = "cuda"), allow(dead_code))]
impl HostPopulation {
  pub(crate) fn get(&self) -> bool {
    self.host.load(std::sync::atomic::Ordering::Acquire)
  }
  pub(crate) fn set(&self, host: bool) {
    self.host.store(host, std::sync::atomic::Ordering::Release);
  }
  /// The device circuits this record admits, or `None` for all.
  pub(crate) fn circuits(&self) -> Option<std::sync::Arc<Vec<bool>>> {
    self
      .circuits
      .read()
      .unwrap_or_else(std::sync::PoisonError::into_inner)
      .clone()
  }
  pub(crate) fn set_circuits(&self, circuits: Option<Vec<bool>>) {
    *self.circuits.write().unwrap_or_else(std::sync::PoisonError::into_inner) =
      circuits.map(std::sync::Arc::new);
  }
  /// What a search under inputs `key` decided, if one ran.
  pub(crate) fn admitted(&self, key: &str) -> Option<Admission> {
    let admitted =
      self.admitted.lock().unwrap_or_else(std::sync::PoisonError::into_inner);
    admitted.as_ref().filter(|(k, _)| k == key).map(|(_, a)| (**a).clone())
  }
  pub(crate) fn set_admitted(&self, key: String, admission: Admission) {
    *self.admitted.lock().unwrap_or_else(std::sync::PoisonError::into_inner) =
      Some((key, std::sync::Arc::new(admission)));
  }
  pub(crate) fn sharded(&self) -> bool {
    self.sharded.load(std::sync::atomic::Ordering::Acquire)
  }
  pub(crate) fn set_sharded(&self, sharded: bool) {
    self.sharded.store(sharded, std::sync::atomic::Ordering::Release);
  }
  /// Whether the device may populate function circuit `ci`.
  pub(crate) fn admits(&self, ci: usize) -> bool {
    self.circuits().is_none_or(|c| c.get(ci).copied().unwrap_or(false))
  }
}

impl Clone for HostPopulation {
  fn clone(&self) -> Self {
    Self {
      host: std::sync::atomic::AtomicBool::new(self.get()),
      circuits: std::sync::RwLock::new(self.circuits()),
      admitted: std::sync::Mutex::new(
        self
          .admitted
          .lock()
          .unwrap_or_else(std::sync::PoisonError::into_inner)
          .clone(),
      ),
      sharded: std::sync::atomic::AtomicBool::new(self.sharded()),
    }
  }
}

/// Query and ROM storage excludes shared program data, hint closures and
/// allocator-retained pages. Hash-table capacity includes control bytes.
#[derive(Clone, Debug, Default, Serialize)]
pub struct RecordStorage {
  pub query_payload_bytes: usize,
  pub query_vector_capacity_bytes: usize,
  pub query_index_estimate_bytes: usize,
  pub rom_payload_bytes: usize,
  pub rom_vector_capacity_bytes: usize,
  pub rom_index_estimate_bytes: usize,
  /// Recorded row references ([`crate::refs`]), as charged.
  pub query_refs_bytes: usize,
}

impl<B: FieldBackend> Execution<B> {
  /// The recorded height of a query of `function` in a finished record: the
  /// longest call path below it within its SCC (zero without a depth word).
  pub fn query_depth(
    &self,
    function: usize,
    args: &[B::Element],
  ) -> Option<u64> {
    let table = self.queries.tables.get(function)?;
    if table.static_map.is_some() {
      return None;
    }
    table.lookup(args).1.map(|row| table.depth(row))
  }

  /// Rows of each query table (zero for fixed tables), then ROM cells, as
  /// whitespace-separated text: the `AIUR_INDEX_SIZES` file that sizes a
  /// later execution's indexes.
  pub fn index_sizes(&self) -> String {
    let rows = self.queries.tables.iter().map(|table| {
      if table.static_map.is_some() { 0 } else { table.len() }
    });
    rows
      .chain([self.memory.len()])
      .map(|n| n.to_string())
      .collect::<Vec<_>>()
      .join(" ")
  }

  pub fn storage_usage(&self) -> RecordStorage {
    let mut usage = RecordStorage::default();
    for table in &self.queries.tables {
      let (payload, capacity, index) = table.storage_usage();
      usage.query_payload_bytes += payload;
      usage.query_vector_capacity_bytes += capacity;
      usage.query_index_estimate_bytes += index;
      usage.query_refs_bytes +=
        table.refs.as_ref().map_or(0, crate::refs::TableRefs::bytes);
    }
    (
      usage.rom_payload_bytes,
      usage.rom_vector_capacity_bytes,
      usage.rom_index_estimate_bytes,
    ) = self.memory.storage_usage();
    usage
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
  // Where this query's references start among the pending ones.
  refs: usize,
  // Its function's reference sites, when it records references.
  records: Option<&'a crate::refs::FunctionRefs>,
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
  // Function SCCs of the depth circuits, when heights are recorded.
  sccs: Option<&'a [u32]>,
  // Which functions record row references, when any do.
  refs: Option<&'a crate::refs::RefPlan>,
  pending: crate::refs::Pending,
}

enum Request {
  Started,
  Cached(usize),
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
    self.execute_inner(entry, args, None, Some(profile))
  }

  /// Empty query tables and ROM for one session, charged to `reservation`.
  pub(crate) fn fresh_storage(
    &self,
    reservation: Option<&crate::budget::RecordReservation>,
  ) -> Result<(QueryMap<B>, Memory<B::Element>), ExecutionError> {
    let columns: Vec<(usize, Vec<bool>)> = self
      .program
      .inputs
      .iter()
      .zip(&self.program.outputs)
      .map(|(inputs, outputs)| {
        let mut narrow = vec![];
        inputs.narrow_words(&mut narrow);
        outputs.narrow_words(&mut narrow);
        (inputs.width(), narrow)
      })
      .collect();
    let mut queries = QueryMap::new(
      columns.iter().map(|(inputs, narrow)| (*inputs, &narrow[..])),
      self.program.field,
    );
    queries.reserve_with(reservation);
    if let Some(sccs) = &self.program.depth {
      queries.track_depth(sccs);
    }
    if let Some(refs) = &self.program.refs {
      queries.record_refs(refs);
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
    // Index sizes of an earlier record of the same claim
    // ([`Execution::index_sizes`]): sizing every index up front avoids the
    // rehashes of growing to them and their transient old-and-new peak.
    if let Some(path) = std::env::var_os("AIUR_INDEX_SIZES") {
      match std::fs::read_to_string(&path).map(|text| {
        text
          .split_whitespace()
          .map(str::parse)
          .collect::<Result<Vec<usize>, _>>()
      }) {
        Ok(Ok(sizes)) if sizes.len() == queries.tables.len() + 1 => {
          memory.reserve_index(sizes[queries.tables.len()])?;
          for (table, &rows) in queries.tables.iter_mut().zip(&sizes) {
            table.reserve_index(rows)?;
          }
        },
        _ => eprintln!(
          "[aiur] ignoring AIUR_INDEX_SIZES={}: not index sizes for this program",
          path.display()
        ),
      }
    }
    Ok((queries, memory))
  }

  fn execute_inner(
    &self,
    entry: &str,
    args: Vec<B::Element>,
    reservation: Option<&crate::budget::RecordReservation>,
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
    let selected = self.program.entry(entry).map_err(error)?;
    self.program.inputs[selected.function]
      .validate(&args, self.program.field)
      .map_err(error)?;
    let root = QueryInput { function: selected.function, args };
    let (queries, memory) = self.fresh_storage(reservation)?;
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
      sccs: self.program.depth.as_deref(),
      refs: self.program.refs.as_deref(),
      pending: crate::refs::Pending::default(),
      record: Execution {
        hints: self.bindings.clone(),
        output: vec![],
        queries,
        memory,
        instructions: 0,
        native_stack_bytes: 0,
        host_population: Default::default(),
      },
    };
    machine.run_query(root)?;
    machine.record.queries.drop_prefetched();
    machine.record.memory.drop_prefetched();
    machine.record.queries.compact_refs()?;
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
    let finished = self.record.queries.tables[frame.function]
      .finish(frame.query, &self.arguments);
    finished.map_err(|e| self.storage_error(&e))?;
    let table = &mut self.record.queries.tables[frame.function];
    table.set_depth(frame.query, frame.depth);
    if let Some(refs) = &mut table.refs {
      let budget = &table.budget;
      self
        .pending
        .take(frame.refs, |pending| refs.finish(frame.query, pending, budget))?;
    }
    self.spare_registers.push(frame.registers);
    #[cfg(feature = "function-profile")]
    if let Some(profile) = &mut self.profile {
      profile.exit(false);
    }
    Ok(())
  }

  fn storage_error(
    &self,
    error: &crate::budget::StorageError,
  ) -> ExecutionError {
    match *error {
      crate::budget::StorageError::Resource(e) => e.into(),
      crate::budget::StorageError::Invalid(e) => self.error(e),
    }
  }

  fn error(&self, message: impl Into<String>) -> ExecutionError {
    if std::env::var_os("AIUR_BACKTRACE").is_some() {
      for frame in self.frames.iter().rev() {
        let name = self.program.callable_name(frame.function).unwrap_or("?");
        let inputs = self.program.inputs[frame.function].width();
        let args: Vec<u64> = frame.registers
          [..inputs.min(frame.registers.len())]
          .iter()
          .map(|v| self.program.field.to_u64(*v))
          .collect();
        eprintln!(
          "  at {name} pc {} query {} args {args:?}",
          frame.pc, frame.query
        );
      }
    }
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
    let intra = self
      .frames
      .last()
      .is_some_and(|parent| self.intra(parent.function, function_id));
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
      self.note(id)?;
      return Ok(Request::Cached(id));
    }
    let function = &self.program.program.functions[function_id];
    let mut registers = self.spare_registers.pop().unwrap_or_default();
    // The checked bytecode initializes every register before reading it.
    // Keep already initialized spare slots when reusing a larger buffer.
    // Static definite-assignment checking prevents stale slots being read.
    if registers.len() < function.registers {
      let extra = function.registers - registers.len();
      budget.vector(&mut registers, extra)?;
      registers.resize(function.registers, self.program.field.zero());
    }
    for &(reg, value) in &self.program.initial_registers[function_id] {
      registers[reg] = value;
    }
    registers[..self.arguments.len()].copy_from_slice(&self.arguments);
    let outputs = table.widths().1;
    let started = table.start(&self.arguments, outputs, hash);
    let query = started.map_err(|e| self.storage_error(&e))?;
    self.note(query)?;
    let budget = &self.record.queries.budget;
    budget.vector(&mut self.frames, 1)?;
    self.frames.push(Frame {
      function: function_id,
      query,
      registers,
      pc: 0,
      cursor: 0,
      destination,
      depth: 0,
      refs: self.pending.mark(),
      records: self.refs.and_then(|plan| plan.functions[function_id].as_ref()),
    });
    Ok(Request::Started)
  }

  /// Records that the innermost query read row or address `value` at its
  /// current instruction, when its function records references.
  #[inline(always)]
  fn note(&mut self, value: usize) -> Result<(), ExecutionError> {
    let Some(frame) = self.frames.last() else { return Ok(()) };
    let Some(refs) = frame.records else { return Ok(()) };
    let site = refs.site(frame.pc);
    match refs.encode(site, value) {
      Some(reference) => self.pending.push(reference),
      None => {
        let table = &mut self.record.queries.tables[frame.function];
        if let Some(recorded) = &mut table.refs {
          recorded.wide(frame.query, site, value, &table.budget)?;
        }
      },
    }
    Ok(())
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
        self.record.queries.tables[root.function].output(id).output.into_owned()
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
              let output = self.record.queries.tables[*function]
                .output_in(id, &mut self.arguments);
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
          let cell = self
            .record
            .memory
            .intern(memory_type, &self.arguments, program.field.modulus())
            .map_err(|e| match e {
              crate::budget::StorageError::Resource(e) => {
                ExecutionError::from(e)
              },
              crate::budget::StorageError::Invalid(e) => self.error(e),
            })?;
          let address = cell.address as u64;
          self.note(cell.address)?;
          let count = self.record.memory.count_mut(cell);
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
          let Some(cell) = self.record.memory.cell(memory_type, address) else {
            return Err(self.error("dangling pointer"));
          };
          self.note(address)?;
          let count = self.record.memory.count_mut(cell);
          *count = count.checked_add(1).ok_or_else(|| ExecutionError {
            function: "<ROM>".into(),
            instruction: 0,
            resource: None,
            message: "ROM multiplicity overflow".into(),
          })?;
          let value = self.record.memory.words(cell);
          self.frames.last_mut().unwrap().write(dest, value);
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
