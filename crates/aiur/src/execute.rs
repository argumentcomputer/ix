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
  /// device population is enabled. Only CUDA builds populate on the device.
  #[cfg_attr(not(feature = "cuda"), allow(dead_code))]
  pub(crate) host_population: HostPopulation,
}

/// A record's population override, kept by value through clones.
#[derive(Debug, Default)]
pub(crate) struct HostPopulation(std::sync::atomic::AtomicBool);

#[cfg_attr(not(feature = "cuda"), allow(dead_code))]
impl HostPopulation {
  pub(crate) fn get(&self) -> bool {
    self.0.load(std::sync::atomic::Ordering::Acquire)
  }
  pub(crate) fn set(&self, host: bool) {
    self.0.store(host, std::sync::atomic::Ordering::Release);
  }
}

impl Clone for HostPopulation {
  fn clone(&self) -> Self {
    Self(std::sync::atomic::AtomicBool::new(self.get()))
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

  pub fn storage_usage(&self) -> RecordStorage {
    let mut usage = RecordStorage::default();
    for table in &self.queries.tables {
      let (payload, capacity, index) = table.storage_usage();
      usage.query_payload_bytes += payload;
      usage.query_vector_capacity_bytes += capacity;
      usage.query_index_estimate_bytes += index;
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

#[derive(Clone, Copy)]
enum FrameDest<'a> {
  Compact(&'a [u32]),
  Wide(&'a [usize]),
}

struct Frame<'a, F> {
  function: usize,
  query: usize,
  registers: Vec<F>,
  pc: usize,
  cursor: usize,
  destination: FrameDest<'a>,
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
  dispatch: &'a dispatch::DispatchProgram<B::Element>,
  // Function SCCs of the depth circuits, when heights are recorded.
  sccs: Option<&'a [u32]>,
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

  #[inline]
  fn write_compact(&mut self, dest: &[u32], values: &[F]) {
    debug_assert_eq!(dest.len(), values.len());
    if let ([reg], [value]) = (dest, values) {
      self.registers[*reg as usize] = *value;
      return;
    }
    for (&reg, &value) in dest.iter().zip(values) {
      self.registers[reg as usize] = value;
    }
  }

  #[inline]
  fn write_dest(&mut self, dest: FrameDest<'_>, values: &[F]) {
    match dest {
      FrameDest::Compact(regs) => self.write_compact(regs, values),
      FrameDest::Wide(regs) => self.write(regs, values),
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
      parent.write_dest(frame.destination, &self.arguments);
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
    destination: FrameDest<'a>,
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
      return Ok(Request::Cached(id));
    }
    self.start_frame(function_id, hash, destination)?;
    Ok(Request::Started)
  }

  #[inline(always)]
  fn start_frame(
    &mut self,
    function_id: usize,
    hash: u64,
    destination: FrameDest<'a>,
  ) -> Result<(), ExecutionError> {
    let budget = &self.record.queries.budget;
    let table = &mut self.record.queries.tables[function_id];
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
    let query = table.start(&self.arguments, outputs, hash)?;
    budget.vector(&mut self.frames, 1)?;
    self.frames.push(Frame {
      function: function_id,
      query,
      registers,
      pc: 0,
      cursor: 0,
      destination,
      depth: 0,
    });
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
    let request = self.request(root.function, FrameDest::Wide(&[]))?;
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
    let program = self.program;
    let field = program.field;
    let reg_lists = &self.dispatch.reg_lists;
    let sccs = self.sccs;

    enum StepExit<'a> {
      Return,
      CallMiss { callee: usize, hash: u64, dest: &'a [u32] },
      Bytecode { pc: usize, next: usize, memory_type: usize, branch: usize },
    }

    #[inline(always)]
    fn site_error<B: FieldBackend>(
      program: &CheckedProgram<B>,
      function: usize,
      instruction: usize,
      message: impl Into<String>,
    ) -> ExecutionError {
      ExecutionError {
        function: program
          .callable_name(function)
          .unwrap_or("<unknown>")
          .to_owned(),
        instruction,
        resource: None,
        message: message.into(),
      }
    }

    while !self.frames.is_empty() {
      let frame_idx = self.frames.len() - 1;
      let cur_fn = self.frames[frame_idx].function;
      let code = &self.dispatch.functions[cur_fn];
      let exit = {
        let frame = &mut self.frames[frame_idx];
        let mut cursor = frame.cursor;
        let regs = frame.registers.as_mut_slice();
        let tables = &mut self.record.queries.tables;
        let memory = &mut self.record.memory;
        let instructions = &mut self.record.instructions;
        let arguments = &mut self.arguments;
        #[cfg(feature = "function-profile")]
        let profile = &mut self.profile;

        loop {
          let step = &code[cursor];
          let Some(next_ins) = instructions.checked_add(step.instructions)
          else {
            return Err(site_error(
              program,
              cur_fn,
              step.pc,
              "instruction counter overflow",
            ));
          };
          *instructions = next_ins;
          match &step.action {
            dispatch::Action::Literal { dest, value } => {
              #[cfg(feature = "function-profile-ops")]
              if let Some(profile) = profile.as_deref_mut() {
                profile.operation("literal");
              }
              regs[*dest as usize] = *value;
              cursor = step.next;
            },
            dispatch::Action::Copy1 { dest, src } => {
              #[cfg(feature = "function-profile-ops")]
              if let Some(profile) = profile.as_deref_mut() {
                profile.operation("copy");
              }
              regs[*dest as usize] = regs[*src as usize];
              cursor = step.next;
            },
            dispatch::Action::CopyDisjoint { dest_off, src_off, len } => {
              #[cfg(feature = "function-profile-ops")]
              if let Some(profile) = profile.as_deref_mut() {
                profile.operation("copy");
              }
              let len = *len as usize;
              let dsts =
                &reg_lists[*dest_off as usize..*dest_off as usize + len];
              let srcs = &reg_lists[*src_off as usize..*src_off as usize + len];
              for (&d, &s) in dsts.iter().zip(srcs) {
                regs[d as usize] = regs[s as usize];
              }
              cursor = step.next;
            },
            dispatch::Action::Neg { dest, src } => {
              #[cfg(feature = "function-profile-ops")]
              if let Some(profile) = profile.as_deref_mut() {
                profile.operation("neg");
              }
              regs[*dest as usize] = field.neg(regs[*src as usize]);
              cursor = step.next;
            },
            dispatch::Action::Add { dest, left, right } => {
              #[cfg(feature = "function-profile-ops")]
              if let Some(profile) = profile.as_deref_mut() {
                profile.operation("add");
              }
              regs[*dest as usize] =
                field.add(regs[*left as usize], regs[*right as usize]);
              cursor = step.next;
            },
            dispatch::Action::Sub { dest, left, right } => {
              #[cfg(feature = "function-profile-ops")]
              if let Some(profile) = profile.as_deref_mut() {
                profile.operation("sub");
              }
              regs[*dest as usize] =
                field.sub(regs[*left as usize], regs[*right as usize]);
              cursor = step.next;
            },
            dispatch::Action::Mul { dest, left, right } => {
              #[cfg(feature = "function-profile-ops")]
              if let Some(profile) = profile.as_deref_mut() {
                profile.operation("mul");
              }
              regs[*dest as usize] =
                field.mul(regs[*left as usize], regs[*right as usize]);
              cursor = step.next;
            },
            dispatch::Action::DivConst { dest, left, inv } => {
              #[cfg(feature = "function-profile-ops")]
              if let Some(profile) = profile.as_deref_mut() {
                profile.operation("div");
              }
              regs[*dest as usize] = field.mul(regs[*left as usize], *inv);
              cursor = step.next;
            },
            dispatch::Action::DivDyn { dest, left, right } => {
              #[cfg(feature = "function-profile-ops")]
              if let Some(profile) = profile.as_deref_mut() {
                profile.operation("div");
              }
              let Some(inv) = field.inverse(regs[*right as usize]) else {
                return Err(site_error(
                  program,
                  cur_fn,
                  step.pc,
                  "division by zero",
                ));
              };
              regs[*dest as usize] = field.mul(regs[*left as usize], inv);
              cursor = step.next;
            },
            dispatch::Action::PtrEq { dest, left, right } => {
              #[cfg(feature = "function-profile-ops")]
              if let Some(profile) = profile.as_deref_mut() {
                profile.operation("ptr_eq");
              }
              regs[*dest as usize] = field.from_u64(u64::from(
                regs[*left as usize] == regs[*right as usize],
              ));
              cursor = step.next;
            },
            dispatch::Action::BranchEq1 { reg, otherwise_cursor, value } => {
              #[cfg(feature = "function-profile-ops")]
              if let Some(profile) = profile.as_deref_mut() {
                profile.operation("branch");
              }
              if regs[*reg as usize] == *value {
                cursor = step.next;
              } else {
                cursor = *otherwise_cursor as usize;
              }
            },
            dispatch::Action::Jump { target_cursor } => {
              #[cfg(feature = "function-profile-ops")]
              if let Some(profile) = profile.as_deref_mut() {
                profile.operation("jump");
              }
              cursor = *target_cursor as usize;
            },
            dispatch::Action::Load {
              pointer,
              memory_type,
              dest_off,
              dest_len,
            } => {
              #[cfg(feature = "function-profile-ops")]
              if let Some(profile) = profile.as_deref_mut() {
                profile.operation("load");
              }
              let Some(address) =
                usize::try_from(field.to_u64(regs[*pointer as usize])).ok()
              else {
                return Err(site_error(
                  program,
                  cur_fn,
                  step.pc,
                  "ROM address overflow",
                ));
              };
              let Some(index) =
                memory.index_for_type(*memory_type as usize, address)
              else {
                return Err(site_error(
                  program,
                  cur_fn,
                  step.pc,
                  "dangling pointer",
                ));
              };
              let count = memory.multiplicity_mut(index);
              let Some(next_count) = count.checked_add(1) else {
                return Err(ExecutionError {
                  function: "<ROM>".into(),
                  instruction: 0,
                  resource: None,
                  message: "ROM multiplicity overflow".into(),
                });
              };
              *count = next_count;
              let entry = memory.get(index).unwrap();
              let dest_regs = &reg_lists
                [*dest_off as usize..*dest_off as usize + *dest_len as usize];
              if let ([reg], [val]) = (dest_regs, entry.cell.value) {
                regs[*reg as usize] = *val;
              } else {
                for (&reg, &val) in dest_regs.iter().zip(entry.cell.value) {
                  regs[reg as usize] = val;
                }
              }
              cursor = step.next;
            },
            dispatch::Action::Store {
              dest,
              memory_type,
              value_off,
              value_len,
            } => {
              #[cfg(feature = "function-profile-ops")]
              if let Some(profile) = profile.as_deref_mut() {
                profile.operation("store");
              }
              let memory_type = *memory_type as usize;
              arguments.clear();
              for &r in &reg_lists
                [*value_off as usize..*value_off as usize + *value_len as usize]
              {
                arguments.push(regs[r as usize]);
              }
              if let Err(e) = program.memory_types[memory_type]
                .1
                .validate_registers(arguments, field)
              {
                return Err(site_error(program, cur_fn, step.pc, e));
              }
              let index =
                match memory.intern(memory_type, arguments, field.modulus()) {
                  Ok(index) => index,
                  Err(crate::budget::StorageError::Resource(e)) => {
                    return Err(ExecutionError::from(e));
                  },
                  Err(crate::budget::StorageError::Invalid(e)) => {
                    return Err(site_error(program, cur_fn, step.pc, e));
                  },
                };
              let address = memory.address(index) as u64;
              let count = memory.multiplicity_mut(index);
              let Some(next_count) = count.checked_add(1) else {
                return Err(ExecutionError {
                  function: "<ROM>".into(),
                  instruction: 0,
                  resource: None,
                  message: "ROM multiplicity overflow".into(),
                });
              };
              *count = next_count;
              regs[*dest as usize] = field.from_u64(address);
              cursor = step.next;
            },
            dispatch::Action::DirectMap { function, op } => {
              #[cfg(feature = "function-profile-ops")]
              if let Some(profile) = profile.as_deref_mut() {
                profile.operation("table");
              }
              let map = tables[*function as usize].static_map.as_mut().unwrap();
              if let Err(message) =
                op.eval(field, regs, reg_lists, &mut map.counts)
              {
                return Err(site_error(program, cur_fn, step.pc, message));
              }
              cursor = step.next;
            },
            dispatch::Action::DirectHint { kind, regs_off } => {
              #[cfg(feature = "function-profile-ops")]
              if let Some(profile) = profile.as_deref_mut() {
                profile.operation("hint");
              }
              if let Err(message) = dispatch::eval_direct_hint(
                *kind,
                field,
                regs,
                &reg_lists[*regs_off as usize..],
              ) {
                return Err(site_error(program, cur_fn, step.pc, message));
              }
              cursor = step.next;
            },
            dispatch::Action::Map { function, call } => {
              #[cfg(feature = "function-profile-ops")]
              if let Some(profile) = profile.as_deref_mut() {
                profile.operation("table");
              }
              let map = tables[*function].static_map.as_mut().unwrap();
              if let Err(message) = call(regs, &mut map.counts) {
                return Err(site_error(program, cur_fn, step.pc, message));
              }
              cursor = step.next;
            },
            dispatch::Action::Hint { call } => {
              #[cfg(feature = "function-profile-ops")]
              if let Some(profile) = profile.as_deref_mut() {
                profile.operation("hint");
              }
              if let Err(message) = call(regs) {
                return Err(site_error(program, cur_fn, step.pc, message));
              }
              cursor = step.next;
            },
            dispatch::Action::Call {
              callee,
              args_off,
              args_len,
              dest_off,
              dest_len,
            } => {
              #[cfg(feature = "function-profile-ops")]
              if let Some(profile) = profile.as_deref_mut() {
                profile.operation("call");
              }
              let callee = *callee as usize;
              let args_off = *args_off as usize;
              let args_len = *args_len as usize;
              let dest_regs = &reg_lists
                [*dest_off as usize..*dest_off as usize + *dest_len as usize];
              #[cfg(feature = "function-profile")]
              if let Some(profile) = profile.as_deref_mut() {
                profile.enter(callee);
              }
              let table = &mut tables[callee];
              let (hash, found, unary_arg) = if args_len == 1 {
                let arg = regs[reg_lists[args_off] as usize];
                let (hash, found) = table.lookup(&[arg]);
                (hash, found, Some(arg))
              } else {
                arguments.clear();
                for &r in &reg_lists[args_off..args_off + args_len] {
                  arguments.push(regs[r as usize]);
                }
                let (hash, found) = table.lookup(arguments);
                (hash, found, None)
              };
              if let Some(id) = found {
                if table.count(id) == 0 {
                  return Err(site_error(
                    program,
                    cur_fn,
                    step.pc,
                    "recursive query is already being evaluated",
                  ));
                }
                if table.bump(id).is_none() {
                  return Err(ExecutionError {
                    function: "<query>".into(),
                    instruction: 0,
                    resource: None,
                    message: "query multiplicity overflow".into(),
                  });
                }
                if sccs.is_some_and(|s| {
                  let scc = s
                    .get(callee)
                    .copied()
                    .unwrap_or(crate::trace::depth::NO_SCC);
                  scc != crate::trace::depth::NO_SCC
                    && s.get(cur_fn) == Some(&scc)
                }) {
                  let height = table.depth(id);
                  frame.depth = frame.depth.max(height.saturating_add(1));
                }
                let output = table.output(id).output;
                if let ([reg], [val]) = (dest_regs, output) {
                  regs[*reg as usize] = *val;
                } else {
                  for (&reg, &val) in dest_regs.iter().zip(output) {
                    regs[reg as usize] = val;
                  }
                }
                #[cfg(feature = "function-profile")]
                if let Some(profile) = profile.as_deref_mut() {
                  profile.exit(true);
                }
                cursor = step.next;
                continue;
              }
              if let Some(arg) = unary_arg {
                arguments.clear();
                arguments.push(arg);
              }
              frame.pc = step.pc + 1;
              frame.cursor = step.next;
              break StepExit::CallMiss { callee, hash, dest: dest_regs };
            },
            dispatch::Action::Return { vals_off, vals_len } => {
              #[cfg(feature = "function-profile-ops")]
              if let Some(profile) = profile.as_deref_mut() {
                profile.operation("return");
              }
              arguments.clear();
              for &r in &reg_lists
                [*vals_off as usize..*vals_off as usize + *vals_len as usize]
              {
                arguments.push(regs[r as usize]);
              }
              frame.pc = step.pc;
              frame.cursor = cursor;
              break StepExit::Return;
            },
            dispatch::Action::ReturnPlan { plan } => {
              #[cfg(feature = "function-profile-ops")]
              if let Some(profile) = profile.as_deref_mut() {
                profile.operation("return");
              }
              let ret = program.returns[cur_fn][*plan].as_ref().unwrap();
              arguments.clear();
              arguments.extend(ret.values.iter().map(|r| regs[*r]));
              frame.pc = step.pc;
              frame.cursor = cursor;
              break StepExit::Return;
            },
            dispatch::Action::Bytecode { memory_type, branch } => {
              frame.pc = step.pc;
              frame.cursor = cursor;
              break StepExit::Bytecode {
                pc: step.pc,
                next: step.next,
                memory_type: *memory_type,
                branch: *branch,
              };
            },
          }
        }
      };

      match exit {
        StepExit::Return => {
          self.finish_return()?;
        },
        StepExit::CallMiss { callee, hash, dest } => {
          self.start_frame(callee, hash, FrameDest::Compact(dest))?;
        },
        StepExit::Bytecode { pc, next, memory_type, branch } => {
          let instruction = &program.execution_functions[cur_fn].code[pc];
          use Instruction::{
            AssertEq, Binary, Branch, Call, Copy, Fail, Guard, Hint, Jump,
            Literal, Load, Neg, PtrEq, Ret, Store,
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
              PtrEq { .. } => "ptr_eq",
            });
          }
          let frame = &mut self.frames[frame_idx];
          match instruction {
            Literal { dest, value } => frame.registers[*dest] = *value,
            Copy { dest, source } => {
              self.arguments.clear();
              self.arguments.extend(source.iter().map(|r| frame.registers[*r]));
              frame.write(dest, &self.arguments);
            },
            Neg { dest, source } => {
              frame.registers[*dest] = field.neg(frame.registers[*source])
            },
            Binary { dest, operator, left, right } => {
              let (a, b) = (frame.registers[*left], frame.registers[*right]);
              let result = match operator {
                BinOp::Add => field.add(a, b),
                BinOp::Sub => field.sub(a, b),
                BinOp::Mul => field.mul(a, b),
                BinOp::Div => match program.division_inverses[cur_fn][pc]
                  .or_else(|| field.inverse(b))
                {
                  Some(inv) => field.mul(a, inv),
                  None => return Err(self.error("division by zero")),
                },
              };
              frame.registers[*dest] = result;
            },
            Guard { tests, message } => {
              if !tests
                .iter()
                .all(|(reg, value)| frame.registers[*reg] == *value)
              {
                return Err(self.error(message));
              }
            },
            Branch { tests, otherwise } => {
              if !tests
                .iter()
                .all(|(reg, value)| frame.registers[*reg] == *value)
              {
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
                self.output_buffer.resize(dest.len(), field.zero());
                let result = map
                  .call(&self.arguments, &mut self.output_buffer)
                  .map(|()| {
                    frame.write(dest, &self.output_buffer);
                  });
                result.map_err(|message| {
                  site_error(program, cur_fn, pc, message)
                })?;
                frame.pc = pc + 1;
                frame.cursor = next;
                continue;
              }
              self.arguments.clear();
              self.arguments.extend(args.iter().map(|r| frame.registers[*r]));
              let output = self.request(*function, FrameDest::Wide(dest))?;
              self.frames[frame_idx].pc = pc + 1;
              self.frames[frame_idx].cursor = next;
              if !matches!(output, Request::Started) {
                if let Request::Cached(id) = output {
                  let output =
                    self.record.queries.tables[*function].output(id).output;
                  self.frames[frame_idx].write(dest, output);
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
                .validate_registers(&self.arguments, field)
                .map_err(|e| self.error(e))?;
              let index = self
                .record
                .memory
                .intern(memory_type, &self.arguments, field.modulus())
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
              self.frames[frame_idx].registers[*dest] = field.from_u64(address);
            },
            Load { pointer, dest, .. } => {
              let address =
                usize::try_from(field.to_u64(frame.registers[*pointer]))
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
              self.frames[frame_idx].write(dest, entry.cell.value);
            },
            Hint { key, dest, .. } => {
              let site = self.hints[cur_fn][pc].as_ref().unwrap();
              self.arguments.clear();
              self.arguments.extend(key.iter().map(|r| frame.registers[*r]));
              self.output_buffer.resize(dest.len(), field.zero());
              let result = site
                .evaluate(&self.arguments, &mut self.output_buffer, field)
                .map(|()| {
                  frame.write(dest, &self.output_buffer);
                });
              result
                .map_err(|message| site_error(program, cur_fn, pc, message))?;
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
            PtrEq { dest, left, right } => {
              frame.registers[*dest] = field.from_u64(u64::from(
                frame.registers[*left] == frame.registers[*right],
              ));
            },
          }
          self.frames[frame_idx].pc = pc + 1;
          self.frames[frame_idx].cursor = next;
        },
      }
    }
    Ok(())
  }
}
