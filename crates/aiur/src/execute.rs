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

struct Frame<'a, F> {
  function: usize,
  query: usize,
  registers: Vec<F>,
  pc: usize,
  cursor: usize,
  destination: &'a [usize],
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
    for map in &self.maps {
      queries
        .budget
        .reserve(map.rows().saturating_mul(std::mem::size_of::<u64>()))?;
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
    if let Some(parent) = self.frames.last_mut() {
      parent.write(frame.destination, &self.arguments);
    } else {
      self.record.output = self.arguments.clone();
    }
    self.record.queries.tables[frame.function]
      .finish(frame.query, &self.arguments);
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
    let (function, instruction) = self
      .frames
      .last()
      .map(|f| {
        (
          self
            .program
            .callable_name(f.function)
            .unwrap_or("<unknown>")
            .to_owned(),
          f.pc,
        )
      })
      .unwrap_or(("<entry>".into(), 0));
    ExecutionError {
      function,
      instruction,
      message: message.into(),
      resource: None,
    }
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
    let query = table.start(&self.arguments, outputs, hash)?;
    budget.vector(&mut self.frames, 1)?;
    self.frames.push(Frame {
      function: function_id,
      query,
      registers,
      pc: 0,
      cursor: 0,
      destination,
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
      use Instruction::*;
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
              .map_err(|_| self.error("ROM address overflow"))?;
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
