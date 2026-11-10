//! Runtime for generated (native) executors.
//!
//! A generator turns a [`NativePlan`] into Rust function bodies; this module
//! owns everything those bodies may not reimplement: memoized calls, pending
//! query rejection, fixed-table calls, hint evaluation, typed ROM operations,
//! record accounting and error attribution. The plan is derived from the same
//! normalized representation the interpreter runs (dead code removed,
//! registers aliased, skippable instructions folded into dispatch entries,
//! copy/jump suffixes folded into return plans), so a generated executor
//! produces the interpreter's record, row for row, and its instruction count.
//!
//! Memory-type indices are assigned from a hash map when a program is checked
//! and may differ between processes. Plans therefore name ROM operations by
//! function and PC, and the runtime resolves their type at execution time.
use crate::bytecode::{Binary, CheckedProgram, Instruction};
use crate::execute::{Execution, ExecutionError};
use crate::field::FieldBackend;
use crate::hints::{HintSite, PreparedHints};
use crate::ixon::Writer;
use serde::{Deserialize, Serialize};

/// Version of the interface between generated code and this runtime. A
/// change to [`NativePlan`]'s meaning or to [`Runtime`]'s contract must bump it.
pub const ABI_VERSION: u32 = 1;

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
pub struct NativePlan {
  pub abi: u32,
  pub modulus: u64,
  pub functions: Vec<NativeFunction>,
  /// Callables after `functions` are fixed-table maps, in program order.
  pub maps: Vec<NativeMap>,
}

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
pub struct NativeMap {
  pub name: String,
  pub inputs: usize,
  pub outputs: usize,
}

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
pub struct NativeFunction {
  pub name: String,
  pub inputs: usize,
  pub outputs: usize,
  pub registers: usize,
  /// Registers written once by a literal, set before the body runs.
  pub initial: Vec<(usize, u64)>,
  /// Dispatch entries; execution starts at entry 0.
  pub entries: Vec<NativeEntry>,
}

/// One interpreter dispatch: the operation at `pc`, after any folded
/// instructions, which are included in `instructions`.
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
pub struct NativeEntry {
  pub pc: usize,
  pub instructions: u64,
  pub op: NativeOp,
  /// The entry that follows when control falls through.
  pub next: Option<usize>,
}

/// Register-level operations. Branch and jump targets are entry indices.
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
#[serde(tag = "op", rename_all = "snake_case")]
pub enum NativeOp {
  Literal {
    dest: usize,
    value: u64,
  },
  Copy {
    dest: Vec<usize>,
    source: Vec<usize>,
  },
  Neg {
    dest: usize,
    source: usize,
  },
  Binary {
    dest: usize,
    operator: Binary,
    left: usize,
    right: usize,
  },
  Guard {
    tests: Vec<(usize, u64)>,
    message: String,
  },
  /// Falls through when every test holds, otherwise continues at `target`.
  Branch {
    tests: Vec<(usize, u64)>,
    target: usize,
  },
  Jump {
    target: usize,
  },
  Call {
    function: usize,
    args: Vec<usize>,
    dest: Vec<usize>,
  },
  Map {
    function: usize,
    args: Vec<usize>,
    dest: Vec<usize>,
  },
  Store {
    value: Vec<usize>,
    dest: usize,
  },
  Load {
    pointer: usize,
    dest: Vec<usize>,
  },
  Hint {
    key: Vec<usize>,
    dest: Vec<usize>,
  },
  Assert {
    left: Vec<usize>,
    right: Vec<usize>,
    message: String,
  },
  /// An operation with no runtime effect (an unchecked assertion).
  Nop,
  Return {
    values: Vec<usize>,
  },
  Fail {
    message: String,
  },
}

impl<B: FieldBackend> CheckedProgram<B> {
  /// The normalized execution representation, in the form generators consume.
  pub fn native_plan(&self) -> NativePlan {
    let field = self.field;
    let functions = self.program.functions.len();
    let mut out = Vec::with_capacity(functions);
    for function in 0..functions {
      let steps = &self.steps[function];
      let code = &self.execution_functions[function].code;
      let returns = &self.returns[function];
      // The same reachable entries, in the same order, as dispatch::prepare.
      let mut reachable = vec![false; steps.len()];
      let mut pending = vec![0];
      while let Some(pc) = pending.pop() {
        if std::mem::replace(&mut reachable[pc], true) {
          continue;
        }
        let step = &steps[pc];
        if returns[step.pc].is_some() {
          continue;
        }
        match &code[step.pc] {
          Instruction::Ret { .. } | Instruction::Fail { .. } => (),
          Instruction::Jump { target } => pending.push(*target),
          Instruction::Branch { tests, otherwise } => {
            if !tests.is_empty() {
              pending.push(*otherwise);
            }
            pending.push(step.pc + 1);
          },
          _ => pending.push(step.pc + 1),
        }
      }
      let pcs: Vec<_> = reachable
        .iter()
        .enumerate()
        .filter_map(|(pc, &reachable)| reachable.then_some(pc))
        .collect();
      let mut index = vec![usize::MAX; steps.len()];
      for (i, &pc) in pcs.iter().enumerate() {
        index[pc] = i;
      }
      let entry =
        |pc: usize| index.get(pc).copied().filter(|&i| i != usize::MAX);
      let word = |value: &B::Element| field.to_u64(*value);
      let tests = |tests: &[(usize, B::Element)]| {
        tests.iter().map(|(r, v)| (*r, word(v))).collect::<Vec<_>>()
      };
      let entries = pcs
        .iter()
        .map(|&pc| {
          let step = &steps[pc];
          if let Some(ret) = &returns[step.pc] {
            return NativeEntry {
              pc: ret.pc,
              instructions: step.skipped + ret.instructions,
              op: NativeOp::Return { values: ret.values.clone() },
              next: None,
            };
          }
          use Instruction as I;
          let op = match &code[step.pc] {
            I::Literal { dest, value } => {
              NativeOp::Literal { dest: *dest, value: word(value) }
            },
            I::Copy { dest, source } => {
              NativeOp::Copy { dest: dest.clone(), source: source.clone() }
            },
            I::Neg { dest, source } => {
              NativeOp::Neg { dest: *dest, source: *source }
            },
            I::Binary { dest, operator, left, right } => NativeOp::Binary {
              dest: *dest,
              operator: *operator,
              left: *left,
              right: *right,
            },
            I::Guard { tests: t, message } => {
              NativeOp::Guard { tests: tests(t), message: message.clone() }
            },
            I::Branch { tests: t, otherwise } if !t.is_empty() => {
              NativeOp::Branch {
                tests: tests(t),
                target: entry(*otherwise).expect("reachable branch target"),
              }
            },
            I::Branch { .. } => NativeOp::Nop,
            I::Jump { target } => NativeOp::Jump {
              target: entry(*target).expect("reachable jump target"),
            },
            I::Call { function: callee, args, dest } => {
              if *callee < functions {
                NativeOp::Call {
                  function: *callee,
                  args: args.clone(),
                  dest: dest.clone(),
                }
              } else {
                NativeOp::Map {
                  function: *callee,
                  args: args.clone(),
                  dest: dest.clone(),
                }
              }
            },
            I::Store { value, dest, .. } => {
              NativeOp::Store { value: value.clone(), dest: *dest }
            },
            I::Load { pointer, dest, .. } => {
              NativeOp::Load { pointer: *pointer, dest: dest.clone() }
            },
            I::Hint { key, dest, .. } => {
              NativeOp::Hint { key: key.clone(), dest: dest.clone() }
            },
            I::AssertEq { left, right, message, runtime_check } => {
              if *runtime_check {
                NativeOp::Assert {
                  left: left.clone(),
                  right: right.clone(),
                  message: message
                    .clone()
                    .unwrap_or_else(|| "equality assertion failed".into()),
                }
              } else {
                NativeOp::Nop
              }
            },
            I::Ret { value } => NativeOp::Return { values: value.clone() },
            I::Fail { message } => NativeOp::Fail { message: message.clone() },
          };
          let next = match op {
            NativeOp::Return { .. }
            | NativeOp::Fail { .. }
            | NativeOp::Jump { .. } => None,
            _ => entry(step.pc + 1),
          };
          NativeEntry { pc: step.pc, instructions: step.skipped + 1, op, next }
        })
        .collect();
      out.push(NativeFunction {
        name: self.program.functions[function].name.clone(),
        inputs: self.inputs[function].width(),
        outputs: self.outputs[function].width(),
        registers: self.execution_functions[function].registers,
        initial: self.initial_registers[function]
          .iter()
          .map(|(r, v)| (*r, word(v)))
          .collect(),
        entries,
      });
    }
    let maps = self
      .program
      .maps
      .iter()
      .enumerate()
      .map(|(i, map)| NativeMap {
        name: map.name.clone(),
        inputs: self.inputs[functions + i].width(),
        outputs: self.outputs[functions + i].width(),
      })
      .collect();
    NativePlan {
      abi: ABI_VERSION,
      modulus: field.modulus(),
      functions: out,
      maps,
    }
  }

  /// Identifies the program and the plan generated code was emitted from:
  /// the whole serialized program (bytecode, enums, tables, maps, entries and
  /// hint-site metadata), its normalized plan, the field and the ABI version.
  /// Computed once per checked program.
  pub fn native_fingerprint(&self) -> &str {
    self
      .native_fingerprint
      .get_or_init(|| native_fingerprint(&self.program, &self.native_plan()))
  }
}

/// Version of the encoding hashed by [`native_fingerprint`]. Bumping it
/// invalidates every generated executor.
pub const NATIVE_FINGERPRINT_SCHEME: u32 = 2;

const NATIVE_FINGERPRINT_DOMAIN: &[u8] = b"aiur-native-fingerprint\0";

/// BLAKE3, as lowercase hex, over the domain, [`NATIVE_FINGERPRINT_SCHEME`],
/// [`ABI_VERSION`], the plan's modulus, the bytecode in Ixon serialization
/// with table rows inline ([`crate::artifact::program_bytes`]) and the
/// encoding of every field of `plan`.
pub fn native_fingerprint(
  program: &crate::Program,
  plan: &NativePlan,
) -> String {
  let program = crate::artifact::program_bytes(program);
  let encoded = plan_bytes(plan);
  let mut hasher = blake3::Hasher::new();
  hasher.update(NATIVE_FINGERPRINT_DOMAIN);
  hasher.update(&NATIVE_FINGERPRINT_SCHEME.to_le_bytes());
  hasher.update(&ABI_VERSION.to_le_bytes());
  hasher.update(&plan.modulus.to_le_bytes());
  hasher.update(&(program.len() as u64).to_le_bytes());
  hasher.update(&program);
  hasher.update(&(encoded.len() as u64).to_le_bytes());
  hasher.update(&encoded);
  hasher.finalize().to_hex().to_string()
}

/// The canonical encoding of every field of a plan, with one tag per
/// operation variant.
fn plan_bytes(plan: &NativePlan) -> Vec<u8> {
  let mut w = Writer::new();
  w.nat(u64::from(plan.abi));
  w.nat(plan.modulus);
  w.usize(plan.functions.len());
  for function in &plan.functions {
    w.str(&function.name);
    w.usize(function.inputs);
    w.usize(function.outputs);
    w.usize(function.registers);
    w.usize(function.initial.len());
    for &(register, value) in &function.initial {
      w.usize(register);
      w.nat(value);
    }
    w.usize(function.entries.len());
    for entry in &function.entries {
      w.usize(entry.pc);
      w.nat(entry.instructions);
      write_op(&mut w, &entry.op);
      match entry.next {
        None => w.u8(0),
        Some(next) => {
          w.u8(1);
          w.usize(next);
        },
      }
    }
  }
  w.usize(plan.maps.len());
  for map in &plan.maps {
    w.str(&map.name);
    w.usize(map.inputs);
    w.usize(map.outputs);
  }
  w.into_bytes()
}

fn write_op(w: &mut Writer, op: &NativeOp) {
  let tests = |w: &mut Writer, tests: &[(usize, u64)]| {
    w.usize(tests.len());
    for &(register, value) in tests {
      w.usize(register);
      w.nat(value);
    }
  };
  match op {
    NativeOp::Literal { dest, value } => {
      w.u8(0);
      w.usize(*dest);
      w.nat(*value);
    },
    NativeOp::Copy { dest, source } => {
      w.u8(1);
      w.usizes(dest);
      w.usizes(source);
    },
    NativeOp::Neg { dest, source } => {
      w.u8(2);
      w.usize(*dest);
      w.usize(*source);
    },
    NativeOp::Binary { dest, operator, left, right } => {
      w.u8(3);
      w.usize(*dest);
      w.u8(match operator {
        Binary::Add => 0,
        Binary::Sub => 1,
        Binary::Mul => 2,
        Binary::Div => 3,
      });
      w.usize(*left);
      w.usize(*right);
    },
    NativeOp::Guard { tests: t, message } => {
      w.u8(4);
      tests(w, t);
      w.str(message);
    },
    NativeOp::Branch { tests: t, target } => {
      w.u8(5);
      tests(w, t);
      w.usize(*target);
    },
    NativeOp::Jump { target } => {
      w.u8(6);
      w.usize(*target);
    },
    NativeOp::Call { function, args, dest } => {
      w.u8(7);
      w.usize(*function);
      w.usizes(args);
      w.usizes(dest);
    },
    NativeOp::Map { function, args, dest } => {
      w.u8(8);
      w.usize(*function);
      w.usizes(args);
      w.usizes(dest);
    },
    NativeOp::Store { value, dest } => {
      w.u8(9);
      w.usizes(value);
      w.usize(*dest);
    },
    NativeOp::Load { pointer, dest } => {
      w.u8(10);
      w.usize(*pointer);
      w.usizes(dest);
    },
    NativeOp::Hint { key, dest } => {
      w.u8(11);
      w.usizes(key);
      w.usizes(dest);
    },
    NativeOp::Assert { left, right, message } => {
      w.u8(12);
      w.usizes(left);
      w.usizes(right);
      w.str(message);
    },
    NativeOp::Nop => w.u8(13),
    NativeOp::Return { values } => {
      w.u8(14);
      w.usizes(values);
    },
    NativeOp::Fail { message } => {
      w.u8(15);
      w.str(message);
    },
  }
}

/// A generated executor for one program.
pub trait Kernel {
  /// [`CheckedProgram::native_fingerprint`] of the program it was emitted from.
  const FINGERPRINT: &'static str;
  /// Run `function`'s body for the pending query `row`, writing its result.
  fn run<B: FieldBackend>(
    rt: &mut Runtime<'_, B>,
    function: usize,
    row: usize,
    args: &[B::Element],
    output: &mut Vec<B::Element>,
  ) -> Result<(), Failed>;
}

/// Stack reserved for the thread a native execution runs on. Pages are only
/// committed when touched, so this bounds recursion depth, not memory use.
const NATIVE_STACK: usize = 4 << 30;

/// Size of each heap segment `stacker` adds beyond [`NATIVE_STACK`].
const STACK_SEGMENT: usize = 1 << 30;

/// Per-thread stack accounting for the running native execution: the stack
/// top when it started, the lowest address [`grow`] has seen on that stack,
/// and the number of heap segments added beyond it.
#[derive(Clone, Copy)]
struct StackUse {
  top: usize,
  lowest: usize,
  segments: usize,
}

thread_local! {
  static STACK_USE: std::cell::Cell<StackUse> =
    const { std::cell::Cell::new(StackUse { top: 0, lowest: 0, segments: 0 }) };
}

#[inline(always)]
fn stack_address() -> usize {
  let marker = 0u8;
  std::hint::black_box(&marker) as *const u8 as usize
}

/// Bytes of stack the current thread's native execution has touched: the
/// depth reached on its own stack plus any heap segments, at their full size.
fn stack_bytes() -> usize {
  let used = STACK_USE.get();
  (used.top - used.lowest) + used.segments * STACK_SEGMENT
}

/// Run `f` with at least `red_zone` bytes of stack. Native executions run on
/// a thread with [`NATIVE_STACK`] bytes, so this only allocates a new segment
/// for recursion deeper than that. Every call also records the stack depth.
#[inline(always)]
pub fn grow<R>(red_zone: usize, f: impl FnOnce() -> R) -> R {
  let here = stack_address();
  let mut used = STACK_USE.get();
  // Addresses on a heap segment are outside the thread's own stack range.
  if here < used.lowest && used.top - here <= NATIVE_STACK {
    used.lowest = here;
    STACK_USE.set(used);
  }
  if stacker::remaining_stack().is_some_and(|left| left < red_zone) {
    used.segments += 1;
    STACK_USE.set(used);
  }
  stacker::maybe_grow(red_zone, STACK_SEGMENT, f)
}

/// The outcome of requesting a query.
pub enum Begin {
  /// A completed query; its multiplicity has been incremented.
  Cached(usize),
  /// A new pending row; the caller must run the body and [`Runtime::finish`] it.
  Started(usize),
}

/// A failed operation. The error itself is held by the [`Runtime`]
/// ([`Runtime::take_failure`]); keeping `Result`s one word wide keeps the
/// many `?` branches in generated code small.
#[derive(Clone, Copy, Debug)]
pub struct Failed;

/// The execution state generated code operates on. Hot entry points are
/// small; everything else is out of line, because generated bodies are
/// straight-line code whose size, not instruction count, limits their speed.
pub struct Runtime<'a, B: FieldBackend> {
  program: &'a CheckedProgram<B>,
  sites: &'a [Vec<Option<HintSite<B::Element>>>],
  record: Execution<B>,
  failure: Option<ExecutionError>,
}

impl<'a, B: FieldBackend> Runtime<'a, B> {
  #[inline(always)]
  pub fn field(&self) -> B {
    self.program.field
  }

  fn error(
    &self,
    function: usize,
    pc: usize,
    message: impl Into<String>,
  ) -> ExecutionError {
    ExecutionError {
      function: self
        .program
        .callable_name(function)
        .unwrap_or("<unknown>")
        .to_owned(),
      instruction: pc,
      message: message.into(),
      resource: None,
    }
  }

  #[cold]
  #[inline(never)]
  fn raise(&mut self, error: ExecutionError) -> Failed {
    self.failure = Some(error);
    Failed
  }

  /// Fail at `function`/`pc` with `message`, as the interpreter reports it.
  #[cold]
  #[inline(never)]
  pub fn fail(&mut self, function: usize, pc: usize, message: &str) -> Failed {
    let error = self.error(function, pc, message);
    self.raise(error)
  }

  /// The error behind a [`Failed`].
  pub fn take_failure(&mut self) -> ExecutionError {
    self.failure.take().expect("a failed operation recorded its error")
  }

  #[inline(always)]
  pub fn count(&mut self, instructions: u64) -> Result<(), Failed> {
    match self.record.instructions.checked_add(instructions) {
      Some(total) => {
        self.record.instructions = total;
        Ok(())
      },
      None => Err(self.raise(ExecutionError {
        function: "<native>".into(),
        instruction: 0,
        message: "instruction counter overflow".into(),
        resource: None,
      })),
    }
  }

  /// Request `function(args)` from `caller` at `pc`. A completed query is
  /// counted and returned; a pending one is an error; a new one is inserted
  /// before its body runs, exactly as the interpreter orders rows.
  #[inline(never)]
  pub fn begin(
    &mut self,
    caller: usize,
    pc: usize,
    function: usize,
    args: &[B::Element],
  ) -> Result<Begin, Failed> {
    let table = &mut self.record.queries.tables[function];
    let (hash, found) = table.lookup(args);
    if let Some(row) = found {
      if table.count(row) == 0 {
        return Err(self.fail(
          caller,
          pc,
          "recursive query is already being evaluated",
        ));
      }
      if table.bump(row).is_none() {
        return Err(self.raise(ExecutionError {
          function: "<query>".into(),
          instruction: 0,
          resource: None,
          message: "query multiplicity overflow".into(),
        }));
      }
      return Ok(Begin::Cached(row));
    }
    match table.start(args, hash) {
      Ok(row) => Ok(Begin::Started(row)),
      Err(e) => Err(self.raise(e.into())),
    }
  }

  /// The output of a completed query.
  #[inline(always)]
  pub fn output(&self, function: usize, row: usize) -> &[B::Element] {
    self.record.queries.tables[function].output(row).output
  }

  /// Validate and record the result of `function`'s pending `row`, returned
  /// at `pc`.
  #[inline(never)]
  pub fn finish(
    &mut self,
    function: usize,
    row: usize,
    pc: usize,
    output: &[B::Element],
  ) -> Result<(), Failed> {
    if let Err(e) = self.program.outputs[function]
      .validate_registers(output, self.program.field)
    {
      return Err(self.fail(function, pc, &e));
    }
    self.record.queries.tables[function].finish(row, output);
    Ok(())
  }

  /// A fixed-table call from `caller` at `pc`, through the bound map and
  /// so through the same registered implementation the interpreter uses.
  #[inline(never)]
  pub fn map(
    &mut self,
    caller: usize,
    pc: usize,
    map: usize,
    args: &[B::Element],
    output: &mut [B::Element],
  ) -> Result<(), Failed> {
    let record = self.record.queries.tables[map].static_map.as_mut().unwrap();
    match record.call(args, output) {
      Ok(()) => Ok(()),
      Err(message) => Err(self.fail(caller, pc, &message)),
    }
  }

  /// Count a call from `caller` at `pc` to the fixed table `map` whose row
  /// the generated code computed along with its outputs. Generators use this
  /// only for maps whose outputs they verified against every table row.
  #[inline(always)]
  pub fn count_map(
    &mut self,
    caller: usize,
    pc: usize,
    map: usize,
    row: usize,
  ) -> Result<(), Failed> {
    let record = self.record.queries.tables[map].static_map.as_mut().unwrap();
    match record.counts.get_mut(row) {
      Some(count) if *count < u64::MAX => {
        *count += 1;
        Ok(())
      },
      Some(_) => Err(self.fail(caller, pc, "map multiplicity overflow")),
      None => {
        Err(self.fail(caller, pc, "map override row index out of bounds"))
      },
    }
  }

  /// Evaluate the hint site at `function`/`pc`.
  #[inline(never)]
  pub fn hint(
    &mut self,
    function: usize,
    pc: usize,
    key: &[B::Element],
    output: &mut [B::Element],
  ) -> Result<(), Failed> {
    let site = self.sites[function][pc].as_ref().unwrap();
    match site.evaluate(key, output, self.program.field) {
      Ok(()) => Ok(()),
      Err(message) => Err(self.fail(function, pc, &message)),
    }
  }

  /// Store `values` at the ROM type of `function`/`pc`; returns its pointer.
  #[inline(never)]
  pub fn store(
    &mut self,
    function: usize,
    pc: usize,
    values: &[B::Element],
  ) -> Result<B::Element, Failed> {
    let program = self.program;
    let memory_type = program.steps[function][pc].memory_type;
    if let Err(e) = program.memory_types[memory_type]
      .1
      .validate_registers(values, program.field)
    {
      return Err(self.fail(function, pc, &e));
    }
    let index = match self.record.memory.intern(
      memory_type,
      values,
      program.field.modulus(),
    ) {
      Ok(index) => index,
      Err(crate::budget::StorageError::Resource(e)) => {
        return Err(self.raise(e.into()));
      },
      Err(crate::budget::StorageError::Invalid(e)) => {
        return Err(self.fail(function, pc, e));
      },
    };
    let address = self.record.memory.address(index) as u64;
    self.bump_rom(index)?;
    Ok(program.field.from_u64(address))
  }

  /// Load the ROM cell at `pointer` with the type of `function`/`pc`.
  #[inline(never)]
  pub fn load(
    &mut self,
    function: usize,
    pc: usize,
    pointer: B::Element,
    output: &mut [B::Element],
  ) -> Result<(), Failed> {
    let program = self.program;
    let memory_type = program.steps[function][pc].memory_type;
    let Ok(address) = usize::try_from(program.field.to_u64(pointer)) else {
      return Err(self.fail(function, pc, "ROM address overflow"));
    };
    let Some(index) = self.record.memory.index_for_type(memory_type, address)
    else {
      return Err(self.fail(function, pc, "dangling pointer"));
    };
    self.bump_rom(index)?;
    let entry = self.record.memory.get(index).unwrap();
    output.copy_from_slice(entry.cell.value);
    Ok(())
  }

  fn bump_rom(&mut self, index: usize) -> Result<(), Failed> {
    let count = self.record.memory.multiplicity_mut(index);
    match count.checked_add(1) {
      Some(next) => {
        *count = next;
        Ok(())
      },
      None => Err(self.raise(ExecutionError {
        function: "<ROM>".into(),
        instruction: 0,
        resource: None,
        message: "ROM multiplicity overflow".into(),
      })),
    }
  }

  /// `a / b` for the division at `function`/`pc`.
  #[inline(never)]
  pub fn divide(
    &mut self,
    function: usize,
    pc: usize,
    a: B::Element,
    b: B::Element,
  ) -> Result<B::Element, Failed> {
    let field = self.program.field;
    match self.program.division_inverses[function][pc]
      .or_else(|| field.inverse(b))
    {
      Some(inverse) => Ok(field.mul(a, inverse)),
      None => Err(self.fail(function, pc, "division by zero")),
    }
  }
}

/// Prepared hints bound to a generated kernel whose fingerprint matches.
pub struct NativeExecutor<'p, 'a, B: FieldBackend, K: Kernel> {
  hints: &'p PreparedHints<'a, B>,
  kernel: std::marker::PhantomData<fn() -> K>,
}

impl<'a, B: FieldBackend> PreparedHints<'a, B> {
  /// Bind a generated kernel. Fails unless it was generated from exactly this
  /// program and plan under the current runtime ABI, and unless every bound
  /// map override answers exactly as its table does: generated code may
  /// compute a table call's outputs from the table itself, where the
  /// interpreter takes the override's.
  pub fn bind_native<K: Kernel>(
    &self,
  ) -> Result<NativeExecutor<'_, 'a, B, K>, String> {
    let expected = self.program.native_fingerprint();
    if K::FINGERPRINT != expected {
      return Err(format!(
        "native kernel fingerprint {} does not match program {expected}",
        K::FINGERPRINT
      ));
    }
    for map in &self.maps {
      map.override_matches_table()?;
    }
    Ok(NativeExecutor { hints: self, kernel: std::marker::PhantomData })
  }
}

impl<B: FieldBackend, K: Kernel> NativeExecutor<'_, '_, B, K> {
  pub fn execute(
    &self,
    entry: &str,
    args: Vec<B::Element>,
  ) -> Result<Execution<B>, ExecutionError> {
    self.execute_inner(entry, args, None)
  }

  /// Execute under a shared record reservation, as
  /// [`PreparedHints::execute_reserved`] does. Record storage is charged as
  /// in the interpreter; native stack frames are not charged.
  pub fn execute_reserved(
    &self,
    entry: &str,
    args: Vec<B::Element>,
    reservation: &crate::budget::RecordReservation,
  ) -> Result<Execution<B>, ExecutionError> {
    self.execute_inner(entry, args, Some(reservation))
  }

  fn execute_inner(
    &self,
    entry: &str,
    args: Vec<B::Element>,
    reservation: Option<&crate::budget::RecordReservation>,
  ) -> Result<Execution<B>, ExecutionError> {
    std::thread::scope(|scope| {
      std::thread::Builder::new()
        .name("aiur-native".into())
        .stack_size(NATIVE_STACK)
        .spawn_scoped(scope, || self.run(entry, args, reservation))
        .map_err(|e| ExecutionError {
          function: "<native>".into(),
          instruction: 0,
          resource: None,
          message: format!("cannot start the native execution thread: {e}"),
        })?
        .join()
        .unwrap_or_else(|panic| std::panic::resume_unwind(panic))
    })
  }

  fn run(
    &self,
    entry: &str,
    args: Vec<B::Element>,
    reservation: Option<&crate::budget::RecordReservation>,
  ) -> Result<Execution<B>, ExecutionError> {
    let hints = self.hints;
    let program = hints.program;
    let error = |message| ExecutionError {
      function: entry.into(),
      instruction: 0,
      resource: None,
      message,
    };
    let selected = program.entry(entry).map_err(error)?;
    let root = selected.function;
    program.inputs[root].validate(&args, program.field).map_err(error)?;
    let (queries, memory) = hints.fresh_storage(reservation)?;
    let top = stack_address();
    STACK_USE.set(StackUse { top, lowest: top, segments: 0 });
    let mut rt = Runtime {
      program,
      sites: &hints.bindings.sites,
      failure: None,
      record: Execution {
        hints: hints.bindings.clone(),
        output: vec![],
        queries,
        memory,
        instructions: 0,
        native_stack_bytes: 0,
      },
    };
    let mut output = vec![];
    if root >= program.program.functions.len() {
      output.resize(program.outputs[root].width(), program.field.zero());
      let record = rt.record.queries.tables[root].static_map.as_mut().unwrap();
      record.call(&args, &mut output).map_err(|e| ExecutionError {
        function: "<entry>".into(),
        instruction: 0,
        resource: None,
        message: e,
      })?;
    } else {
      let row = match rt.begin(root, 0, root, &args) {
        Ok(Begin::Started(row)) => row,
        Ok(Begin::Cached(_)) => {
          unreachable!("a fresh session has no completed queries")
        },
        Err(Failed) => return Err(rt.take_failure()),
      };
      if K::run(&mut rt, root, row, &args, &mut output).is_err() {
        return Err(rt.take_failure());
      }
    }
    rt.record.output = output;
    rt.record.native_stack_bytes = stack_bytes();
    Ok(rt.record)
  }
}

/// [`record_diff`] for two executions that may fail: `Ok` means identical
/// records, or failures at the same function, instruction and message.
pub fn outcome_diff<B: FieldBackend>(
  a: &Result<Execution<B>, ExecutionError>,
  b: &Result<Execution<B>, ExecutionError>,
) -> Result<(), String> {
  match (a, b) {
    (Ok(a), Ok(b)) => record_diff(a, b),
    (Err(a), Err(b)) => {
      if (&a.function, a.instruction, &a.message)
        == (&b.function, b.instruction, &b.message)
      {
        Ok(())
      } else {
        Err(format!("different failures: {a} and {b}"))
      }
    },
    (Ok(_), Err(e)) => Err(format!("only the second failed: {e}")),
    (Err(e), Ok(_)) => Err(format!("only the first failed: {e}")),
  }
}

/// The first difference between two records, comparing everything a trace
/// or proof can depend on, including row order. `Ok` means identical.
pub fn record_diff<B: FieldBackend>(
  a: &Execution<B>,
  b: &Execution<B>,
) -> Result<(), String> {
  if a.output != b.output {
    return Err("outputs differ".into());
  }
  if a.instructions != b.instructions {
    return Err(format!(
      "instruction counts differ: {} and {}",
      a.instructions, b.instructions
    ));
  }
  if a.queries.tables.len() != b.queries.tables.len() {
    return Err("callable counts differ".into());
  }
  for (function, (x, y)) in
    a.queries.tables.iter().zip(&b.queries.tables).enumerate()
  {
    match (&x.static_map, &y.static_map) {
      (Some(p), Some(q)) => {
        if p.counts != q.counts {
          return Err(format!("map {function}: row counts differ"));
        }
      },
      (None, None) => {
        if x.len() != y.len() {
          return Err(format!(
            "function {function}: {} rows and {} rows",
            x.len(),
            y.len()
          ));
        }
        for row in 0..x.len() {
          if x.input(row) != y.input(row)
            || x.output(row).output != y.output(row).output
            || x.count(row) != y.count(row)
          {
            return Err(format!("function {function}: row {row} differs"));
          }
        }
      },
      _ => return Err(format!("callable {function}: kinds differ")),
    }
  }
  if a.memory.len() != b.memory.len() {
    return Err(format!(
      "ROM sizes differ: {} and {}",
      a.memory.len(),
      b.memory.len()
    ));
  }
  for (index, (x, y)) in a.memory.iter().zip(b.memory.iter()).enumerate() {
    if x.address != y.address
      || x.multiplicity != y.multiplicity
      || x.cell.value != y.cell.value
      || x.cell.r#type != y.cell.r#type
    {
      return Err(format!("ROM entry {index} differs"));
    }
  }
  Ok(())
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::bytecode::{Entry, Function, Program, Type};
  use crate::value::IoType;

  fn program(literal: u64, channel: &str) -> Program {
    use Instruction as I;
    Program {
      version: 2,
      modulus: 0xffff_ffff_0000_0001,
      functions: vec![Function {
        name: "main".into(),
        params: vec![Type::Field],
        result: Type::Field,
        registers: 3,
        code: vec![
          I::Literal { dest: 1, value: literal },
          I::Hint {
            channel: channel.into(),
            r#type: Type::Field,
            key_type: Type::Field,
            key: vec![0],
            dest: vec![2],
          },
          I::Binary { dest: 1, operator: Binary::Add, left: 1, right: 2 },
          I::Ret { value: vec![1] },
        ],
      }],
      enums: vec![],
      tables: vec![],
      maps: vec![],
      entries: vec![Entry {
        name: "main".into(),
        function: 0,
        inputs: vec![IoType::Field],
        output: Some(IoType::Field),
      }],
    }
  }

  fn fingerprint(program: Program) -> (String, Program, NativePlan) {
    let checked = program.check().unwrap();
    let plan = checked.native_plan();
    let fingerprint = native_fingerprint(checked.program(), &plan);
    assert_eq!(checked.native_fingerprint(), fingerprint);
    (fingerprint, checked.program().clone(), plan)
  }

  #[test]
  fn fingerprint_is_deterministic_and_covers_its_inputs() {
    let (base, program, plan) = fingerprint(self::program(5, "c"));
    assert_eq!(base.len(), 64);
    assert!(base.bytes().all(|b| matches!(b, b'0'..=b'9' | b'a'..=b'f')));
    assert_eq!(fingerprint(self::program(5, "c")).0, base);
    assert_ne!(fingerprint(self::program(6, "c")).0, base);
    assert_ne!(fingerprint(self::program(5, "d")).0, base);

    let changed = |edit: &dyn Fn(&mut NativePlan)| {
      let mut plan = plan.clone();
      edit(&mut plan);
      native_fingerprint(&program, &plan)
    };
    assert_ne!(changed(&|p| p.functions[0].entries[0].next = None), base);
    assert_ne!(changed(&|p| p.functions[0].entries[0].instructions += 1), base);
    assert_ne!(changed(&|p| p.functions[0].registers += 1), base);
    assert_ne!(
      changed(&|p| p.functions[0].entries[0].op = NativeOp::Nop),
      base
    );
    assert_ne!(
      changed(&|p| p.maps.push(NativeMap {
        name: "m".into(),
        inputs: 1,
        outputs: 1
      })),
      base
    );
    let mut renamed = program.clone();
    renamed.entries[0].name = "start".into();
    assert_ne!(native_fingerprint(&renamed, &plan), base);
  }

  #[test]
  fn fingerprint_hashes_the_versioned_domain() {
    let (base, program, plan) = fingerprint(self::program(5, "c"));
    let hash = |scheme: u32| {
      let program = crate::artifact::program_bytes(&program);
      let encoded = plan_bytes(&plan);
      let mut hasher = blake3::Hasher::new();
      hasher.update(b"aiur-native-fingerprint\0");
      hasher.update(&scheme.to_le_bytes());
      hasher.update(&ABI_VERSION.to_le_bytes());
      hasher.update(&plan.modulus.to_le_bytes());
      hasher.update(&(program.len() as u64).to_le_bytes());
      hasher.update(&program);
      hasher.update(&(encoded.len() as u64).to_le_bytes());
      hasher.update(&encoded);
      hasher.finalize().to_hex().to_string()
    };
    assert_eq!(hash(NATIVE_FINGERPRINT_SCHEME), base);
    assert_ne!(hash(1), base);
  }
}
