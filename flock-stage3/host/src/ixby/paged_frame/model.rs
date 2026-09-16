use flock_prover::field::F128;

pub const STATE_WORDS: usize = 5;
pub const LOCALS: u64 = 4 << 36;
pub const CONTINUATIONS: u64 = 5 << 36;
pub const SCRATCH: u64 = 6 << 36;
pub const HEAP: u64 = 7 << 36;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum Phase {
  Eval = 0,
  Return = 1,
  Halted = 2,
  Apply = 3,
  Copy = 4,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Vector {
  pub pointer: u64,
  pub count: u8,
}
impl Vector {
  pub fn word(self) -> F128 {
    F128::new(self.pointer, u64::from(self.count))
  }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FrameState {
  pub phase: Phase,
  pub function: u16,
  pub block: u8,
  pub locals: u8,
  pub depth: u16,
  pub copy_index: u8,
  pub copy_count: u8,
  pub copy_base: u8,
  pub copy_pointer: u64,
  pub value: [F128; 2],
  pub arguments: Vector,
}
impl FrameState {
  pub fn eval(function: u16, block: u8, locals: u8, depth: u16) -> Self {
    Self {
      phase: Phase::Eval,
      function,
      block,
      locals,
      depth,
      copy_index: 0,
      copy_count: 0,
      copy_base: 0,
      copy_pointer: 0,
      value: [F128::ZERO; 2],
      arguments: Vector::default(),
    }
  }
  pub fn words(self) -> [F128; STATE_WORDS] {
    [
      F128::new(
        self.phase as u64
          | u64::from(self.function) << 8
          | u64::from(self.block) << 24
          | u64::from(self.locals) << 32
          | u64::from(self.depth) << 48,
        u64::from(self.copy_index)
          | u64::from(self.copy_count) << 8
          | u64::from(self.copy_base) << 16,
      ),
      F128::new(self.copy_pointer, 0),
      self.value[0],
      self.value[1],
      self.arguments.word(),
    ]
  }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum ActionKind {
  Bind = 1,
  Call = 2,
  TailCall = 3,
  Return = 4,
  Jump = 5,
  Append = 6,
  Apply = 7,
  TailApply = 8,
  ApplyReturn = 9,
  ApplyEnter = 10,
}

/// A constrained instruction/primitive consumer produces this command.
/// `arguments` must reference its completely resolved scratch vector or a
/// checked heap field vector. Persistent Apply vectors must be in the heap.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Action {
  pub kind: ActionKind,
  pub target: u8,
  pub callee: u16,
  pub entry: u8,
  pub arity: u8,
  pub arguments: Vector,
  pub value: [F128; 2],
  pub rest: Vector,
}
impl Action {
  pub fn new(kind: ActionKind) -> Self {
    Self {
      kind,
      target: 0,
      callee: 0,
      entry: 0,
      arity: 0,
      arguments: Vector::default(),
      value: [F128::ZERO; 2],
      rest: Vector::default(),
    }
  }
  pub fn words(self) -> [F128; 5] {
    [
      F128::new(
        self.kind as u64
          | u64::from(self.target) << 8
          | u64::from(self.callee) << 16
          | u64::from(self.entry) << 32
          | u64::from(self.arity) << 40,
        0,
      ),
      self.arguments.word(),
      self.value[0],
      self.value[1],
      self.rest.word(),
    ]
  }
}
