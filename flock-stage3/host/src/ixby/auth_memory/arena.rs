use super::*;

/// Root and allocated prefix. A segment must authenticate all three boundary
/// words; a root alone does not prove that a cell was allocated.
#[derive(Clone, Copy)]
pub struct ArenaStateWires {
  root: [Wire; 2],
  allocated: Wire,
}
impl ArenaStateWires {
  pub fn from_boundary(words: [Wire; 3]) -> Self {
    Self { root: [words[0], words[1]], allocated: words[2] }
  }
  pub fn words(self) -> [Wire; 3] {
    [self.root[0], self.root[1], self.allocated]
  }
}

/// Immutable cells are allocated in exact increasing order. Reading requires
/// an index inside that prefix; allocation authenticates an all-zero old cell
/// before replacing it and incrementing the full-width counter without wrap.
pub struct ImmutableArenaSlots {
  memory: MemoryAccessSlots,
  index: (SlotId, MemoryGate),
  empty: [Wire; 2],
  zero: Wire,
  one: Wire,
  residual: Wire,
}
impl ImmutableArenaSlots {
  pub fn declare(
    b: &mut impl CircuitEmitter,
    nu: usize,
    depth: MemoryDepth,
  ) -> Result<Self> {
    let memory = MemoryAccessSlots::declare(b, nu, depth)?;
    let gate = MemoryGate::new(nu, depth, MemoryGateKind::Index)?;
    let index = (b.slot(gate.clone()), gate);
    // These are proof-free setup constants, bound by the circuit digest.
    let empty =
      SparseMemory::new(depth).empty_root().map(|v| b.fixed_public_input(v));
    Ok(Self {
      memory,
      index,
      empty,
      zero: b.fixed_public_input(F128::ZERO),
      one: b.fixed_public_input(F128::ONE),
      residual: b.fixed_public_input(F128::ZERO),
    })
  }
  pub fn memory(&self) -> &MemoryAccessSlots {
    &self.memory
  }
  pub fn index_gate(&self) -> (SlotId, &MemoryGate) {
    (self.index.0, &self.index.1)
  }
  pub fn initialize(&self) -> ArenaStateWires {
    ArenaStateWires { root: self.empty, allocated: self.zero }
  }
  fn index(
    &self,
    b: &mut impl CircuitEmitter,
    state: ArenaStateWires,
    address: Wire,
    mode: Wire,
  ) -> Wire {
    let output = b.gate(self.index.0, &[address, state.allocated, mode]);
    b.connect(output[1], self.residual);
    output[0]
  }
  pub fn allocate(
    &self,
    b: &mut impl CircuitEmitter,
    state: ArenaStateWires,
    value: [Wire; 2],
    opening: &MemoryOpeningWires,
  ) -> (ArenaStateWires, Wire) {
    let address = state.allocated;
    let allocated = self.index(b, state, address, self.one);
    for word in opening.value {
      b.connect(word, self.zero);
    }
    let root = self.memory.replace(b, state.root, address, opening, value);
    (ArenaStateWires { root, allocated }, address)
  }
  pub fn read(
    &self,
    b: &mut impl CircuitEmitter,
    state: ArenaStateWires,
    address: Wire,
    opening: &MemoryOpeningWires,
  ) -> [Wire; 2] {
    self.index(b, state, address, self.zero);
    self.memory.read(b, state.root, address, opening)
  }
}
