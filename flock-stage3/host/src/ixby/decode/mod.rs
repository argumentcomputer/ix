//! Canonical scalar/control byte admission. All parsing loops are bounded by
//! setup capacities; actual counts, tags, offsets and references are circuit
//! values. No host decoder's acceptance bit is an input to these gates.

mod bytes;
mod fetch;
mod input;
mod operands;
mod program;
mod scalar;
#[cfg(test)]
pub(crate) mod test_support;

pub use fetch::{ProgramFetchGate, ProgramFetchRow, ProgramFetchSlot};
pub use input::{
  InputCapacities, InputDecodeGate, InputDecodeRow, InputDecodeSlot,
};
pub use operands::{OperandResolveGate, OperandResolveRow, OperandResolveSlot};
pub use program::{
  ProgramCapacities, ProgramDecodeGate, ProgramDecodeRow, ProgramDecodeSlot,
  ProgramLayout,
};

use super::bits::{evaluate_words as evaluate, fill_words};
use anyhow::{Result, ensure};

/// Existing crypto-v0 opcodes in the first-order scalar slice. This is the
/// same subset as the reference control corpus, not a new guest instruction set.
pub const SCALAR_PRIMITIVES: &[u8] =
  &[0, 3, 4, 5, 9, 10, 13, 14, 15, 16, 17, 18, 21, 22, 23, 24, 25, 26, 27, 28];

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PrimitiveSet(u64);

impl PrimitiveSet {
  pub fn new(opcodes: &[u8]) -> Result<Self> {
    let mut mask = 0;
    for opcode in opcodes {
      ensure!(
        SCALAR_PRIMITIVES.contains(opcode),
        "unsupported scalar primitive"
      );
      let bit = 1u64 << opcode;
      ensure!(mask & bit == 0, "duplicate scalar primitive");
      mask |= bit;
    }
    Ok(Self(mask))
  }
  pub fn scalar() -> Self {
    Self::new(SCALAR_PRIMITIVES).unwrap()
  }
  pub fn contains(self, opcode: u8) -> bool {
    opcode < 64 && self.0 & (1u64 << opcode) != 0
  }
  pub fn opcodes(self) -> impl Iterator<Item = u8> {
    SCALAR_PRIMITIVES
      .iter()
      .copied()
      .filter(move |opcode| self.contains(*opcode))
  }
}

pub fn scalar_primitive_arity(opcode: u8) -> Option<usize> {
  SCALAR_PRIMITIVES
    .contains(&opcode)
    .then_some(if matches!(opcode, 13 | 17 | 24 | 27 | 28) { 1 } else { 2 })
}
