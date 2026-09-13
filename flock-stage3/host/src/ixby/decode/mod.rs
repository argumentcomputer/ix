//! Canonical scalar/byte/control admission. All parsing loops are bounded by
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
mod tree;

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

/// Existing crypto-v0 opcodes in the original twenty-opcode scalar slice.
/// Retained unchanged for the approved legacy scalar and byte setups.
pub const SCALAR_PRIMITIVES: &[u8] =
  &[0, 3, 4, 5, 9, 10, 13, 14, 15, 16, 17, 18, 21, 22, 23, 24, 25, 26, 27, 28];
/// Existing crypto-v0 byte/conversion/hash opcodes, not new guest semantics.
pub const BYTE_PRIMITIVES: &[u8] = &[11, 12, 19, 20, 29, 30, 31, 32, 33, 34];
/// Remaining fixed-width word operations in the complete crypto-v0 registry.
pub const EXTRA_WORD_PRIMITIVES: &[u8] = &[1, 2, 6, 7, 8];
pub const NAT_PRIMITIVES: &[u8] = &[35, 36, 37, 38, 39, 40, 41];

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
  pub fn with_bytes(opcodes: &[u8]) -> Result<Self> {
    let mut mask = 0;
    for opcode in opcodes {
      ensure!(
        SCALAR_PRIMITIVES.contains(opcode) || BYTE_PRIMITIVES.contains(opcode),
        "unsupported byte-profile primitive"
      );
      let bit = 1u64 << opcode;
      ensure!(mask & bit == 0, "duplicate byte-profile primitive");
      mask |= bit;
    }
    Ok(Self(mask))
  }
  pub fn crypto_bytes() -> Self {
    Self::with_bytes(&[SCALAR_PRIMITIVES, BYTE_PRIMITIVES].concat()).unwrap()
  }
  /// Explicit upgrade to any subset of the existing 35 crypto-v0 opcodes.
  /// The older scalar and 30-opcode byte registries retain their identities.
  pub fn with_crypto(opcodes: &[u8]) -> Result<Self> {
    let mut mask = 0;
    for opcode in opcodes {
      ensure!(*opcode < 35, "unsupported crypto-v0 primitive");
      let bit = 1u64 << opcode;
      ensure!(mask & bit == 0, "duplicate crypto-v0 primitive");
      mask |= bit;
    }
    Ok(Self(mask))
  }
  pub fn crypto() -> Self {
    Self::with_crypto(&(0..35).collect::<Vec<_>>()).unwrap()
  }
  /// Explicit revision-1 opcode family; v0 constructors retain their bounds.
  pub fn with_nat(opcodes: &[u8]) -> Result<Self> {
    let mut mask = 0;
    for opcode in opcodes {
      ensure!(*opcode < 42, "unsupported crypto-Nat-v1 primitive");
      let bit = 1u64 << opcode;
      ensure!(mask & bit == 0, "duplicate crypto-Nat-v1 primitive");
      mask |= bit;
    }
    Ok(Self(mask))
  }
  pub fn crypto_nat() -> Self {
    Self::with_nat(&(0..42).collect::<Vec<_>>()).unwrap()
  }
  pub(crate) fn crypto_subset(self) -> Self {
    Self::with_crypto(&self.opcodes().filter(|op| *op < 35).collect::<Vec<_>>())
      .unwrap()
  }
  pub(crate) fn crypto_scalar_subset(self) -> Self {
    Self::with_crypto(
      &self
        .opcodes()
        .filter(|opcode| *opcode < 35 && !BYTE_PRIMITIVES.contains(opcode))
        .collect::<Vec<_>>(),
    )
    .unwrap()
  }
  pub(crate) fn scalar_subset(self) -> Self {
    Self::new(
      &self
        .opcodes()
        .filter(|opcode| SCALAR_PRIMITIVES.contains(opcode))
        .collect::<Vec<_>>(),
    )
    .unwrap()
  }
  pub fn contains(self, opcode: u8) -> bool {
    opcode < 64 && self.0 & (1u64 << opcode) != 0
  }
  pub fn opcodes(self) -> impl Iterator<Item = u8> {
    (0u8..42).filter(move |opcode| self.contains(*opcode))
  }
}

pub fn primitive_arity(opcode: u8) -> Option<usize> {
  if NAT_PRIMITIVES.contains(&opcode) {
    Some(2)
  } else if BYTE_PRIMITIVES.contains(&opcode) {
    Some(match opcode {
      30 | 31 | 33 => 2,
      32 => 3,
      _ => 1,
    })
  } else if EXTRA_WORD_PRIMITIVES.contains(&opcode) {
    Some(2)
  } else {
    scalar_primitive_arity(opcode)
  }
}

pub fn scalar_primitive_arity(opcode: u8) -> Option<usize> {
  SCALAR_PRIMITIVES
    .contains(&opcode)
    .then_some(if matches!(opcode, 13 | 17 | 24 | 27 | 28) { 1 } else { 2 })
}
