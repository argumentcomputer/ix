//! Internal scalar gate selectors. These are circuit controls, not wire opcodes.
use anyhow::{Result, ensure};

/// Selector codes implemented by the base scalar gate.
pub const SCALAR_PRIMITIVES: &[u8] =
  &[0, 3, 4, 5, 9, 10, 13, 14, 15, 16, 17, 18, 21, 22, 23, 24, 25, 26, 27, 28];
/// Selector codes reserved for byte operations.
pub const BYTE_PRIMITIVES: &[u8] = &[11, 12, 19, 20, 29, 30, 31, 32, 33, 34];
/// Additional fixed-width word selectors.
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
        "unsupported scalar/byte circuit selector"
      );
      let bit = 1u64 << opcode;
      ensure!(mask & bit == 0, "duplicate scalar/byte circuit selector");
      mask |= bit;
    }
    Ok(Self(mask))
  }
  pub fn crypto_bytes() -> Self {
    Self::with_bytes(&[SCALAR_PRIMITIVES, BYTE_PRIMITIVES].concat()).unwrap()
  }
  /// Select a subset of the scalar and byte circuit controls.
  pub fn with_crypto(opcodes: &[u8]) -> Result<Self> {
    let mut mask = 0;
    for opcode in opcodes {
      ensure!(*opcode < 35, "unsupported scalar/byte circuit selector");
      let bit = 1u64 << opcode;
      ensure!(mask & bit == 0, "duplicate scalar/byte circuit selector");
      mask |= bit;
    }
    Ok(Self(mask))
  }
  pub fn crypto() -> Self {
    Self::with_crypto(&(0..35).collect::<Vec<_>>()).unwrap()
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
  #[cfg(test)]
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
