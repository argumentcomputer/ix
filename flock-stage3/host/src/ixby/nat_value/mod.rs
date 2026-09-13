//! Exact bounded natural numbers. Nat cells have their own tag and point into
//! the authenticated immutable magnitude arena; they are never Word32 values.
//! The bit bound is verifier-owned setup, not a witness-selected limb count.

mod arithmetic;
mod bits;
mod dispatch;
#[cfg(test)]
mod tests;

pub(crate) use dispatch::NatDispatchGate;

use anyhow::{Result, ensure};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct NatCapacity(usize);

impl NatCapacity {
  pub fn new(bits: usize) -> Result<Self> {
    // This is a bounded Boolean prototype, not a scalable big-integer VM.
    ensure!(bits <= 1024, "prototype Nat bit capacity");
    Ok(Self(bits))
  }
  pub fn bits(self) -> usize {
    self.0
  }
  pub fn bytes(self) -> usize {
    self.0.div_ceil(8)
  }
}

/// Check the *minimal* byte magnitude and its exact (possibly partial-byte)
/// bound. Padding after `length` is checked by the ordinary arena reader.
pub(crate) fn canonical_magnitude(
  b: &mut crate::boolean::BooleanR1csBuilder,
  one: usize,
  zero: usize,
  violations: &mut Vec<usize>,
  enabled: usize,
  capacity: NatCapacity,
  buffer: &[usize],
) {
  use super::bits::{
    any, constant_bits, equal_constant, require, require_zero, subtract,
  };
  assert!(buffer.len() >= 128 + capacity.bits());
  let maximum = constant_bits(one, zero, (capacity.bytes() + 1) as u32);
  let fits = subtract(b, one, zero, &buffer[..32], &maximum).1;
  require(b, one, violations, enabled, fits);
  for byte in 0..capacity.bytes() {
    let last = equal_constant(b, one, &buffer[..32], (byte + 1) as u64);
    let last = b.and(enabled, last);
    let nonzero = any(b, one, &buffer[128 + 8 * byte..136 + 8 * byte]);
    require(b, one, violations, last, nonzero);
  }
  require_zero(b, one, violations, enabled, &buffer[128 + capacity.bits()..]);
}
