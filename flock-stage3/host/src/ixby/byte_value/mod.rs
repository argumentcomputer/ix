//! Immutable byte values for the generic executor. Frames contain two-word
//! tagged handles; array records are derived from authenticated decoders or
//! preceding constrained operations, never supplied as an ambient host heap.
//! Each physical allocation has a setup-fixed index. Unallocated records are
//! zero, distinguishable from a present empty array by the presence bit.
//!
//! Record word 0 is `(length:u32, present:bit, zeros)`; remaining words pack
//! bytes little-endian, sixteen per F128, with canonical zero padding. The
//! selector implementation is a bounded prototype, not a scalable RAM proof.

mod primitive;
mod read;
#[cfg(test)]
mod tests;

pub use primitive::{BytePrimitiveGate, BytePrimitiveRow};
pub use read::{ByteReadGate, ByteReadRow, ByteReadSlot};

use anyhow::{Result, ensure};

/// Checked setup data. This is a per-array bound, distinct from serialized
/// program/input/output buffer limits and the number of immutable records.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ByteCapacity(usize);

impl ByteCapacity {
  pub fn new(bytes: usize) -> Result<Self> {
    ensure!((1..=4096).contains(&bytes), "prototype byte-array capacity");
    Ok(Self(bytes))
  }
  pub fn bytes(self) -> usize {
    self.0
  }
  pub fn data_words(self) -> usize {
    self.0.div_ceil(16)
  }
  pub fn record_words(self) -> usize {
    1 + self.data_words()
  }
}

/// Decoder-owned allocation range. A handle for source slot i is base+i;
/// nothing in a guest's serialized value chooses that physical index.
#[derive(Clone, Copy, Debug)]
pub(crate) struct ByteDecodeLayout {
  pub capacity: ByteCapacity,
  pub base: usize,
}

impl ByteDecodeLayout {
  pub(crate) fn validate(self, records: usize) -> Result<()> {
    ensure!(
      self.base.checked_add(records).is_some_and(|end| end <= 1024),
      "prototype immutable-byte allocation range"
    );
    Ok(())
  }
}

pub(super) fn validate_entries(entries: usize) -> Result<()> {
  ensure!((1..=1024).contains(&entries), "prototype immutable-byte entries");
  Ok(())
}
