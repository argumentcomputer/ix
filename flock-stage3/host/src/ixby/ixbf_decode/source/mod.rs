//! Original-byte reads authenticated to the standard unkeyed BLAKE3 digest.
//! This is not an Exec commitment format or whole-file grammar admission.
//! In particular, a chunk path alone does not bind a claimed file length:
//! the reader also authenticates that length's final chunk to the SAME root.

mod block;
mod path;
#[cfg(test)]
mod proof_tests;
mod reader;
#[cfg(test)]
mod tests;
#[cfg(test)]
pub(in crate::ixby::ixbf_decode) fn test_chunk_advice(
  bytes: &[u8],
  index: usize,
  depth: usize,
) -> Vec<flock_prover::field::F128> {
  tests::NativeTree::new(bytes.to_vec()).proof(index, depth).inputs()
}
mod window;

pub use block::{SourceBlockGate, SourceBlockRow};
pub use path::{SourcePathGate, SourcePathRow};
pub use reader::{SourceChunkProofWires, SourceReadSlots, SourceReadWires};
pub use window::{SourceWindowGate, SourceWindowRow};

use super::synthesis::{Bits, Builder};
use crate::ixby::bits::subtract;
use anyhow::{Result, ensure};

pub const SOURCE_CHUNK_BYTES: usize = 1024;
pub const SOURCE_CHUNK_WORDS: usize = 64;
/// u64 byte lengths require at most 54 chunk-tree levels. No old buffer,
/// profile, factory or guest limit is enlarged by admitting this component.
pub const MAX_SOURCE_DEPTH: usize = 54;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SourceCapacity {
  depth: usize,
  window: usize,
}

impl SourceCapacity {
  pub fn new(depth: usize, window: usize) -> Result<Self> {
    ensure!(depth <= MAX_SOURCE_DEPTH, "source tree depth admission");
    ensure!(window <= SOURCE_CHUNK_BYTES, "source read window admission");
    Ok(Self { depth, window })
  }
  pub fn depth(self) -> usize {
    self.depth
  }
  pub fn window_bytes(self) -> usize {
    self.window
  }
  pub fn window_words(self) -> usize {
    self.window.div_ceil(16)
  }
  pub fn admits_length(self, length: u64) -> bool {
    last_index(length) >> self.depth == 0
  }
}

pub(super) fn last_index(length: u64) -> u64 {
  length.saturating_sub(1) >> 10
}

pub(super) fn choose(
  b: &mut Builder,
  flag: usize,
  yes: usize,
  no: usize,
) -> usize {
  let delta = b.b.product_of_parities(&[flag], &[yes, no]);
  b.sum(&[no, delta])
}

pub(super) fn choose_bits(
  b: &mut Builder,
  flag: usize,
  yes: &[usize],
  no: &[usize],
) -> Bits {
  assert_eq!(yes.len(), no.len());
  yes.iter().zip(no).map(|(&y, &n)| choose(b, flag, y, n)).collect()
}

pub(super) struct FileBits {
  last: Bits,
  /// Eleven-bit exact length of the last chunk, including empty-file zero.
  tail: Bits,
  single: usize,
}

/// All sizes are derived from the exact 64-bit byte length. Empty files have
/// one empty chunk. The last index is floor((length - 1) / 1024), not length/1024.
pub(super) fn file_bits(
  b: &mut Builder,
  length: &[usize],
  depth: usize,
) -> FileBits {
  assert_eq!(length.len(), 64);
  let one = b.constant(64, 1);
  let (less_one, _) = subtract(&mut b.b, b.one, b.zero, length, &one);
  let nonempty = b.any(length);
  let mut last: Bits =
    less_one[10..].iter().map(|&bit| b.b.and(nonempty, bit)).collect();
  last.resize(64, b.zero);
  b.require_zero(b.one, &last[depth..]);
  let any_last = b.any(&last);
  let single = b.not(any_last);
  let mut tail = less_one[..10].to_vec();
  tail.push(b.zero);
  let one = b.constant(11, 1);
  let (tail, _) = crate::ixby::bits::add(&mut b.b, b.one, b.zero, &tail, &one);
  let tail = tail.iter().map(|&bit| b.b.and(nonempty, bit)).collect();
  FileBits { last, tail, single }
}

pub(super) fn require_index(b: &mut Builder, index: &[usize], last: &[usize]) {
  let (_, bad) = subtract(&mut b.b, b.one, b.zero, last, index);
  b.violations.push(bad);
}

/// Derive all `i < value` bits for a small integer without a full-width
/// subtraction per byte. Equality leaves and suffixes are mutually exclusive.
fn small_prefix(b: &mut Builder, bits: &[usize]) -> Bits {
  let mut equal = vec![b.one];
  for &bit in bits.iter().rev() {
    equal = equal
      .into_iter()
      .flat_map(|flag| {
        [b.b.product_of_parities(&[flag], &[bit, b.one]), b.b.and(flag, bit)]
      })
      .collect();
  }
  let mut output = vec![b.zero; equal.len()];
  let mut suffix = b.zero;
  for index in (0..equal.len()).rev() {
    output[index] = suffix;
    suffix = b.sum(&[suffix, equal[index]]);
  }
  output
}

pub(super) fn prefix(b: &mut Builder, value: &[usize], count: usize) -> Bits {
  if count == 0 {
    return Vec::new();
  }
  let width = count.next_power_of_two().ilog2() as usize;
  let large = b.any(&value[width..]);
  small_prefix(b, &value[..width])
    .into_iter()
    .take(count)
    .map(|small| crate::ixby::bits::or(&mut b.b, b.one, large, small))
    .collect()
}
