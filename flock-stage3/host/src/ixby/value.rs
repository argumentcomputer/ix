//! Experimental physical scalar cells: one canonical tag word and one full
//! F128 payload. This is NOT the variable-length IxBy byte codec. Zero/zero is
//! unused padding, distinct from the live Bool(false) and erased values.
//! The control component treats cells opaquely except at a Bool branch;
//! separate value/primitive/codec constraints must establish live canonicality.

use crate::{
  boolean::BooleanR1csBuilder,
  ixby::bits::{any, equal_constant, not, require, require_zero},
};
use flock_prover::field::F128;

pub type ValueWords = [F128; 2];

pub const BOOL_TAG: u64 = 1;
pub const WORD32_TAG: u64 = 2;
pub const FIELD_TAG: u64 = 3;
pub const EXT_TAG: u64 = 4;
pub const ERASED_TAG: u64 = 5;

pub fn bool_words(value: bool) -> ValueWords {
  [F128::new(BOOL_TAG, 0), F128::new(u64::from(value), 0)]
}

pub fn word32_words(value: u32) -> ValueWords {
  [F128::new(WORD32_TAG, 0), F128::new(u64::from(value), 0)]
}

/// Canonical live scalar cell, or exactly zero padding when disabled. Returns
/// the five mutually exclusive, enabled physical tag flags in tag order.
pub(super) fn scalar_cell(
  b: &mut BooleanR1csBuilder,
  one: usize,
  violations: &mut Vec<usize>,
  enabled: usize,
  bits: &[usize],
) -> [usize; 5] {
  assert_eq!(bits.len(), 256);
  let disabled = not(b, one, enabled);
  require_zero(b, one, violations, disabled, bits);
  require_zero(b, one, violations, enabled, &bits[64..128]);
  let matches: Vec<_> =
    (1..=5).map(|tag| equal_constant(b, one, &bits[..64], tag)).collect();
  let valid = b.xor(&matches, one);
  require(b, one, violations, enabled, valid);
  let flags: [usize; 5] = matches
    .iter()
    .map(|flag| b.and(enabled, *flag))
    .collect::<Vec<_>>()
    .try_into()
    .unwrap();
  let [boolean, word, field, extension, erased] = flags;
  require_zero(b, one, violations, boolean, &bits[129..]);
  require_zero(b, one, violations, word, &bits[160..]);
  require_zero(b, one, violations, field, &bits[192..]);
  require_zero(b, one, violations, erased, &bits[128..]);
  let first = b.xor(&[field, extension], one);
  for (flag, base) in [(first, 128), (extension, 192)] {
    let high =
      equal_constant(b, one, &bits[base + 32..base + 64], u32::MAX as u64);
    let low = any(b, one, &bits[base..base + 32]);
    let bad = b.and(high, low);
    violations.push(b.and(flag, bad));
  }
  flags
}
