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
/// Physical immutable-byte handle. The payload is a canonical u32 arena
/// index, never the array's contents or a prover-chosen digest.
pub const BYTES_TAG: u64 = 6;
/// Physical immutable constructor handle; its semantic identity is in the
/// authenticated declaration table, not in this numeric arena index.
pub const CTOR_TAG: u64 = 7;
/// Revision-1 exact Nat magnitude in the authenticated immutable arena.
pub const NAT_TAG: u64 = 8;
/// Immutable function/capture handle in the explicitly approved PAP setup.
pub const PAP_TAG: u64 = 9;

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

/// Byte-capable representation, deliberately separate from `scalar_cell` so
/// scalar-only tables retain their exact matrices and identities. Allocation
/// and dereferencing must additionally bind this index to a present immutable
/// record. This check alone does not authenticate any arena contents.
pub(super) fn cell_with_byte_handles(
  b: &mut BooleanR1csBuilder,
  one: usize,
  violations: &mut Vec<usize>,
  enabled: usize,
  bits: &[usize],
  entries: usize,
) -> [usize; 6] {
  use super::bits::{constant_bits, subtract};
  assert_eq!(bits.len(), 256);
  assert!(entries > 0 && entries <= u32::MAX as usize);
  let zero = b.xor(&[one, one], one);
  let disabled = not(b, one, enabled);
  require_zero(b, one, violations, disabled, bits);
  let byte_tag = equal_constant(b, one, &bits[..64], BYTES_TAG);
  let bytes = b.and(enabled, byte_tag);
  let not_bytes = not(b, one, byte_tag);
  let scalar = b.and(enabled, not_bytes);
  let masked: Vec<_> = bits.iter().map(|bit| b.and(scalar, *bit)).collect();
  let flags = scalar_cell(b, one, violations, scalar, &masked);
  require_zero(b, one, violations, bytes, &bits[64..128]);
  require_zero(b, one, violations, bytes, &bits[160..]);
  let maximum = constant_bits(one, zero, entries as u32);
  let in_range = subtract(b, one, zero, &bits[128..160], &maximum).1;
  require(b, one, violations, bytes, in_range);
  [flags[0], flags[1], flags[2], flags[3], flags[4], bytes]
}

pub(super) fn cell_with_object_handles(
  b: &mut BooleanR1csBuilder,
  one: usize,
  violations: &mut Vec<usize>,
  enabled: usize,
  bits: &[usize],
  byte_entries: usize,
  object_entries: usize,
) -> [usize; 7] {
  use super::bits::{constant_bits, subtract};
  let zero = b.xor(&[one, one], one);
  let disabled = not(b, one, enabled);
  require_zero(b, one, violations, disabled, bits);
  let ctor_tag = equal_constant(b, one, &bits[..64], CTOR_TAG);
  let ctor = b.and(enabled, ctor_tag);
  let other = b.xor(&[enabled, ctor], one);
  let masked: Vec<_> = bits.iter().map(|bit| b.and(other, *bit)).collect();
  let flags =
    cell_with_byte_handles(b, one, violations, other, &masked, byte_entries);
  require_zero(b, one, violations, ctor, &bits[64..128]);
  require_zero(b, one, violations, ctor, &bits[160..]);
  let limit = constant_bits(one, zero, object_entries as u32);
  let in_range = subtract(b, one, zero, &bits[128..160], &limit).1;
  require(b, one, violations, ctor, in_range);
  [flags[0], flags[1], flags[2], flags[3], flags[4], flags[5], ctor]
}

/// Revision-1 physical canonicality, including a distinct exact-Nat handle.
/// Magnitude canonicality is established by its producer and selected read.
pub(super) fn cell_with_nat_handles(
  b: &mut BooleanR1csBuilder,
  one: usize,
  violations: &mut Vec<usize>,
  enabled: usize,
  bits: &[usize],
  byte_entries: usize,
  object_entries: Option<usize>,
) -> [usize; 8] {
  use super::bits::{constant_bits, subtract};
  let zero = b.xor(&[one, one], one);
  let is_nat = equal_constant(b, one, &bits[..64], NAT_TAG);
  let nat = b.and(enabled, is_nat);
  let other = b.xor(&[enabled, nat], one);
  let masked: Vec<_> = bits.iter().map(|bit| b.and(other, *bit)).collect();
  let flags = match object_entries {
    Some(entries) => cell_with_object_handles(
      b,
      one,
      violations,
      other,
      &masked,
      byte_entries,
      entries,
    ),
    None => {
      let f = cell_with_byte_handles(
        b,
        one,
        violations,
        other,
        &masked,
        byte_entries,
      );
      [f[0], f[1], f[2], f[3], f[4], f[5], zero]
    },
  };
  let disabled = not(b, one, enabled);
  require_zero(b, one, violations, disabled, bits);
  require_zero(b, one, violations, nat, &bits[64..128]);
  require_zero(b, one, violations, nat, &bits[160..]);
  let limit = constant_bits(one, zero, byte_entries as u32);
  let fits = subtract(b, one, zero, &bits[128..160], &limit).1;
  require(b, one, violations, nat, fits);
  [flags[0], flags[1], flags[2], flags[3], flags[4], flags[5], flags[6], nat]
}

/// Explicit application setup: PAP handles share the immutable object arena,
/// but have a distinct tag and checked record kind at each selected read.
pub(super) fn cell_with_application_handles(
  b: &mut BooleanR1csBuilder,
  one: usize,
  violations: &mut Vec<usize>,
  enabled: usize,
  bits: &[usize],
  values: (usize, usize, bool),
) -> [usize; 9] {
  use super::bits::{constant_bits, subtract};
  let (bytes, objects, nats) = values;
  let zero = b.xor(&[one, one], one);
  let is_pap = equal_constant(b, one, &bits[..64], PAP_TAG);
  let pap = b.and(enabled, is_pap);
  let other = b.xor(&[enabled, pap], one);
  let masked: Vec<_> = bits.iter().map(|bit| b.and(other, *bit)).collect();
  let flags = if nats {
    cell_with_nat_handles(
      b,
      one,
      violations,
      other,
      &masked,
      bytes,
      Some(objects),
    )
  } else {
    let f = cell_with_object_handles(
      b, one, violations, other, &masked, bytes, objects,
    );
    [f[0], f[1], f[2], f[3], f[4], f[5], f[6], zero]
  };
  let disabled = not(b, one, enabled);
  require_zero(b, one, violations, disabled, bits);
  require_zero(b, one, violations, pap, &bits[64..128]);
  require_zero(b, one, violations, pap, &bits[160..]);
  let maximum = constant_bits(one, zero, objects as u32);
  let fits = subtract(b, one, zero, &bits[128..160], &maximum).1;
  require(b, one, violations, pap, fits);
  [
    flags[0], flags[1], flags[2], flags[3], flags[4], flags[5], flags[6],
    flags[7], pap,
  ]
}
