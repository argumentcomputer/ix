//! Canonical 32-byte values for the paged execution component. Exact Nat
//! magnitudes occupy the full 128-bit payload. Constructors/PAPs name a
//! declaration plus an immutable field vector; bytes name an actual byte
//! range. These are deliberately different from the old fixed-arena handles.
//! Allocation, source binding, and semantic limits are separate consumers.
use crate::{
  boolean::BooleanR1csBuilder,
  ixby::{
    bits::{add, any, equal_constant, not, require, require_zero, subtract},
    paged_frame::HEAP,
    value::scalar_cell,
  },
};

pub const PROGRAM_BYTES: u64 = 8 << 36;
pub const INPUT_BYTES: u64 = 9 << 36;
pub const DYNAMIC_BYTES: u64 = 10 << 36;
pub const STRING_TAG: u64 = 10;

fn constant(one: usize, zero: usize, length: usize, value: u64) -> Vec<usize> {
  (0..length).map(|i| if value & (1 << i) == 0 { zero } else { one }).collect()
}

pub(super) fn cell(
  b: &mut BooleanR1csBuilder,
  one: usize,
  violations: &mut Vec<usize>,
  enabled: usize,
  bits: &[usize],
  literal_only: bool,
) -> [usize; 10] {
  assert_eq!(bits.len(), 256);
  let zero = b.xor(&[one, one], one);
  let disabled = not(b, one, enabled);
  require_zero(b, one, violations, disabled, bits);
  let tags = (1..=10)
    .map(|tag| equal_constant(b, one, &bits[..64], tag))
    .collect::<Vec<_>>();
  let valid = b.xor(&tags, one);
  require(b, one, violations, enabled, valid);
  let flags = tags.iter().map(|&tag| b.and(enabled, tag)).collect::<Vec<_>>();
  if literal_only {
    violations.extend([flags[6], flags[8]]);
  }
  let scalar = b.xor(&flags[..5], one);
  let masked = bits.iter().map(|&bit| b.and(scalar, bit)).collect::<Vec<_>>();
  scalar_cell(b, one, violations, scalar, &masked);
  let bytes = b.xor(&[flags[5], flags[9]], one);
  let plain_header = b.xor(&[bytes, flags[7]], one);
  require_zero(b, one, violations, plain_header, &bits[64..128]);

  // Byte pointers include the byte offset within a 32-byte authenticated cell.
  require_zero(b, one, violations, bytes, &bits[173..192]);
  require_zero(b, one, violations, bytes, &bits[228..]);
  let empty = equal_constant(b, one, &bits[192..228], 0);
  let nonempty = not(b, one, empty);
  let byte_live = b.and(bytes, nonempty);
  let byte_empty = b.and(bytes, empty);
  require_zero(b, one, violations, byte_empty, &bits[128..173]);
  let banks = [PROGRAM_BYTES, INPUT_BYTES, DYNAMIC_BYTES]
    .map(|bank| equal_constant(b, one, &bits[169..173], bank >> 36));
  let valid_bank = b.xor(&banks, one);
  require(b, one, violations, byte_live, valid_bank);
  let mut offset = bits[128..169].to_vec();
  offset.push(zero);
  let mut length = bits[192..228].to_vec();
  length.resize(42, zero);
  let end = add(b, one, zero, &offset, &length).0;
  let end_low = any(b, one, &end[..41]);
  let over = b.and(end[41], end_low);
  violations.push(b.and(byte_live, over));

  let objects = b.xor(&[flags[6], flags[8]], one);
  require_zero(b, one, violations, objects, &bits[168..192]);
  require_zero(b, one, violations, objects, &bits[200..]);
  for (flag, maximum) in [(flags[6], 256), (flags[8], 1024)] {
    let bound = constant(one, zero, 64, maximum);
    let fits = subtract(b, one, zero, &bits[64..128], &bound).1;
    require(b, one, violations, flag, fits);
  }
  let bound = constant(one, zero, 8, 65);
  let count_ok = subtract(b, one, zero, &bits[192..200], &bound).1;
  require(b, one, violations, objects, count_ok);
  let empty = equal_constant(b, one, &bits[192..200], 0);
  let nonempty = not(b, one, empty);
  let object_live = b.and(objects, nonempty);
  let object_empty = b.and(objects, empty);
  require_zero(b, one, violations, object_empty, &bits[128..168]);
  let heap = equal_constant(b, one, &bits[164..168], HEAP >> 36);
  require(b, one, violations, object_live, heap);
  let mut offset = bits[128..164].to_vec();
  offset.push(zero);
  let mut count = bits[192..200].to_vec();
  count.resize(37, zero);
  let end = add(b, one, zero, &offset, &count).0;
  let end_low = any(b, one, &end[..36]);
  let over = b.and(end[36], end_low);
  violations.push(b.and(object_live, over));
  flags.try_into().unwrap()
}
