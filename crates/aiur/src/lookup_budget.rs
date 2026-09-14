// Copyright (c) 2026 Argument Computer Corporation.
// SPDX-License-Identifier: MIT OR Apache-2.0

use multi_stark::p3_field::PrimeField64;

use crate::G;

/// Upper bound on unit lookup consumers: one public claim plus every
/// lookup slot of every active trace row. Provider slots also count, making
/// this conservative without relying on witness multiplicities. Degrees
/// are indexed by active position; slot counts use canonical circuit order.
/// Reject malformed alignment and any bound reaching the characteristic.
pub(crate) fn lookup_query_bound(
  slot_counts: impl ExactSizeIterator<Item = usize>,
  active: &[bool],
  log_degrees: &[u8],
) -> Option<u64> {
  if slot_counts.len() != active.len() || !active.contains(&true) {
    return None;
  }
  let mut degrees = log_degrees.iter();
  let mut total = 1_u64;
  for (slots, &is_active) in slot_counts.zip(active) {
    if is_active {
      let height = 1_u64.checked_shl(u32::from(*degrees.next()?))?;
      let count = height.checked_mul(u64::try_from(slots).ok()?)?;
      total = total.checked_add(count)?;
      if total >= G::ORDER_U64 {
        return None;
      }
    }
  }
  degrees.next().is_none().then_some(total)
}
