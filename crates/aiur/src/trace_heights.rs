// Copyright (c) 2026 Argument Computer Corporation.
// SPDX-License-Identifier: MIT OR Apache-2.0

/// Match active-order degrees to canonical fixed preprocessed heights.
/// Zero denotes a circuit without a fixed height; inactive unfixed circuits
/// consume no degree. Fixed circuits must be active. This check precedes PCS
/// verification so fixed-table extraction
/// has an explicit height condition at the Aiur verifier boundary.
pub(crate) fn fixed_trace_heights(
  heights: impl ExactSizeIterator<Item = usize>,
  active: &[bool],
  log_degrees: &[u8],
) -> bool {
  if heights.len() != active.len() {
    return false;
  }
  let mut degrees = log_degrees.iter();
  for (height, &is_active) in heights.zip(active) {
    if height != 0 && !is_active {
      return false;
    }
    if is_active {
      let Some(&degree) = degrees.next() else {
        return false;
      };
      if height != 0 {
        let Some(actual) = 1_u64.checked_shl(u32::from(degree)) else {
          return false;
        };
        if u64::try_from(height) != Ok(actual) {
          return false;
        }
      }
    }
  }
  degrees.next().is_none()
}

/// Every input matrix must be injected before the path reaches the cap.
/// The native MMCS clamps a cap to the tallest matrix's tree depth; that
/// still omits shorter matrices when the cap lies below their injection.
/// Subtract the shared blowup first, avoiding machine addition overflow.
pub(crate) fn trace_cap_coverage(
  log_blowup: usize,
  cap_height: usize,
  log_degrees: &[u8],
) -> bool {
  let maximum = log_degrees.iter().copied().max().unwrap_or(0);
  let effective =
    cap_height.saturating_sub(log_blowup).min(usize::from(maximum));
  log_degrees.iter().all(|&degree| effective <= usize::from(degree))
}
