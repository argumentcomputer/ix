//! Direct advice for byte windows and scalar reads. The proof uses bytes.rs.
use super::{bytes::*, *};
use crate::ixby::{
  paged_frame::ActionKind,
  paged_value::{DYNAMIC_BYTES, INPUT_BYTES, PROGRAM_BYTES},
};
fn w(n: u64) -> F128 {
  F128::new(n, 0)
}
pub(super) fn evaluate(
  kind: ByteKind,
  state: &[F128],
  x: &[F128],
) -> Option<Vec<F128>> {
  match kind {
    ByteKind::Window => {
      let pointer = x[0].lo;
      let count = x[1].lo;
      if x[0].hi != 0
        || x[1].hi != 0
        || pointer >= 1 << 45
        || count > 64
        || (count == 0 && pointer != 0)
        || (count != 0
          && ![PROGRAM_BYTES, INPUT_BYTES, DYNAMIC_BYTES]
            .contains(&((pointer >> 5) & (15 << 36))))
        || (pointer & ((1 << 41) - 1)).checked_add(count)? > 1 << 41
      {
        return None;
      }
      let offset = (pointer & 31) as usize;
      let cells = (offset + count as usize).div_ceil(32);
      if x[2 + 2 * cells..].iter().any(|&v| v != F128::ZERO) {
        return None;
      }
      let mut raw = [0u8; 96];
      for (i, word) in x[2..].iter().enumerate() {
        raw[16 * i..16 * i + 8].copy_from_slice(&word.lo.to_le_bytes());
        raw[16 * i + 8..16 * i + 16].copy_from_slice(&word.hi.to_le_bytes());
      }
      let mut data = [0u8; 64];
      data[..count as usize]
        .copy_from_slice(&raw[offset..offset + count as usize]);
      let mut out = data
        .as_chunks::<16>()
        .0
        .iter()
        .map(|bytes| {
          F128::new(
            u64::from_le_bytes(bytes[..8].try_into().unwrap()),
            u64::from_le_bytes(bytes[8..].try_into().unwrap()),
          )
        })
        .collect::<Vec<_>>();
      for i in 0..3 {
        out.extend([
          w(if i < cells { (pointer >> 5) + i as u64 } else { 0 }),
          F128::ZERO,
          x[2 + 2 * i],
          x[3 + 2 * i],
        ]);
      }
      Some(out)
    },
    ByteKind::ReadRequest | ByteKind::ReadFinish => {
      let opcode = (state[HEADER].lo >> 24) as u8;
      let count = match opcode {
        22 => 4,
        30 => 8,
        40 => 1,
        _ => return None,
      };
      let position = state[POSITION].lo;
      if state[POSITION].hi != 0
        || position.checked_add(count)? > state[A].hi
        || (opcode != 40 && (position != 0 || state[A].hi != count))
        || (opcode == 40 && position > u64::from(u32::MAX))
      {
        return None;
      }
      if kind == ByteKind::ReadRequest {
        Some(vec![w(state[A].lo.checked_add(position)?), w(count)])
      } else {
        if x[0].hi != 0
          || x[1..].iter().any(|&v| v != F128::ZERO)
          || (opcode == 30 && x[0].lo >= crate::goldilocks::GOLDILOCKS_MODULUS)
          || (opcode != 30 && x[0].lo > u64::from(u32::MAX))
        {
          return None;
        }
        let mut out = state.to_vec();
        out[RESULT + 1] = x[0];
        out[CONTROL] = w(BYTE_FINISH);
        Some(out)
      }
    },
    ByteKind::Finish => Some(vec![
      w(ActionKind::Bind as u64 | ((state[HEADER].hi >> 16) & 255) << 8),
      F128::ZERO,
      state[RESULT],
      state[RESULT + 1],
      F128::ZERO,
    ]),
    _ => None,
  }
}
