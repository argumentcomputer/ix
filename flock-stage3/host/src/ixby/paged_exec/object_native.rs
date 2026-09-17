//! Untrusted object advice; Boolean relations remain the proof's validators.
use super::*;
use crate::ixby::paged_frame::{ActionKind, HEAP, SCRATCH};

fn w(n: u64) -> F128 {
  F128::new(n, 0)
}
fn vector(pointer: u64, count: u64) -> F128 {
  F128::new(if count == 0 { 0 } else { pointer }, count)
}
pub(super) fn evaluate(
  kind: ObjectKind,
  state: &[F128],
  x: &[F128],
) -> Option<Vec<F128>> {
  let h = state[HEADER];
  let target = (h.hi >> 16) & 255;
  let count = (h.lo >> 40) & 255;
  let mut action = vec![F128::ZERO; 5];
  action[0] = w(ActionKind::Bind as u64 | target << 8);
  match kind {
    ObjectKind::Reference => Some(vec![w(h.hi & 65535)]),
    ObjectKind::OperandRequest => Some(vec![w(SCRATCH), w((h.lo >> 48) & 255)]),
    ObjectKind::Construct
    | ObjectKind::Closure
    | ObjectKind::ApplyInstruction => {
      let heap = state[HEAP_COUNT].lo;
      let reserved = heap.checked_add(count)?;
      if count > 64 || state[HEAP_COUNT].hi != 0 || reserved > 1 << 36 {
        return None;
      }
      let result = vector(HEAP + heap, count);
      let applying = kind == ObjectKind::ApplyInstruction;
      if applying {
        action[0] = if (h.lo >> 8) & 255 == 0 {
          w(ActionKind::Apply as u64 | target << 8)
        } else {
          w(ActionKind::TailApply as u64)
        };
        action[1] = result;
        action[2..4].copy_from_slice(x);
      } else {
        let constructor = kind == ObjectKind::Construct;
        if (constructor && count != x[0].lo & 255)
          || (!constructor && count >= x[0].lo & 255)
        {
          return None;
        }
        action[2] = F128::new(if constructor { 7 } else { 9 }, h.hi & 65535);
        action[3] = result;
      }
      let mut out = state.to_vec();
      out[HEAP_COUNT] = w(reserved);
      out[CONTROL] = w(STORE | count << 16 | 1 << 24);
      out[PENDING..PENDING + 5].copy_from_slice(&action);
      out[SOURCE_A] = vector(SCRATCH + u64::from(applying), count);
      out[SOURCE_B] = F128::ZERO;
      out[DESTINATION] = w(result.lo);
      out[OLD_HEAP] = w(heap);
      Some(out)
    },
    ObjectKind::CaseAction => {
      action[0] = w(ActionKind::Append as u64 | ((x[2].lo >> 8) & 255) << 8);
      action[1] = x[1];
      Some(action)
    },
    ObjectKind::ProjectRequest | ObjectKind::ProjectAction => {
      let constructor = x[0].lo == 7;
      if !constructor && x[0] != w(5) {
        return None;
      }
      let index = (h.hi >> 32) & 65535;
      if constructor && index >= x[1].hi {
        return None;
      }
      if kind == ObjectKind::ProjectRequest {
        Some(vec![w(if constructor {
          x[1].lo.checked_add(index)?
        } else {
          0
        })])
      } else {
        action[2] = if constructor { x[2] } else { w(5) };
        action[3] = if constructor { x[3] } else { F128::ZERO };
        Some(action)
      }
    },
    ObjectKind::StoreRequest
    | ObjectKind::StoreCopy
    | ObjectKind::StoreFinish => {
      let index = (state[CONTROL].lo >> 8) & 255;
      let count = (state[CONTROL].lo >> 16) & 255;
      if count > 64 || index > count {
        return None;
      }
      if kind == ObjectKind::StoreFinish {
        return (index == count).then(|| state[PENDING..PENDING + 5].to_vec());
      }
      if index == count {
        return None;
      }
      let a = state[SOURCE_A];
      let b = state[SOURCE_B];
      let source = if index < a.hi {
        a.lo.checked_add(index)?
      } else {
        b.lo.checked_add(index - a.hi)?
      };
      if kind == ObjectKind::StoreRequest {
        Some(vec![w(source)])
      } else {
        let mut out = state.to_vec();
        out[CONTROL].lo += 1 << 8;
        out.extend([
          w(source),
          F128::ZERO,
          x[0],
          x[1],
          w(state[DESTINATION].lo.checked_add(index)?),
          F128::ONE,
          x[0],
          x[1],
        ]);
        Some(out)
      }
    },
    ObjectKind::ApplyRequest | ObjectKind::ApplyStart => None,
  }
}
