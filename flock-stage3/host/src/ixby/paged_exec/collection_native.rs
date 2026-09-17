//! Untrusted integer advice generation, independently checked against the
//! Boolean collection relations in tests and against constraints in proofs.
use super::{collections::*, *};
use crate::ixby::{
  paged_frame::{ActionKind, HEAP},
  paged_value::{DYNAMIC_BYTES, FLAT_ARRAY},
};

fn w(n: u64) -> F128 {
  F128::new(n, 0)
}
fn push_write(out: &mut Vec<F128>, on: bool, address: u64, value: [F128; 2]) {
  out.extend(if on {
    [w(address), F128::ONE, value[0], value[1]]
  } else {
    [F128::ZERO; 4]
  });
}
fn buffer(words: &[F128]) -> Vec<u8> {
  words
    .iter()
    .flat_map(|v| [v.lo.to_le_bytes(), v.hi.to_le_bytes()].concat())
    .collect()
}
fn packed(bytes: &[u8]) -> F128 {
  F128::new(
    u64::from_le_bytes(bytes[..8].try_into().unwrap()),
    u64::from_le_bytes(bytes[8..16].try_into().unwrap()),
  )
}
pub(super) fn evaluate(
  kind: CollectionKind,
  state: &[F128],
  x: &[F128],
) -> Option<Vec<F128>> {
  let opcode = (state[HEADER].lo >> 24) as u8;
  let mut out = state.to_vec();
  let heap = state[HEAP_COUNT].lo;
  let raw_pointer = state[15].lo & !FLAT_ARRAY;
  match kind {
    CollectionKind::Start => {
      let prim = crate::ixby::ixbf::Primitive::from_opcode(opcode)?;
      if !is_collection(opcode)
        || (state[HEADER].lo >> 32) as u8 as usize != prim.arity()
      {
        return None;
      }
      let len = x[0].hi;
      for value in &mut out[10..] {
        *value = F128::ZERO;
      }
      out[CONTROL] = w(FINISH);
      let mut writes = [(false, 0, [F128::ZERO; 2]); 2];
      match opcode {
        49 => {
          out[10] = w(11);
        },
        50..=53 => {
          if x[0].lo != 11 || len > u64::from(u32::MAX) {
            return None;
          }
          if opcode == 50 {
            out[10] = w(8);
            out[11] = w(len);
          } else {
            let index = if opcode == 53 {
              len
            } else {
              if x[2] != w(8) || x[3].hi != 0 || x[3].lo >= len {
                return None;
              }
              x[3].lo
            };
            if opcode == 53 && len == u64::from(u32::MAX) {
              return None;
            }
            let capacity = len.max(1).next_power_of_two();
            let growing = opcode == 53 && len != 0 && len == capacity;
            out[CONTROL] = w(ARRAY_DOWN);
            out[12] = w(len);
            out[13] = w(if growing { 0 } else { index });
            out[14] = w(capacity);
            out[15] = if growing { F128::ZERO } else { x[1] };
            out[16] = w(u64::from(growing));
            if opcode != 51 {
              out[10] = F128::new(11, len + u64::from(opcode == 53));
              out[17..19].copy_from_slice(if opcode == 52 {
                &x[4..6]
              } else {
                &x[2..4]
              });
            }
            out[19] = w(heap);
            out[20] = w(if growing { len } else { 0 });
            writes[0] = (growing, STACK, [F128::new(x[1].lo, 1), F128::ZERO]);
          }
        },
        54 => {
          out[10] = w(12);
        },
        55..=57 => {
          if x[0].lo != 12 || len >= 1 << 36 || len > x[6].hi {
            return None;
          }
          if opcode == 55 {
            if x[2] != w(6) {
              return None;
            }
            let total = len.checked_add(x[3].hi)?;
            if total > x[6].hi || total >= 1 << 36 {
              return None;
            }
            let allocate = x[3].hi != 0;
            if allocate && heap.checked_add(2)? > 1 << 36 {
              return None;
            }
            out[10] = F128::new(12, total);
            out[11] = if allocate { w(HEAP + heap) } else { x[1] };
            out[HEAP_COUNT] = w(heap + 2 * u64::from(allocate));
            writes = [
              (allocate, HEAP + heap, [x[0], x[1]]),
              (allocate, HEAP + heap + 1, [x[2], x[3]]),
            ];
          } else if opcode == 56 {
            let allocated =
              state[BYTE_COUNT].lo.checked_add(len.div_ceil(32))?;
            if allocated > 1 << 36 {
              return None;
            }
            out[10] = w(6);
            out[11] = F128::new(
              if len == 0 {
                0
              } else {
                (DYNAMIC_BYTES + state[BYTE_COUNT].lo) << 5
              },
              len,
            );
            out[12..14].copy_from_slice(&x[..2]);
            out[16] = w(len);
            out[17] = w(heap);
            out[18] = state[BYTE_COUNT];
            out[BYTE_COUNT] = w(allocated);
            out[CONTROL] = w(if len == 0 { FINISH } else { BUILDER_NODE });
          } else {
            out[10] = w(8);
            out[11] = w(len);
          }
        },
        _ => return None,
      }
      for (on, address, value) in writes {
        push_write(&mut out, on, address, value);
      }
    },
    CollectionKind::ArrayRequest => {
      let leaf = state[14].lo == 1;
      let read = state[20].lo < state[12].lo
        && ((!leaf && state[15].lo & FLAT_ARRAY == 0)
          || (leaf && opcode == 51));
      return Some(vec![w(if read { raw_pointer } else { 0 })]);
    },
    CollectionKind::ArrayStep => {
      let cap = state[14].lo;
      if cap == 0 {
        return None;
      }
      let branch = cap != 1;
      let get = opcode == 51;
      let mut sibling = 0;
      let mut go_right = false;
      if branch {
        let half = cap / 2;
        let right_offset = state[20].lo.checked_add(half)?;
        let (left, right) = if state[15].lo & FLAT_ARRAY != 0 {
          (
            state[15].lo,
            if right_offset < state[12].lo {
              raw_pointer.checked_add(half)? | FLAT_ARRAY
            } else {
              0
            },
          )
        } else {
          (x[0].lo, x[0].hi)
        };
        go_right = state[13].lo >= half;
        sibling = if go_right { left } else { right };
        out[15] = w(if go_right { right } else { left });
        out[14] = w(half);
        out[13] = w(if go_right { state[13].lo - half } else { state[13].lo });
        out[20] = w(if go_right { right_offset } else { state[20].lo });
        out[16] = w(state[16].lo.checked_add(1)?);
      } else {
        out[15] = w(HEAP + heap);
        if get {
          out[10..12].copy_from_slice(x);
        } else {
          let next = heap.checked_add(1)?;
          if next > 1 << 36 {
            return None;
          }
          out[HEAP_COUNT] = w(next);
          if state[16].lo == 0 {
            out[11] = w(HEAP + heap);
          }
        }
      }
      out[CONTROL] = w(if branch {
        ARRAY_DOWN
      } else if !get && state[16].lo != 0 {
        ARRAY_UP
      } else {
        FINISH
      });
      push_write(
        &mut out,
        branch && !get,
        STACK + state[16].lo,
        [F128::new(sibling, u64::from(go_right)), F128::ZERO],
      );
      push_write(
        &mut out,
        !branch && !get,
        HEAP + heap,
        [state[17], state[18]],
      );
    },
    CollectionKind::AscendRequest => {
      return Some(vec![w(STACK + state[16].lo.checked_sub(1)?)]);
    },
    CollectionKind::Ascend => {
      let depth = state[16].lo.checked_sub(1)?;
      let next = heap.checked_add(1)?;
      if next > 1 << 36 {
        return None;
      }
      out[HEAP_COUNT] = w(next);
      out[15] = w(HEAP + heap);
      out[16] = w(depth);
      out[14] = w(state[14].lo.checked_mul(2)?);
      if depth == 0 {
        out[11] = w(HEAP + heap);
      }
      out[CONTROL] = w(if depth == 0 { FINISH } else { ARRAY_UP });
      let (left, right) = if x[0].hi == 1 {
        (x[0].lo, state[15].lo)
      } else {
        (state[15].lo, x[0].lo)
      };
      push_write(
        &mut out,
        true,
        HEAP + heap,
        [F128::new(left, right), F128::ZERO],
      );
    },
    CollectionKind::BuilderRequest => {
      return Some(vec![state[13], w(state[13].lo.checked_add(1)?)]);
    },
    CollectionKind::BuilderNode => {
      if x[0].lo != 12
        || x[2] != w(6)
        || x[3].hi == 0
        || x[0].hi.checked_add(x[3].hi)? != state[12].hi
      {
        return None;
      }
      out[12..14].copy_from_slice(&x[..2]);
      out[14] = x[3];
      out[15] = w(x[3].hi);
      out[CONTROL] = w(BUILDER_COPY);
    },
    CollectionKind::CopyRequest | CollectionKind::Copy => {
      let room = if state[16].lo & 31 == 0 { 32 } else { state[16].lo & 31 };
      let count = state[15].lo.min(room);
      if count == 0 {
        return None;
      }
      let remain = state[15].lo - count;
      let end = state[16].lo.checked_sub(count)?;
      if kind == CollectionKind::CopyRequest {
        return Some(vec![w(state[14].lo.checked_add(remain)?), w(count)]);
      }
      let mut output = buffer(&state[19..21]);
      let data = buffer(&x[..2]);
      for i in 0..count as usize {
        output[(end & 31) as usize + i] ^= data[i];
      }
      out[19] = packed(&output[..16]);
      out[20] = packed(&output[16..]);
      out[16] = w(end);
      out[15] = w(remain);
      if remain == 0 {
        out[14] = F128::ZERO;
      }
      out[CONTROL] = w(if end & 31 == 0 {
        BUILDER_EMIT
      } else if remain != 0 {
        BUILDER_COPY
      } else {
        BUILDER_NODE
      });
    },
    CollectionKind::Emit => {
      out[19..21].fill(F128::ZERO);
      out[CONTROL] = w(if state[16].lo == 0 {
        FINISH
      } else if state[15].lo != 0 {
        BUILDER_COPY
      } else {
        BUILDER_NODE
      });
      push_write(
        &mut out,
        true,
        DYNAMIC_BYTES + state[18].lo + state[16].lo / 32,
        [state[19], state[20]],
      );
    },
    CollectionKind::Finish => {
      return Some(vec![
        w(ActionKind::Bind as u64 | ((state[HEADER].hi >> 16) & 255) << 8),
        F128::ZERO,
        state[10],
        state[11],
        F128::ZERO,
      ]);
    },
  }
  Some(out)
}
