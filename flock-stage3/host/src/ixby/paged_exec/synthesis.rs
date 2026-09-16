use super::*;
use crate::{
  boolean::{BooleanR1csBuilder as Builder, BooleanR1csPlan},
  ixby::{
    bits::{
      add, any, equal, equal_constant, not, require, require_zero, subtract,
    },
    paged_frame::{ActionKind, Phase, SCRATCH},
    paged_value,
  },
};
fn word(i: usize) -> Vec<usize> {
  (i * 128..(i + 1) * 128).collect()
}
fn constant(one: usize, zero: usize, n: usize, value: u64) -> Vec<usize> {
  (0..n)
    .map(|i| if i < 64 && value & (1 << i) != 0 { one } else { zero })
    .collect()
}
fn mask(b: &mut Builder, flag: usize, bits: &[usize]) -> Vec<usize> {
  bits.iter().map(|&x| b.and(flag, x)).collect()
}
fn eq_const(b: &mut Builder, one: usize, bits: &[usize], value: u64) -> usize {
  let lo = equal_constant(b, one, &bits[..64.min(bits.len())], value);
  if bits.len() > 64 {
    let hi = equal_constant(b, one, &bits[64..], 0);
    b.and(lo, hi)
  } else {
    lo
  }
}
fn copy_output(
  b: &mut Builder,
  one: usize,
  zero: usize,
  at: usize,
  bits: &[usize],
) {
  for i in 0..128 {
    b.write_xor(at * 128 + i, &[bits.get(i).copied().unwrap_or(zero)], one);
  }
}
pub(super) fn build(kind: MicroKind) -> BooleanR1csPlan {
  if let MicroKind::Object(kind) = kind {
    return objects::build(kind);
  }
  let ni = kind.inputs();
  let no = kind.outputs();
  let mut b = Builder::new(16, (ni + no) * 128);
  for bit in 0..ni * 128 {
    b.free_boolean_at(bit);
  }
  let one = b.alloc_constant_one();
  let zero = b.xor(&[one, one], one);
  let mut bad = Vec::new();
  let mut out = vec![vec![zero; 128]; no - 1];
  if kind == MicroKind::Parameters {
    bad.extend(128 + 64..256);
    bad.extend(256 + 64..384);
    let bound = constant(one, zero, 64, 128);
    let below = subtract(&mut b, one, zero, &word(2)[..64], &bound).1;
    bad.push(below);
  } else {
    let enabled = 0;
    bad.extend(1..128);
    let disabled = not(&mut b, one, enabled);
    let state = (0..STATE_WORDS).map(|i| word(1 + i)).collect::<Vec<_>>();
    if !matches!(kind, MicroKind::FrameRequest | MicroKind::Complete) {
      for bits in &state[10..] {
        require_zero(&mut b, one, &mut bad, enabled, bits);
      }
    }
    for i in [HEAP_COUNT, BYTE_COUNT] {
      require_zero(&mut b, one, &mut bad, enabled, &state[i][37..]);
      let low = any(&mut b, one, &state[i][..36]);
      let over = b.and(state[i][36], low);
      bad.push(b.and(enabled, over));
    }
    let phase = state[CONTROL][..8].to_vec();
    let index = state[CONTROL][8..16].to_vec();
    let frame_phase = state[0][..8].to_vec();
    let header = &state[HEADER];
    let instruction = &header[8..16];
    let operation = &header[16..24];
    let count = &header[32..40];
    let args = &header[40..48];
    let target = &header[80..88];
    let other = &header[88..96];
    let eval = eq_const(&mut b, one, &frame_phase, Phase::Eval as u64);
    let expected_phase = match kind {
      MicroKind::Fetch | MicroKind::Resume => Some(READY),
      MicroKind::ResolveRequest | MicroKind::ResolveFinish => Some(RESOLVE),
      MicroKind::FrameRequest | MicroKind::Complete => None,
      _ => Some(EXECUTE),
    };
    if let Some(expected_phase) = expected_phase {
      let correct = eq_const(&mut b, one, &phase, expected_phase);
      require(&mut b, one, &mut bad, enabled, correct);
      if expected_phase != RESOLVE {
        require_zero(&mut b, one, &mut bad, enabled, &state[CONTROL][8..]);
      } else {
        require_zero(&mut b, one, &mut bad, enabled, &state[CONTROL][16..]);
      }
      if kind != MicroKind::Resume {
        require(&mut b, one, &mut bad, enabled, eval);
      }
      if expected_phase == READY {
        require_zero(&mut b, one, &mut bad, enabled, header);
      }
    }
    match kind {
      MicroKind::Fetch => {
        let loaded = word(1 + STATE_WORDS);
        let loaded_count = &loaded[32..40];
        let empty = eq_const(&mut b, one, loaded_count, 0);
        let nonempty = not(&mut b, one, empty);
        out[..STATE_WORDS].clone_from_slice(&state);
        out[CONTROL] = vec![zero; 128];
        out[CONTROL][0] = nonempty;
        out[CONTROL][1] = empty;
        out[HEADER] = loaded;
      },
      MicroKind::ResolveRequest | MicroKind::ResolveFinish => {
        let bound = constant(one, zero, 8, 66);
        let valid_count = subtract(&mut b, one, zero, count, &bound).1;
        let valid_index = subtract(&mut b, one, zero, &index, count).1;
        for valid in [valid_count, valid_index] {
          require(&mut b, one, &mut bad, enabled, valid);
        }
        if kind == MicroKind::ResolveRequest {
          out[0] = index;
          out[1] = count.to_vec();
        } else {
          let increment =
            add(&mut b, one, zero, &index, &constant(one, zero, 8, 1)).0;
          let done = equal(&mut b, one, &increment, count);
          let more = not(&mut b, one, done);
          out[..STATE_WORDS].clone_from_slice(&state);
          out[CONTROL] = vec![zero; 128];
          out[CONTROL][0] = more;
          out[CONTROL][1] = done;
          for i in 0..8 {
            out[CONTROL][8 + i] = b.and(more, increment[i]);
          }
          out[STATE_WORDS] = constant(one, zero, 128, SCRATCH);
          out[STATE_WORDS][..8].copy_from_slice(&index);
          out[STATE_WORDS + 1] = vec![one];
          out[STATE_WORDS + 2] = word(1 + STATE_WORDS);
          out[STATE_WORDS + 3] = word(2 + STATE_WORDS);
        }
      },
      MicroKind::Scratch(n) => {
        let bound = constant(one, zero, 8, (n + 1) as u64);
        let fits = subtract(&mut b, one, zero, count, &bound).1;
        require(&mut b, one, &mut bad, enabled, fits);
        for i in 0..n {
          let live = subtract(
            &mut b,
            one,
            zero,
            &constant(one, zero, 8, i as u64),
            count,
          )
          .1;
          let live = b.and(enabled, live);
          let unused = not(&mut b, one, live);
          let value =
            [word(1 + STATE_WORDS + 2 * i), word(2 + STATE_WORDS + 2 * i)];
          for v in &value {
            require_zero(&mut b, one, &mut bad, unused, v);
          }
          out[4 * i] =
            mask(&mut b, live, &constant(one, zero, 128, SCRATCH + i as u64));
          out[4 * i + 2] = value[0].clone();
          out[4 * i + 3] = value[1].clone();
        }
      },
      MicroKind::NumericAction | MicroKind::ControlAction => {
        let value = word(1 + STATE_WORDS)
          .into_iter()
          .chain(word(2 + STATE_WORDS))
          .collect::<Vec<_>>();
        let tags =
          paged_value::cell(&mut b, one, &mut bad, enabled, &value, false);
        let is_let = eq_const(&mut b, one, instruction, 0);
        let mut action = vec![zero; 128];
        let mut result = value.clone();
        if kind == MicroKind::NumericAction {
          let primitive = eq_const(&mut b, one, operation, 1);
          for yes in [is_let, primitive] {
            require(&mut b, one, &mut bad, enabled, yes);
          }
          action[..8].copy_from_slice(&constant(
            one,
            zero,
            8,
            ActionKind::Bind as u64,
          ));
          action[8..16].copy_from_slice(target);
        } else {
          let copy_op = eq_const(&mut b, one, operation, 0);
          let copy = b.and(is_let, copy_op);
          let ret = eq_const(&mut b, one, instruction, 1);
          let case_nat = eq_const(&mut b, one, instruction, 6);
          let branch = eq_const(&mut b, one, instruction, 7);
          let allowed = any(&mut b, one, &[copy, ret, case_nat, branch]);
          require(&mut b, one, &mut bad, enabled, allowed);
          let one_operand = eq_const(&mut b, one, count, 1);
          require(&mut b, one, &mut bad, enabled, one_operand);
          let nat_step = b.and(enabled, case_nat);
          let bool_step = b.and(enabled, branch);
          require(&mut b, one, &mut bad, nat_step, tags[7]);
          require(&mut b, one, &mut bad, bool_step, tags[0]);
          let magnitude = &value[128..];
          let is_zero = eq_const(&mut b, one, magnitude, 0);
          let nonzero = not(&mut b, one, is_zero);
          let successor = b.and(case_nat, nonzero);
          let nat_zero = b.and(case_nat, is_zero);
          let bind = any(&mut b, one, &[copy, successor]);
          let jump = any(&mut b, one, &[nat_zero, branch]);
          let predecessor = subtract(
            &mut b,
            one,
            zero,
            magnitude,
            &constant(one, zero, 128, 1),
          )
          .0;
          let retain = any(&mut b, one, &[copy, ret]);
          for i in 0..256 {
            let original = b.and(retain, value[i]);
            let pred = if i < 128 {
              constant(one, zero, 128, 8)[i]
            } else {
              predecessor[i - 128]
            };
            let pred = b.and(successor, pred);
            result[i] = b.xor(&[original, pred], one);
          }
          for (i, bit) in action.iter_mut().take(8).enumerate() {
            let terms = [
              (bind, ActionKind::Bind),
              (ret, ActionKind::Return),
              (jump, ActionKind::Jump),
            ]
            .into_iter()
            .filter(|(_, v)| (*v as u64) & (1 << i) != 0)
            .map(|(s, _)| s)
            .collect::<Vec<_>>();
            *bit = if terms.is_empty() { zero } else { b.xor(&terms, one) };
          }
          let bool_true = b.and(branch, value[128]);
          let bool_false = b.product_of_parities(&[branch], &[value[128], one]);
          let use_target = any(&mut b, one, &[copy, nat_zero, bool_true]);
          let use_other = any(&mut b, one, &[successor, bool_false]);
          for i in 0..8 {
            let a = b.and(use_target, target[i]);
            let c = b.and(use_other, other[i]);
            action[8 + i] = b.xor(&[a, c], one);
          }
        }
        out[0] = action;
        out[2] = result[..128].to_vec();
        out[3] = result[128..].to_vec();
      },
      MicroKind::CallReference | MicroKind::CallAction => {
        let is_let = eq_const(&mut b, one, instruction, 0);
        let direct = eq_const(&mut b, one, operation, 5);
        let self_op = eq_const(&mut b, one, operation, 6);
        let direct = b.and(is_let, direct);
        let self_call = b.and(is_let, self_op);
        let tail_direct = eq_const(&mut b, one, instruction, 2);
        let tail_self = eq_const(&mut b, one, instruction, 3);
        let direct = any(&mut b, one, &[direct, tail_direct]);
        let recursive = any(&mut b, one, &[self_call, tail_self]);
        let allowed = any(&mut b, one, &[direct, recursive]);
        require(&mut b, one, &mut bad, enabled, allowed);
        let mut reference = Vec::new();
        for i in 0..16 {
          let a = b.and(direct, header[64 + i]);
          let c = b.and(recursive, state[0][8 + i]);
          reference.push(b.xor(&[a, c], one));
        }
        if kind == MicroKind::CallReference {
          out[0] = reference;
        } else {
          let decl = word(1 + STATE_WORDS);
          let arity = &decl[..8];
          let entry = &decl[8..16];
          let same = equal(&mut b, one, args, arity);
          require(&mut b, one, &mut bad, enabled, same);
          let tail = any(&mut b, one, &[tail_direct, tail_self]);
          let call = not(&mut b, one, tail);
          let mut action = vec![zero; 128];
          action[0] = tail;
          action[1] = one;
          for i in 0..8 {
            action[8 + i] = b.and(call, target[i]);
          }
          action[16..32].copy_from_slice(&reference);
          action[32..40].copy_from_slice(entry);
          action[40..48].copy_from_slice(arity);
          out[0] = action;
          let empty = eq_const(&mut b, one, arity, 0);
          let nonempty = not(&mut b, one, empty);
          out[1] = mask(&mut b, nonempty, &constant(one, zero, 128, SCRATCH));
          out[1][64..72].copy_from_slice(arity);
        }
      },
      MicroKind::Resume => {
        let ret = eq_const(&mut b, one, &frame_phase, Phase::Return as u64);
        let copy = eq_const(&mut b, one, &frame_phase, Phase::Copy as u64);
        let allowed = any(&mut b, one, &[ret, copy]);
        require(&mut b, one, &mut bad, enabled, allowed);
      },
      MicroKind::FrameRequest => {
        for i in 0..5 {
          out[i] = mask(&mut b, enabled, &state[i]);
        }
        out[0][1] = b.xor(&[out[0][1], disabled], one); // canonical halted inactive frame
        let budget = word(1 + STATE_WORDS);
        out[5] = (0..128)
          .map(|i| {
            let a = b.and(enabled, state[FUEL][i]);
            let c = b.and(disabled, budget[i]);
            b.xor(&[a, c], one)
          })
          .collect();
      },
      MicroKind::Complete => {
        out[..STATE_WORDS].clone_from_slice(&state);
        for (i, value) in out.iter_mut().take(6).enumerate() {
          *value = word(1 + STATE_WORDS + i);
        }
        out[CONTROL] = vec![zero; 128];
        out[HEADER] = vec![zero; 128];
        for value in &mut out[10..] {
          *value = vec![zero; 128];
        }
      },
      MicroKind::Parameters | MicroKind::Object(_) => unreachable!(),
    }
    // A frame request intentionally supplies a halted frame and initial fuel
    // for inactive rows. Every other output is canonical zero when disabled.
    if kind != MicroKind::FrameRequest {
      for value in &mut out {
        *value = mask(&mut b, enabled, value);
      }
    }
  }
  for (i, value) in out.iter().enumerate() {
    copy_output(&mut b, one, zero, ni + i, value);
  }
  let invalid = any(&mut b, one, &bad);
  copy_output(&mut b, one, zero, ni + no - 1, &[invalid]);
  b.finish()
}
