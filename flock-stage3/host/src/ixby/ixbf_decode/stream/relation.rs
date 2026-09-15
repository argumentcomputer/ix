use super::*;
use crate::{
  boolean::BooleanR1csPlan,
  ixby::{
    bits::{add, subtract},
    ixbf_decode::source::{choose_bits, file_bits, last_index, require_index},
  },
  sizing::CountedGate,
};
use flock_prover::field::F128;

pub(super) fn evaluate(g: &StreamGate, input: &[F128]) -> Vec<F128> {
  match g.op() {
    StreamOp::Cache => {
      let length = input[0].lo;
      let first = input[1].lo;
      let last = last_index(length);
      let bad = input[0].hi != 0
        || input[1].hi != 0
        || !g.capacity().admits_length(length)
        || first > last;
      [first.wrapping_add(1).min(last), last, u64::from(bad)]
        .map(|v| F128::new(v, 0))
        .to_vec()
    },
    StreamOp::Read => {
      let [cursor, take, length, first] = input.try_into().unwrap();
      let last = last_index(length.lo);
      let selected = (cursor.lo >> 10).min(last);
      let bad = length.hi != 0
        || first.hi != 0
        || take.hi != 0
        || cursor.hi != length.lo
        || cursor.lo > length.lo
        || !g.capacity().admits_length(length.lo)
        || first.lo > last
        || take.lo > g.capacity().window_bytes() as u64
        || (take.lo != 0 && selected != first.lo);
      vec![
        if take.lo == 0 {
          F128::new(first.lo << 10, length.lo)
        } else {
          cursor
        },
        take,
        F128::new(u64::from(bad), 0),
      ]
    },
    StreamOp::Prepare => {
      let remaining = input[0].lo;
      let active = remaining != 0;
      let mut out = vec![
        F128::new(remaining.saturating_sub(1), 0),
        F128::new(u64::from(active), 0),
      ];
      if active {
        out.extend_from_slice(&input[1..]);
      } else {
        // A canonical Done state is used only inside a padding row. The
        // actual carried state is selected back unchanged after decoding.
        let mut dummy = [F128::ZERO; 30];
        dummy[0] = F128::new(input[1].hi, input[1].hi);
        dummy[1] = F128::new(20, 0);
        out.extend(dummy);
      }
      out.push(F128::new(u64::from(input[0].hi != 0), 0));
      out
    },
  }
}

pub(super) fn plan(g: &StreamGate) -> BooleanR1csPlan {
  let n = g.input_count();
  let mut b = Builder::new(n, g.output_count(), 1 << 15);
  match g.op() {
    StreamOp::Cache => {
      b.require_zero(b.one, &word(0)[64..]);
      b.require_zero(b.one, &word(1)[64..]);
      let file = file_bits(&mut b, &word(0)[..64], g.capacity().depth());
      require_index(&mut b, &word(1)[..64], &file.last);
      let one = b.constant(64, 1);
      let (successor, _) = add(&mut b.b, b.one, b.zero, &word(1)[..64], &one);
      let (_, clamp) =
        subtract(&mut b.b, b.one, b.zero, &file.last, &successor);
      let next = choose_bits(&mut b, clamp, &file.last, &successor);
      b.write(n, &next);
      b.write(n + 1, &file.last);
    },
    StreamOp::Read => {
      for at in [1, 2, 3] {
        b.require_zero(b.one, &word(at)[64..]);
      }
      let length = word(2)[..64].to_vec();
      let first = word(3)[..64].to_vec();
      let equal_length = b.equal(&word(0)[64..], &length);
      b.require(b.one, equal_length);
      let (_, past) =
        subtract(&mut b.b, b.one, b.zero, &length, &word(0)[..64]);
      b.violations.push(past);
      let maximum = b.constant(64, g.capacity().window_bytes() as u64);
      let (_, too_much) =
        subtract(&mut b.b, b.one, b.zero, &maximum, &word(1)[..64]);
      b.violations.push(too_much);
      let file = file_bits(&mut b, &length, g.capacity().depth());
      require_index(&mut b, &first, &file.last);
      let mut index = word(0)[10..64].to_vec();
      index.resize(64, b.zero);
      let (_, clamp) = subtract(&mut b.b, b.one, b.zero, &file.last, &index);
      let selected = choose_bits(&mut b, clamp, &file.last, &index);
      let live = b.any(&word(1)[..64]);
      let correct = b.equal(&selected, &first);
      b.require(live, correct);
      let safe = [b.constant(10, 0), first[..54].to_vec(), length].concat();
      let cursor = choose_bits(&mut b, live, &word(0), &safe);
      b.write(n, &cursor);
      b.write(n + 1, &word(1));
    },
    StreamOp::Prepare => {
      b.require_zero(b.one, &word(0)[64..]);
      let active = b.any(&word(0)[..64]);
      let one = b.constant(64, 1);
      let (decrement, _) =
        subtract(&mut b.b, b.one, b.zero, &word(0)[..64], &one);
      let zero = b.constant(64, 0);
      let next = choose_bits(&mut b, active, &decrement, &zero);
      b.write(n, &next);
      b.write(n + 1, &[active]);
      for at in 0..30 {
        let dummy = match at {
          0 => [word(1)[64..].to_vec(), word(1)[64..].to_vec()].concat(),
          1 => b.constant(128, 20),
          _ => b.constant(128, 0),
        };
        let value = choose_bits(&mut b, active, &word(at + 1), &dummy);
        b.write(n + 2 + at, &value);
      }
    },
  }
  b.finish(n + g.output_count() - 1)
}
