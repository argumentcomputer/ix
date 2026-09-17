use super::*;
use crate::ixby::{ixbf_decode::source::prefix, paged_value};

pub(super) fn plan(op: OutputBytesOp) -> crate::boolean::BooleanR1csPlan {
  let ni = op.inputs();
  let no = op.outputs();
  let mut builder = Builder::new(ni, no, 1 << 15);
  let b = &mut builder;
  if op == OutputBytesOp::Header {
    // length, value2, first 32 source bytes, initial window index.
    bound(b, b.one, &word(0), 1 << 24);
    let value = [word(1), word(2)].concat();
    paged_value::cell(&mut b.b, b.one, &mut b.violations, b.one, &value, false);
    same(b, b.one, &word(1), &b.constant(128, 6));
    let length = word(2)[64..128].to_vec();
    bound(b, b.one, &length, 1 << 24);
    let source = [word(3), word(4)].concat();
    let fixed = *b"IXFO\x01\0\0\0\x02\0\0\0\0\x06";
    for (i, byte) in fixed.into_iter().enumerate() {
      same(b, b.one, &source[8 * i..8 * i + 8], &b.constant(8, byte as u64));
    }
    let mut present = Vec::new();
    for i in 0..4 {
      let live = if i == 0 { b.one } else { b.any(&length[7 * i..]) };
      let more = b.any(&length[7 * (i + 1)..]);
      let mut byte = length[7 * i..7 * i + 7].to_vec();
      byte.push(more);
      same(b, live, &source[8 * (14 + i)..8 * (15 + i)], &byte);
      present.push(live);
    }
    let mut header = b.constant(64, 14);
    for on in present {
      let mut term = b.constant(64, 0);
      term[0] = on;
      header = plus(b, b.one, &header, &term);
    }
    let total = plus(b, b.one, &header, &length);
    let narrow_length = word(0)[..64].to_vec();
    same(b, b.one, &total, &narrow_length);
    let windows = windows(b, &length);
    b.require_zero(b.one, &word(5)[64..]);
    let live = lt(b, &word(5)[..64], &windows);
    b.require(b.one, live);
    b.write(ni, &header);
    b.write(ni + 1, &windows);
  } else {
    // value2, header length, source length, index, enabled, two memory replies.
    b.require_zero(b.one, &word(5)[1..]);
    let on = word(5)[0];
    for i in [2, 3, 4] {
      b.require_zero(b.one, &word(i)[64..]);
    }
    bound(b, b.one, &word(2)[..64], 18);
    bound(b, b.one, &word(3)[..64], 1 << 24);
    bound(b, b.one, &word(4)[..64], 1 << 19);
    let length = word(1)[64..128].to_vec();
    let count = windows(b, &length);
    let available = lt(b, &word(4)[..64], &count);
    b.require(on, available);
    le(b, b.one, &word(4)[..64], &count);
    let offset = [vec![b.zero; 5], word(4)[..59].to_vec()].concat();
    let empty = eqc(b, &length, 0);
    let nonempty = b.not(empty);
    let active = b.b.and(on, nonempty);
    let remaining = minus(b, active, &length, &offset);
    let thirty_two = b.constant(64, 32);
    let short = lt(b, &remaining, &thirty_two);
    let take = choose(b, short, &remaining, &thirty_two);
    let take = mask(b, active, &take);
    let p = plus(b, active, &word(1)[..64], &offset);
    let zero = b.constant(64, 0);
    let address = [p[5..].to_vec(), vec![b.zero; 5]].concat();
    let address = choose(b, active, &address, &zero);
    let within = plus(
      b,
      b.one,
      &p[..5]
        .iter()
        .copied()
        .chain(std::iter::repeat_n(b.zero, 59))
        .collect::<Vec<_>>(),
      &take,
    );
    let crosses = lt(b, &thirty_two, &within);
    let second_live = b.b.and(active, crosses);
    let successor = plus(b, active, &address, &b.constant(64, 1));
    let second = choose(b, second_live, &successor, &zero);
    let mut bytes = [word(6), word(7), word(8), word(9)].concat();
    for (i, flag) in p[..5].iter().copied().enumerate() {
      bytes = (0..bytes.len())
        .map(|bit| {
          let shifted =
            bytes.get(bit + 8 * (1 << i)).copied().unwrap_or(b.zero);
          let d = b.b.product_of_parities(&[flag], &[bytes[bit], shifted]);
          b.sum(&[bytes[bit], d])
        })
        .collect();
    }
    let live_bytes = prefix(b, &take, 32);
    let data = (0..256)
      .map(|i| b.b.and(live_bytes[i / 8], bytes[i]))
      .collect::<Vec<_>>();
    let mut increment = b.constant(64, 0);
    increment[0] = on;
    let next = plus(b, b.one, &word(4)[..64], &increment);
    let cursor = plus(b, on, &word(2)[..64], &offset);
    b.write(ni, &next);
    let cursor = choose(b, on, &cursor, &word(3)[..64]);
    b.write(ni + 1, &[cursor, word(3)[..64].to_vec()].concat());
    b.write(ni + 2, &take);
    b.write(ni + 3, &address);
    b.write(ni + 4, &second);
    b.write(ni + 5, &data[..128]);
    b.write(ni + 6, &data[128..]);
  }
  builder.finish(ni + no - 1)
}
fn windows(b: &mut Builder, length: &[usize]) -> Bits {
  let sum = plus(b, b.one, length, &b.constant(64, 31));
  let mut rounded = sum[5..].to_vec();
  rounded.resize(64, b.zero);
  let empty = eqc(b, length, 0);
  choose(b, empty, &b.constant(64, 1), &rounded)
}
