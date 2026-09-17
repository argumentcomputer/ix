use super::super::source::choose_bits;
use super::*;
use crate::{boolean::BooleanR1csPlan, sizing::CountedGate};
use flock_prover::field::F128;

pub(super) fn route(config: DispatchConfig, input: &[F128]) -> Vec<F128> {
  let tag = input[0].lo as u8 as usize;
  let mut out: Vec<_> =
    (0..18).map(|i| F128::new(u64::from(tag == i), 0)).collect();
  for record in 0..13 {
    for index in [1, 2, 3, 9, 10, 11, 12, 13, 14] {
      out.push(if tag == record { input[index] } else { F128::ZERO });
    }
  }
  out.push(if tag == 13 { input[6] } else { F128::new(25, 0) });
  for index in 0..17 {
    out.push(if tag == 13 {
      input[9 + index]
    } else if index == 0 {
      F128::new(0x0000_0001_4642_5849, 2)
    } else {
      F128::ZERO
    });
  }
  for index in 0..config.natural.encoded_words() {
    out.push(if tag == 14 { input[9 + index] } else { F128::ZERO });
  }
  for index in 0..2 {
    out.push(if tag == 15 { input[9 + index] } else { F128::ZERO });
  }
  out.push(F128::new(u64::from(tag == 15 || tag == 16), 0));
  out.push(F128::new(u64::from(input[0].hi != 0 || input[0].lo > 17), 0));
  out
}
pub(super) fn route_plan(g: &DispatchGate) -> BooleanR1csPlan {
  let mut b = g.builder(1 << 16);
  let start = g.input_count();
  let flags = tags(&mut b, 0);
  for (index, &flag) in flags.iter().enumerate() {
    b.write(start + index, &[flag]);
  }
  for (record, &flag) in flags[..13].iter().enumerate() {
    for (port, index) in
      [1, 2, 3, 9, 10, 11, 12, 13, 14].into_iter().enumerate()
    {
      let bits = masked(&mut b, flag, &word(index));
      b.write(start + RECORD_PORTS + record * 9 + port, &bits);
    }
  }
  let dummy_len = b.constant(128, 25);
  let length = choose_bits(&mut b, flags[13], &word(6), &dummy_len);
  b.write(start + HEADER_PORT, &length);
  for index in 0..17 {
    let mut dummy =
      b.constant(128, if index == 0 { 0x0000_0001_4642_5849 } else { 0 });
    if index == 0 {
      dummy[65] = b.one; // IXBF program semantics 2, including inactive rows.
    }
    let bits = choose_bits(&mut b, flags[13], &word(9 + index), &dummy);
    b.write(start + HEADER_PORT + 1 + index, &bits);
  }
  let n = g.config.natural.encoded_words();
  for index in 0..n {
    let bits = masked(&mut b, flags[14], &word(9 + index));
    b.write(start + NATURAL_PORT + index, &bits);
  }
  for index in 0..2 {
    let bits = masked(&mut b, flags[15], &word(9 + index));
    b.write(start + NATURAL_PORT + n + index, &bits);
  }
  let payload = b.sum(&[flags[15], flags[16]]);
  b.write(start + NATURAL_PORT + n + 2, &[payload]);
  b.finish(start + g.output_count() - 1)
}

/// Mask the exact first-terminator prefix. Canonicality and magnitude bounds
/// remain obligations of the existing NaturalDecode/Limit gates downstream.
pub(super) fn natural(config: DispatchConfig, input: &[F128]) -> Vec<F128> {
  let enable = input[0];
  let mut live = enable.lo & 1 != 0;
  let mut out = vec![F128::ZERO; config.natural.encoded_words() + 2];
  let mut length = 0;
  for index in 0..config.natural.encoded_bytes() {
    let source = input[1 + index / 16];
    let byte = if index % 16 < 8 {
      (source.lo >> (8 * (index % 8))) as u8
    } else {
      (source.hi >> (8 * (index % 8))) as u8
    };
    if live {
      let dest = &mut out[1 + index / 16];
      if index % 16 < 8 {
        dest.lo |= u64::from(byte) << (8 * (index % 8));
      } else {
        dest.hi |= u64::from(byte) << (8 * (index % 8));
      }
      if byte < 128 {
        length = index + 1;
        live = false;
      }
    }
  }
  out[0] = F128::new(length as u64, 0);
  let bad = enable.hi != 0
    || enable.lo > 1
    || live
    || (enable.lo & 1 == 0 && input[1..].iter().any(|v| *v != F128::ZERO));
  *out.last_mut().unwrap() = F128::new(u64::from(bad), 0);
  out
}
pub(super) fn natural_plan(g: &DispatchGate) -> BooleanR1csPlan {
  let mut b = g.builder(1024 + 36 * g.config.natural.encoded_bytes());
  let n = g.config.natural.encoded_words();
  let start = g.input_count();
  b.require_zero(b.one, &word(0)[1..]);
  let disabled = b.not(0);
  b.require_zero(disabled, &(128..start * 128).collect::<Bits>());
  let mut live = 0;
  let mut ends = Vec::new();
  let mut encoded = vec![b.zero; n * 128];
  for index in 0..g.config.natural.encoded_bytes() {
    let byte: Bits = (128 + index * 8..128 + (index + 1) * 8).collect();
    encoded[index * 8..(index + 1) * 8]
      .copy_from_slice(&masked(&mut b, live, &byte));
    let last = b.not(byte[7]);
    ends.push(b.b.and(live, last));
    live = b.b.and(live, byte[7]);
  }
  b.violations.push(live);
  let length: Bits = (0..64)
    .map(|bit| {
      let terms: Bits = ends
        .iter()
        .enumerate()
        .filter_map(|(i, &flag)| {
          (((i as u64 + 1) >> bit) & 1 == 1).then_some(flag)
        })
        .collect();
      b.sum(&terms)
    })
    .collect();
  b.write(start, &length);
  for index in 0..n {
    b.write(start + 1 + index, &encoded[index * 128..(index + 1) * 128]);
  }
  b.finish(start + 1 + n)
}

/// tag, grammar cursor, header[14], thirteen record outputs[7], Nat length,
/// Nat next and whole-payload next. Only constrained decoder outputs belong
/// here; disabled decoder fields are not free witnesses either.
pub(super) fn merge(input: &[F128]) -> Vec<F128> {
  let tag = input[0].lo as u8 as usize;
  let mut out = vec![F128::ZERO; 15];
  match tag {
    0..=12 => {
      let record = 16 + tag * 7;
      out[..6].copy_from_slice(&input[record..record + 6]);
      out[13] = input[record + 6];
    },
    13 => out[..14].copy_from_slice(&input[2..16]),
    14 => {
      out[0] = input[107];
      out[13] = input[108];
    },
    15 | 16 => out[13] = input[109],
    17 => out[13] = input[1],
    _ => {},
  }
  out[14] = F128::new(u64::from(input[0].hi != 0 || input[0].lo > 17), 0);
  out
}
pub(super) fn merge_plan(g: &DispatchGate) -> BooleanR1csPlan {
  let mut b = g.builder(1 << 15);
  let flags = tags(&mut b, 0);
  for index in 0..13 {
    let mut choices = vec![(flags[13], word(2 + index))];
    if index < 6 {
      for (record, &flag) in flags[..13].iter().enumerate() {
        choices.push((flag, word(16 + record * 7 + index)));
      }
    }
    if index == 0 {
      choices.push((flags[14], word(107)));
    }
    let bits = select(&mut b, &choices, 128);
    b.write(110 + index, &bits);
  }
  let mut choices: Vec<_> = flags[..13]
    .iter()
    .enumerate()
    .map(|(record, &flag)| (flag, word(16 + record * 7 + 6)))
    .collect();
  choices.extend([
    (flags[13], word(15)),
    (flags[14], word(108)),
    (flags[15], word(109)),
    (flags[16], word(109)),
    (flags[17], word(1)),
  ]);
  let next = select(&mut b, &choices, 128);
  b.write(123, &next);
  b.finish(124)
}
