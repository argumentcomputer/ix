//! Checked integer witness preparation, independent of the Boolean synthesis.
//! It is never a verifier predicate or a source of trusted program metadata.
use super::{
  super::grammar::{self, Phase},
  *,
};
use flock_prover::field::F128;
fn value(w: F128) -> u128 {
  u128::from(w.lo) | (u128::from(w.hi) << 64)
}
fn word(v: u128) -> F128 {
  F128::new(v as u64, (v >> 64) as u64)
}
fn flag(w: F128) -> bool {
  w.lo & 1 != 0
}
fn canonical(bank: &[F128], stride: usize, bad: &mut bool) -> Vec<bool> {
  bank
    .chunks_exact(stride)
    .map(|r| {
      let live = flag(r[0]);
      *bad |=
        value(r[0]) > 1 || (!live && r[1..].iter().any(|w| *w != F128::ZERO));
      live
    })
    .collect()
}
fn events(
  input: &[F128],
  committed: usize,
  tag: usize,
  bad: &mut bool,
) -> (bool, u128) {
  let commit = flag(input[committed]);
  let tag = value(input[tag]);
  *bad |= value(input[committed]) > 1
    || tag >= 18
    || (!matches!(tag, 15 | 17) && !commit)
    || (tag == 17 && commit);
  (commit, tag)
}
fn prefix(count: F128, live: &[bool], bad: &mut bool) {
  *bad |= value(count) > live.len() as u128;
  for (i, on) in live.iter().enumerate() {
    *bad |= *on != ((i as u128) < value(count));
  }
}
pub(super) fn evaluate(
  config: ValueConfig,
  op: ValueOp,
  input: &[F128],
) -> Vec<F128> {
  let mut bad = false;
  let mut out = match op {
    ValueOp::Link => link(config, input, &mut bad),
    ValueOp::Node => node(config, input, &mut bad),
    ValueOp::Capture => capture(config.arena, input, &mut bad),
    ValueOp::Finish => finish(config, input, &mut bad),
    _ => read(config.arena, op, input, &mut bad),
  };
  out.push(F128::new(u64::from(bad), 0));
  out
}
fn link(c: ValueConfig, input: &[F128], bad: &mut bool) -> Vec<F128> {
  let (commit, tag) = events(input, 0, 1, bad);
  let active = commit && tag == 9;
  let kind = value(input[2]);
  *bad |= active && kind >= 4;
  let ctor = active && kind == 1;
  let pap = active && kind == 2;
  *bad |= active
    && matches!(kind, 0 | 3)
    && input[3..8].iter().any(|w| *w != F128::ZERO);
  *bad |= pap && input[4..7].iter().any(|w| *w != F128::ZERO);
  *bad |= active && input[8..LINK_BANK].iter().any(|w| *w != F128::ZERO);
  let mut found = 0;
  let mut index = 0;
  for (constructors, count, stride, offset) in [
    (true, c.registry.constructors(), 7, 0),
    (false, c.registry.functions(), 5, c.registry.constructors() * 7),
  ] {
    for i in 0..count {
      let at = LINK_BANK + offset + i * stride;
      let live = canonical(&input[at..at + stride], stride, bad)[0];
      let selected = live
        && if constructors {
          ctor && input[3..7] == input[at + 1..at + 5]
        } else {
          pap && value(input[3]) == i as u128
        };
      if selected {
        found += 1;
        index ^= i as u128;
        *bad |= if constructors {
          input[7] != input[at + 5]
        } else {
          value(input[7]) >= value(input[at + 1])
        };
      }
    }
  }
  *bad |= ((ctor || pap) && found == 0) || found > 1;
  vec![word(index)]
}
fn node(c: ValueConfig, input: &[F128], bad: &mut bool) -> Vec<F128> {
  let a = c.arena;
  let acc = NAT + a.natural.magnitude_words();
  let pending = flag(input[acc]);
  let v = |i| value(input[i]);
  let cursor = input[0];
  let next = input[NEXT];
  *bad |= v(acc) > 1
    || input[acc + 1].hi != 0
    || v(acc + 2) >= 8
    || input[acc + 3].hi != 0;
  *bad |= !pending && (v(acc + 1) != 0 || v(acc + 2) != 0);
  *bad |= cursor.lo > cursor.hi
    || cursor.lo > next.lo
    || next.lo > cursor.hi
    || next.hi != cursor.hi;
  *bad |= pending
    && (input[acc + 1].lo > cursor.lo || input[acc + 3].lo > input[acc + 1].lo);
  *bad |= v(1) >> 40 != 0;
  let (commit, tag) = events(input, COMMIT, TAG, bad);
  let phase = input[1].lo as u8;
  let phases = [
    Phase::Start,
    Phase::Value,
    Phase::Scalar,
    Phase::Natural,
    Phase::StringCount,
    Phase::StringPayload,
    Phase::BytesCount,
    Phase::BytesPayload,
    Phase::Done,
  ];
  let p = phases.map(|p| phase == p as u8);
  *bad |= !p.iter().any(|p| *p);
  for (on, expected) in p.into_iter().zip([
    if c.kind == GrammarKind::Input { 7 } else { 8 },
    9,
    11,
    14,
    1,
    15,
    1,
    16,
    17,
  ]) {
    *bad |= on && tag != expected;
  }
  let [
    header,
    value,
    scalar,
    natural,
    string_count,
    string_payload,
    bytes_count,
    bytes_payload,
    done,
  ] = p;
  *bad |= header
    && (input[acc..acc + 4].iter().any(|w| *w != F128::ZERO) || cursor.lo != 0);
  *bad |= !header && v(acc + 3) == 0;
  *bad |= commit && cursor.lo >= next.lo;
  *bad |= (done && (cursor != next || pending)) || (value && pending);
  let kind = v(FIELDS);
  *bad |= value && kind >= 4;
  let begin = value && kind == 0;
  let aggregate = value && matches!(kind, 1 | 2);
  let non_scalar = value && matches!(kind, 1..=3);
  *bad |= !aggregate && v(RESOLVED) != 0;
  *bad |= value && kind == 2 && input[RESOLVED] != input[FIELDS + 1];
  *bad |= scalar && (kind >= 7 || !pending || v(acc + 2) != 7);
  for (on, tag) in [
    (natural, 0),
    (string_count, 1),
    (string_payload, 1),
    (bytes_count, 6),
    (bytes_payload, 6),
  ] {
    *bad |= on && (!pending || v(acc + 2) != tag);
  }
  let fixed = scalar && matches!(kind, 2..=5);
  let empty = (string_count || bytes_count) && kind == 0;
  let payload_done = (string_payload && commit) || bytes_payload;
  let scalar_done = fixed || natural || empty || payload_done;
  let emit = non_scalar || scalar_done;
  let mut out = input[acc..acc + 4].to_vec();
  if begin {
    out[0] = F128::ONE;
    out[1] = F128::new(cursor.lo, 0);
    out[2] = F128::new(7, 0);
  }
  if scalar {
    out[2] = input[FIELDS];
  }
  if scalar_done {
    out[..3].fill(F128::ZERO);
  }
  if header {
    out[3] = F128::new(next.lo, 0);
  }
  let (previous, borrow) = v(grammar::SEEN).overflowing_sub(1);
  *bad |= scalar_done && borrow;
  out.push(word(if non_scalar {
    v(grammar::SEEN)
  } else if scalar_done {
    previous
  } else {
    0
  }));
  let mut r = vec![F128::ZERO; a.record_words()];
  r[PRESENT] = word(u128::from(emit));
  if non_scalar {
    r[KIND] = input[FIELDS];
  }
  if fixed {
    r[SCALAR] = input[FIELDS];
    r[FIXED] = input[FIELDS + 1];
  }
  if natural || empty || payload_done {
    r[SCALAR] = input[acc + 2];
  }
  if aggregate {
    r[REFERENCE] = input[RESOLVED];
    r[CHILDREN] = input[FIELDS + 5];
  }
  if emit {
    r[SPAN] = F128::new(
      if non_scalar { cursor.lo } else { input[acc + 1].lo },
      next.lo,
    );
  }
  if natural {
    r[MAGNITUDE..].copy_from_slice(&input[NAT..acc]);
  }
  for (on, range, length) in [
    (natural, input[NAT_RANGE], v(FIELDS)),
    (payload_done, input[BYTE_RANGE], v(grammar::PAYLOAD)),
  ] {
    let (end, overflow) = range.lo.overflowing_add(range.hi);
    *bad |= on
      && (range.lo != cursor.lo
        || u128::from(range.hi) != length
        || overflow
        || end != next.lo);
  }
  r[PAYLOAD] = if natural {
    input[NAT_RANGE]
  } else if payload_done {
    input[BYTE_RANGE]
  } else if empty {
    F128::new(next.lo, 0)
  } else {
    F128::ZERO
  };
  out.extend(r);
  out
}
fn capture(a: ValueCapacity, input: &[F128], bad: &mut bool) -> Vec<F128> {
  let r = a.record_words();
  let packet = &input[2..2 + r];
  let bank = &input[2 + r..];
  let emit = canonical(packet, r, bad)[0];
  let live = canonical(bank, r, bad);
  prefix(input[0], &live, bad);
  *bad |= !emit && input[1] != F128::ZERO;
  *bad |= emit && (input[1] != input[0] || value(input[0]) >= a.nodes as u128);
  let (count, overflow) = value(input[0]).overflowing_add(u128::from(emit));
  *bad |= overflow;
  let mut out = vec![word(count)];
  out.extend(bank);
  for (i, on) in live.iter().enumerate() {
    if emit && value(input[1]) == i as u128 {
      *bad |= *on;
      out[1 + i * r..1 + (i + 1) * r].copy_from_slice(packet);
    }
  }
  out
}
fn finish(c: ValueConfig, input: &[F128], bad: &mut bool) -> Vec<F128> {
  let a = c.arena;
  let r = a.record_words();
  let bank = &input[33..];
  let count = input[32];
  let cursor = input[0];
  let live = canonical(bank, r, bad);
  prefix(count, &live, bad);
  *bad |= count != input[grammar::SEEN]
    || value(input[1]) >> 40 != 0
    || input[1].lo as u8 != Phase::Done as u8
    || cursor.lo != cursor.hi;
  for at in [
    grammar::CTORS_LEFT,
    grammar::FUNCTIONS_LEFT,
    grammar::BLOCKS_LEFT,
    grammar::ITEMS,
    grammar::PAYLOAD,
    grammar::PENDING,
    28,
    29,
    30,
  ] {
    *bad |= input[at] != F128::ZERO;
  }
  *bad |=
    input[31].hi != 0 || input[31].lo > cursor.lo || input[31] == F128::ZERO;
  *bad |= count == F128::ZERO && input[31].lo != cursor.lo;
  for (i, on) in live.iter().copied().enumerate() {
    let rec = &bank[i * r..(i + 1) * r];
    let span = rec[SPAN];
    let payload = rec[PAYLOAD];
    let previous =
      if i == 0 { input[31].lo } else { bank[(i - 1) * r + SPAN].hi };
    *bad |=
      on && (span.lo >= span.hi || span.hi > cursor.lo || span.lo != previous);
    *bad |= on && (i + 1 == a.nodes || !live[i + 1]) && span.hi != cursor.lo;
    let kind = value(rec[KIND]);
    let tag = value(rec[SCALAR]);
    let scalar = on && kind == 0;
    let refs = on && matches!(kind, 1 | 2);
    *bad |= on && kind >= 4;
    *bad |= !scalar && tag != 0;
    *bad |=
      !refs && (rec[REFERENCE] != F128::ZERO || rec[CHILDREN] != F128::ZERO);
    *bad |= on
      && kind == 1
      && value(rec[REFERENCE]) >= c.registry.constructors() as u128;
    *bad |= on
      && kind == 2
      && value(rec[REFERENCE]) >= c.registry.functions() as u128;
    *bad |= on && value(rec[CHILDREN]) > a.nodes as u128;
    *bad |= scalar && tag >= 7;
    let nat = scalar && tag == 0;
    let payload_scalar = scalar && matches!(tag, 0 | 1 | 6);
    let fixed = scalar && matches!(tag, 2..=5);
    *bad |= !payload_scalar && payload != F128::ZERO;
    let (end, overflow) = payload.lo.overflowing_add(payload.hi);
    *bad |=
      payload_scalar && (span.lo >= payload.lo || overflow || end != span.hi);
    *bad |=
      nat && (payload.hi == 0 || payload.hi > a.natural.encoded_bytes() as u64);
    *bad |= !fixed && rec[FIXED] != F128::ZERO;
    *bad |= scalar
      && match tag {
        2 => value(rec[FIXED]) > 1,
        3 => value(rec[FIXED]) > u32::MAX as u128,
        4 => rec[FIXED].hi != 0 || rec[FIXED].lo >= 0xffff_ffff_0000_0001,
        5 => {
          rec[FIXED].lo >= 0xffff_ffff_0000_0001
            || rec[FIXED].hi >= 0xffff_ffff_0000_0001
        },
        _ => false,
      };
    for (j, limb) in rec[MAGNITUDE..].iter().enumerate() {
      *bad |= !nat && *limb != F128::ZERO;
      let used = a.natural.bits().saturating_sub(j * 128).min(128);
      *bad |= used < 128 && value(*limb) >> used != 0;
    }
  }
  let mut ends = vec![0u8; a.nodes];
  let mut span_ends = vec![0u64; a.nodes];
  for i in 0..a.nodes {
    let mut pending = u8::from(live[i]);
    for j in i..a.nodes {
      if pending == 0 {
        continue;
      }
      *bad |= !live[j];
      let (sum, carry) =
        pending.overflowing_add(bank[j * r + CHILDREN].lo as u8);
      let (next, borrow) = sum.overflowing_sub(1);
      *bad |= carry || borrow;
      if next == 0 {
        ends[i] = (j + 1) as u8;
        span_ends[i] = bank[j * r + SPAN].hi;
      }
      pending = next;
    }
    *bad |= pending != 0;
  }
  let mut parents = vec![0u8; a.nodes];
  let mut depths = vec![0u8; a.nodes];
  for i in 0..a.nodes {
    depths[i] = u8::from(live[i]);
    for (j, end) in ends.iter().enumerate().take(i) {
      if live[i] && (i as u8) < *end {
        parents[i] = (j + 1) as u8;
        depths[i] += 1;
      }
    }
    *bad |= live[i] && depths[i] as usize > a.depth;
  }
  let roots = live
    .iter()
    .zip(&parents)
    .filter(|(on, parent)| **on && **parent == 0)
    .count();
  let expected = if c.kind == GrammarKind::Input {
    value(input[grammar::ENTRY_ARITY])
  } else {
    1
  };
  *bad |= roots as u128 != expected;
  let mut out = vec![
    count,
    word(roots as u128),
    word(*depths.iter().max().unwrap() as u128),
  ];
  for i in 0..a.nodes {
    let ordinal = (0..i)
      .filter(|j| live[i] && live[*j] && parents[*j] == parents[i])
      .count();
    let children = (0..a.nodes)
      .filter(|j| live[*j] && parents[*j] as usize == i + 1)
      .count();
    *bad |= live[i] && value(bank[i * r + CHILDREN]) != children as u128;
    out.extend(&bank[i * r..(i + 1) * r]);
    out.extend([
      word(parents[i] as u128),
      word(ordinal as u128),
      word(ends[i] as u128),
      word(depths[i] as u128),
      F128::new(bank[i * r + SPAN].lo, span_ends[i]),
    ]);
  }
  out
}
fn read(
  a: ValueCapacity,
  op: ValueOp,
  input: &[F128],
  bad: &mut bool,
) -> Vec<F128> {
  let enabled = flag(input[0]);
  let r = a.record_words();
  let stride = a.finished_record_words();
  let bank = &input[3..];
  *bad |= value(input[0]) > 1
    || (!enabled && (input[1] != F128::ZERO || input[2] != F128::ZERO));
  *bad |= op != ValueOp::ReadChild && input[2] != F128::ZERO;
  let (owner, overflow) = value(input[2]).overflowing_add(1);
  *bad |= enabled && overflow;
  *bad |=
    op == ValueOp::ReadChild && enabled && value(input[2]) >= a.nodes as u128;
  let live = canonical(bank, stride, bad);
  let mut found = 0;
  let mut out = vec![F128::ZERO; 1 + stride];
  for (i, on) in live.iter().copied().enumerate() {
    let rec = &bank[i * stride..(i + 1) * stride];
    let matches = if op == ValueOp::ReadNode {
      value(input[1]) == i as u128
    } else {
      value(rec[r]) == if op == ValueOp::ReadRoot { 0 } else { owner }
        && rec[r + 1] == input[1]
    };
    if enabled && on && matches {
      found += 1;
      out[0].lo ^= i as u64;
      for (out, w) in out[1..].iter_mut().zip(rec) {
        out.lo ^= w.lo;
        out.hi ^= w.hi;
      }
    }
  }
  *bad |= (enabled && found == 0) || found > 1;
  out
}
