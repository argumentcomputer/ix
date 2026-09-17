use super::{
  super::grammar::{self, Phase},
  synthesis::*,
  *,
};
use crate::sizing::CountedGate;

pub(super) fn build(b: &mut Builder, g: &ValueGate) {
  let a = g.config.arena;
  let acc = NAT + a.natural.magnitude_words();
  let pending = flag(b, acc);
  b.require_zero(b.one, &word(acc + 1)[64..]);
  b.require_zero(b.one, &word(acc + 2)[3..]);
  b.require_zero(b.one, &word(acc + 3)[64..]);
  let idle = b.not(pending);
  b.require_zero(idle, &word(acc + 1));
  b.require_zero(idle, &word(acc + 2));
  let cursor = word(0);
  let next = word(NEXT);
  le(b, b.one, &cursor[..64], &cursor[64..]);
  le(b, b.one, &cursor[..64], &next[..64]);
  le(b, b.one, &next[..64], &cursor[64..]);
  same(b, b.one, &next[64..], &cursor[64..]);
  le(b, pending, &word(acc + 1)[..64], &cursor[..64]);
  le(b, pending, &word(acc + 3)[..64], &word(acc + 1)[..64]);
  b.require_zero(b.one, &word(1)[40..]);
  let (commit, tags) = events(b, COMMIT, TAG);
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
  let p: Vec<_> =
    phases.iter().map(|v| eqc(b, &word(1)[..8], *v as u64)).collect();
  let valid = b.any(&p);
  b.require(b.one, valid);
  for (flag, tag) in p.iter().copied().zip([
    if g.config.kind == GrammarKind::Input { 7 } else { 8 },
    9,
    11,
    14,
    1,
    15,
    1,
    16,
    17,
  ]) {
    b.require(flag, tags[tag]);
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
  ]: [usize; 9] = p.try_into().unwrap();
  for i in acc..acc + ACC_WORDS {
    b.require_zero(header, &word(i));
  }
  b.require_zero(header, &cursor[..64]);
  let not_header = b.not(header);
  let started = b.any(&word(acc + 3));
  b.require(not_header, started);
  let progress = lt(b, &cursor[..64], &next[..64]);
  b.require(commit, progress);
  same(b, done, &cursor, &next);
  b.require_zero(done, &[pending]);
  b.require_zero(value, &[pending]);
  let kinds: Vec<_> = (0..5).map(|i| eqc(b, &word(FIELDS), i)).collect();
  let valid = b.any(&kinds);
  b.require(value, valid);
  let begin = b.b.and(value, kinds[0]);
  let aggregate = b.any(&[kinds[1], kinds[2]]);
  let aggregate = b.b.and(value, aggregate);
  let children = b.any(&[kinds[1], kinds[2], kinds[4]]);
  let children = b.b.and(value, children);
  let non_scalar = b.any(&[kinds[1], kinds[2], kinds[3], kinds[4]]);
  let non_scalar = b.b.and(value, non_scalar);
  let no_ref = b.not(aggregate);
  b.require_zero(no_ref, &word(RESOLVED));
  let pap = b.b.and(value, kinds[2]);
  same(b, pap, &word(RESOLVED), &word(FIELDS + 1));
  let scalar_tags: Vec<_> = (0..7).map(|i| eqc(b, &word(FIELDS), i)).collect();
  let valid = b.any(&scalar_tags);
  b.require(scalar, valid);
  b.require(scalar, pending);
  let unset = eqc(b, &word(acc + 2), 7);
  b.require(scalar, unset);
  for (on, tag) in [
    (natural, 0),
    (string_count, 1),
    (string_payload, 1),
    (bytes_count, 6),
    (bytes_payload, 6),
  ] {
    b.require(on, pending);
    let right = eqc(b, &word(acc + 2), tag);
    b.require(on, right);
  }
  let fixed = b.any(&scalar_tags[2..6]);
  let fixed = b.b.and(scalar, fixed);
  let empty = eqc(b, &word(FIELDS), 0);
  let counts = b.any(&[string_count, bytes_count]);
  let empty = b.b.and(counts, empty);
  let string_done = b.b.and(string_payload, commit);
  let payload_done = b.any(&[string_done, bytes_payload]);
  let scalar_done = b.any(&[fixed, natural, empty, payload_done]);
  let emit = b.any(&[non_scalar, scalar_done]);
  let mut state: Vec<_> = (acc..acc + ACC_WORDS).map(word).collect();
  let prefix = [cursor[..64].to_vec(), vec![b.zero; 64]].concat();
  state[0] = choose(b, begin, &b.constant(128, 1), &state[0]);
  state[1] = choose(b, begin, &prefix, &state[1]);
  state[2] = choose(b, begin, &b.constant(128, 7), &state[2]);
  state[2] = choose(b, scalar, &word(FIELDS), &state[2]);
  let keep = b.not(scalar_done);
  for word in state.iter_mut().take(3) {
    *word = mask(b, keep, word);
  }
  let header_end = [next[..64].to_vec(), vec![b.zero; 64]].concat();
  state[3] = choose(b, header, &header_end, &state[3]);
  for (i, word) in state.iter().enumerate() {
    b.write(g.input_count() + i, word);
  }
  let previous =
    minus(b, scalar_done, &word(grammar::SEEN), &b.constant(128, 1));
  let index = select(
    b,
    &[(non_scalar, word(grammar::SEEN)), (scalar_done, previous)],
    128,
  );
  b.write(g.input_count() + PACKET_INDEX, &index);
  let mut record = vec![b.constant(128, 0); a.record_words()];
  record[PRESENT][0] = emit;
  record[KIND] = mask(b, non_scalar, &word(FIELDS));
  let later = b.any(&[natural, empty, payload_done]);
  record[SCALAR] =
    select(b, &[(fixed, word(FIELDS)), (later, word(acc + 2))], 128);
  record[REFERENCE] = mask(b, aggregate, &word(RESOLVED));
  record[CHILDREN] = mask(b, children, &word(FIELDS + 5));
  let start = select(
    b,
    &[
      (non_scalar, cursor[..64].to_vec()),
      (scalar_done, word(acc + 1)[..64].to_vec()),
    ],
    64,
  );
  record[SPAN] = [start, mask(b, emit, &next[..64])].concat();
  record[FIXED] = mask(b, fixed, &word(FIELDS + 1));
  for i in 0..a.natural.magnitude_words() {
    record[MAGNITUDE + i] = mask(b, natural, &word(NAT + i));
  }
  let nat_range = word(NAT_RANGE);
  let byte_range = word(BYTE_RANGE);
  for (on, range, length) in [
    (natural, &nat_range, word(FIELDS)),
    (payload_done, &byte_range, word(grammar::PAYLOAD)),
  ] {
    same(b, on, &range[..64], &cursor[..64]);
    let wide = [range[64..].to_vec(), vec![b.zero; 64]].concat();
    same(b, on, &wide, &length);
    let end = plus(b, on, &range[..64], &range[64..]);
    same(b, on, &end, &next[..64]);
  }
  let empty_range = [next[..64].to_vec(), vec![b.zero; 64]].concat();
  record[PAYLOAD] = select(
    b,
    &[(natural, nat_range), (payload_done, byte_range), (empty, empty_range)],
    128,
  );
  for (i, word) in record.iter().enumerate() {
    b.write(g.input_count() + PACKET_RECORD + i, word);
  }
}
