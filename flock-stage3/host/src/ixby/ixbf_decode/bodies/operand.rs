use super::{
  super::grammar::{self, Phase},
  synthesis::*,
  *,
};
pub(super) fn assemble(
  b: &mut Builder,
  c: BodyCapacity,
  phases: &[usize],
  commit: usize,
) -> (Vec<Bits>, usize, Vec<Bits>) {
  let s = c.state();
  let at = s + CONTROL_WORDS;
  let pending = flag(b, s + 2);
  let idle = b.not(pending);
  b.require_zero(b.one, &word(s + 3)[64..]);
  b.require_zero(b.one, &word(s + 4)[3..]);
  b.require_zero(idle, &word(s + 3));
  b.require_zero(idle, &word(s + 4));
  let cursor = word(0);
  let next = word(NEXT);
  le(b, pending, &word(at + HEADER_END)[..64], &word(s + 3)[..64]);
  le(b, pending, &word(s + 3)[..64], &cursor[..64]);
  let operand = phases[Phase::Operand as usize];
  let scalar = phases[Phase::Scalar as usize];
  let natural = phases[Phase::Natural as usize];
  b.require_zero(operand, &[pending]);
  let kinds: Vec<_> = (0..3).map(|v| eqc(b, &word(FIELDS), v)).collect();
  let valid = b.any(&kinds);
  b.require(operand, valid);
  let local = b.b.and(operand, kinds[0]);
  let erased = b.b.and(operand, kinds[2]);
  let begin = b.b.and(operand, kinds[1]);
  let direct = b.any(&[local, erased]);
  b.require(scalar, pending);
  let unset = eqc(b, &word(s + 4), 7);
  b.require(scalar, unset);
  let tags: Vec<_> = (0..7).map(|v| eqc(b, &word(FIELDS), v)).collect();
  let valid = b.any(&tags);
  b.require(scalar, valid);
  for (phase, tag) in [
    (Phase::Natural, 0),
    (Phase::StringCount, 1),
    (Phase::StringPayload, 1),
    (Phase::BytesCount, 6),
    (Phase::BytesPayload, 6),
  ] {
    let on = phases[phase as usize];
    b.require(on, pending);
    let matches = eqc(b, &word(s + 4), tag);
    b.require(on, matches);
  }
  let fixed = b.any(&tags[2..6]);
  let fixed = b.b.and(scalar, fixed);
  let zero = eqc(b, &word(FIELDS), 0);
  let count = b.any(&[
    phases[Phase::StringCount as usize],
    phases[Phase::BytesCount as usize],
  ]);
  let empty = b.b.and(count, zero);
  let string = b.b.and(phases[Phase::StringPayload as usize], commit);
  let payload = b.any(&[string, phases[Phase::BytesPayload as usize]]);
  let scalar_done = b.any(&[fixed, natural, empty, payload]);
  let emit = b.any(&[direct, scalar_done]);
  let mut state: Vec<_> = (s + 2..s + 5).map(word).collect();
  state[0] = choose(b, begin, &b.constant(128, 1), &state[0]);
  state[1] = choose(
    b,
    begin,
    &[cursor[..64].to_vec(), vec![b.zero; 64]].concat(),
    &state[1],
  );
  state[2] = choose(b, begin, &b.constant(128, 7), &state[2]);
  state[2] = choose(b, scalar, &word(FIELDS), &state[2]);
  let keep = b.not(scalar_done);
  for w in &mut state {
    *w = mask(b, keep, w);
  }
  let mut record = vec![b.constant(128, 0); c.operand_words()];
  record[0][0] = emit;
  record[O_KIND] = select(
    b,
    &[(erased, b.constant(128, 2)), (scalar_done, b.constant(128, 1))],
    128,
  );
  record[O_LOCAL] = mask(b, local, &word(FIELDS + 1));
  let later = b.any(&[natural, empty, payload]);
  record[O_SCALAR] =
    select(b, &[(fixed, word(FIELDS)), (later, word(s + 4))], 128);
  let start = select(
    b,
    &[
      (direct, cursor[..64].to_vec()),
      (scalar_done, word(s + 3)[..64].to_vec()),
    ],
    64,
  );
  record[O_SPAN] = [start, mask(b, emit, &next[..64])].concat();
  record[O_FIXED] = mask(b, fixed, &word(FIELDS + 1));
  for i in 0..c.natural.magnitude_words() {
    record[O_MAGNITUDE + i] = mask(b, natural, &word(NAT + i));
  }
  for (on, range, length) in [
    (natural, word(NAT_RANGE), word(FIELDS)),
    (payload, word(BYTE_RANGE), word(grammar::PAYLOAD)),
  ] {
    same(b, on, &range[..64], &cursor[..64]);
    same(b, on, &[range[64..].to_vec(), vec![b.zero; 64]].concat(), &length);
    let end = plus(b, on, &range[..64], &range[64..]);
    same(b, on, &end, &next[..64]);
  }
  record[O_PAYLOAD] = select(
    b,
    &[
      (natural, word(NAT_RANGE)),
      (payload, word(BYTE_RANGE)),
      (empty, [next[..64].to_vec(), vec![b.zero; 64]].concat()),
    ],
    128,
  );
  (state, emit, record)
}
