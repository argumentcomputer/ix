use super::*;
use crate::{
  boolean::BooleanR1csPlan,
  ixby::{
    ixbf_decode::grammar::Phase,
    paged_code::{BLOCKS, CONSTRUCTORS, FUNCTIONS},
    paged_value::PROGRAM_BYTES,
  },
};

fn field(i: usize) -> Bits {
  word(FIELDS + i)
}
fn put(
  b: &mut Builder,
  h: &mut Bits,
  on: usize,
  start: usize,
  width: usize,
  value: &[usize],
) {
  b.require_zero(on, &value[width..]);
  let out = choose(b, on, &value[..width], &h[start..start + width]);
  h[start..start + width].copy_from_slice(&out);
}
fn write(b: &mut Builder, at: usize, choices: &[(usize, Bits, [Bits; 2])]) {
  let enables = choices.iter().map(|(e, _, _)| *e).collect::<Vec<_>>();
  let e = b.any(&enables);
  let address = select(
    b,
    &choices.iter().map(|(e, a, _)| (*e, a.clone())).collect::<Vec<_>>(),
    128,
  );
  b.write(INPUTS + at, &address);
  b.write(INPUTS + at + 1, &[e]);
  for part in 0..2 {
    let value = select(
      b,
      &choices
        .iter()
        .map(|(e, _, v)| (*e, v[part].clone()))
        .collect::<Vec<_>>(),
      128,
    );
    b.write(INPUTS + at + 2 + part, &value);
  }
}
pub(super) fn plan() -> BooleanR1csPlan {
  let mut builder = Builder::new(INPUTS, OUTPUTS, 1 << 17);
  let b = &mut builder;
  let opened = word(OPEN)[0];
  b.require_zero(b.one, &word(OPEN)[1..]);
  let idle = b.not(opened);
  for at in STATE..STATE + STATE_WORDS {
    b.require_zero(idle, &word(at));
  }
  b.require_zero(b.one, &word(CURRENT)[10..64]);
  b.require_zero(b.one, &word(CURRENT)[72..]);
  let h0 = word(HEADER);
  b.require_zero(b.one, &h0[32..40]);
  b.require_zero(b.one, &h0[56..64]);
  b.require_zero(b.one, &h0[112..]);
  bound(b, opened, &h0[..8], 128);
  b.require_zero(b.one, &h0[11..16]);
  b.require_zero(b.one, &h0[19..24]);
  bound(b, b.one, &word(OPERANDS), 65);
  bound(b, b.one, &word(SCALAR), 4);
  let commit = word(COMMITTED)[0];
  b.require_zero(b.one, &word(COMMITTED)[1..]);
  let tags = (0..18).map(|i| eqc(b, &word(TAG), i)).collect::<Vec<_>>();
  let valid = b.any(&tags);
  b.require(b.one, valid);
  let optional = b.any(&[tags[15], tags[17]]);
  let mandatory = b.not(optional);
  b.require(mandatory, commit);
  b.require_zero(tags[17], &[commit]);
  let active = b.not(tags[17]);
  b.require_zero(b.one, &word(1)[40..]);
  b.require_zero(b.one, &word(NEXT_CONTROL)[40..]);
  let phases = (0..=20).map(|i| eqc(b, &word(1)[..8], i)).collect::<Vec<_>>();
  let valid = b.any(&phases);
  b.require(b.one, valid);
  b.require_zero(b.one, &[phases[19]]);
  let body = b.any(&phases[5..=18]);
  same(b, b.one, &[opened], &[body]);
  let case = eqc(b, &h0[8..16], 5);
  let noncase = b.not(case);
  b.require_zero(noncase, &word(SEEN));
  b.require_zero(noncase, &word(SEEN + 1));
  let on = phases.iter().map(|&p| b.b.and(active, p)).collect::<Vec<_>>();
  for (&e, tag) in on.iter().zip([
    13, 3, 1, 4, 5, 12, 10, 1, 2, 0, 2, 1, 6, 11, 14, 1, 15, 1, 16, 9, 17,
  ]) {
    b.require(e, tags[tag]);
  }
  let begin = on[Phase::Block as usize];
  let in_body = b.b.and(active, body);
  let boundary = [Phase::Block, Phase::Function, Phase::Done]
    .map(|p| eqc(b, &word(NEXT_CONTROL)[..8], p as u64));
  let boundary = b.any(&boundary);
  let closing = b.b.and(in_body, boundary);
  let closing = b.b.and(closing, commit);
  let owner_live = b.any(&[begin, in_body]);
  let owner = minus(b, owner_live, &word(5), &b.constant(128, 1));
  bound(b, owner_live, &owner, 1023);
  let ordinal = minus(b, owner_live, &word(6), &word(7));
  let previous = minus(b, in_body, &ordinal, &b.constant(128, 1));
  same(b, in_body, &owner[..64], &word(CURRENT)[..64]);
  same(b, in_body, &previous[..64], &word(CURRENT)[64..]);
  bound(b, begin, &ordinal, 255);
  let current = choose(
    b,
    begin,
    &[owner[..64].to_vec(), ordinal[..64].to_vec()].concat(),
    &word(CURRENT),
  );
  let mut h = choose(b, begin, &b.constant(128, 0), &h0);
  bound(b, begin, &field(0), 128);
  put(b, &mut h, begin, 0, 8, &field(0));
  put(b, &mut h, begin, 8, 3, &field(1));
  let instructions = (0..8).map(|i| eqc(b, &h0[8..16], i)).collect::<Vec<_>>();
  let operation = on[5];
  b.require(operation, instructions[0]);
  let ops = (0..8).map(|i| eqc(b, &field(0), i)).collect::<Vec<_>>();
  let valid = b.any(&ops);
  b.require(operation, valid);
  put(b, &mut h, operation, 16, 8, &field(0));
  let prim = b.b.and(operation, ops[1]);
  put(b, &mut h, prim, 24, 8, &field(1));
  let refs = b.any(&[ops[2], ops[4], ops[5]]);
  let refs = b.b.and(operation, refs);
  put(b, &mut h, refs, 64, 16, &field(2));
  let counted = b.any(&[ops[1], ops[2], ops[4], ops[5], ops[6]]);
  let counted = b.b.and(operation, counted);
  bound(b, counted, &field(3), 64);
  put(b, &mut h, counted, 40, 8, &field(3));
  b.require(on[10], instructions[2]);
  put(b, &mut h, on[10], 64, 16, &field(0));
  let apply = eqc(b, &h0[16..24], 7);
  let let_apply = b.b.and(instructions[0], apply);
  let allowed =
    b.any(&[let_apply, instructions[2], instructions[3], instructions[4]]);
  b.require(on[7], allowed);
  bound(b, on[7], &field(0), 64);
  put(b, &mut h, on[7], 40, 8, &field(0));
  let project = eqc(b, &h0[16..24], 3);
  let project = b.b.and(instructions[0], project);
  b.require(on[9], project);
  put(b, &mut h, on[9], 96, 16, &field(0));
  let target = on[8];
  let allowed = b.any(&[instructions[0], instructions[6], instructions[7]]);
  b.require(target, allowed);
  let one = eqc(b, &word(1)[32..40], 1);
  let two = eqc(b, &word(1)[32..40], 2);
  let valid = b.any(&[one, two]);
  b.require(target, valid);
  let islet = b.b.and(target, instructions[0]);
  b.require(islet, one);
  let first = b.any(&[instructions[0], two]);
  let first = b.b.and(target, first);
  let notlet = b.not(instructions[0]);
  let second = b.b.and(target, notlet);
  let second = b.b.and(second, one);
  put(b, &mut h, first, 80, 8, &field(0));
  put(b, &mut h, second, 88, 8, &field(0));
  b.require(on[11], instructions[5]);
  bound(b, on[11], &field(0), 128);
  put(b, &mut h, on[11], 48, 8, &field(0));
  let alt = on[12];
  b.require(alt, instructions[5]);
  let mut alternatives = h0[48..56].to_vec();
  alternatives.resize(128, b.zero);
  let alt_index = minus(b, alt, &alternatives, &word(8));
  let left = b.any(&word(8));
  b.require(alt, left);
  bound(b, alt, &alt_index, 127);
  b.require_zero(alt, &field(0)[8..]);
  b.require_zero(alt, &field(1)[8..]);
  let mut seen = [word(SEEN), word(SEEN + 1)].concat();
  for (i, bit) in seen.iter_mut().enumerate() {
    let matches = eqc(b, &field(0)[..8], i as u64);
    let insert = b.b.and(alt, matches);
    b.require_zero(insert, &[*bit]);
    *bit = b.sum(&[*bit, insert]);
  }
  let (pending, emit, operand) = scalar(b, &on, commit, &h0);
  let room = lt(b, &word(OPERANDS), &b.constant(128, 65));
  b.require(emit, room);
  let mut increment = b.constant(128, 0);
  increment[0] = emit;
  let count = plus(b, b.one, &word(OPERANDS), &increment);
  let mut complete = h.clone();
  complete[32..40].copy_from_slice(&count[..8]);
  b.require_zero(closing, &pending);
  let mut base = b.constant(128, BLOCKS);
  base[8..16].copy_from_slice(&word(CURRENT)[64..72]);
  base[16..26].copy_from_slice(&word(CURRENT)[..10]);
  let operand_offset = plus(b, emit, &word(OPERANDS), &b.constant(128, 1));
  let operand_address = plus(b, emit, &base, &operand_offset);
  let alt_offset = plus(b, alt, &alt_index, &b.constant(128, 128));
  let alt_address = plus(b, alt, &base, &alt_offset);
  let mut alt_value = b.constant(128, 0);
  alt_value[..8].copy_from_slice(&field(0)[..8]);
  alt_value[8..16].copy_from_slice(&field(1)[..8]);
  // Declaration addresses and values use actual grammar counters/fields.
  let ctor = on[1];
  let function = on[3];
  bound(b, on[0], &field(12), 256);
  bound(b, on[2], &field(0), 1024);
  let ci = minus(b, ctor, &word(2), &word(4));
  bound(b, ctor, &ci, 255);
  let nonzero = b.any(&word(4));
  b.require(ctor, nonzero);
  let twice = plus(b, ctor, &ci, &ci);
  let triple = plus(b, ctor, &ci, &twice);
  let ctor0 = plus(b, ctor, &triple, &b.constant(128, CONSTRUCTORS));
  let ctor1 = plus(b, ctor, &ctor0, &b.constant(128, 1));
  let ctor2 = plus(b, ctor, &ctor0, &b.constant(128, 2));
  bound(b, ctor, &field(4), 64);
  bound(b, function, &word(5), 1023);
  let fnaddress = plus(b, function, &word(5), &b.constant(128, FUNCTIONS));
  bound(b, function, &field(0), 64);
  bound(b, function, &field(1), 255);
  bound(b, function, &field(2), 256);
  let entryok = lt(b, &field(1), &field(2));
  b.require(function, entryok);
  let mut fnvalue = b.constant(128, 0);
  fnvalue[..8].copy_from_slice(&field(0)[..8]);
  fnvalue[8..16].copy_from_slice(&field(1)[..8]);
  fnvalue[16..32].copy_from_slice(&field(2)[..16]);
  let zero = b.constant(128, 0);
  write(
    b,
    7,
    &[
      (ctor, ctor0, [field(0), field(1)]),
      (function, fnaddress, [fnvalue, zero.clone()]),
      (emit, operand_address, operand),
      (alt, alt_address, [alt_value, zero.clone()]),
    ],
  );
  write(
    b,
    11,
    &[
      (ctor, ctor1, [field(2), field(3)]),
      (closing, base, [complete.clone(), zero.clone()]),
    ],
  );
  write(b, 15, &[(ctor, ctor2, [field(4), zero.clone()])]);
  let keep = b.not(closing);
  let opened = b.any(&[opened, begin]);
  let next = [
    current,
    vec![opened].into_iter().chain(std::iter::repeat_n(b.zero, 127)).collect(),
    h,
    count,
    pending,
    seen[..128].to_vec(),
    seen[128..].to_vec(),
  ];
  for (i, word) in next.iter().enumerate() {
    let word = mask(b, keep, word);
    b.write(INPUTS + i, &word);
  }
  b.write(INPUTS + 19, &[closing]);
  let mut frame = b.constant(128, 0);
  frame[8..18].copy_from_slice(&word(CURRENT)[..10]);
  frame[24..32].copy_from_slice(&word(CURRENT)[64..72]);
  frame[32..40].copy_from_slice(&complete[..8]);
  let frame = mask(b, closing, &frame);
  b.write(INPUTS + 20, &frame);
  let complete = mask(b, closing, &complete);
  b.write(INPUTS + 21, &complete);
  builder.finish(INPUTS + OUTPUTS - 1)
}

fn scalar(
  b: &mut Builder,
  on: &[usize],
  commit: usize,
  h: &[usize],
) -> (Bits, usize, [Bits; 2]) {
  let operand = on[6];
  let scalar = on[13];
  let natural = on[14];
  b.require_zero(operand, &word(SCALAR));
  let unset = eqc(b, &word(SCALAR), 1);
  b.require(scalar, unset);
  for (phase, tag) in [(14, 2), (15, 3), (16, 3), (17, 4), (18, 4)] {
    let valid = eqc(b, &word(SCALAR), tag);
    b.require(on[phase], valid);
  }
  let kinds = (0..3).map(|i| eqc(b, &field(0), i)).collect::<Vec<_>>();
  let valid = b.any(&kinds);
  b.require(operand, valid);
  let local = b.b.and(operand, kinds[0]);
  let begin = b.b.and(operand, kinds[1]);
  let erased = b.b.and(operand, kinds[2]);
  b.require_zero(local, &field(1)[7..]);
  let room = lt(b, &field(1)[..8], &h[..8]);
  b.require(local, room);
  let tags = (0..7).map(|i| eqc(b, &field(0), i)).collect::<Vec<_>>();
  let valid = b.any(&tags);
  b.require(scalar, valid);
  let fixed = b.any(&tags[2..6]);
  let fixed = b.b.and(scalar, fixed);
  let nat = b.b.and(scalar, tags[0]);
  let string = b.b.and(scalar, tags[1]);
  let bytes = b.b.and(scalar, tags[6]);
  let count = b.any(&[on[15], on[17]]);
  let zero = eqc(b, &field(0), 0);
  let empty = b.b.and(count, zero);
  let str_done = b.b.and(on[16], commit);
  let payload = b.any(&[str_done, on[18]]);
  let done = b.any(&[fixed, natural, empty, payload]);
  let emit = b.any(&[local, erased, done]);
  let mut pending = choose(b, begin, &b.constant(128, 1), &word(SCALAR));
  for (on, tag) in [(nat, 2), (string, 3), (bytes, 4)] {
    pending = choose(b, on, &b.constant(128, tag), &pending);
  }
  let keep = b.not(done);
  pending = mask(b, keep, &pending);
  let bool_ = b.b.and(scalar, tags[2]);
  let word_ = b.b.and(scalar, tags[3]);
  let gold = b.b.and(scalar, tags[4]);
  let ext = b.b.and(scalar, tags[5]);
  // Fixed scalar canonicality comes from the actual Scalar decoder wires.
  let string_value = b.any(&[on[15], str_done]);
  let bytes_value = b.any(&[on[17], on[18]]);
  let string_value = b.b.and(done, string_value);
  let bytes_value = b.b.and(done, bytes_value);
  let tag = select(
    b,
    &[
      (erased, b.constant(128, 5)),
      (bool_, b.constant(128, 1)),
      (word_, b.constant(128, 2)),
      (gold, b.constant(128, 3)),
      (ext, b.constant(128, 4)),
      (natural, b.constant(128, 8)),
      (string_value, b.constant(128, 10)),
      (bytes_value, b.constant(128, 6)),
    ],
    128,
  );
  let range = word(RANGE);
  same(b, payload, &range[..64], &word(0)[..64]);
  let mut length = range[64..].to_vec();
  length.resize(128, b.zero);
  same(b, payload, &length, &word(9));
  b.require_zero(payload, &range[41..64]);
  b.require_zero(payload, &range[100..]);
  let end = plus(b, payload, &range[..64], &range[64..]);
  same(b, payload, &end, &word(NEXT)[..64]);
  le(b, payload, &end, &word(0)[64..]);
  bound(b, payload, &end, 1 << 41);
  let pointer =
    plus(b, payload, &range[..64], &b.constant(64, PROGRAM_BYTES << 5));
  let pointer = [pointer, range[64..].to_vec()].concat();
  let value = select(
    b,
    &[
      (local, field(1)),
      (fixed, field(1)),
      (natural, word(NATURAL)),
      (payload, pointer),
    ],
    128,
  );
  (pending, emit, [tag, value])
}
