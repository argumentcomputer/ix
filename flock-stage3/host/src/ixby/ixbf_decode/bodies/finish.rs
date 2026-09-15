use super::{super::grammar, synthesis::*, *};
use crate::sizing::CountedGate;
pub(super) fn build(b: &mut Builder, g: &BodyGate) {
  let c = g.capacity;
  let r = c.block_words();
  let registry = 28 + c.state_words();
  let bank = registry + c.registry.words();
  let done = eqc(b, &word(1)[..8], grammar::Phase::Done as u64);
  b.require(b.one, done);
  b.require_zero(b.one, &word(1)[40..]);
  same(b, b.one, &word(0)[..64], &word(0)[64..]);
  for at in 28..registry {
    b.require_zero(b.one, &word(at));
  }
  for at in [
    grammar::CTORS_LEFT,
    grammar::FUNCTIONS_LEFT,
    grammar::BLOCKS_LEFT,
    grammar::ITEMS,
    grammar::PAYLOAD,
    grammar::PENDING,
  ] {
    b.require_zero(b.one, &word(at));
  }
  le(
    b,
    b.one,
    &word(grammar::FUNCTIONS),
    &b.constant(128, c.registry.functions() as u64),
  );
  let nonzero = b.any(&word(grammar::FUNCTIONS));
  b.require(b.one, nonzero);
  let live = bank::canonical(b, bank, c.blocks(), r);
  let mut function_live = Vec::new();
  let mut function_spans = Vec::new();
  for f in 0..c.registry.functions() {
    let func = registry + c.registry.constructors() * 7 + f * 5;
    let present = flag(b, func);
    function_live.push(present);
    let expected = lt(b, &b.constant(128, f as u64), &word(grammar::FUNCTIONS));
    same(b, b.one, &[present], &[expected]);
    let absent = b.not(present);
    for j in 1..5 {
      b.require_zero(absent, &word(func + j));
    }
    le(
      b,
      present,
      &word(func + 3),
      &b.constant(128, c.registry.blocks_per_function() as u64),
    );
    let nonzero = b.any(&word(func + 3));
    b.require(present, nonzero);
    let mut choices = Vec::new();
    for block in 0..c.registry.blocks_per_function() {
      let index = f * c.registry.blocks_per_function() + block;
      let at = bank + index * r;
      let reg = registry + c.registry_block(f, block);
      let on = live[index];
      let expected = lt(b, &b.constant(128, block as u64), &word(func + 3));
      let expected = b.b.and(present, expected);
      same(b, b.one, &[on], &[expected]);
      same(b, b.one, &word(at), &word(reg));
      same(b, on, &word(at + LOCALS), &word(reg + 1));
      same(b, on, &word(at + INSTRUCTION), &word(reg + 2));
      let span = word(at + SPAN);
      let header = word(reg + 3);
      same(b, on, &span[..64], &header[..64]);
      same(b, on, &word(at + HEADER_END)[..64], &header[64..]);
      b.require_zero(b.one, &word(at + HEADER_END)[64..]);
      let nonempty = lt(b, &header[..64], &header[64..]);
      b.require(on, nonempty);
      let body = lt(b, &header[64..], &span[64..]);
      b.require(on, body);
      le(b, on, &span[64..], &word(0)[..64]);
      let previous = if block == 0 {
        word(func + 4)[64..].to_vec()
      } else {
        word(at - r + SPAN)[64..].to_vec()
      };
      same(b, on, &span[..64], &previous);
      let last = eqc(b, &word(func + 3), (block + 1) as u64);
      let last = b.b.and(on, last);
      choices.push((last, span[64..].to_vec()));
      block_record(b, c, at, on, func);
    }
    let end = select(b, &choices, 64);
    let start = mask(b, present, &word(func + 4)[..64]);
    let span = [start, end].concat();
    function_spans.push(span.clone());
    let dest = g.input_count() + f * FUNCTION_WORDS;
    for j in 0..4 {
      b.write(dest + j, &word(func + j));
    }
    b.write(dest + 4, &span);
  }
  for f in 0..c.registry.functions() {
    let on = function_live[f];
    let span = &function_spans[f];
    let valid = lt(b, &span[..64], &span[64..]);
    b.require(on, valid);
    if f > 0 {
      same(b, on, &span[..64], &function_spans[f - 1][64..]);
    }
    let last = if f + 1 == c.registry.functions() {
      on
    } else {
      let absent = b.not(function_live[f + 1]);
      b.b.and(on, absent)
    };
    same(b, last, &span[64..], &word(0)[..64]);
  }
  for i in 0..c.bank_words() {
    b.write(
      g.input_count() + c.registry.functions() * FUNCTION_WORDS + i,
      &word(bank + i),
    );
  }
}
fn block_record(
  b: &mut Builder,
  c: BodyCapacity,
  at: usize,
  on: usize,
  func: usize,
) {
  let ins: Vec<_> = (0..8)
    .map(|v| {
      let tag = eqc(b, &word(at + INSTRUCTION), v);
      b.b.and(on, tag)
    })
    .collect();
  let valid = b.any(&ins);
  b.require(on, valid);
  let ops: Vec<_> = (0..8)
    .map(|v| {
      let tag = eqc(b, &word(at + OPERATION), v);
      b.b.and(ins[0], tag)
    })
    .collect();
  let valid = b.any(&ops);
  b.require(ins[0], valid);
  let not_let = b.not(ins[0]);
  b.require_zero(not_let, &word(at + OPERATION));
  let refs = b.any(&[ins[2], ops[2], ops[4], ops[5]]);
  let args = b.any(&[
    ins[2], ins[3], ins[4], ops[1], ops[2], ops[4], ops[5], ops[6], ops[7],
  ]);
  let target0 = b.any(&[ins[0], ins[6], ins[7]]);
  let target1 = b.any(&[ins[6], ins[7]]);
  for (enabled, offset) in [
    (ops[1], PRIMITIVE),
    (refs, REFERENCE),
    (ops[3], PROJECTION),
    (args, ARGUMENTS),
    (target0, TARGET0),
    (target1, TARGET1),
    (ins[5], ALTERNATIVES),
  ] {
    let disabled = b.not(enabled);
    b.require_zero(disabled, &word(at + offset));
  }
  let bound = lt(b, &word(at + REFERENCE), &word(grammar::CTORS));
  b.require(ops[2], bound);
  let function = b.any(&[ins[2], ops[4], ops[5]]);
  let bound = lt(b, &word(at + REFERENCE), &word(grammar::FUNCTIONS));
  b.require(function, bound);
  for (enabled, offset) in [(target0, TARGET0), (target1, TARGET1)] {
    let bound = lt(b, &word(at + offset), &word(func + 3));
    b.require(enabled, bound);
  }
  let primitives: Vec<_> = crate::ixby::ixbf::Primitive::ALL
    .into_iter()
    .map(|p| {
      let matched = eqc(b, &word(at + PRIMITIVE), p.opcode() as u64);
      let selected = b.b.and(ops[1], matched);
      let arity = eqc(b, &word(at + ARGUMENTS), p.arity() as u64);
      b.require(selected, arity);
      selected
    })
    .collect();
  let valid = b.any(&primitives);
  b.require(ops[1], valid);
  let one = b.any(&[ins[1], ins[5], ins[6], ins[7], ops[0], ops[3]]);
  let counted =
    b.any(&[ins[2], ins[3], ops[1], ops[2], ops[4], ops[5], ops[6]]);
  let apply = b.any(&[ins[4], ops[7]]);
  let plus_one = plus(b, apply, &word(at + ARGUMENTS), &b.constant(128, 1));
  let expected = select(
    b,
    &[
      (one, b.constant(128, 1)),
      (counted, word(at + ARGUMENTS)),
      (apply, plus_one),
    ],
    128,
  );
  same(b, on, &word(at + OPERANDS), &expected);
  le(b, on, &word(at + OPERANDS), &b.constant(128, c.operands as u64));
  le(
    b,
    on,
    &word(at + ALTERNATIVES),
    &b.constant(128, c.registry.constructors() as u64),
  );
  let operands =
    bank::canonical(b, at + HEADER_WORDS, c.operands, c.operand_words());
  for (i, present) in operands.iter().copied().enumerate() {
    let expected = lt(b, &b.constant(128, i as u64), &word(at + OPERANDS));
    let expected = b.b.and(on, expected);
    same(b, b.one, &[present], &[expected]);
    let operand = at + HEADER_WORDS + i * c.operand_words();
    let previous = if i == 0 {
      word(at + HEADER_END)[..64].to_vec()
    } else {
      word(operand - c.operand_words() + O_SPAN)[64..].to_vec()
    };
    le(b, present, &previous, &word(operand + O_SPAN)[..64]);
    scalar_record(b, c, at, operand, present);
  }
  let alts = bank::canonical(
    b,
    at + c.alternatives(),
    c.registry.constructors(),
    ALT_WORDS,
  );
  for (i, present) in alts.iter().copied().enumerate() {
    let expected = lt(b, &b.constant(128, i as u64), &word(at + ALTERNATIVES));
    let expected = b.b.and(on, expected);
    same(b, b.one, &[present], &[expected]);
    let alt = at + c.alternatives() + i * ALT_WORDS;
    let span = word(alt + 3);
    let valid = lt(b, &span[..64], &span[64..]);
    b.require(present, valid);
    le(b, present, &span[64..], &word(at + SPAN)[64..]);
    let previous = if i == 0 {
      word(at + HEADER_WORDS + O_SPAN)[64..].to_vec()
    } else {
      word(alt - ALT_WORDS + 3)[64..].to_vec()
    };
    le(b, present, &previous, &span[..64]);
    let ctor = lt(b, &word(alt + 1), &word(grammar::CTORS));
    b.require(present, ctor);
    let target = lt(b, &word(alt + 2), &word(func + 3));
    b.require(present, target);
    for (j, previous) in alts.iter().copied().enumerate().take(i) {
      let both = b.b.and(present, previous);
      let equal = b.equal(
        &word(alt + 1),
        &word(at + c.alternatives() + j * ALT_WORDS + 1),
      );
      b.require_zero(both, &[equal]);
    }
  }
}
fn scalar_record(
  b: &mut Builder,
  c: BodyCapacity,
  block: usize,
  at: usize,
  on: usize,
) {
  let kinds: Vec<_> = (0..3)
    .map(|v| {
      let tag = eqc(b, &word(at + O_KIND), v);
      b.b.and(on, tag)
    })
    .collect();
  let valid = b.any(&kinds);
  b.require(on, valid);
  let not_local = b.not(kinds[0]);
  b.require_zero(not_local, &word(at + O_LOCAL));
  let bound = lt(b, &word(at + O_LOCAL), &word(block + LOCALS));
  b.require(kinds[0], bound);
  let scalar = kinds[1];
  let not_scalar = b.not(scalar);
  b.require_zero(not_scalar, &word(at + O_SCALAR));
  let span = word(at + O_SPAN);
  let payload = word(at + O_PAYLOAD);
  let valid = lt(b, &span[..64], &span[64..]);
  b.require(on, valid);
  le(b, on, &span[64..], &word(block + SPAN)[64..]);
  let tags: Vec<_> = (0..7)
    .map(|v| {
      let tag = eqc(b, &word(at + O_SCALAR), v);
      b.b.and(scalar, tag)
    })
    .collect();
  let valid = b.any(&tags);
  b.require(scalar, valid);
  let has_payload = b.any(&[tags[0], tags[1], tags[6]]);
  let none = b.not(has_payload);
  b.require_zero(none, &payload);
  let start = lt(b, &span[..64], &payload[..64]);
  b.require(has_payload, start);
  let end = plus(b, has_payload, &payload[..64], &payload[64..]);
  same(b, has_payload, &end, &span[64..]);
  let nonzero = b.any(&payload[64..]);
  b.require(tags[0], nonzero);
  le(
    b,
    tags[0],
    &payload[64..],
    &b.constant(64, c.natural.encoded_bytes() as u64),
  );
  let fixed = b.any(&tags[2..6]);
  let none = b.not(fixed);
  b.require_zero(none, &word(at + O_FIXED));
  b.require_zero(tags[2], &word(at + O_FIXED)[1..]);
  b.require_zero(tags[3], &word(at + O_FIXED)[32..]);
  b.require_zero(tags[4], &word(at + O_FIXED)[64..]);
  let gold = b.any(&[tags[4], tags[5]]);
  let p = b.constant(64, 0xffff_ffff_0000_0001);
  let valid = lt(b, &word(at + O_FIXED)[..64], &p);
  b.require(gold, valid);
  let valid = lt(b, &word(at + O_FIXED)[64..], &p);
  b.require(tags[5], valid);
  let not_nat = b.not(tags[0]);
  for i in 0..c.natural.magnitude_words() {
    let w = word(at + O_MAGNITUDE + i);
    b.require_zero(not_nat, &w);
    let used = c.natural.bits().saturating_sub(i * 128).min(128);
    b.require_zero(b.one, &w[used..]);
  }
}
