use super::{
  super::grammar::{self, Phase},
  synthesis::*,
  *,
};
use crate::sizing::CountedGate;

pub(super) fn build(b: &mut Builder, g: &BodyGate) {
  let c = g.capacity;
  let s = c.state();
  let at = s + CONTROL_WORDS;
  let r = c.block_words();
  let opened = bank::canonical(b, at, 1, r)[0];
  let idle = b.not(opened);
  for i in s..at {
    b.require_zero(idle, &word(i));
  }
  let (commit, tags) = events(b, COMMITTED, TAG);
  b.require_zero(b.one, &word(1)[40..]);
  b.require_zero(b.one, &word(NEXT_CONTROL)[40..]);
  let phases: Vec<_> =
    (0..=Phase::Done as u64).map(|v| eqc(b, &word(1)[..8], v)).collect();
  let valid = b.any(&phases);
  b.require(b.one, valid);
  b.require_zero(b.one, &[phases[Phase::Value as usize]]);
  for (on, tag) in phases.iter().copied().zip([
    13, 3, 1, 4, 5, 12, 10, 1, 2, 0, 2, 1, 6, 11, 14, 1, 15, 1, 16, 9, 17,
  ]) {
    b.require(on, tags[tag]);
  }
  let header = phases[Phase::Start as usize];
  let begin = phases[Phase::Block as usize];
  let done = phases[Phase::Done as usize];
  let body =
    b.any(&phases[Phase::Operation as usize..=Phase::BytesPayload as usize]);
  same(b, b.one, &[opened], &[body]);
  let cursor = word(0);
  let next = word(NEXT);
  le(b, b.one, &cursor[..64], &cursor[64..]);
  le(b, b.one, &cursor[..64], &next[..64]);
  le(b, b.one, &next[..64], &cursor[64..]);
  let ordinary = b.not(header);
  same(b, ordinary, &next[64..], &cursor[64..]);
  b.require_zero(header, &next[64..]);
  b.require_zero(header, &cursor[..64]);
  let progress = lt(b, &cursor[..64], &next[..64]);
  b.require(commit, progress);
  same(b, done, &cursor, &next);
  let continuing: Vec<_> = (Phase::Operation as u64
    ..=Phase::BytesPayload as u64)
    .map(|v| eqc(b, &word(NEXT_CONTROL)[..8], v))
    .collect();
  let next_body = b.any(&continuing);
  b.require(begin, next_body);
  let boundary: Vec<_> = [Phase::Block, Phase::Function, Phase::Done]
    .into_iter()
    .map(|v| eqc(b, &word(NEXT_CONTROL)[..8], v as u64))
    .collect();
  let boundary = b.any(&boundary);
  let allowed = b.any(&[boundary, next_body]);
  b.require(body, allowed);
  let closing = b.b.and(body, boundary);
  let closing = b.b.and(commit, closing);
  let active = b.any(&[begin, body]);
  let owner =
    minus(b, active, &word(grammar::FUNCTION_INDEX), &b.constant(128, 1));
  let ordinal =
    minus(b, active, &word(grammar::BLOCKS), &word(grammar::BLOCKS_LEFT));
  let previous = minus(b, body, &ordinal, &b.constant(128, 1));
  same(b, body, &owner, &word(s));
  same(b, body, &previous, &word(s + 1));
  let room = lt(b, &owner, &b.constant(128, c.registry.functions() as u64));
  b.require(active, room);
  let block_index = choose(b, begin, &ordinal, &word(s + 1));
  let room = lt(
    b,
    &block_index,
    &b.constant(128, c.registry.blocks_per_function() as u64),
  );
  b.require(active, room);
  same(b, body, &word(at + SPAN)[64..], &cursor[..64]);
  let mut record: Vec<_> = (at..at + r).map(word).collect();
  let zero = b.constant(128, 0);
  for w in &mut record {
    *w = choose(b, begin, &zero, w);
  }
  record[PRESENT] = choose(b, begin, &b.constant(128, 1), &record[PRESENT]);
  record[LOCALS] = choose(b, begin, &word(FIELDS), &record[LOCALS]);
  record[INSTRUCTION] =
    choose(b, begin, &word(FIELDS + 1), &record[INSTRUCTION]);
  record[HEADER_END] = choose(
    b,
    begin,
    &[next[..64].to_vec(), vec![b.zero; 64]].concat(),
    &record[HEADER_END],
  );
  let start = choose(b, begin, &cursor[..64], &word(at + SPAN)[..64]);
  let consumed = b.b.and(active, commit);
  let end = choose(b, consumed, &next[..64], &word(at + SPAN)[64..]);
  record[SPAN] = [start, end].concat();
  let instructions: Vec<_> =
    (0..8).map(|v| eqc(b, &word(at + INSTRUCTION), v)).collect();
  let valid = b.any(&instructions);
  b.require(body, valid);
  let operation = phases[Phase::Operation as usize];
  b.require(operation, instructions[0]);
  let ops: Vec<_> = (0..8).map(|v| eqc(b, &word(FIELDS), v)).collect();
  let valid = b.any(&ops);
  b.require(operation, valid);
  record[OPERATION] = choose(b, operation, &word(FIELDS), &record[OPERATION]);
  let primitive = b.b.and(operation, ops[1]);
  record[PRIMITIVE] =
    choose(b, primitive, &word(FIELDS + 1), &record[PRIMITIVE]);
  let refs = b.any(&[ops[2], ops[4], ops[5]]);
  let refs = b.b.and(operation, refs);
  record[REFERENCE] = choose(b, refs, &word(FIELDS + 2), &record[REFERENCE]);
  let counted = b.any(&[ops[1], ops[2], ops[4], ops[5], ops[6]]);
  let counted = b.b.and(operation, counted);
  record[ARGUMENTS] = choose(b, counted, &word(FIELDS + 3), &record[ARGUMENTS]);
  let tail = phases[Phase::FunctionIndex as usize];
  b.require(tail, instructions[2]);
  record[REFERENCE] = choose(b, tail, &word(FIELDS), &record[REFERENCE]);
  let count = phases[Phase::OperandCount as usize];
  let apply = eqc(b, &word(at + OPERATION), 7);
  let let_apply = b.b.and(instructions[0], apply);
  let allowed =
    b.any(&[let_apply, instructions[2], instructions[3], instructions[4]]);
  b.require(count, allowed);
  record[ARGUMENTS] = choose(b, count, &word(FIELDS), &record[ARGUMENTS]);
  let projection = phases[Phase::Projection as usize];
  let project = eqc(b, &word(at + OPERATION), 3);
  let project = b.b.and(instructions[0], project);
  b.require(projection, project);
  record[PROJECTION] =
    choose(b, projection, &word(FIELDS), &record[PROJECTION]);
  let target = phases[Phase::Target as usize];
  let allowed = b.any(&[instructions[0], instructions[6], instructions[7]]);
  b.require(target, allowed);
  let one = eqc(b, &word(1)[32..40], 1);
  let two = eqc(b, &word(1)[32..40], 2);
  let valid = b.any(&[one, two]);
  b.require(target, valid);
  let let_target = b.b.and(target, instructions[0]);
  b.require(let_target, one);
  let first = b.any(&[instructions[0], two]);
  let first = b.b.and(target, first);
  let not_let = b.not(instructions[0]);
  let second = b.b.and(target, not_let);
  let second = b.b.and(second, one);
  record[TARGET0] = choose(b, first, &word(FIELDS), &record[TARGET0]);
  record[TARGET1] = choose(b, second, &word(FIELDS), &record[TARGET1]);
  let alt_count = phases[Phase::AlternativeCount as usize];
  b.require(alt_count, instructions[5]);
  le(
    b,
    alt_count,
    &word(FIELDS),
    &b.constant(128, c.registry.constructors() as u64),
  );
  record[ALTERNATIVES] =
    choose(b, alt_count, &word(FIELDS), &record[ALTERNATIVES]);
  let alt = phases[Phase::Alternative as usize];
  b.require(alt, instructions[5]);
  let index = minus(b, alt, &word(at + ALTERNATIVES), &word(grammar::ITEMS));
  let nonzero = b.any(&word(grammar::ITEMS));
  b.require(alt, nonzero);
  let bounded =
    lt(b, &index, &b.constant(128, c.registry.constructors() as u64));
  b.require(alt, bounded);
  let alt_record = [
    b.constant(128, 1),
    word(FIELDS),
    word(FIELDS + 1),
    [cursor[..64].to_vec(), next[..64].to_vec()].concat(),
  ];
  for i in 0..c.registry.constructors() {
    let matches = eqc(b, &index, i as u64);
    let insert = b.b.and(alt, matches);
    let offset = c.alternatives() + i * ALT_WORDS;
    b.require_zero(insert, &word(at + offset));
    for (j, w) in alt_record.iter().enumerate() {
      record[offset + j] = choose(b, insert, w, &record[offset + j]);
    }
  }
  let (scalar, emit, operand) = operand::assemble(b, c, &phases, commit);
  let room = lt(b, &word(at + OPERANDS), &b.constant(128, c.operands as u64));
  b.require(emit, room);
  let increment = [vec![emit], vec![b.zero; 127]].concat();
  record[OPERANDS] = plus(b, b.one, &record[OPERANDS], &increment);
  for i in 0..c.operands {
    let matches = eqc(b, &word(at + OPERANDS), i as u64);
    let insert = b.b.and(emit, matches);
    let offset = HEADER_WORDS + i * c.operand_words();
    b.require_zero(insert, &word(at + offset));
    for (j, w) in operand.iter().enumerate() {
      record[offset + j] = choose(b, insert, w, &record[offset + j]);
    }
  }
  for w in &scalar {
    b.require_zero(closing, w);
  }
  let owner = choose(b, begin, &owner, &word(s));
  let keep = b.not(closing);
  for (i, w) in [owner.clone(), block_index.clone()]
    .into_iter()
    .chain(scalar)
    .chain(record.clone())
    .enumerate()
  {
    let w = mask(b, keep, &w);
    b.write(g.input_count() + i, &w);
  }
  let packet = g.input_count() + c.state_words();
  for (i, w) in [owner, block_index].into_iter().chain(record).enumerate() {
    let w = mask(b, closing, &w);
    b.write(packet + i, &w);
  }
}
