use super::{synthesis::*, *};
use crate::sizing::CountedGate;
pub(super) fn build(b: &mut Builder, g: &BodyGate) {
  let c = g.capacity;
  let enabled = flag(b, 0);
  let disabled = b.not(enabled);
  for i in 1..4 {
    b.require_zero(disabled, &word(i));
  }
  if g.op == BodyOp::ReadFunction {
    b.require_zero(b.one, &word(2));
  }
  if matches!(g.op, BodyOp::ReadFunction | BodyOp::ReadBlock) {
    b.require_zero(b.one, &word(3));
  }
  let functions = bank::canonical(b, 4, c.registry.functions(), FUNCTION_WORDS);
  let blocks = 4 + c.registry.functions() * FUNCTION_WORDS;
  let live = bank::canonical(b, blocks, c.blocks(), c.block_words());
  let mut choices = Vec::new();
  for (f, present) in functions.iter().copied().enumerate() {
    let owner = eqc(b, &word(1), f as u64);
    let owner = b.b.and(enabled, owner);
    let owner = b.b.and(owner, present);
    if g.op == BodyOp::ReadFunction {
      choices.push((owner, 4 + f * FUNCTION_WORDS));
      continue;
    }
    for block in 0..c.registry.blocks_per_function() {
      let index = f * c.registry.blocks_per_function() + block;
      let matched = eqc(b, &word(2), block as u64);
      let on = b.b.and(owner, matched);
      let on = b.b.and(on, live[index]);
      let at = blocks + index * c.block_words();
      if g.op == BodyOp::ReadBlock {
        choices.push((on, at));
        continue;
      }
      let (n, offset, stride, count) = if g.op == BodyOp::ReadOperand {
        (c.operands, HEADER_WORDS, c.operand_words(), OPERANDS)
      } else {
        (c.registry.constructors(), c.alternatives(), ALT_WORDS, ALTERNATIVES)
      };
      let cells = bank::canonical(b, at + offset, n, stride);
      for (i, present) in cells.iter().copied().enumerate() {
        let matched = eqc(b, &word(3), i as u64);
        let selected = b.b.and(on, matched);
        let selected = b.b.and(selected, present);
        let bounded = lt(b, &word(3), &word(at + count));
        b.require(selected, bounded);
        choices.push((selected, at + offset + i * stride));
      }
    }
  }
  let flags: Vec<_> = choices.iter().map(|(on, _)| *on).collect();
  let found = b.any(&flags);
  b.require(enabled, found);
  for i in 0..flags.len() {
    for j in i + 1..flags.len() {
      b.require_zero(flags[i], &[flags[j]]);
    }
  }
  for i in 0..g.output_count() - 1 {
    let sources: Vec<_> =
      choices.iter().map(|(on, at)| (*on, word(at + i))).collect();
    let result = select(b, &sources, 128);
    b.write(g.input_count() + i, &result);
  }
}
