use super::{
  super::{
    grammar::{self, Phase},
    synthesis::{Bits, Builder},
  },
  *,
};
use crate::{
  boolean::BooleanR1csPlan,
  ixby::bits::{add, subtract},
  sizing::CountedGate,
};

fn word(i: usize) -> Bits {
  (128 * i..128 * (i + 1)).collect()
}
fn eqc(b: &mut Builder, value: &[usize], constant: u64) -> usize {
  b.equal(value, &b.constant(value.len(), constant))
}
fn flag(b: &mut Builder, i: usize) -> usize {
  b.require_zero(b.one, &word(i)[1..]);
  word(i)[0]
}
fn same(b: &mut Builder, on: usize, x: &[usize], y: &[usize]) {
  let good = b.equal(x, y);
  b.require(on, good);
}
fn lt(b: &mut Builder, x: &[usize], y: &[usize]) -> usize {
  subtract(&mut b.b, b.one, b.zero, x, y).1
}
fn choose(b: &mut Builder, on: usize, yes: &[usize], no: &[usize]) -> Bits {
  yes
    .iter()
    .zip(no)
    .map(|(&y, &n)| {
      let delta = b.b.product_of_parities(&[on], &[y, n]);
      b.sum(&[n, delta])
    })
    .collect()
}
fn select(b: &mut Builder, choices: &[(usize, Bits)]) -> Bits {
  (0..128)
    .map(|i| {
      let terms: Vec<_> =
        choices.iter().map(|(on, v)| b.b.and(*on, v[i])).collect();
      b.sum(&terms)
    })
    .collect()
}
fn mask(b: &mut Builder, on: usize, value: &[usize]) -> Bits {
  value.iter().map(|bit| b.b.and(on, *bit)).collect()
}

pub(super) fn build(gate: &ReferenceGate) -> BooleanR1csPlan {
  let mut b = gate.builder();
  match gate.op {
    ReferenceOp::Request => request(&mut b, gate),
    ReferenceOp::Check => check(&mut b),
  }
  b.finish(gate.input_count() + gate.output_count() - 1)
}

fn request(b: &mut Builder, gate: &ReferenceGate) {
  let commit = flag(b, COMMITTED);
  let tags: Vec<_> = (0..18).map(|v| eqc(b, &word(TAG), v)).collect();
  let valid = b.any(&tags);
  b.require(b.one, valid);
  let may_not_commit = b.any(&[tags[15], tags[17]]);
  let must_commit = b.not(may_not_commit);
  b.require(must_commit, commit);
  b.require_zero(tags[17], &[commit]);
  b.require_zero(b.one, &word(1)[40..]);
  let phases: Vec<_> =
    (0..=Phase::Done as u64).map(|p| eqc(b, &word(1)[..8], p)).collect();
  let valid = b.any(&phases);
  b.require(b.one, valid);
  b.require_zero(b.one, &[phases[Phase::Value as usize]]);
  let active: Vec<_> = phases.iter().map(|p| b.b.and(commit, *p)).collect();
  let block = active[Phase::Block as usize];
  let op = active[Phase::Operation as usize];
  let tail_index = active[Phase::FunctionIndex as usize];
  let count = active[Phase::OperandCount as usize];
  let target = active[Phase::Target as usize];
  let alternative = active[Phase::Alternative as usize];
  for (on, tag) in [
    (block, 5),
    (op, 12),
    (tail_index, 2),
    (count, 1),
    (target, 2),
    (alternative, 6),
  ] {
    b.require(on, tags[tag]);
  }
  b.require_zero(b.one, &word(STATE)[3..]);
  b.require_zero(b.one, &word(STATE + 2)[gate.capacity.constructors()..]);
  b.require_zero(block, &word(FIELDS + 1)[3..]);
  let instructions: Vec<_> = (0..8).map(|i| eqc(b, &word(STATE), i)).collect();
  b.require(op, instructions[0]);
  b.require(tail_index, instructions[2]);
  let valid = b.any(&[
    instructions[0],
    instructions[2],
    instructions[3],
    instructions[4],
  ]);
  b.require(count, valid);
  b.require(alternative, instructions[5]);
  let valid = b.any(&[instructions[0], instructions[6], instructions[7]]);
  b.require(target, valid);
  let one_target = eqc(b, &word(1)[32..40], 1);
  let two_targets = eqc(b, &word(1)[32..40], 2);
  let valid = b.any(&[one_target, two_targets]);
  b.require(target, valid);
  let let_target = b.b.and(target, instructions[0]);
  b.require(let_target, one_target);
  let ops: Vec<_> = (0..8).map(|i| eqc(b, &word(FIELDS), i)).collect();
  let valid = b.any(&ops);
  b.require(op, valid);
  let construct = b.b.and(op, ops[2]);
  let closure = b.b.and(op, ops[4]);
  let call = b.b.and(op, ops[5]);
  let self_call = b.b.and(op, ops[6]);
  let tail_call = b.b.and(count, instructions[2]);
  let tail_self = b.b.and(count, instructions[3]);
  let function = b.any(&[closure, call, self_call, tail_call, tail_self]);
  let needs_owner = b.any(&[self_call, tail_self, target, alternative]);
  let one = b.constant(128, 1);
  let (owner, borrow) =
    subtract(&mut b.b, b.one, b.zero, &word(grammar::FUNCTION_INDEX), &one);
  b.require_zero(needs_owner, &[borrow]);
  let instruction = choose(b, block, &word(FIELDS + 1), &word(STATE));
  let not_block = b.not(block);
  let cleared = mask(b, not_block, &word(STATE + 1));
  let callee = choose(b, tail_index, &word(FIELDS), &cleared);
  let mut seen = word(STATE + 2);
  let mut selectors = Vec::new();
  for (i, bit) in seen.iter_mut().enumerate().take(gate.capacity.constructors())
  {
    let matches = eqc(b, &word(FIELDS), i as u64);
    let selected = b.b.and(alternative, matches);
    b.require_zero(selected, &[*bit]);
    selectors.push(selected);
    *bit = b.any(&[*bit, selected]);
  }
  let selected = b.any(&selectors);
  b.require(alternative, selected);
  let not_block = b.not(block);
  let seen = mask(b, not_block, &seen);
  for (i, value) in [instruction, callee, seen].iter().enumerate() {
    b.write(REQUEST_INPUTS + i, value);
  }
  let ctor = b.any(&[construct, alternative]);
  let block_read = b.any(&[target, alternative]);
  let explicit = b.any(&[closure, call]);
  let self_read = b.any(&[self_call, tail_self]);
  let arity_op = b.any(&[construct, closure, call, self_call]);
  let arity_count = b.any(&[tail_call, tail_self]);
  let nat = b.b.and(target, instructions[6]);
  let successor = b.b.and(nat, one_target);
  let add_one = b.any(&[let_target, successor]);
  let mut facts = vec![b.constant(128, 0); FACTS];
  for (i, bit) in [
    (CTOR_ENABLE, ctor),
    (FUNCTION_ENABLE, function),
    (BLOCK_ENABLE, block_read),
    (PARTIAL, closure),
    (CONSTRUCT, construct),
    (ADD_ONE, add_one),
    (ADD_CTOR, alternative),
  ] {
    facts[i][0] = bit;
  }
  facts[CTOR_INDEX] =
    select(b, &[(construct, word(FIELDS + 2)), (alternative, word(FIELDS))]);
  facts[FUNCTION_INDEX] = select(
    b,
    &[
      (explicit, word(FIELDS + 2)),
      (self_read, owner.clone()),
      (tail_call, word(STATE + 1)),
    ],
  );
  facts[BLOCK_OWNER] = mask(b, block_read, &owner);
  facts[BLOCK_INDEX] =
    select(b, &[(target, word(FIELDS)), (alternative, word(FIELDS + 1))]);
  facts[ARGUMENTS] =
    select(b, &[(arity_op, word(FIELDS + 3)), (arity_count, word(FIELDS))]);
  facts[LOCALS] = mask(b, block_read, &word(grammar::LOCALS));
  facts[LOCAL_LIMIT] = mask(b, block_read, &word(grammar::LIMITS + 3));
  for (i, value) in facts.iter().enumerate() {
    b.write(REQUEST_INPUTS + STATE_WORDS + i, value);
  }
}

fn check(b: &mut Builder) {
  let ctor = flag(b, CTOR_ENABLE);
  let function = flag(b, FUNCTION_ENABLE);
  let block = flag(b, BLOCK_ENABLE);
  let partial = flag(b, PARTIAL);
  let construct = flag(b, CONSTRUCT);
  let add_one = flag(b, ADD_ONE);
  let add_ctor = flag(b, ADD_CTOR);
  let expected_ctor = b.any(&[construct, add_ctor]);
  same(b, b.one, &[ctor], &[expected_ctor]);
  b.require_zero(construct, &[add_ctor, function]);
  b.require(partial, function);
  b.require(add_ctor, block);
  b.require(add_one, block);
  b.require_zero(add_one, &[add_ctor]);
  let arity = b.any(&[construct, function]);
  for (on, indices) in [
    (ctor, vec![CTOR_INDEX]),
    (function, vec![FUNCTION_INDEX, PARTIAL]),
    (
      block,
      vec![BLOCK_OWNER, BLOCK_INDEX, LOCALS, ADD_ONE, ADD_CTOR, LOCAL_LIMIT],
    ),
    (arity, vec![ARGUMENTS]),
  ] {
    let off = b.not(on);
    for index in indices {
      b.require_zero(off, &word(index));
    }
  }
  for (on, start) in [(ctor, CTOR), (function, FUNCTION), (block, BLOCK)] {
    let off = b.not(on);
    for i in start..start + 5 {
      b.require_zero(off, &word(i));
    }
  }
  for i in [FUNCTION + 3, FUNCTION + 4, BLOCK + 2, BLOCK + 3, BLOCK + 4] {
    b.require_zero(b.one, &word(i));
  }
  same(b, construct, &word(ARGUMENTS), &word(CTOR + 4));
  let not_partial = b.not(partial);
  let exact = b.b.and(function, not_partial);
  same(b, exact, &word(ARGUMENTS), &word(FUNCTION));
  let undersaturated = lt(b, &word(ARGUMENTS), &word(FUNCTION));
  b.require(partial, undersaturated);
  let extra =
    select(b, &[(add_one, b.constant(128, 1)), (add_ctor, word(CTOR + 4))]);
  let (sum, carry) = add(&mut b.b, b.one, b.zero, &word(LOCALS), &extra);
  b.require_zero(block, &[carry]);
  same(b, block, &sum, &word(BLOCK));
  let exceeds = lt(b, &word(LOCAL_LIMIT), &word(BLOCK));
  b.require_zero(block, &[exceeds]);
}
