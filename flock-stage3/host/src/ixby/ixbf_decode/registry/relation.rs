use super::{
  super::{
    grammar,
    synthesis::{Bits, Builder},
  },
  *,
};
use crate::{
  boolean::BooleanR1csPlan, ixby::bits::subtract, sizing::CountedGate,
};

fn word(index: usize) -> Bits {
  (128 * index..128 * (index + 1)).collect()
}
fn eqc(b: &mut Builder, value: &[usize], constant: u64) -> usize {
  b.equal(value, &b.constant(value.len(), constant))
}
fn less(b: &mut Builder, left: &[usize], right: &[usize]) -> usize {
  subtract(&mut b.b, b.one, b.zero, left, right).1
}
fn le(b: &mut Builder, flag: usize, left: &[usize], right: &[usize]) {
  let wrong = less(b, right, left);
  b.require_zero(flag, &[wrong]);
}
fn same(b: &mut Builder, flag: usize, left: &[usize], right: &[usize]) {
  let good = b.equal(left, right);
  b.require(flag, good);
}
fn minus(
  b: &mut Builder,
  flag: usize,
  left: &[usize],
  right: &[usize],
) -> Bits {
  let (value, borrow) = subtract(&mut b.b, b.one, b.zero, left, right);
  b.require_zero(flag, &[borrow]);
  value
}
fn choose(b: &mut Builder, flag: usize, new: &[usize], old: &[usize]) -> Bits {
  new
    .iter()
    .zip(old)
    .map(|(&n, &o)| {
      let change = b.b.product_of_parities(&[flag], &[n, o]);
      b.b.xor(&[o, change], b.one)
    })
    .collect()
}

/// Presence is Boolean, absent cells are entirely zero, live header ranges
/// are nonempty, and narrow instruction tags never discard high bits.
fn canonical(b: &mut Builder, cap: RegistryCapacity, base: usize) {
  for cell in cap.cells() {
    let at = base + cell.offset;
    let live = word(at)[0];
    b.require_zero(b.one, &word(at)[1..]);
    let absent = b.not(live);
    for i in 1..cell.fields + 2 {
      b.require_zero(absent, &word(at + i));
    }
    let span = word(at + cell.fields + 1);
    let nonempty = less(b, &span[..64], &span[64..]);
    b.require(live, nonempty);
    if cell.kind == RegistryOp::Function {
      let blocks = word(at + 3);
      let nonempty = b.any(&blocks);
      b.require(live, nonempty);
      le(b, live, &blocks, &b.constant(128, cap.blocks as u64));
      let entry = less(b, &word(at + 2), &blocks);
      b.require(live, entry);
    } else if cell.kind == RegistryOp::Block {
      b.require_zero(b.one, &word(at + 2)[3..]);
    }
  }
}

pub(super) fn build(gate: &RegistryGate) -> BooleanR1csPlan {
  let mut b = gate.builder();
  canonical(&mut b, gate.capacity, gate.op.bank());
  match gate.op {
    RegistryOp::Capture => capture(&mut b, gate),
    RegistryOp::Finish => finish(&mut b, gate),
    _ => read(&mut b, gate),
  }
  b.finish(gate.input_count() + gate.output_count() - 1)
}

fn capture(b: &mut Builder, gate: &RegistryGate) {
  let cap = gate.capacity;
  let commit = word(COMMITTED)[0];
  b.require_zero(b.one, &word(COMMITTED)[1..]);
  let tags: Vec<_> = (0..18).map(|i| eqc(b, &word(TAG), i)).collect();
  let valid = b.any(&tags);
  b.require(b.one, valid);
  let may_not_commit = b.any(&[tags[15], tags[17]]);
  let must_commit = b.not(may_not_commit);
  b.require(must_commit, commit);
  b.require_zero(tags[17], &[commit]);
  let enables = [3usize, 4, 5].map(|tag| b.b.and(commit, tags[tag]));
  let active = b.any(&enables);
  for (enabled, phase) in enables.into_iter().zip([
    grammar::Phase::Constructor,
    grammar::Phase::Function,
    grammar::Phase::Block,
  ]) {
    let expected = eqc(b, &word(1)[..8], phase as u64);
    b.require(enabled, expected);
  }
  b.require_zero(b.one, &word(1)[40..]);
  let cursor = word(0);
  let next = word(NEXT);
  same(b, active, &next[64..], &cursor[64..]);
  let progress = less(b, &cursor[..64], &next[..64]);
  b.require(active, progress);
  le(b, active, &next[..64], &cursor[64..]);
  let span = [cursor[..64].to_vec(), next[..64].to_vec()].concat();

  let ctor_index =
    minus(b, enables[0], &word(grammar::CTORS), &word(grammar::CTORS_LEFT));
  let ctor_left = b.any(&word(grammar::CTORS_LEFT));
  b.require(enables[0], ctor_left);
  let function_index = word(grammar::FUNCTION_INDEX);
  let ordinal = minus(
    b,
    enables[1],
    &word(grammar::FUNCTIONS),
    &word(grammar::FUNCTIONS_LEFT),
  );
  same(b, enables[1], &function_index, &ordinal);
  let function_left = b.any(&word(grammar::FUNCTIONS_LEFT));
  b.require(enables[1], function_left);
  let owner = minus(b, enables[2], &function_index, &b.constant(128, 1));
  let block_index =
    minus(b, enables[2], &word(grammar::BLOCKS), &word(grammar::BLOCKS_LEFT));
  let block_left = b.any(&word(grammar::BLOCKS_LEFT));
  b.require(enables[2], block_left);
  le(b, enables[1], &word(FIELDS + 2), &b.constant(128, cap.blocks as u64));

  let mut selectors = Vec::new();
  for cell in cap.cells() {
    let (enabled, index) = match cell.kind {
      RegistryOp::Constructor => (enables[0], &ctor_index),
      RegistryOp::Function => (enables[1], &function_index),
      RegistryOp::Block => (enables[2], &block_index),
      _ => unreachable!(),
    };
    let index_matches = eqc(b, index, cell.index as u64);
    let mut selected = b.b.and(enabled, index_matches);
    if cell.kind == RegistryOp::Block {
      let owner_matches = eqc(b, &owner, cell.owner as u64);
      selected = b.b.and(selected, owner_matches);
    }
    selectors.push(selected);
    let at = CAPTURE_BANK + cell.offset;
    b.require_zero(selected, &word(at)); // immutable, write exactly once
    if cell.index > 0 {
      let previous = at - (cell.fields + 2);
      b.require(selected, word(previous)[0]);
      let previous_span = word(previous + cell.fields + 1);
      le(b, selected, &previous_span[64..], &cursor[..64]);
    }
    if cell.kind == RegistryOp::Block {
      let parent = CAPTURE_BANK + cap.function(cell.owner);
      b.require(selected, word(parent)[0]);
      same(b, selected, &word(parent + 3), &word(grammar::BLOCKS));
      same(b, selected, &word(parent + 1), &word(grammar::ARITY));
      let in_bounds = less(b, &block_index, &word(parent + 3));
      b.require(selected, in_bounds);
      let parent_span = word(parent + 4);
      le(b, selected, &parent_span[64..], &cursor[..64]);
    }
    for field in cell.fields..13 {
      b.require_zero(selected, &word(FIELDS + field));
    }
    for i in 0..cell.fields + 2 {
      let value = if i == 0 {
        b.constant(128, 1)
      } else if i == cell.fields + 1 {
        span.clone()
      } else {
        word(FIELDS + i - 1)
      };
      let out = choose(b, selected, &value, &word(at + i));
      b.write(gate.input_count() + cell.offset + i, &out);
    }
  }
  let inserted = b.any(&selectors);
  b.require(active, inserted);
}

fn finish(b: &mut Builder, gate: &RegistryGate) {
  let cap = gate.capacity;
  let done = eqc(b, &word(1)[..8], grammar::Phase::Done as u64);
  b.require(b.one, done);
  b.require_zero(b.one, &word(1)[40..]);
  same(b, b.one, &word(0)[..64], &word(0)[64..]);
  for index in [
    grammar::CTORS_LEFT,
    grammar::FUNCTIONS_LEFT,
    grammar::BLOCKS_LEFT,
    grammar::ITEMS,
    grammar::PAYLOAD,
    grammar::PENDING,
  ] {
    b.require_zero(b.one, &word(index));
  }
  le(
    b,
    b.one,
    &word(grammar::CTORS),
    &b.constant(128, cap.constructors as u64),
  );
  le(
    b,
    b.one,
    &word(grammar::FUNCTIONS),
    &b.constant(128, cap.functions as u64),
  );
  let nonempty = b.any(&word(grammar::FUNCTIONS));
  b.require(b.one, nonempty);
  same(b, b.one, &word(grammar::FUNCTION_INDEX), &word(grammar::FUNCTIONS));
  let entry = less(b, &word(grammar::ENTRY), &word(grammar::FUNCTIONS));
  b.require(b.one, entry);
  for cell in cap.cells() {
    let at = FINISH_BANK + cell.offset;
    let live = word(at)[0];
    let count = match cell.kind {
      RegistryOp::Constructor => word(grammar::CTORS),
      RegistryOp::Function => word(grammar::FUNCTIONS),
      RegistryOp::Block => word(FINISH_BANK + cap.function(cell.owner) + 3),
      _ => unreachable!(),
    };
    let mut expected = less(b, &b.constant(128, cell.index as u64), &count);
    if cell.kind == RegistryOp::Block {
      let parent_live = word(FINISH_BANK + cap.function(cell.owner))[0];
      expected = b.b.and(expected, parent_live);
    }
    same(b, b.one, &[live], &[expected]);
    let span = word(at + cell.fields + 1);
    le(b, live, &span[64..], &word(0)[64..]);
    let bounded = match cell.kind {
      RegistryOp::Constructor => word(at + 5),
      _ => word(at + 1),
    };
    let limit = if cell.kind == RegistryOp::Block { 3 } else { 4 };
    le(b, live, &bounded, &word(grammar::LIMITS + limit));
    if cell.kind == RegistryOp::Function {
      le(b, live, &bounded, &word(grammar::LIMITS + 3));
      let is_entry = eqc(b, &word(grammar::ENTRY), cell.index as u64);
      let is_entry = b.b.and(live, is_entry);
      same(b, is_entry, &word(at + 1), &word(grammar::ENTRY_ARITY));
      for index in 0..cap.blocks {
        let chosen = eqc(b, &word(at + 2), index as u64);
        let chosen = b.b.and(live, chosen);
        let block = FINISH_BANK + cap.block(cell.index, index);
        b.require(chosen, word(block)[0]);
        same(b, chosen, &word(at + 1), &word(block + 1));
      }
    }
  }
  for left in 0..cap.constructors {
    for right in left + 1..cap.constructors {
      let first = FINISH_BANK + left * 7;
      let second = FINISH_BANK + right * 7;
      let both = b.b.and(word(first)[0], word(second)[0]);
      let a: Bits = (1..=4).flat_map(|i| word(first + i)).collect();
      let z: Bits = (1..=4).flat_map(|i| word(second + i)).collect();
      let equal = b.equal(&a, &z);
      b.require_zero(both, &[equal]); // changing field count is not uniqueness
    }
  }
}

fn read(b: &mut Builder, gate: &RegistryGate) {
  let enabled = word(0)[0];
  b.require_zero(b.one, &word(0)[1..]);
  let disabled = b.not(enabled);
  b.require_zero(disabled, &word(1));
  b.require_zero(disabled, &word(2));
  if gate.op != RegistryOp::Block {
    b.require_zero(b.one, &word(2));
  }
  let mut selected = Vec::new();
  for cell in gate.capacity.cells().into_iter().filter(|c| c.kind == gate.op) {
    let index = eqc(b, &word(1), cell.index as u64);
    let owner = eqc(b, &word(2), cell.owner as u64);
    let both = b.b.and(index, owner);
    let flag = b.b.and(enabled, both);
    b.require(flag, word(READ_BANK + cell.offset)[0]);
    selected.push((flag, cell));
  }
  let found =
    b.any(&selected.iter().map(|(flag, _)| *flag).collect::<Vec<_>>());
  b.require(enabled, found);
  for field in 0..6 {
    let mut out = Vec::with_capacity(128);
    for bit in 0..128 {
      let mut terms = Vec::new();
      for &(flag, cell) in &selected {
        let source = if field == 5 {
          Some(cell.offset + cell.fields + 1)
        } else if field < cell.fields {
          Some(cell.offset + field + 1)
        } else {
          None
        };
        if let Some(source) = source {
          terms.push(b.b.and(flag, word(READ_BANK + source)[bit]));
        }
      }
      out.push(b.sum(&terms));
    }
    b.write(gate.input_count() + field, &out);
  }
}
