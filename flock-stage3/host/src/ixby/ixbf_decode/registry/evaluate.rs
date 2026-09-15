//! Independent checked-integer witness preparation. Never used by a verifier
//! as an admission predicate or to authenticate a registry.
use super::{super::grammar, *};
use flock_prover::field::F128;

fn value(word: F128) -> u128 {
  u128::from(word.lo) | (u128::from(word.hi) << 64)
}
fn live(word: F128) -> bool {
  word.lo & 1 != 0
}
fn canonical(cap: RegistryCapacity, bank: &[F128]) -> bool {
  let mut bad = false;
  for cell in cap.cells() {
    let at = cell.offset;
    let present = live(bank[at]);
    bad |= value(bank[at]) > 1;
    if !present {
      bad |=
        bank[at + 1..at + cell.fields + 2].iter().any(|w| *w != F128::ZERO);
    }
    let span = bank[at + cell.fields + 1];
    bad |= present && span.lo >= span.hi;
    if cell.kind == RegistryOp::Function {
      let blocks = value(bank[at + 3]);
      bad |= present
        && (blocks == 0
          || blocks > cap.blocks as u128
          || value(bank[at + 2]) >= blocks);
    } else if cell.kind == RegistryOp::Block {
      bad |= value(bank[at + 2]) >= 8;
    }
  }
  bad
}

pub(super) fn evaluate(
  cap: RegistryCapacity,
  op: RegistryOp,
  input: &[F128],
) -> Vec<F128> {
  let mut bad = canonical(cap, &input[op.bank()..]);
  let mut out = match op {
    RegistryOp::Capture => capture(cap, input, &mut bad),
    RegistryOp::Finish => {
      finish(cap, input, &mut bad);
      Vec::new()
    },
    _ => read(cap, op, input, &mut bad),
  };
  out.push(F128::new(u64::from(bad), 0));
  out
}

fn capture(cap: RegistryCapacity, input: &[F128], bad: &mut bool) -> Vec<F128> {
  let v = |index| value(input[index]);
  let commit = live(input[COMMITTED]);
  let tag = v(TAG);
  *bad |= v(COMMITTED) > 1 || tag >= 18 || v(1) >> 40 != 0;
  *bad |= !matches!(tag, 15 | 17) && !commit;
  *bad |= tag == 17 && commit;
  let enables = [3, 4, 5].map(|i| commit && tag == i);
  let active = enables.iter().any(|flag| *flag);
  for (enabled, phase) in enables.into_iter().zip([
    grammar::Phase::Constructor,
    grammar::Phase::Function,
    grammar::Phase::Block,
  ]) {
    *bad |= enabled && input[1].lo as u8 != phase as u8;
  }
  let cursor = input[0];
  let next = input[NEXT];
  *bad |= active
    && (next.hi != cursor.hi || next.lo <= cursor.lo || next.lo > cursor.hi);
  let (ctor_index, overflow) =
    v(grammar::CTORS).overflowing_sub(v(grammar::CTORS_LEFT));
  *bad |= enables[0] && (overflow || v(grammar::CTORS_LEFT) == 0);
  let function_index = v(grammar::FUNCTION_INDEX);
  let (ordinal, overflow) =
    v(grammar::FUNCTIONS).overflowing_sub(v(grammar::FUNCTIONS_LEFT));
  *bad |= enables[1]
    && (overflow
      || v(grammar::FUNCTIONS_LEFT) == 0
      || ordinal != function_index);
  let (owner, overflow) = function_index.overflowing_sub(1);
  *bad |= enables[2] && overflow;
  let (block_index, overflow) =
    v(grammar::BLOCKS).overflowing_sub(v(grammar::BLOCKS_LEFT));
  *bad |= enables[2] && (overflow || v(grammar::BLOCKS_LEFT) == 0);
  *bad |= enables[1] && v(FIELDS + 2) > cap.blocks as u128;
  let bank = &input[CAPTURE_BANK..];
  let mut out = bank.to_vec();
  let mut inserted = false;
  for cell in cap.cells() {
    let selected = match cell.kind {
      RegistryOp::Constructor => enables[0] && ctor_index == cell.index as u128,
      RegistryOp::Function => {
        enables[1] && function_index == cell.index as u128
      },
      RegistryOp::Block => {
        enables[2]
          && owner == cell.owner as u128
          && block_index == cell.index as u128
      },
      _ => unreachable!(),
    };
    if !selected {
      continue;
    }
    inserted = true;
    let at = cell.offset;
    *bad |= bank[at] != F128::ZERO;
    if cell.index > 0 {
      let previous = at - cell.fields - 2;
      *bad |= !live(bank[previous])
        || bank[previous + cell.fields + 1].hi > cursor.lo;
    }
    if cell.kind == RegistryOp::Block {
      let parent = cap.function(cell.owner);
      *bad |= !live(bank[parent])
        || bank[parent + 3] != input[grammar::BLOCKS]
        || bank[parent + 1] != input[grammar::ARITY]
        || block_index >= value(bank[parent + 3])
        || bank[parent + 4].hi > cursor.lo;
    }
    *bad |=
      input[FIELDS + cell.fields..FIELDS + 13].iter().any(|w| *w != F128::ZERO);
    out[at] = F128::ONE;
    out[at + 1..at + cell.fields + 1]
      .copy_from_slice(&input[FIELDS..FIELDS + cell.fields]);
    out[at + cell.fields + 1] = F128::new(cursor.lo, next.lo);
  }
  *bad |= active && !inserted;
  out
}

fn finish(cap: RegistryCapacity, input: &[F128], bad: &mut bool) {
  let v = |index| value(input[index]);
  let bank = &input[FINISH_BANK..];
  *bad |= input[1].lo as u8 != grammar::Phase::Done as u8
    || v(1) >> 40 != 0
    || input[0].lo != input[0].hi;
  for index in [
    grammar::CTORS_LEFT,
    grammar::FUNCTIONS_LEFT,
    grammar::BLOCKS_LEFT,
    grammar::ITEMS,
    grammar::PAYLOAD,
    grammar::PENDING,
  ] {
    *bad |= input[index] != F128::ZERO;
  }
  *bad |= v(grammar::CTORS) > cap.constructors as u128
    || v(grammar::FUNCTIONS) == 0
    || v(grammar::FUNCTIONS) > cap.functions as u128
    || input[grammar::FUNCTION_INDEX] != input[grammar::FUNCTIONS]
    || v(grammar::ENTRY) >= v(grammar::FUNCTIONS);
  for cell in cap.cells() {
    let at = cell.offset;
    let present = live(bank[at]);
    let expected = match cell.kind {
      RegistryOp::Constructor => (cell.index as u128) < v(grammar::CTORS),
      RegistryOp::Function => (cell.index as u128) < v(grammar::FUNCTIONS),
      RegistryOp::Block => {
        live(bank[cap.function(cell.owner)])
          && (cell.index as u128) < value(bank[cap.function(cell.owner) + 3])
      },
      _ => unreachable!(),
    };
    *bad |= present != expected;
    *bad |= present && bank[at + cell.fields + 1].hi > input[0].hi;
    let bounded = if cell.kind == RegistryOp::Constructor {
      bank[at + 5]
    } else {
      bank[at + 1]
    };
    let limit = if cell.kind == RegistryOp::Block { 3 } else { 4 };
    *bad |= present && value(bounded) > v(grammar::LIMITS + limit);
    if cell.kind == RegistryOp::Function {
      *bad |= present && value(bounded) > v(grammar::LIMITS + 3);
      *bad |= present
        && v(grammar::ENTRY) == cell.index as u128
        && bank[at + 1] != input[grammar::ENTRY_ARITY];
      for index in 0..cap.blocks {
        if present && value(bank[at + 2]) == index as u128 {
          let block = cap.block(cell.index, index);
          *bad |= !live(bank[block]) || bank[at + 1] != bank[block + 1];
        }
      }
    }
  }
  for left in 0..cap.constructors {
    for right in left + 1..cap.constructors {
      let (first, second) = (left * 7, right * 7);
      *bad |= live(bank[first])
        && live(bank[second])
        && bank[first + 1..first + 5] == bank[second + 1..second + 5];
    }
  }
}

fn read(
  cap: RegistryCapacity,
  op: RegistryOp,
  input: &[F128],
  bad: &mut bool,
) -> Vec<F128> {
  let enabled = live(input[0]);
  *bad |= value(input[0]) > 1;
  *bad |= !enabled && (input[1] != F128::ZERO || input[2] != F128::ZERO);
  *bad |= op != RegistryOp::Block && input[2] != F128::ZERO;
  let bank = &input[READ_BANK..];
  let mut out = vec![F128::ZERO; 6];
  let mut found = false;
  for cell in cap.cells().into_iter().filter(|c| c.kind == op) {
    if enabled
      && value(input[1]) == cell.index as u128
      && value(input[2]) == cell.owner as u128
    {
      found = true;
      *bad |= !live(bank[cell.offset]);
      out[..cell.fields]
        .copy_from_slice(&bank[cell.offset + 1..cell.offset + cell.fields + 1]);
      out[5] = bank[cell.offset + cell.fields + 1];
    }
  }
  *bad |= enabled && !found;
  out
}
