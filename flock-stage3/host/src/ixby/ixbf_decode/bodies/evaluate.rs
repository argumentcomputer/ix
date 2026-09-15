//! Independent checked-integer witness preparation. Never a verifier oracle.
use super::{
  super::grammar::{self, Phase},
  *,
};
use flock_prover::field::F128;
fn v(w: F128) -> u128 {
  u128::from(w.lo) | (u128::from(w.hi) << 64)
}
fn w(v: u128) -> F128 {
  F128::new(v as u64, (v >> 64) as u64)
}
fn flag(w: F128) -> bool {
  w.lo & 1 != 0
}
fn canonical(input: &[F128], stride: usize, bad: &mut bool) -> Vec<bool> {
  input
    .chunks_exact(stride)
    .map(|r| {
      let live = flag(r[0]);
      *bad |= v(r[0]) > 1 || (!live && r[1..].iter().any(|w| *w != F128::ZERO));
      live
    })
    .collect()
}
fn sub(a: u128, b: u128, on: bool, bad: &mut bool) -> u128 {
  let (v, overflow) = a.overflowing_sub(b);
  *bad |= on && overflow;
  v
}
fn add(a: u128, b: u128, on: bool, bad: &mut bool) -> u128 {
  let (v, overflow) = a.overflowing_add(b);
  *bad |= on && overflow;
  v
}
pub(super) fn evaluate(
  c: BodyCapacity,
  op: BodyOp,
  input: &[F128],
) -> Vec<F128> {
  let mut bad = false;
  let mut out = match op {
    BodyOp::Step => step(c, input, &mut bad),
    BodyOp::Capture => capture(c, input, &mut bad),
    BodyOp::Finish => finish(c, input, &mut bad),
    _ => read(c, op, input, &mut bad),
  };
  out.push(w(u128::from(bad)));
  out
}
fn step(c: BodyCapacity, input: &[F128], bad: &mut bool) -> Vec<F128> {
  let s = c.state();
  let at = s + CONTROL_WORDS;
  let mut record = input[at..].to_vec();
  let opened = canonical(&record, c.block_words(), bad)[0];
  *bad |= !opened && input[s..at].iter().any(|w| *w != F128::ZERO);
  let commit = flag(input[COMMITTED]);
  let tag = v(input[TAG]);
  *bad |= v(input[COMMITTED]) > 1
    || tag >= 18
    || (!matches!(tag, 15 | 17) && !commit)
    || (tag == 17 && commit);
  *bad |= v(input[1]) >> 40 != 0 || v(input[NEXT_CONTROL]) >> 40 != 0;
  let phase = input[1].lo as u8;
  let p = |p: Phase| phase == p as u8;
  *bad |= phase > Phase::Done as u8 || p(Phase::Value);
  let expected =
    [13, 3, 1, 4, 5, 12, 10, 1, 2, 0, 2, 1, 6, 11, 14, 1, 15, 1, 16, 9, 17];
  if let Some(t) = expected.get(phase as usize) {
    *bad |= tag != *t;
  }
  let header = p(Phase::Start);
  let begin = p(Phase::Block);
  let body =
    (Phase::Operation as u8..=Phase::BytesPayload as u8).contains(&phase);
  *bad |= opened != body;
  let cursor = input[0];
  let next = input[NEXT];
  *bad |= cursor.lo > cursor.hi || cursor.lo > next.lo || next.lo > cursor.hi;
  *bad |=
    if header { next.hi != 0 || cursor.lo != 0 } else { next.hi != cursor.hi };
  *bad |= commit && cursor.lo >= next.lo;
  *bad |= p(Phase::Done) && cursor != next;
  let next_phase = input[NEXT_CONTROL].lo as u8;
  let next_body =
    (Phase::Operation as u8..=Phase::BytesPayload as u8).contains(&next_phase);
  let boundary = [Phase::Block, Phase::Function, Phase::Done]
    .iter()
    .any(|p| *p as u8 == next_phase);
  *bad |= (begin && !next_body) || (body && !(boundary || next_body));
  let closing = body && boundary && commit;
  let active = begin || body;
  let owner = sub(v(input[grammar::FUNCTION_INDEX]), 1, active, bad);
  let ordinal =
    sub(v(input[grammar::BLOCKS]), v(input[grammar::BLOCKS_LEFT]), active, bad);
  let previous = sub(ordinal, 1, body, bad);
  *bad |= body && (owner != v(input[s]) || previous != v(input[s + 1]));
  *bad |= active && owner >= c.registry.functions() as u128;
  let block_index = if begin { ordinal } else { v(input[s + 1]) };
  *bad |= active && block_index >= c.registry.blocks_per_function() as u128;
  *bad |= body && input[at + SPAN].hi != cursor.lo;
  if begin {
    record.fill(F128::ZERO);
    record[PRESENT] = F128::ONE;
    record[LOCALS] = input[FIELDS];
    record[INSTRUCTION] = input[FIELDS + 1];
    record[HEADER_END] = F128::new(next.lo, 0);
  }
  record[SPAN] = F128::new(
    if begin { cursor.lo } else { input[at + SPAN].lo },
    if active && commit { next.lo } else { input[at + SPAN].hi },
  );
  let ins = v(input[at + INSTRUCTION]);
  let old_op = v(input[at + OPERATION]);
  let op = v(input[FIELDS]);
  *bad |= body && ins >= 8;
  if p(Phase::Operation) {
    *bad |= ins != 0 || op >= 8;
    record[OPERATION] = input[FIELDS];
    if op == 1 {
      record[PRIMITIVE] = input[FIELDS + 1];
    }
    if matches!(op, 2 | 4 | 5) {
      record[REFERENCE] = input[FIELDS + 2];
    }
    if matches!(op, 1 | 2 | 4 | 5 | 6) {
      record[ARGUMENTS] = input[FIELDS + 3];
    }
  }
  if p(Phase::FunctionIndex) {
    *bad |= ins != 2;
    record[REFERENCE] = input[FIELDS];
  }
  if p(Phase::OperandCount) {
    *bad |= !((ins == 0 && old_op == 7) || matches!(ins, 2..=4));
    record[ARGUMENTS] = input[FIELDS];
  }
  if p(Phase::Projection) {
    *bad |= ins != 0 || old_op != 3;
    record[PROJECTION] = input[FIELDS];
  }
  if p(Phase::Target) {
    let left = (input[1].lo >> 32) as u8;
    *bad |= !matches!(ins, 0 | 6 | 7)
      || !matches!(left, 1 | 2)
      || (ins == 0 && left != 1);
    if ins == 0 || left == 2 {
      record[TARGET0] = input[FIELDS];
    }
    if ins != 0 && left == 1 {
      record[TARGET1] = input[FIELDS];
    }
  }
  if p(Phase::AlternativeCount) {
    *bad |= ins != 5 || op > c.registry.constructors() as u128;
    record[ALTERNATIVES] = input[FIELDS];
  }
  let alt = p(Phase::Alternative);
  let alt_index =
    sub(v(input[at + ALTERNATIVES]), v(input[grammar::ITEMS]), alt, bad);
  *bad |= alt
    && (ins != 5
      || input[grammar::ITEMS] == F128::ZERO
      || alt_index >= c.registry.constructors() as u128);
  if alt {
    for i in 0..c.registry.constructors() {
      if alt_index == i as u128 {
        let offset = c.alternatives() + i * ALT_WORDS;
        *bad |= input[at + offset] != F128::ZERO;
        record[offset..offset + 4].copy_from_slice(&[
          F128::ONE,
          input[FIELDS],
          input[FIELDS + 1],
          F128::new(cursor.lo, next.lo),
        ]);
      }
    }
  }
  let (scalar, emit, operand) = operand(c, input, bad);
  *bad |= emit && v(input[at + OPERANDS]) >= c.operands as u128;
  record[OPERANDS] = w(add(v(record[OPERANDS]), u128::from(emit), true, bad));
  for i in 0..c.operands {
    if emit && v(input[at + OPERANDS]) == i as u128 {
      let offset = HEADER_WORDS + i * c.operand_words();
      *bad |= input[at + offset] != F128::ZERO;
      record[offset..offset + c.operand_words()].copy_from_slice(&operand);
    }
  }
  *bad |= closing && scalar.iter().any(|w| *w != F128::ZERO);
  let owner = if begin { w(owner) } else { input[s] };
  let block_index = w(block_index);
  let mut out = vec![owner, block_index];
  out.extend(scalar);
  out.extend(&record);
  if closing {
    out.fill(F128::ZERO);
  }
  if closing {
    out.extend([owner, block_index]);
    out.extend(record);
  } else {
    out.extend(vec![F128::ZERO; 2 + c.block_words()]);
  }
  out
}
fn operand(
  c: BodyCapacity,
  input: &[F128],
  bad: &mut bool,
) -> (Vec<F128>, bool, Vec<F128>) {
  let s = c.state();
  let at = s + CONTROL_WORDS;
  let pending = flag(input[s + 2]);
  let cursor = input[0];
  let next = input[NEXT];
  let phase = input[1].lo as u8;
  let p = |p: Phase| phase == p as u8;
  let tag = v(input[FIELDS]);
  *bad |= v(input[s + 2]) > 1
    || input[s + 3].hi != 0
    || v(input[s + 4]) >= 8
    || (!pending && (input[s + 3] != F128::ZERO || input[s + 4] != F128::ZERO));
  *bad |= pending
    && (input[at + HEADER_END].lo > input[s + 3].lo
      || input[s + 3].lo > cursor.lo);
  *bad |= p(Phase::Operand) && (pending || tag >= 3);
  *bad |= p(Phase::Scalar) && (!pending || v(input[s + 4]) != 7 || tag >= 7);
  for (phase, tag) in [
    (Phase::Natural, 0),
    (Phase::StringCount, 1),
    (Phase::StringPayload, 1),
    (Phase::BytesCount, 6),
    (Phase::BytesPayload, 6),
  ] {
    *bad |= p(phase) && (!pending || v(input[s + 4]) != tag);
  }
  let local = p(Phase::Operand) && tag == 0;
  let erased = p(Phase::Operand) && tag == 2;
  let begin = p(Phase::Operand) && tag == 1;
  let direct = local || erased;
  let fixed = p(Phase::Scalar) && matches!(tag, 2..=5);
  let natural = p(Phase::Natural);
  let empty = (p(Phase::StringCount) || p(Phase::BytesCount)) && tag == 0;
  let payload = (p(Phase::StringPayload) && flag(input[COMMITTED]))
    || p(Phase::BytesPayload);
  let scalar_done = fixed || natural || empty || payload;
  let emit = direct || scalar_done;
  let mut state = input[s + 2..s + 5].to_vec();
  if begin {
    state = [F128::ONE, F128::new(cursor.lo, 0), w(7)].to_vec();
  }
  if p(Phase::Scalar) {
    state[2] = input[FIELDS];
  }
  if scalar_done {
    state.fill(F128::ZERO);
  }
  let mut record = vec![F128::ZERO; c.operand_words()];
  record[0] = w(u128::from(emit));
  if erased {
    record[O_KIND] = w(2);
  }
  if scalar_done {
    record[O_KIND] = F128::ONE;
  }
  if local {
    record[O_LOCAL] = input[FIELDS + 1];
  }
  if fixed {
    record[O_SCALAR] = input[FIELDS];
    record[O_FIXED] = input[FIELDS + 1];
  }
  if natural || empty || payload {
    record[O_SCALAR] = input[s + 4];
  }
  if emit {
    record[O_SPAN] =
      F128::new(if direct { cursor.lo } else { input[s + 3].lo }, next.lo);
  }
  if natural {
    record[O_MAGNITUDE..].copy_from_slice(&input[NAT..s]);
  }
  for (on, range, len) in [
    (natural, input[NAT_RANGE], v(input[FIELDS])),
    (payload, input[BYTE_RANGE], v(input[grammar::PAYLOAD])),
  ] {
    let (end, overflow) = range.lo.overflowing_add(range.hi);
    *bad |= on
      && (range.lo != cursor.lo
        || u128::from(range.hi) != len
        || overflow
        || end != next.lo);
  }
  record[O_PAYLOAD] = if natural {
    input[NAT_RANGE]
  } else if payload {
    input[BYTE_RANGE]
  } else if empty {
    F128::new(next.lo, 0)
  } else {
    F128::ZERO
  };
  (state, emit, record)
}
fn capture(c: BodyCapacity, input: &[F128], bad: &mut bool) -> Vec<F128> {
  let r = c.block_words();
  let packet = &input[2..2 + r];
  let live = canonical(packet, r, bad)[0];
  let bank = &input[2 + r..];
  let old = canonical(bank, r, bad);
  *bad |= !live && (input[0] != F128::ZERO || input[1] != F128::ZERO);
  let mut out = bank.to_vec();
  let mut found = false;
  for f in 0..c.registry.functions() {
    for block in 0..c.registry.blocks_per_function() {
      if live && v(input[0]) == f as u128 && v(input[1]) == block as u128 {
        found = true;
        let i = f * c.registry.blocks_per_function() + block;
        *bad |= old[i];
        if block > 0 {
          *bad |= !old[i - 1] || bank[(i - 1) * r + SPAN].hi != packet[SPAN].lo;
        }
        out[i * r..(i + 1) * r].copy_from_slice(packet);
      }
    }
  }
  *bad |= live && !found;
  out
}
fn finish(c: BodyCapacity, input: &[F128], bad: &mut bool) -> Vec<F128> {
  let r = c.block_words();
  let registry = 28 + c.state_words();
  let bank = registry + c.registry.words();
  *bad |= input[1].lo as u8 != Phase::Done as u8
    || v(input[1]) >> 40 != 0
    || input[0].lo != input[0].hi
    || input[28..registry].iter().any(|w| *w != F128::ZERO);
  for at in [
    grammar::CTORS_LEFT,
    grammar::FUNCTIONS_LEFT,
    grammar::BLOCKS_LEFT,
    grammar::ITEMS,
    grammar::PAYLOAD,
    grammar::PENDING,
  ] {
    *bad |= input[at] != F128::ZERO;
  }
  *bad |= v(input[grammar::FUNCTIONS]) > c.registry.functions() as u128
    || input[grammar::FUNCTIONS] == F128::ZERO;
  let live = canonical(&input[bank..], r, bad);
  let mut functions = Vec::new();
  let mut spans = Vec::new();
  let mut out = Vec::new();
  for f in 0..c.registry.functions() {
    let func = registry + c.registry.constructors() * 7 + f * 5;
    let present = canonical(&input[func..func + 5], 5, bad)[0];
    functions.push(present);
    *bad |= present != ((f as u128) < v(input[grammar::FUNCTIONS]));
    *bad |= present
      && (input[func + 3] == F128::ZERO
        || v(input[func + 3]) > c.registry.blocks_per_function() as u128);
    let mut end = 0;
    for block in 0..c.registry.blocks_per_function() {
      let i = f * c.registry.blocks_per_function() + block;
      let at = bank + i * r;
      let reg = registry + c.registry_block(f, block);
      let on = live[i];
      *bad |= on != (present && (block as u128) < v(input[func + 3]))
        || input[at] != input[reg];
      let span = input[at + SPAN];
      let header = input[reg + 3];
      *bad |= input[at + HEADER_END].hi != 0;
      *bad |= on
        && (input[at + LOCALS] != input[reg + 1]
          || input[at + INSTRUCTION] != input[reg + 2]
          || span.lo != header.lo
          || input[at + HEADER_END].lo != header.hi
          || header.lo >= header.hi
          || header.hi >= span.hi
          || span.hi > input[0].lo);
      let previous =
        if block == 0 { input[func + 4].hi } else { input[at - r + SPAN].hi };
      *bad |= on && span.lo != previous;
      if on && v(input[func + 3]) == (block + 1) as u128 {
        end ^= span.hi;
      }
      block_record(c, input, at, on, func, bad);
    }
    let span = F128::new(if present { input[func + 4].lo } else { 0 }, end);
    spans.push(span);
    out.extend(&input[func..func + 4]);
    out.push(span);
  }
  for f in 0..c.registry.functions() {
    let on = functions[f];
    let span = spans[f];
    *bad |= on && span.lo >= span.hi;
    if f > 0 {
      *bad |= on && span.lo != spans[f - 1].hi;
    }
    *bad |= on
      && (f + 1 == c.registry.functions() || !functions[f + 1])
      && span.hi != input[0].lo;
  }
  out.extend(&input[bank..]);
  out
}
fn block_record(
  c: BodyCapacity,
  input: &[F128],
  at: usize,
  on: bool,
  func: usize,
  bad: &mut bool,
) {
  let ins = v(input[at + INSTRUCTION]);
  let op = v(input[at + OPERATION]);
  let let_op = on && ins == 0;
  let i = |v| on && ins == v;
  let o = |v| let_op && op == v;
  *bad |= on && ins >= 8;
  *bad |= let_op && op >= 8;
  *bad |= !let_op && op != 0;
  let refs = i(2) || o(2) || o(4) || o(5);
  let args = i(2) || i(3) || i(4) || [1, 2, 4, 5, 6, 7].into_iter().any(o);
  let target0 = i(0) || i(6) || i(7);
  let target1 = i(6) || i(7);
  for (enabled, offset) in [
    (o(1), PRIMITIVE),
    (refs, REFERENCE),
    (o(3), PROJECTION),
    (args, ARGUMENTS),
    (target0, TARGET0),
    (target1, TARGET1),
    (i(5), ALTERNATIVES),
  ] {
    *bad |= !enabled && input[at + offset] != F128::ZERO;
  }
  *bad |= o(2) && v(input[at + REFERENCE]) >= v(input[grammar::CTORS]);
  *bad |= (i(2) || o(4) || o(5))
    && v(input[at + REFERENCE]) >= v(input[grammar::FUNCTIONS]);
  for (enabled, offset) in [(target0, TARGET0), (target1, TARGET1)] {
    *bad |= enabled && v(input[at + offset]) >= v(input[func + 3]);
  }
  if o(1) {
    let primitive = crate::ixby::ixbf::Primitive::ALL
      .into_iter()
      .find(|p| u128::from(p.opcode()) == v(input[at + PRIMITIVE]));
    *bad |=
      primitive.is_none_or(|p| v(input[at + ARGUMENTS]) != p.arity() as u128);
  }
  let one = i(1) || i(5) || i(6) || i(7) || o(0) || o(3);
  let counted = i(2) || i(3) || [1, 2, 4, 5, 6].into_iter().any(o);
  let apply = i(4) || o(7);
  let plus_one = add(v(input[at + ARGUMENTS]), 1, apply, bad);
  let expected = if one {
    1
  } else if counted {
    v(input[at + ARGUMENTS])
  } else if apply {
    plus_one
  } else {
    0
  };
  *bad |= on
    && (v(input[at + OPERANDS]) != expected
      || v(input[at + OPERANDS]) > c.operands as u128
      || v(input[at + ALTERNATIVES]) > c.registry.constructors() as u128);
  let operands = canonical(
    &input[at + HEADER_WORDS..at + c.alternatives()],
    c.operand_words(),
    bad,
  );
  for (i, present) in operands.iter().copied().enumerate() {
    *bad |= present != (on && (i as u128) < v(input[at + OPERANDS]));
    let operand = at + HEADER_WORDS + i * c.operand_words();
    let previous = if i == 0 {
      input[at + HEADER_END].lo
    } else {
      input[operand - c.operand_words() + O_SPAN].hi
    };
    *bad |= present && previous > input[operand + O_SPAN].lo;
    scalar_record(c, input, at, operand, present, bad);
  }
  let alts = canonical(
    &input[at + c.alternatives()..at + c.block_words()],
    ALT_WORDS,
    bad,
  );
  for (i, present) in alts.iter().copied().enumerate() {
    *bad |= present != (on && (i as u128) < v(input[at + ALTERNATIVES]));
    let alt = at + c.alternatives() + i * ALT_WORDS;
    let span = input[alt + 3];
    let previous = if i == 0 {
      input[at + HEADER_WORDS + O_SPAN].hi
    } else {
      input[alt - ALT_WORDS + 3].hi
    };
    *bad |= present
      && (span.lo >= span.hi
        || span.hi > input[at + SPAN].hi
        || previous > span.lo
        || v(input[alt + 1]) >= v(input[grammar::CTORS])
        || v(input[alt + 2]) >= v(input[func + 3]));
    for (j, prev) in alts.iter().copied().enumerate().take(i) {
      *bad |= present
        && prev
        && input[alt + 1] == input[at + c.alternatives() + j * ALT_WORDS + 1];
    }
  }
}
fn scalar_record(
  c: BodyCapacity,
  input: &[F128],
  block: usize,
  at: usize,
  on: bool,
  bad: &mut bool,
) {
  let kind = v(input[at + O_KIND]);
  let local = on && kind == 0;
  let scalar = on && kind == 1;
  let tag = v(input[at + O_SCALAR]);
  let span = input[at + O_SPAN];
  let payload = input[at + O_PAYLOAD];
  let fixed = input[at + O_FIXED];
  *bad |= on && kind >= 3;
  *bad |= !local && input[at + O_LOCAL] != F128::ZERO;
  *bad |= local && v(input[at + O_LOCAL]) >= v(input[block + LOCALS]);
  *bad |= !scalar && tag != 0;
  *bad |= on && (span.lo >= span.hi || span.hi > input[block + SPAN].hi);
  *bad |= scalar && tag >= 7;
  let has_payload = scalar && matches!(tag, 0 | 1 | 6);
  let nat = scalar && tag == 0;
  *bad |= !has_payload && payload != F128::ZERO;
  let (end, overflow) = payload.lo.overflowing_add(payload.hi);
  *bad |= has_payload && (span.lo >= payload.lo || overflow || end != span.hi);
  *bad |=
    nat && (payload.hi == 0 || payload.hi > c.natural.encoded_bytes() as u64);
  let has_fixed = scalar && matches!(tag, 2..=5);
  *bad |= !has_fixed && fixed != F128::ZERO;
  *bad |= scalar
    && match tag {
      2 => v(fixed) > 1,
      3 => v(fixed) > u32::MAX as u128,
      4 => fixed.hi != 0 || fixed.lo >= 0xffff_ffff_0000_0001,
      5 => {
        fixed.lo >= 0xffff_ffff_0000_0001 || fixed.hi >= 0xffff_ffff_0000_0001
      },
      _ => false,
    };
  for i in 0..c.natural.magnitude_words() {
    let limb = input[at + O_MAGNITUDE + i];
    *bad |= !nat && limb != F128::ZERO;
    let used = c.natural.bits().saturating_sub(i * 128).min(128);
    *bad |= used < 128 && v(limb) >> used != 0;
  }
}
fn read(
  c: BodyCapacity,
  op: BodyOp,
  input: &[F128],
  bad: &mut bool,
) -> Vec<F128> {
  let enabled = flag(input[0]);
  *bad |= v(input[0]) > 1
    || (!enabled && input[1..4].iter().any(|w| *w != F128::ZERO));
  *bad |= op == BodyOp::ReadFunction && input[2] != F128::ZERO;
  *bad |= matches!(op, BodyOp::ReadFunction | BodyOp::ReadBlock)
    && input[3] != F128::ZERO;
  let blocks = 4 + c.registry.functions() * FUNCTION_WORDS;
  let functions = canonical(&input[4..blocks], FUNCTION_WORDS, bad);
  let live = canonical(&input[blocks..], c.block_words(), bad);
  let mut choices = Vec::new();
  for (f, present) in functions.iter().copied().enumerate() {
    let owner = enabled && v(input[1]) == f as u128 && present;
    if op == BodyOp::ReadFunction {
      if owner {
        choices.push(4 + f * FUNCTION_WORDS);
      }
      continue;
    }
    for block in 0..c.registry.blocks_per_function() {
      let i = f * c.registry.blocks_per_function() + block;
      let on = owner && v(input[2]) == block as u128 && live[i];
      let at = blocks + i * c.block_words();
      if op == BodyOp::ReadBlock {
        if on {
          choices.push(at);
        }
        continue;
      }
      let (n, offset, stride, count) = if op == BodyOp::ReadOperand {
        (c.operands, HEADER_WORDS, c.operand_words(), OPERANDS)
      } else {
        (c.registry.constructors(), c.alternatives(), ALT_WORDS, ALTERNATIVES)
      };
      let cells =
        canonical(&input[at + offset..at + offset + n * stride], stride, bad);
      for (i, present) in cells.iter().copied().enumerate() {
        if on && v(input[3]) == i as u128 && present {
          *bad |= v(input[3]) >= v(input[at + count]);
          choices.push(at + offset + i * stride);
        }
      }
    }
  }
  *bad |= (enabled && choices.is_empty()) || choices.len() > 1;
  let width = match op {
    BodyOp::ReadFunction => FUNCTION_WORDS,
    BodyOp::ReadBlock => HEADER_WORDS,
    BodyOp::ReadOperand => c.operand_words(),
    _ => ALT_WORDS,
  };
  let mut out = vec![F128::ZERO; width];
  for at in choices {
    for (out, input) in out.iter_mut().zip(&input[at..at + width]) {
      out.lo ^= input.lo;
      out.hi ^= input.hi;
    }
  }
  out
}
