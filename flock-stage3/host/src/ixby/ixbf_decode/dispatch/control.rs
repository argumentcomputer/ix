use super::super::{GrammarKind, grammar::*, source::choose_bits};
use super::*;
use crate::{
  boolean::BooleanR1csPlan,
  ixby::bits::{add, subtract},
};
use flock_prover::field::F128;

fn integer(word: F128) -> u128 {
  u128::from(word.lo) | (u128::from(word.hi) << 64)
}
fn packed(value: u128) -> F128 {
  F128::new(value as u64, (value >> 64) as u64)
}

pub(super) fn initialize(config: DispatchConfig, input: &[F128]) -> Vec<F128> {
  let mut out = vec![F128::ZERO; DISPATCH_STATE_WORDS + 1];
  out[0] = F128::new(0, input[0].lo);
  for (index, &at) in DISPATCH_CONTEXT_INDICES.iter().enumerate() {
    out[at] = input[index + 1];
  }
  let bad = input[0].hi != 0
    || (config.kind == GrammarKind::Program
      && input[1..].iter().any(|v| *v != F128::ZERO));
  out[DISPATCH_STATE_WORDS] = F128::new(u64::from(bad), 0);
  out
}
pub(super) fn initialize_plan(g: &DispatchGate) -> BooleanR1csPlan {
  let mut b = g.builder(1 << 13);
  b.require_zero(b.one, &word(0)[64..]);
  if g.config.kind == GrammarKind::Program {
    b.require_zero(b.one, &(128..16 * 128).collect::<Bits>());
  }
  for at in 0..DISPATCH_STATE_WORDS {
    let bits = if at == 0 {
      [b.constant(64, 0), word(0)[..64].to_vec()].concat()
    } else if let Some(index) =
      DISPATCH_CONTEXT_INDICES.iter().position(|i| *i == at)
    {
      word(1 + index)
    } else {
      b.constant(128, 0)
    };
    b.write(16 + at, &bits);
  }
  b.finish(16 + DISPATCH_STATE_WORDS)
}

fn phase_tag(kind: GrammarKind, phase: u8) -> u64 {
  match phase {
    0 => match kind {
      GrammarKind::Program => 13,
      GrammarKind::Input => 7,
      GrammarKind::Output => 8,
    },
    1 => 3,
    2 | 7 | 11 | 15 | 17 => 1,
    3 => 4,
    4 => 5,
    5 => 12,
    6 => 10,
    8 | 10 => 2,
    9 => 0,
    12 => 6,
    13 => 11,
    14 => 14,
    16 => 15,
    18 => 16,
    19 => 9,
    20 => 17,
    _ => 0,
  }
}

/// [tag, bounds[3], read cursor, read take, file length, UTF-8 state,
/// whole payload length, residual]. All selectors derive from the state.
pub(super) fn request(config: DispatchConfig, input: &[F128]) -> Vec<F128> {
  let phase = input[1].lo as u8;
  let tag = phase_tag(config.kind, phase);
  let s: Vec<_> = input.iter().copied().map(integer).collect();
  let (seen, carry) = s[SEEN].overflowing_add(1);
  let (remaining, borrow) = s[LIMITS + 6].overflowing_sub(seen);
  let bounds = match phase {
    0 => match config.kind {
      GrammarKind::Program => [u128::from(input[0].hi), 0, 0],
      GrammarKind::Input => [s[LIMITS + 4], s[ENTRY_ARITY], s[LIMITS + 6]],
      GrammarKind::Output => [s[LIMITS + 6], 0, 0],
    },
    1 | 7 => [s[LIMITS + 4], 0, 0],
    2 => [s[LIMITS], 0, 0],
    3 => [s[LIMITS + 4], s[LIMITS + 3], s[LIMITS + 2]],
    4 => [s[LIMITS + 3], 0, 0],
    5 => [s[LIMITS + 4], s[CTORS], s[FUNCTIONS]],
    6 => [s[LOCALS], 0, 0],
    8 => [s[BLOCKS], 0, 0],
    10 => [s[FUNCTIONS], 0, 0],
    11 => [s[LIMITS + 1], 0, 0],
    12 => [s[CTORS], s[BLOCKS], 0],
    15 => [s[LIMITS + 8], 0, 0],
    17 => [s[LIMITS + 9], 0, 0],
    19 => [s[LIMITS + 4], s[FUNCTIONS], remaining],
    _ => [0; 3],
  };
  let string = phase == Phase::StringPayload as u8;
  let payload = string || phase == Phase::BytesPayload as u8;
  let stream = input[29] != F128::ZERO;
  let cursor = if stream { input[28] } else { input[0] };
  let bad = phase > 20
    || input[1].hi != 0
    || input[1].lo >> 40 != 0
    || (config.kind == GrammarKind::Program && phase == 19)
    || (config.kind != GrammarKind::Program && (1..=12).contains(&phase))
    || input[0].lo > input[0].hi
    || cursor.lo > cursor.hi
    || (stream
      && (!string
        || input[29].lo == 0
        || input[28].hi != input[0].hi
        || input[28].lo <= input[0].lo))
    || (!stream && input[28] != F128::ZERO)
    || (payload && input[PAYLOAD].hi != 0)
    || (phase == 19 && (carry || borrow));
  let take = match phase {
    0 if config.kind == GrammarKind::Program => {
      super::super::HEADER_PREFIX_BYTES
    },
    14 => config.natural.encoded_words() * 16,
    16 => 32,
    18 | 20 => 0,
    0..=19 => super::super::RECORD_LOOKAHEAD_BYTES,
    _ => 0,
  };
  let mut out = vec![F128::new(tag, 0)];
  out.extend(bounds.map(packed));
  out.extend([
    cursor,
    F128::new(take as u64, 0),
    F128::new(input[0].hi, 0),
    if string {
      if stream { input[29] } else { input[PAYLOAD] }
    } else {
      F128::ZERO
    },
    if payload { input[PAYLOAD] } else { F128::ZERO },
    F128::new(u64::from(bad), 0),
  ]);
  out
}

pub(super) fn request_plan(g: &DispatchGate) -> BooleanR1csPlan {
  let mut b = g.builder(1 << 15);
  let phases: Bits = (0..=20).map(|p| b.eq_const(&word(1)[..8], p)).collect();
  let valid = b.any(&phases);
  b.require(b.one, valid);
  b.require_zero(b.one, &word(1)[40..]);
  if g.config.kind == GrammarKind::Program {
    b.violations.push(phases[19]);
  } else {
    b.violations.extend_from_slice(&phases[1..13]);
  }
  let one = b.constant(128, 1);
  let (seen, carry) = add(&mut b.b, b.one, b.zero, &word(SEEN), &one);
  let (remaining, borrow) =
    subtract(&mut b.b, b.one, b.zero, &word(LIMITS + 6), &seen);
  b.violations.push(b.b.and(phases[19], carry));
  b.violations.push(b.b.and(phases[19], borrow));
  let mut length = word(0)[64..].to_vec();
  length.resize(128, b.zero);
  let mut tag_choices = Vec::new();
  let mut bound_choices = [Vec::new(), Vec::new(), Vec::new()];
  let mut take_choices = Vec::new();
  for (phase, &flag) in phases.iter().enumerate() {
    tag_choices
      .push((flag, b.constant(128, phase_tag(g.config.kind, phase as u8))));
    let z = b.constant(128, 0);
    let bounds = match phase {
      0 => match g.config.kind {
        GrammarKind::Program => [length.clone(), z.clone(), z.clone()],
        GrammarKind::Input => {
          [word(LIMITS + 4), word(ENTRY_ARITY), word(LIMITS + 6)]
        },
        GrammarKind::Output => [word(LIMITS + 6), z.clone(), z.clone()],
      },
      1 | 7 => [word(LIMITS + 4), z.clone(), z.clone()],
      2 => [word(LIMITS), z.clone(), z.clone()],
      3 => [word(LIMITS + 4), word(LIMITS + 3), word(LIMITS + 2)],
      4 => [word(LIMITS + 3), z.clone(), z.clone()],
      5 => [word(LIMITS + 4), word(CTORS), word(FUNCTIONS)],
      6 => [word(LOCALS), z.clone(), z.clone()],
      8 => [word(BLOCKS), z.clone(), z.clone()],
      10 => [word(FUNCTIONS), z.clone(), z.clone()],
      11 => [word(LIMITS + 1), z.clone(), z.clone()],
      12 => [word(CTORS), word(BLOCKS), z.clone()],
      15 => [word(LIMITS + 8), z.clone(), z.clone()],
      17 => [word(LIMITS + 9), z.clone(), z.clone()],
      19 => [word(LIMITS + 4), word(FUNCTIONS), remaining.clone()],
      _ => [z.clone(), z.clone(), z],
    };
    for (index, bits) in bounds.into_iter().enumerate() {
      bound_choices[index].push((flag, bits));
    }
    let take = match phase {
      0 if g.config.kind == GrammarKind::Program => {
        super::super::HEADER_PREFIX_BYTES
      },
      14 => g.config.natural.encoded_words() * 16,
      16 => 32,
      18 | 20 => 0,
      _ => super::super::RECORD_LOOKAHEAD_BYTES,
    };
    take_choices.push((flag, b.constant(128, take as u64)));
  }
  let tag = select(&mut b, &tag_choices, 128);
  b.write(30, &tag);
  for (index, choices) in bound_choices.iter().enumerate() {
    let bits = select(&mut b, choices, 128);
    b.write(31 + index, &bits);
  }
  let stream = b.any(&word(29));
  let idle = b.not(stream);
  b.require(stream, phases[16]);
  let left = b.any(&word(29)[..64]);
  b.require(stream, left);
  b.require_zero(idle, &word(28));
  let same = b.equal(&word(28)[64..], &word(0)[64..]);
  b.require(stream, same);
  let (_, progressed) =
    subtract(&mut b.b, b.one, b.zero, &word(0)[..64], &word(28)[..64]);
  b.require(stream, progressed);
  let cursor = choose_bits(&mut b, stream, &word(28), &word(0));
  for cur in [&word(0), &cursor] {
    let (_, bad) = subtract(&mut b.b, b.one, b.zero, &cur[64..], &cur[..64]);
    b.violations.push(bad);
  }
  b.write(34, &cursor);
  let take = select(&mut b, &take_choices, 128);
  b.write(35, &take);
  b.write(36, &length);
  let utf8 = choose_bits(&mut b, stream, &word(29), &word(PAYLOAD));
  let utf8 = masked(&mut b, phases[16], &utf8);
  b.write(37, &utf8);
  let payload = b.sum(&[phases[16], phases[18]]);
  b.require_zero(payload, &word(PAYLOAD)[64..]);
  let len = masked(&mut b, payload, &word(PAYLOAD));
  b.write(38, &len);
  b.finish(39)
}

/// old state[30], grammar result[28], UTF-8 next/state, payload next, tag.
pub(super) fn finish(input: &[F128]) -> Vec<F128> {
  let tag = input[61].lo as u8;
  let string = tag == 15;
  let more = string && input[59].lo != 0;
  let mut out =
    if more { input[..28].to_vec() } else { input[30..58].to_vec() };
  out.extend(if more { [input[58], input[59]] } else { [F128::ZERO; 2] });
  out.push(F128::new(u64::from(!more && tag != 17), 0));
  let bad = input[61].hi != 0
    || input[61].lo > 17
    || (string && !more && (input[59] != F128::ZERO || input[58] != input[60]));
  out.push(F128::new(u64::from(bad), 0));
  out
}
pub(super) fn finish_plan(g: &DispatchGate) -> BooleanR1csPlan {
  let mut b = g.builder(1 << 15);
  let tag = tags(&mut b, 61);
  let left = b.any(&word(59)[..64]);
  let more = b.b.and(tag[15], left);
  let complete = b.not(more);
  let last_string = b.b.and(tag[15], complete);
  b.require_zero(last_string, &word(59));
  let same = b.equal(&word(58), &word(60));
  b.require(last_string, same);
  for at in 0..28 {
    let bits = choose_bits(&mut b, more, &word(at), &word(30 + at));
    b.write(62 + at, &bits);
  }
  for at in 0..2 {
    let bits = masked(&mut b, more, &word(58 + at));
    b.write(90 + at, &bits);
  }
  let not_done = b.not(tag[17]);
  let commit = b.b.and(complete, not_done);
  b.write(92, &[commit]);
  b.finish(93)
}
