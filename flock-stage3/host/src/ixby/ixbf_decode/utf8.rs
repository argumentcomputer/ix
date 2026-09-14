//! Streaming strict UTF-8 over original 32-byte source windows. The cursor
//! and all DFA state must be shared between rows; initial state is the actual
//! decoded narrow payload length, and final state must be verifier-pinned zero.
//! Source-window authentication is a separate required argument.

use super::synthesis::Builder;
use crate::{
  boolean::{BooleanR1csPlan, generate_boolean_witness_into},
  ixby::bits::{add, fill_words, or, subtract},
  sizing::{CircuitEmitter, CountedGate},
};
use anyhow::{Result, ensure};
use flock_prover::{
  circuit::builder::{GateType, SlotId, SlotWitness, Wire},
  field::F128,
  r1cs::BlockR1cs,
  schedule::{IoWord, TableType},
  union::SlotWitnessDest,
};
use std::sync::{Arc, OnceLock};

/// Inputs: cursor `(offset, file length)`, state `(remaining bytes, DFA)`,
/// narrow Boolean enable, and two original-source lookahead words. DFA 0 is
/// ground; 1/2/3 expect that many continuations; 4/5/6/7 expect the restricted
/// first continuation after E0/ED/F0/F4 respectively. Every active row consumes
/// exactly min(32, remaining). Bytes after the payload but before file EOF are
/// ignored, not padding. Disabled or empty rows require all lookahead zero.
/// Disabled rows preserve valid state; remaining zero requires ground state
/// even when disabled, so an unfinished character cannot be padded away.
#[derive(Clone, Debug)]
pub struct Utf8ChunkGate {
  pub(super) nu: usize,
  pub(super) plan: Arc<OnceLock<BooleanR1csPlan>>,
}

#[derive(Clone, Copy, Debug)]
pub struct Utf8ChunkRow(pub(super) [F128; 5]);

impl Utf8ChunkGate {
  pub fn new(nu: usize) -> Result<Self> {
    ensure!((3..=20).contains(&nu), "functional UTF-8 chunk row domain");
    Ok(Self { nu, plan: Arc::new(OnceLock::new()) })
  }
  pub(super) fn plan(&self) -> &BooleanR1csPlan {
    self.plan.get_or_init(build_plan)
  }
  pub fn r1cs(&self) -> BlockR1cs {
    self.plan().block_r1cs(self.nu)
  }
  pub fn generate_witness_into(
    &self,
    rows: &[Utf8ChunkRow],
    mut dst: SlotWitnessDest<'_>,
  ) -> Vec<u8> {
    dst.elide_padding_writes = false;
    generate_boolean_witness_into(
      self.plan(),
      rows,
      self.nu,
      dst,
      |row, bits| fill_words(&row.0, bits),
    )
  }
}

impl CountedGate for Utf8ChunkGate {
  fn input_count(&self) -> usize {
    5
  }
  fn output_count(&self) -> usize {
    3
  }
  fn table_at(&self, nu: usize) -> TableType {
    let mut gate = self.clone();
    gate.nu = nu;
    gate.table()
  }
}

impl GateType for Utf8ChunkGate {
  type Row = Utf8ChunkRow;
  type Hint = ();
  fn table(&self) -> TableType {
    crate::boolean::table_from_block_r1cs(self.r1cs()).with_io_schema(
      (0..5).map(IoWord::input).chain((5..8).map(IoWord::output)).collect(),
    )
  }
  fn eval(
    &self,
    inputs: &[F128],
    _: &(),
    outputs: &mut Vec<F128>,
  ) -> Self::Row {
    let input = inputs.try_into().expect("fixed UTF-8 chunk input width");
    outputs.extend(evaluate(&input));
    Utf8ChunkRow(input)
  }
  fn witness(&self, _: &[Self::Row], _: usize) -> SlotWitness {
    SlotWitness::DeferredToRows
  }
}

#[derive(Clone, Copy, Debug)]
pub struct Utf8ChunkWires {
  pub next: Wire,
  pub state: Wire,
}

#[derive(Clone, Copy, Debug)]
pub struct Utf8ChunkSlot {
  slot: SlotId,
  zero: Wire,
}

impl Utf8ChunkSlot {
  pub fn declare(b: &mut impl CircuitEmitter, gate: Utf8ChunkGate) -> Self {
    Self { slot: b.slot(gate), zero: b.fixed_public_input(F128::ZERO) }
  }
  pub fn slot(&self) -> SlotId {
    self.slot
  }
  pub fn check(
    &self,
    b: &mut impl CircuitEmitter,
    cursor: Wire,
    state: Wire,
    enabled: Wire,
    lookahead: [Wire; 2],
  ) -> Utf8ChunkWires {
    let output =
      b.gate(self.slot, &[cursor, state, enabled, lookahead[0], lookahead[1]]);
    b.connect(output[2], self.zero);
    Utf8ChunkWires { next: output[0], state: output[1] }
  }
}

// Independent integer witness computation, not a verifier admission predicate.
fn step(state: u64, byte: u8) -> Option<u64> {
  match (state, byte) {
    (0, 0x00..=0x7f) | (1, 0x80..=0xbf) => Some(0),
    (0, 0xc2..=0xdf)
    | (2, 0x80..=0xbf)
    | (4, 0xa0..=0xbf)
    | (5, 0x80..=0x9f) => Some(1),
    (0, 0xe1..=0xec | 0xee..=0xef)
    | (3, 0x80..=0xbf)
    | (6, 0x90..=0xbf)
    | (7, 0x80..=0x8f) => Some(2),
    (0, 0xf1..=0xf3) => Some(3),
    (0, 0xe0) => Some(4),
    (0, 0xed) => Some(5),
    (0, 0xf0) => Some(6),
    (0, 0xf4) => Some(7),
    _ => None,
  }
}

pub(super) fn evaluate(input: &[F128; 5]) -> [F128; 3] {
  let [cursor, state, enable, first, second] = *input;
  let enabled = enable.lo & 1 == 1;
  let consumed = if enabled { state.lo.min(32) } else { 0 };
  let mut dfa = state.hi & 7;
  let bytes: Vec<_> = [first, second]
    .iter()
    .flat_map(|word| {
      word.lo.to_le_bytes().into_iter().chain(word.hi.to_le_bytes())
    })
    .collect();
  let available = cursor.hi.saturating_sub(cursor.lo);
  let mut violation = cursor.lo > cursor.hi
    || state.lo > available
    || state.hi > 7
    || enable.hi != 0
    || enable.lo > 1;
  for (index, &byte) in bytes.iter().enumerate() {
    violation |=
      (!enabled || state.lo == 0 || index as u64 >= available) && byte != 0;
    if (index as u64) < consumed {
      match step(dfa, byte) {
        Some(next) => dfa = next,
        None => {
          dfa = 0;
          violation = true;
        },
      }
    }
  }
  let (next, carry) = cursor.lo.overflowing_add(consumed);
  let remaining = state.lo - consumed;
  violation |= carry || next > cursor.hi || (remaining == 0 && dfa != 0);
  [
    F128::new(next, cursor.hi),
    F128::new(remaining, dfa),
    F128::new(u64::from(violation), 0),
  ]
}

fn build_plan() -> BooleanR1csPlan {
  let mut b = Builder::new(5, 3, 1 << 14);
  let offset: Vec<_> = (0..64).collect();
  let file: Vec<_> = (64..128).collect();
  let remaining: Vec<_> = (128..192).collect();
  let mut state: Vec<_> = (192..195).collect();
  let enabled = 256;
  b.require_zero(b.one, &(195..256).collect::<Vec<_>>());
  b.require_zero(b.one, &(257..384).collect::<Vec<_>>());
  let (available, borrow) = subtract(&mut b.b, b.one, b.zero, &file, &offset);
  b.violations.push(borrow);
  let (_, borrow) = subtract(&mut b.b, b.one, b.zero, &available, &remaining);
  b.violations.push(borrow);
  let large = b.any(&remaining[5..]);
  let file_large = b.any(&available[5..]);
  let nonempty = b.any(&remaining);
  let active = b.b.and(enabled, nonempty);
  let no_bytes = b.not(active);
  b.require_zero(no_bytes, &(384..640).collect::<Vec<_>>());
  for index in 0..32 {
    let at = b.constant(5, index);
    let (_, small_live) =
      subtract(&mut b.b, b.one, b.zero, &at, &remaining[..5]);
    let within = or(&mut b.b, b.one, small_live, large);
    let live = b.b.and(enabled, within);
    let (_, file_small) =
      subtract(&mut b.b, b.one, b.zero, &at, &available[..5]);
    let file_live = or(&mut b.b, b.one, file_small, file_large);
    let file_padding = b.not(file_live);
    let byte: Vec<_> =
      (384 + index as usize * 8..392 + index as usize * 8).collect();
    b.require_zero(file_padding, &byte);
    let s: Vec<_> = (0..8).map(|value| b.eq_const(&state, value)).collect();
    let ascii = b.not(byte[7]);
    let cont = b.eq_const(&byte[6..], 2);
    let a0bf = b.eq_const(&byte[5..], 5);
    let b809f = b.eq_const(&byte[5..], 4);
    let b808f = b.eq_const(&byte[4..], 8);
    let not_808f = b.any(&byte[4..6]);
    let b90bf = b.b.and(cont, not_808f);
    let c0df = b.eq_const(&byte[5..], 6);
    let not_c0c1 = b.any(&byte[1..5]);
    let c2df = b.b.and(c0df, not_c0c1);
    let e0 = b.eq_const(&byte, 0xe0);
    let ed = b.eq_const(&byte, 0xed);
    let e_group = b.eq_const(&byte[4..], 0xe);
    let e_other = b.b.product_of_parities(&[e_group], &[e0, ed, b.one]);
    let f0 = b.eq_const(&byte, 0xf0);
    let f4 = b.eq_const(&byte, 0xf4);
    let f0f3 = b.eq_const(&byte[2..], 0x3c);
    let not_f0 = b.any(&byte[..2]);
    let f1f3 = b.b.and(f0f3, not_f0);
    let transitions: [&[(usize, usize)]; 8] = [
      &[(s[0], ascii), (s[1], cont)],
      &[(s[0], c2df), (s[2], cont), (s[4], a0bf), (s[5], b809f)],
      &[(s[0], e_other), (s[3], cont), (s[6], b90bf), (s[7], b808f)],
      &[(s[0], f1f3)],
      &[(s[0], e0)],
      &[(s[0], ed)],
      &[(s[0], f0)],
      &[(s[0], f4)],
    ];
    let mut next = Vec::with_capacity(8);
    for cases in transitions {
      let flags: Vec<_> = cases.iter().map(|&(a, c)| b.b.and(a, c)).collect();
      next.push(b.sum(&flags));
    }
    let valid = b.sum(&next);
    b.require(live, valid);
    let unused = b.not(live);
    state = (0..3)
      .map(|bit| {
        let flags: Vec<_> = next
          .iter()
          .enumerate()
          .filter_map(|(value, flag)| {
            (value & (1 << bit) != 0).then_some(*flag)
          })
          .collect();
        let value = b.sum(&flags);
        let new = b.b.and(live, value);
        let old = b.b.and(unused, state[bit]);
        b.sum(&[new, old])
      })
      .collect();
  }
  let small = b.not(large);
  let small_enabled = b.b.and(enabled, small);
  let mut consumed: Vec<_> =
    remaining[..5].iter().map(|&bit| b.b.and(small_enabled, bit)).collect();
  consumed.push(b.b.and(enabled, large));
  consumed.resize(64, b.zero);
  let (left, borrow) = subtract(&mut b.b, b.one, b.zero, &remaining, &consumed);
  b.violations.push(borrow);
  let (next, carry) = add(&mut b.b, b.one, b.zero, &offset, &consumed);
  b.violations.push(carry);
  let (_, borrow) = subtract(&mut b.b, b.one, b.zero, &file, &next);
  b.violations.push(borrow);
  let not_empty = b.any(&left);
  let empty = b.not(not_empty);
  b.require_zero(empty, &state);
  b.write(5, &[next, file].concat());
  b.write(6, &[left, state].concat());
  b.finish(7)
}
