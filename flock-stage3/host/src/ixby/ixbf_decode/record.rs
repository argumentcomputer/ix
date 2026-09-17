//! Original-wire body and transport records. These are local parser relations,
//! not a whole-image parser or an authenticated registry. The caller must wire
//! the selected record kind, source cursor/window, limits and registry facts
//! into the surrounding grammar, original-byte authentication and consumers.

use super::synthesis::{Bits, Builder};
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

pub const RECORD_LOOKAHEAD_WORDS: usize = 6;
pub const RECORD_LOOKAHEAD_BYTES: usize = 16 * RECORD_LOOKAHEAD_WORDS;
pub const RECORD_INPUTS: usize = 5 + RECORD_LOOKAHEAD_WORDS;
pub const RECORD_FIELDS: usize = 6;
const OUTPUTS: usize = RECORD_FIELDS + 2;
const SOURCE: usize = 5 * 128;

/// The kind is setup-owned, not a proof-header instruction to the verifier.
/// Bounds below are exact u128 words; every unused bound must be zero.
/// All integers in these records have an explicit 128-bit codec capacity.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum RecordKind {
  /// One natural. No semantic bound; e.g. a projection's field number.
  Metadata,
  /// One vector count <= bounds[0] and <= remaining file bytes.
  Count,
  /// One index strictly below bounds[0].
  Index,
  /// block[32], member, tag, fields; fields <= bounds[0] (operand limit).
  Constructor,
  /// arity, entry, blocks; bounds = [operands, locals, blocks].
  Function,
  /// locals and instruction tag; bounds[0] = local-frame limit.
  Block,
  /// constructor and target indices; bounds = [constructor count, blocks, 0].
  Alternative,
  /// IXFI header at offset zero; bounds = [operands, entry arity, input nodes].
  Input,
  /// IXFO header at offset zero, implicit one root; bounds = [input nodes, 0, 0].
  Output,
  /// Value prefix; bounds = [operands, function count, remaining child budget].
  /// Constructor/PAP child arity and the provenance of the budget are separate.
  Value,
  /// Operand tag and a local index when present; bounds = [locals, 0, 0].
  /// A literal leaves its scalar at the returned cursor.
  Operand,
  /// Scalar tag and fixed-size payload. Variable Nat/String/ByteArray payloads
  /// start at the returned cursor and still need their dedicated decoders.
  Scalar,
  /// Operation prefix and any leading primitive/index/argument count;
  /// bounds = [operands, constructors, functions]. Operand bodies, post-operand
  /// projection fields and callee arity are separate parser obligations.
  Operation,
}

impl RecordKind {
  pub const ALL: [Self; 13] = [
    Self::Metadata,
    Self::Count,
    Self::Index,
    Self::Constructor,
    Self::Function,
    Self::Block,
    Self::Alternative,
    Self::Input,
    Self::Output,
    Self::Value,
    Self::Operand,
    Self::Scalar,
    Self::Operation,
  ];
}

/// Inputs: cursor `(offset, file length)` in u64 lanes, enable (0 or 1),
/// three u128 bounds, and six original-source lookahead words. Disabled rows
/// preserve the cursor, require zero lookahead, and return zero fields. The
/// cursor is always in bounds. Only bytes after EOF are padding on active rows.
#[derive(Clone, Debug)]
pub struct RecordDecodeGate {
  pub(super) nu: usize,
  pub(super) kind: RecordKind,
  pub(super) plan: Arc<OnceLock<BooleanR1csPlan>>,
}

#[derive(Clone, Debug)]
pub struct RecordDecodeRow(pub(super) [F128; RECORD_INPUTS]);

impl RecordDecodeGate {
  pub fn new(nu: usize, kind: RecordKind) -> Result<Self> {
    ensure!((3..=20).contains(&nu), "functional record row domain");
    Ok(Self { nu, kind, plan: Arc::new(OnceLock::new()) })
  }
  pub fn kind(&self) -> RecordKind {
    self.kind
  }
  pub(super) fn plan(&self) -> &BooleanR1csPlan {
    self.plan.get_or_init(|| build_plan(self.kind))
  }
  pub fn r1cs(&self) -> BlockR1cs {
    self.plan().block_r1cs(self.nu)
  }
  pub fn generate_witness_into(
    &self,
    rows: &[RecordDecodeRow],
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

impl CountedGate for RecordDecodeGate {
  fn input_count(&self) -> usize {
    RECORD_INPUTS
  }
  fn output_count(&self) -> usize {
    OUTPUTS
  }
  fn table_at(&self, nu: usize) -> TableType {
    let mut gate = self.clone();
    gate.nu = nu;
    gate.table()
  }
}

impl GateType for RecordDecodeGate {
  type Row = RecordDecodeRow;
  type Hint = ();
  fn table(&self) -> TableType {
    crate::boolean::table_from_block_r1cs(self.r1cs()).with_io_schema(
      (0..RECORD_INPUTS)
        .map(IoWord::input)
        .chain((RECORD_INPUTS..RECORD_INPUTS + OUTPUTS).map(IoWord::output))
        .collect(),
    )
  }
  fn eval(&self, input: &[F128], _: &(), output: &mut Vec<F128>) -> Self::Row {
    let input = input.try_into().expect("fixed record input width");
    output.extend(evaluate(self.kind, input));
    RecordDecodeRow(*input)
  }
  fn witness(&self, _: &[Self::Row], _: usize) -> SlotWitness {
    SlotWitness::DeferredToRows
  }
}

#[derive(Clone, Copy, Debug)]
pub struct RecordWires {
  /// Metadata/Count/Index: [value]; Constructor: [block0, block1, member, tag,
  /// fields]; Function: [arity, entry, blocks]; Block: [locals, instruction];
  /// Alternative: [constructor, target]; Input/Output: [roots];
  /// Value: [kind, block0-or-function, block1, member, tag, children];
  /// Operand: [kind, local]; Scalar: [kind, fixed payload];
  /// Operation: [kind, primitive, target, count, primitive arity].
  /// Unlisted fields and padding within narrow fields are zero. Disabled
  /// rows produce zero in every field.
  pub fields: [Wire; RECORD_FIELDS],
  /// `(next offset, unchanged file length)` in exact u64 lanes.
  pub next: Wire,
}

#[derive(Clone, Copy, Debug)]
pub struct RecordDecodeSlot {
  slot: SlotId,
  zero: Wire,
}

impl RecordDecodeSlot {
  pub fn declare(b: &mut impl CircuitEmitter, gate: RecordDecodeGate) -> Self {
    Self { slot: b.slot(gate), zero: b.fixed_public_input(F128::ZERO) }
  }
  pub fn slot(&self) -> SlotId {
    self.slot
  }
  pub fn decode(
    &self,
    b: &mut impl CircuitEmitter,
    cursor: Wire,
    enabled: Wire,
    bounds: [Wire; 3],
    lookahead: [Wire; RECORD_LOOKAHEAD_WORDS],
  ) -> RecordWires {
    let mut input = vec![cursor, enabled];
    input.extend(bounds);
    input.extend(lookahead);
    let output = b.gate(self.slot, &input);
    b.connect(output[OUTPUTS - 1], self.zero);
    RecordWires {
      fields: output[..RECORD_FIELDS].try_into().unwrap(),
      next: output[RECORD_FIELDS],
    }
  }
}

struct Reader {
  b: Builder,
  cursor: Bits,
  remaining: Bits,
}

impl Reader {
  fn new(kind: RecordKind) -> Self {
    let columns = match kind {
      RecordKind::Metadata
      | RecordKind::Count
      | RecordKind::Index
      | RecordKind::Block
      | RecordKind::Output
      | RecordKind::Operand => 1 << 14,
      RecordKind::Value => 1 << 16,
      _ => 1 << 15,
    };
    let mut b = Builder::new(RECORD_INPUTS, OUTPUTS, columns);
    b.violations.extend(129..256);
    let offset: Vec<_> = (0..64).collect();
    let length: Vec<_> = (64..128).collect();
    let (remaining, borrow) =
      subtract(&mut b.b, b.one, b.zero, &length, &offset);
    b.violations.push(borrow);
    let large = b.any(&remaining[7..]);
    let disabled = b.not(128);
    for byte in 0..RECORD_LOOKAHEAD_BYTES {
      let at = b.constant(7, byte as u64);
      let (_, within) = subtract(&mut b.b, b.one, b.zero, &at, &remaining[..7]);
      let live = or(&mut b.b, b.one, within, large);
      let outside = b.not(live);
      let padding = or(&mut b.b, b.one, outside, disabled);
      b.require_zero(
        padding,
        &(SOURCE + byte * 8..SOURCE + (byte + 1) * 8).collect::<Vec<_>>(),
      );
    }
    let cursor = b.constant(64, 0);
    Self { b, cursor, remaining }
  }
  fn bound(&self, index: usize) -> Bits {
    (256 + index * 128..384 + index * 128).collect()
  }
  fn unused(&mut self, from: usize) {
    for index in from..3 {
      self.b.require_zero(self.b.one, &self.bound(index));
    }
  }
  fn window(&mut self, bytes: usize) -> Bits {
    let b = &mut self.b;
    let selected: Vec<_> = (0..RECORD_LOOKAHEAD_WORDS)
      .map(|word| b.eq_const(&self.cursor[4..], word as u64))
      .collect();
    let mut source: Vec<_> = (0..8 * (15 + bytes))
      .map(|bit| {
        let products: Vec<_> = selected
          .iter()
          .enumerate()
          .filter_map(|(word, flag)| {
            let index = word * 128 + bit;
            (index < RECORD_LOOKAHEAD_BYTES * 8)
              .then(|| b.b.and(*flag, SOURCE + index))
          })
          .collect();
        b.sum(&products)
      })
      .collect();
    for (shift_bit, flag) in self.cursor[..4].iter().enumerate() {
      let shift = 8 << shift_bit;
      source = (0..source.len() - shift)
        .map(|bit| {
          let delta = b
            .b
            .product_of_parities(&[*flag], &[source[bit], source[bit + shift]]);
          b.sum(&[source[bit], delta])
        })
        .collect();
    }
    source
  }
  fn advance(&mut self, length: &[usize]) {
    let (cursor, carry) =
      add(&mut self.b.b, self.b.one, self.b.zero, &self.cursor, length);
    self.b.violations.push(carry);
    self.cursor = cursor;
  }
  fn fixed(&mut self, bytes: usize, enabled: usize) -> Bits {
    let source = self.window(bytes);
    let value = source.iter().map(|bit| self.b.b.and(enabled, *bit)).collect();
    let length: Vec<_> = (0..64)
      .map(|bit| {
        if bytes as u64 & (1u64 << bit) != 0 { enabled } else { self.b.zero }
      })
      .collect();
    self.advance(&length);
    value
  }
  fn natural(&mut self, enabled: usize) -> Bits {
    let source = self.window(19);
    let decoded = self.b.natural(&source, enabled, 128);
    self.advance(&decoded.consumed);
    decoded.value
  }
  fn le(&mut self, enabled: usize, value: &[usize], bound: &[usize]) {
    let (_, borrow) =
      subtract(&mut self.b.b, self.b.one, self.b.zero, bound, value);
    let good = self.b.not(borrow);
    self.b.require(enabled, good);
  }
  fn lt(&mut self, enabled: usize, value: &[usize], bound: &[usize]) {
    let (_, borrow) =
      subtract(&mut self.b.b, self.b.one, self.b.zero, value, bound);
    self.b.require(enabled, borrow);
  }
  fn count(&mut self, enabled: usize, count: &[usize]) {
    let (mut remaining, borrow) = subtract(
      &mut self.b.b,
      self.b.one,
      self.b.zero,
      &self.remaining,
      &self.cursor,
    );
    self.b.violations.push(borrow);
    remaining.resize(128, self.b.zero);
    self.le(enabled, count, &remaining);
  }
  fn tags(
    &mut self,
    enabled: usize,
    tag: &[usize],
    count: usize,
  ) -> Vec<usize> {
    let flags: Vec<_> = (0..count)
      .map(|value| {
        let same = self.b.eq_const(tag, value as u64);
        self.b.b.and(enabled, same)
      })
      .collect();
    let good = self.b.sum(&flags);
    self.b.require(enabled, good);
    flags
  }
  fn header(&mut self, magic: &[u8; 4], enabled: usize) {
    let bytes = self.fixed(12, enabled);
    let expected: Vec<_> =
      magic.iter().copied().chain([1, 0, 0, 0, 2, 0, 0, 0]).collect();
    for (byte, value) in bytes.as_chunks::<8>().0.iter().zip(expected) {
      let good = self.b.eq_const(byte, u64::from(value));
      self.b.require(enabled, good);
    }
  }
  fn finish(mut self, fields: &[Bits; RECORD_FIELDS]) -> BooleanR1csPlan {
    let offset: Vec<_> = (0..64).collect();
    let (next, carry) =
      add(&mut self.b.b, self.b.one, self.b.zero, &offset, &self.cursor);
    self.b.violations.push(carry);
    let length: Vec<_> = (64..128).collect();
    let (_, borrow) =
      subtract(&mut self.b.b, self.b.one, self.b.zero, &length, &next);
    self.b.violations.push(borrow);
    for (index, field) in fields.iter().enumerate() {
      self.b.write(RECORD_INPUTS + index, field);
    }
    self.b.write(RECORD_INPUTS + RECORD_FIELDS, &[next, length].concat());
    self.b.finish(RECORD_INPUTS + OUTPUTS - 1)
  }
}

fn build_plan(kind: RecordKind) -> BooleanR1csPlan {
  let mut r = Reader::new(kind);
  let enabled = 128;
  let mut fields: [Bits; RECORD_FIELDS] = std::array::from_fn(|_| Vec::new());
  match kind {
    RecordKind::Metadata | RecordKind::Count | RecordKind::Index => {
      fields[0] = r.natural(enabled);
      r.unused(if kind == RecordKind::Metadata { 0 } else { 1 });
      if kind == RecordKind::Count {
        r.le(enabled, &fields[0], &r.bound(0));
        r.count(enabled, &fields[0]);
      } else if kind == RecordKind::Index {
        r.lt(enabled, &fields[0], &r.bound(0));
      }
    },
    RecordKind::Constructor => {
      r.unused(1);
      let block = r.fixed(32, enabled);
      fields[0] = block[..128].to_vec();
      fields[1] = block[128..].to_vec();
      for field in &mut fields[2..5] {
        *field = r.natural(enabled);
      }
      r.le(enabled, &fields[4], &r.bound(0));
    },
    RecordKind::Function => {
      for field in &mut fields[..3] {
        *field = r.natural(enabled);
      }
      r.le(enabled, &fields[0], &r.bound(0));
      r.le(enabled, &fields[0], &r.bound(1));
      r.le(enabled, &fields[2], &r.bound(2));
      r.lt(enabled, &fields[1], &fields[2]);
      r.count(enabled, &fields[2]);
    },
    RecordKind::Block => {
      r.unused(1);
      fields[0] = r.natural(enabled);
      r.le(enabled, &fields[0], &r.bound(0));
      fields[1] = r.fixed(1, enabled);
      r.tags(enabled, &fields[1], 8);
    },
    RecordKind::Alternative => {
      r.unused(2);
      fields[0] = r.natural(enabled);
      fields[1] = r.natural(enabled);
      r.lt(enabled, &fields[0], &r.bound(0));
      r.lt(enabled, &fields[1], &r.bound(1));
    },
    RecordKind::Input | RecordKind::Output => {
      r.b.require_zero(enabled, &(0..64).collect::<Vec<_>>());
      r.header(
        if kind == RecordKind::Input { b"IXFI" } else { b"IXFO" },
        enabled,
      );
      if kind == RecordKind::Input {
        fields[0] = r.natural(enabled);
        r.le(enabled, &fields[0], &r.bound(0));
        let same = r.b.equal(&fields[0], &r.bound(1));
        r.b.require(enabled, same);
        r.le(enabled, &fields[0], &r.bound(2));
      } else {
        r.unused(1);
        fields[0] = vec![r.b.zero; 128];
        fields[0][0] = enabled;
        r.le(enabled, &fields[0], &r.bound(0));
      }
      r.count(enabled, &fields[0]);
    },
    RecordKind::Value => {
      fields[0] = r.fixed(1, enabled);
      let tags = r.tags(enabled, &fields[0], 5);
      let block = r.fixed(32, tags[1]);
      fields[1] = block[..128].to_vec();
      fields[2] = block[128..].to_vec();
      fields[3] = r.natural(tags[1]);
      fields[4] = r.natural(tags[1]);
      let function = r.natural(tags[2]);
      r.lt(tags[2], &function, &r.bound(1));
      fields[1] = fields[1]
        .iter()
        .zip(function)
        .map(|(a, b)| r.b.sum(&[*a, b]))
        .collect();
      let object = r.b.sum(&[tags[1], tags[2]]);
      let children = r.b.sum(&[object, tags[4]]);
      fields[5] = r.natural(children);
      r.le(object, &fields[5], &r.bound(0));
      r.lt(tags[4], &fields[5], &r.b.constant(128, 1 << 32));
      r.le(children, &fields[5], &r.bound(2));
      r.count(children, &fields[5]);
    },
    RecordKind::Operand => {
      r.unused(1);
      fields[0] = r.fixed(1, enabled);
      let tags = r.tags(enabled, &fields[0], 3);
      fields[1] = r.natural(tags[0]);
      r.lt(tags[0], &fields[1], &r.bound(0));
    },
    RecordKind::Scalar => {
      r.unused(0);
      fields[0] = r.fixed(1, enabled);
      let tags = r.tags(enabled, &fields[0], 7);
      let boolean = r.fixed(1, tags[2]);
      r.b.require_zero(tags[2], &boolean[1..]);
      let word = r.fixed(4, tags[3]);
      let base = r.b.sum(&[tags[4], tags[5]]);
      let first = r.fixed(8, base);
      let second = r.fixed(8, tags[5]);
      let modulus = r.b.constant(64, 0xffff_ffff_0000_0001);
      r.lt(base, &first, &modulus);
      r.lt(tags[5], &second, &modulus);
      fields[1] = (0..128)
        .map(|bit| {
          let sources: Vec<_> = [
            boolean.get(bit),
            word.get(bit),
            first.get(bit),
            bit.checked_sub(64).and_then(|bit| second.get(bit)),
          ]
          .into_iter()
          .flatten()
          .copied()
          .collect();
          r.b.sum(&sources)
        })
        .collect();
    },
    RecordKind::Operation => {
      fields[0] = r.fixed(1, enabled);
      let tags = r.tags(enabled, &fields[0], 8);
      fields[1] = r.fixed(1, tags[1]);
      let primitives = r.tags(tags[1], &fields[1], 58);
      fields[4] = (0..128)
        .map(|bit| {
          let sources: Vec<_> = primitives
            .iter()
            .enumerate()
            .filter_map(|(index, flag)| {
              let arity = primitive_arity(index as u8);
              (bit < 8 && arity & (1 << bit) != 0).then_some(*flag)
            })
            .collect();
          r.b.sum(&sources)
        })
        .collect();
      let indexed = r.b.sum(&[tags[2], tags[4], tags[5]]);
      fields[2] = r.natural(indexed);
      r.lt(tags[2], &fields[2], &r.bound(1));
      let function = r.b.sum(&[tags[4], tags[5]]);
      r.lt(function, &fields[2], &r.bound(2));
      let has_args = r.b.sum(&[tags[1], tags[2], tags[4], tags[5], tags[6]]);
      fields[3] = r.natural(has_args);
      r.le(has_args, &fields[3], &r.bound(0));
      r.count(has_args, &fields[3]);
      let same = r.b.equal(&fields[3], &fields[4]);
      r.b.require(tags[1], same);
    },
  }
  r.finish(&fields)
}

// Kept explicit in circuit synthesis. Tests compare all 58 entries against
// the independent functional opcode registry; this is not a native-opcode map.
fn primitive_arity(opcode: u8) -> u8 {
  match opcode {
    49 | 54 => 0,
    8 | 21 | 22 | 23 | 27 | 29 | 30 | 34 | 37 | 38 | 39 | 44 | 45 | 46 | 47
    | 48 | 50 | 56 | 57 => 1,
    42 | 52 => 3,
    _ => 2,
  }
}

struct NativeReader {
  bytes: [u8; RECORD_LOOKAHEAD_BYTES],
  cursor: usize,
  bad: bool,
}

impl NativeReader {
  fn fixed(&mut self, count: usize, enabled: bool) -> Vec<u8> {
    if !enabled {
      return vec![0; count];
    }
    let value = (self.cursor..self.cursor + count)
      .map(|index| self.bytes.get(index).copied().unwrap_or(0))
      .collect();
    self.cursor += count;
    value
  }
  fn integer(&mut self, enabled: bool) -> u128 {
    if !enabled {
      return 0;
    }
    let mut value = 0u128;
    for index in 0..19 {
      let byte = self.bytes.get(self.cursor + index).copied().unwrap_or(0);
      let digit = u128::from(byte & 127);
      self.bad |= index == 18 && digit > 3;
      value |= (digit & if index == 18 { 3 } else { 127 }) << (7 * index);
      if byte < 128 {
        self.bad |= index != 0 && byte == 0;
        self.cursor += index + 1;
        return value;
      }
    }
    self.bad = true;
    value
  }
  fn tag(&mut self, enabled: bool, count: u8) -> u8 {
    let value = self.fixed(1, enabled)[0];
    self.bad |= enabled && value >= count;
    value
  }
  fn number(&mut self, count: usize, enabled: bool) -> u128 {
    let mut bytes = self.fixed(count, enabled);
    bytes.resize(16, 0);
    u128::from_le_bytes(bytes.try_into().unwrap())
  }
  fn header(&mut self, magic: &[u8; 4], enabled: bool) {
    let expected: Vec<_> =
      magic.iter().copied().chain([1, 0, 0, 0, 2, 0, 0, 0]).collect();
    let bytes = self.fixed(12, enabled);
    self.bad |= enabled && bytes != expected;
  }
}

/// Independent total integer evaluator, including disabled and malformed rows.
pub(super) fn evaluate(
  kind: RecordKind,
  input: &[F128; RECORD_INPUTS],
) -> [F128; OUTPUTS] {
  let enabled = input[1].lo & 1 != 0;
  let offset = input[0].lo;
  let length = input[0].hi;
  let bounds = input[2..5]
    .iter()
    .map(|word| u128::from(word.lo) | (u128::from(word.hi) << 64))
    .collect::<Vec<_>>();
  let bytes: Vec<_> = input[5..]
    .iter()
    .flat_map(|word| {
      word.lo.to_le_bytes().into_iter().chain(word.hi.to_le_bytes())
    })
    .collect();
  let remaining = length.saturating_sub(offset);
  let mut r = NativeReader {
    bytes: bytes.try_into().unwrap(),
    cursor: 0,
    bad: offset > length || input[1].lo > 1 || input[1].hi != 0,
  };
  r.bad |=
    r.bytes.iter().enumerate().any(|(index, byte)| {
      (!enabled || index as u64 >= remaining) && *byte != 0
    });
  let used_bounds = match kind {
    RecordKind::Metadata | RecordKind::Scalar => 0,
    RecordKind::Count
    | RecordKind::Index
    | RecordKind::Constructor
    | RecordKind::Block
    | RecordKind::Output
    | RecordKind::Operand => 1,
    RecordKind::Alternative => 2,
    _ => 3,
  };
  r.bad |= bounds[used_bounds..].iter().any(|value| *value != 0);
  let mut fields = [0u128; RECORD_FIELDS];
  let mut count = None;
  match kind {
    RecordKind::Metadata | RecordKind::Count | RecordKind::Index => {
      fields[0] = r.integer(enabled);
      if kind == RecordKind::Count {
        r.bad |= enabled && fields[0] > bounds[0];
        count = Some(fields[0]);
      } else if kind == RecordKind::Index {
        r.bad |= enabled && fields[0] >= bounds[0];
      }
    },
    RecordKind::Constructor => {
      fields[0] = r.number(16, enabled);
      fields[1] = r.number(16, enabled);
      for field in &mut fields[2..5] {
        *field = r.integer(enabled);
      }
      r.bad |= enabled && fields[4] > bounds[0];
    },
    RecordKind::Function => {
      for field in &mut fields[..3] {
        *field = r.integer(enabled);
      }
      r.bad |= enabled
        && (fields[0] > bounds[0]
          || fields[0] > bounds[1]
          || fields[2] > bounds[2]
          || fields[1] >= fields[2]);
      count = Some(fields[2]);
    },
    RecordKind::Block => {
      fields[0] = r.integer(enabled);
      r.bad |= enabled && fields[0] > bounds[0];
      fields[1] = u128::from(r.tag(enabled, 8));
    },
    RecordKind::Alternative => {
      fields[0] = r.integer(enabled);
      fields[1] = r.integer(enabled);
      r.bad |= enabled && (fields[0] >= bounds[0] || fields[1] >= bounds[1]);
    },
    RecordKind::Input | RecordKind::Output => {
      r.bad |= enabled && offset != 0;
      r.header(
        if kind == RecordKind::Input { b"IXFI" } else { b"IXFO" },
        enabled,
      );
      fields[0] = if kind == RecordKind::Input {
        r.integer(enabled)
      } else {
        u128::from(enabled)
      };
      r.bad |= enabled && fields[0] > bounds[0];
      if kind == RecordKind::Input {
        r.bad |= enabled && (fields[0] != bounds[1] || fields[0] > bounds[2]);
      }
      count = Some(fields[0]);
    },
    RecordKind::Value => {
      let tag = r.tag(enabled, 5);
      fields[0] = u128::from(tag);
      if enabled && tag == 1 {
        fields[1] = r.number(16, true);
        fields[2] = r.number(16, true);
        fields[3] = r.integer(true);
        fields[4] = r.integer(true);
      } else if enabled && tag == 2 {
        fields[1] = r.integer(true);
        r.bad |= fields[1] >= bounds[1];
      }
      if enabled && (tag == 1 || tag == 2 || tag == 4) {
        fields[5] = r.integer(true);
        r.bad |= (tag != 4 && fields[5] > bounds[0])
          || fields[5] > bounds[2]
          || (tag == 4 && fields[5] >= 1 << 32);
      }
      count = Some(fields[5]);
    },
    RecordKind::Operand => {
      let tag = r.tag(enabled, 3);
      fields[0] = u128::from(tag);
      fields[1] = r.integer(enabled && tag == 0);
      r.bad |= enabled && tag == 0 && fields[1] >= bounds[0];
    },
    RecordKind::Scalar => {
      let tag = r.tag(enabled, 7);
      fields[0] = u128::from(tag);
      if enabled {
        match tag {
          2 => {
            fields[1] = r.number(1, true);
            r.bad |= fields[1] > 1;
          },
          3 => fields[1] = r.number(4, true),
          4 | 5 => {
            fields[1] = r.number(8, true);
            r.bad |= fields[1] >= 0xffff_ffff_0000_0001;
            if tag == 5 {
              let second = r.number(8, true);
              r.bad |= second >= 0xffff_ffff_0000_0001;
              fields[1] |= second << 64;
            }
          },
          _ => {},
        }
      }
    },
    RecordKind::Operation => {
      let tag = r.tag(enabled, 8);
      fields[0] = u128::from(tag);
      if enabled && tag == 1 {
        fields[1] = u128::from(r.tag(true, 58));
        fields[4] = if fields[1] < 58 {
          u128::from(primitive_arity(fields[1] as u8))
        } else {
          0
        };
      }
      if enabled && [2, 4, 5].contains(&tag) {
        fields[2] = r.integer(true);
        r.bad |= fields[2] >= bounds[if tag == 2 { 1 } else { 2 }];
      }
      if enabled && [1, 2, 4, 5, 6].contains(&tag) {
        fields[3] = r.integer(true);
        r.bad |= fields[3] > bounds[0];
      }
      r.bad |= enabled && tag == 1 && fields[3] != fields[4];
      count = Some(fields[3]);
    },
  }
  if let Some(count) = count {
    r.bad |=
      enabled && count > u128::from(remaining.saturating_sub(r.cursor as u64));
  }
  let (next, carry) = offset.overflowing_add(r.cursor as u64);
  r.bad |= carry || next > length;
  let mut output = [F128::ZERO; OUTPUTS];
  for (output, field) in output.iter_mut().zip(fields) {
    *output = F128::new(field as u64, (field >> 64) as u64);
  }
  output[RECORD_FIELDS] = F128::new(next, length);
  output[RECORD_FIELDS + 1] = F128::new(u64::from(r.bad), 0);
  output
}
