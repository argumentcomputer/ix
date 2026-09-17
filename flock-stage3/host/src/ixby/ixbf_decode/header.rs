//! The original IXBF prefix through the constructor-vector length. It does
//! not validate the constructor/function bodies, entry target, or execution.
//! Metadata is exact unsigned 128-bit data, never a field-arithmetic sum.

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

pub const HEADER_METADATA_BITS: usize = 128;
pub const HEADER_FIELDS: usize = 13;
const INTEGER_BYTES: usize = HEADER_METADATA_BITS.div_ceil(7);
pub const MAX_HEADER_BYTES: usize = 12 + HEADER_FIELDS * INTEGER_BYTES;
pub const HEADER_PREFIX_WORDS: usize = MAX_HEADER_BYTES.div_ceil(16);
pub const HEADER_PREFIX_BYTES: usize = HEADER_PREFIX_WORDS * 16;
const INPUTS: usize = 1 + HEADER_PREFIX_WORDS;
const OUTPUTS: usize = HEADER_FIELDS + 2;

#[derive(Clone, Debug)]
pub struct HeaderDecodeGate {
  pub(super) nu: usize,
  pub(super) plan: Arc<OnceLock<BooleanR1csPlan>>,
}

#[derive(Clone, Debug)]
pub struct HeaderDecodeRow(pub(super) Vec<F128>);

impl HeaderDecodeGate {
  pub fn new(nu: usize) -> Result<Self> {
    ensure!((3..=20).contains(&nu), "functional header codec row domain");
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
    rows: &[HeaderDecodeRow],
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

impl CountedGate for HeaderDecodeGate {
  fn input_count(&self) -> usize {
    INPUTS
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

impl GateType for HeaderDecodeGate {
  type Row = HeaderDecodeRow;
  type Hint = ();
  fn table(&self) -> TableType {
    let schema = (0..INPUTS)
      .map(IoWord::input)
      .chain((INPUTS..INPUTS + OUTPUTS).map(IoWord::output))
      .collect();
    crate::boolean::table_from_block_r1cs(self.r1cs()).with_io_schema(schema)
  }
  fn eval(
    &self,
    inputs: &[F128],
    _: &(),
    outputs: &mut Vec<F128>,
  ) -> Self::Row {
    assert_eq!(inputs.len(), INPUTS, "fixed functional header input width");
    outputs.extend(evaluate(inputs));
    HeaderDecodeRow(inputs.to_vec())
  }
  fn witness(&self, _: &[Self::Row], _: usize) -> SlotWitness {
    SlotWitness::DeferredToRows
  }
}

#[derive(Clone, Copy, Debug)]
pub struct HeaderWires {
  /// functions, constructors, blocks, locals, operands, continuations,
  /// inputNodes, natBits, stringBytes, byteArrayBytes, in original wire order.
  pub limits: [Wire; 10],
  pub max_steps: Wire,
  pub entry: Wire,
  pub constructor_count: Wire,
  /// Exact u64 byte offset immediately after the constructor count.
  pub constructors_offset: Wire,
}

/// `prefix` must be the first fixed 272 bytes of the original artifact's
/// authenticated buffer (zero after file EOF). It is not a host-selected
/// substitute header. Bytes belonging to the following body remain untouched.
#[derive(Clone, Copy, Debug)]
pub struct HeaderDecodeSlot {
  slot: SlotId,
  zero: Wire,
}

impl HeaderDecodeSlot {
  pub fn declare(b: &mut impl CircuitEmitter, gate: HeaderDecodeGate) -> Self {
    Self { slot: b.slot(gate), zero: b.fixed_public_input(F128::ZERO) }
  }
  pub fn slot(&self) -> SlotId {
    self.slot
  }
  pub fn decode(
    &self,
    b: &mut impl CircuitEmitter,
    file_length: Wire,
    prefix: &[Wire],
  ) -> HeaderWires {
    assert_eq!(prefix.len(), HEADER_PREFIX_WORDS);
    let mut inputs = vec![file_length];
    inputs.extend_from_slice(prefix);
    let output = b.gate(self.slot, &inputs);
    b.connect(output[OUTPUTS - 1], self.zero);
    HeaderWires {
      limits: output[..10].try_into().unwrap(),
      max_steps: output[10],
      entry: output[11],
      constructor_count: output[12],
      constructors_offset: output[13],
    }
  }
}

/// Independent total integer evaluator, including malformed byte prefixes.
pub(super) fn evaluate(input: &[F128]) -> Vec<F128> {
  let length = input[0].lo;
  let bytes: Vec<_> = input[1..]
    .iter()
    .flat_map(|word| {
      word.lo.to_le_bytes().into_iter().chain(word.hi.to_le_bytes())
    })
    .collect();
  let expected = *b"IXBF\x01\0\0\0\x02\0\0\0";
  let mut violation = input[0].hi != 0 || bytes[..12] != expected;
  violation |= bytes
    .iter()
    .enumerate()
    .any(|(index, byte)| index as u64 >= length && *byte != 0);
  let mut cursor = 12usize;
  let mut values = Vec::with_capacity(HEADER_FIELDS);
  for _ in 0..HEADER_FIELDS {
    let mut value = 0u128;
    let mut consumed = 0;
    for index in 0..INTEGER_BYTES {
      let byte = bytes.get(cursor + index).copied().unwrap_or(0);
      let digit = u128::from(byte & 127);
      if index == INTEGER_BYTES - 1 {
        violation |= digit > 3;
      }
      value |= (digit & if index == INTEGER_BYTES - 1 { 3 } else { 127 })
        << (7 * index);
      if byte < 128 {
        violation |= index != 0 && byte == 0;
        consumed = index + 1;
        break;
      }
    }
    violation |= consumed == 0;
    cursor += consumed;
    violation |= cursor as u64 > length;
    values.push(value);
  }
  violation |= values[12] > values[1];
  violation |= values[12] > u128::from(length.saturating_sub(cursor as u64));
  let mut result: Vec<_> = values
    .iter()
    .map(|value| F128::new(*value as u64, (value >> 64) as u64))
    .collect();
  result.push(F128::new(cursor as u64, 0));
  result.push(F128::new(u64::from(violation), 0));
  result
}

/// Fixed local prefix selection, independent of the full program's byte
/// capacity. The four shifts choose a byte offset within packed 16-byte words.
fn window(b: &mut Builder, cursor: &[usize]) -> Bits {
  let selected: Vec<_> = (0..HEADER_PREFIX_WORDS)
    .map(|word| b.eq_const(&cursor[4..], word as u64))
    .collect();
  let mut source: Vec<_> = (0..8 * (15 + INTEGER_BYTES))
    .map(|bit| {
      let products: Vec<_> = selected
        .iter()
        .enumerate()
        .filter_map(|(word, flag)| {
          let index = word * 128 + bit;
          (index < HEADER_PREFIX_WORDS * 128)
            .then(|| b.b.and(*flag, 128 + index))
        })
        .collect();
      b.sum(&products)
    })
    .collect();
  for (shift_bit, flag) in cursor[..4].iter().enumerate() {
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
  assert_eq!(source.len(), INTEGER_BYTES * 8);
  source
}

fn build_plan() -> BooleanR1csPlan {
  // The fixed synthesis uses 129,069 columns. Keep the inner domain at the
  // next power of two, independently of the artifact length or metadata.
  let mut b = Builder::new(INPUTS, OUTPUTS, 1 << 17);
  b.violations.extend(64..128);
  let length: Vec<_> = (0..64).collect();
  let large = b.any(&length[9..]);
  for index in 0..HEADER_PREFIX_BYTES {
    let at = b.constant(9, index as u64);
    let (_, within) = subtract(&mut b.b, b.one, b.zero, &at, &length[..9]);
    let live = or(&mut b.b, b.one, within, large);
    let padding = b.not(live);
    b.require_zero(
      padding,
      &(128 + index * 8..136 + index * 8).collect::<Vec<_>>(),
    );
  }
  for (index, byte) in b"IXBF\x01\0\0\0\x02\0\0\0".iter().enumerate() {
    let good = b.eq_const(
      &(128 + index * 8..136 + index * 8).collect::<Vec<_>>(),
      u64::from(*byte),
    );
    b.require(b.one, good);
  }
  let mut cursor = b.constant(64, 12);
  let mut fields = Vec::with_capacity(HEADER_FIELDS);
  for index in 0..HEADER_FIELDS {
    let bytes = window(&mut b, &cursor);
    let decoded = b.natural(&bytes, b.one, HEADER_METADATA_BITS);
    let (next, carry) =
      add(&mut b.b, b.one, b.zero, &cursor, &decoded.consumed);
    b.violations.push(carry);
    let (_, overflow) = subtract(&mut b.b, b.one, b.zero, &length, &next);
    b.violations.push(overflow);
    cursor = next;
    b.write(INPUTS + index, &decoded.value);
    fields.push(decoded.value);
  }
  let (_, too_many) =
    subtract(&mut b.b, b.one, b.zero, &fields[1], &fields[12]);
  b.violations.push(too_many);
  let (mut remaining, borrow) =
    subtract(&mut b.b, b.one, b.zero, &length, &cursor);
  b.violations.push(borrow);
  remaining.resize(128, b.zero);
  let (_, too_many) =
    subtract(&mut b.b, b.one, b.zero, &remaining, &fields[12]);
  b.violations.push(too_many);
  b.write(INPUTS + HEADER_FIELDS, &cursor);
  b.finish(INPUTS + OUTPUTS - 1)
}
