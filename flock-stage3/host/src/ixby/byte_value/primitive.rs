//! Existing byte opcodes over constrained dereferences. Hash output inputs
//! must be wired to `BoundedBlake3`, and scalar headers/results to the scalar
//! dispatch network. The row has no free operation result or acceptance bit.

use super::{ByteCapacity, validate_entries};
use crate::{
  boolean::{
    BooleanR1csBuilder, BooleanR1csPlan, generate_boolean_witness_into,
  },
  ixby::{
    bits::{
      add, any, constant_bits, equal, equal_constant, evaluate_words,
      fill_words, not, require, require_zero, subtract,
    },
    decode::{BYTE_PRIMITIVES, PrimitiveSet, primitive_arity},
    value::{
      BOOL_TAG, BYTES_TAG, FIELD_TAG, WORD32_TAG, cell_with_byte_handles,
    },
  },
  sizing::CountedGate,
};
use anyhow::{Result, ensure};
use flock_prover::{
  circuit::builder::{GateType, SlotWitness},
  field::F128,
  r1cs::BlockR1cs,
  schedule::{IoWord, TableType},
  union::SlotWitnessDest,
};
use std::sync::{Arc, OnceLock};

#[derive(Clone, Debug)]
pub struct BytePrimitiveGate {
  nu: usize,
  capacity: ByteCapacity,
  entries: usize,
  operands: usize,
  registry: PrimitiveSet,
  plan: Arc<OnceLock<BooleanR1csPlan>>,
}

#[derive(Clone, Debug)]
pub struct BytePrimitiveRow(pub(super) Vec<F128>);

#[cfg(test)]
impl BytePrimitiveRow {
  pub(crate) fn inputs(&self) -> &[F128] {
    &self.0
  }
}

impl BytePrimitiveGate {
  pub fn new(
    nu: usize,
    capacity: ByteCapacity,
    entries: usize,
    operands: usize,
    registry: PrimitiveSet,
  ) -> Result<Self> {
    ensure!((3..=20).contains(&nu), "byte-primitive row-domain admission");
    validate_entries(entries)?;
    ensure!((1..=4).contains(&operands), "byte-primitive operand capacity");
    ensure!(
      registry == registry.crypto_subset(),
      "Nat primitives require separate Nat dispatch"
    );
    Ok(Self {
      nu,
      capacity,
      entries,
      operands,
      registry,
      plan: Arc::new(OnceLock::new()),
    })
  }
  pub(super) fn plan(&self) -> &BooleanR1csPlan {
    self.plan.get_or_init(|| build(self))
  }
  pub fn r1cs(&self) -> BlockR1cs {
    self.plan().block_r1cs(self.nu)
  }
  pub fn generate_witness_into(
    &self,
    rows: &[BytePrimitiveRow],
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

impl CountedGate for BytePrimitiveGate {
  // Fetched headers, setup-fixed allocation id, cells, two dereferenced byte
  // buffers, and the two digest words from the fixed BLAKE3 network.
  fn input_count(&self) -> usize {
    5 + 2 * self.operands + 2 * self.capacity.record_words()
  }
  // Byte-operation flag, masked scalar headers, byte-operation result cell,
  // allocated immutable byte record (zero for non-array results), residual.
  fn output_count(&self) -> usize {
    6 + self.capacity.record_words()
  }
  fn table_at(&self, nu: usize) -> TableType {
    let mut gate = self.clone();
    gate.nu = nu;
    gate.table()
  }
}

impl GateType for BytePrimitiveGate {
  type Row = BytePrimitiveRow;
  type Hint = ();
  fn table(&self) -> TableType {
    let mut schema: Vec<_> =
      (0..self.input_count()).map(IoWord::input).collect();
    schema.extend(
      (self.input_count()..self.input_count() + self.output_count())
        .map(IoWord::output),
    );
    crate::boolean::table_from_block_r1cs(self.r1cs()).with_io_schema(schema)
  }
  fn eval(&self, input: &[F128], _: &(), output: &mut Vec<F128>) -> Self::Row {
    assert_eq!(input.len(), self.input_count());
    output.extend(evaluate_words(self.plan(), input, self.output_count()));
    BytePrimitiveRow(input.to_vec())
  }
  fn witness(&self, _: &[Self::Row], _: usize) -> SlotWitness {
    SlotWitness::DeferredToRows
  }
}

fn flags(
  b: &mut BooleanR1csBuilder,
  one: usize,
  selected: &[usize],
  opcodes: &[u8],
) -> usize {
  b.xor(
    &opcodes
      .iter()
      .map(|opcode| selected[*opcode as usize])
      .collect::<Vec<_>>(),
    one,
  )
}

fn choose(
  b: &mut BooleanR1csBuilder,
  one: usize,
  zero: usize,
  terms: &[(usize, &[usize])],
  width: usize,
) -> Vec<usize> {
  (0..width)
    .map(|bit| {
      let terms: Vec<_> = terms
        .iter()
        .filter_map(|(flag, source)| {
          source.get(bit).map(|source| b.and(*flag, *source))
        })
        .collect();
      if terms.is_empty() { zero } else { b.xor(&terms, one) }
    })
    .collect()
}

/// Full u32 shift in BYTE units, with zero fill. Bits beyond the physical
/// buffer's address width erase the result; they never alias a low index.
fn shift(
  b: &mut BooleanR1csBuilder,
  one: usize,
  zero: usize,
  input: &[usize],
  index: &[usize],
  right: bool,
) -> Vec<usize> {
  assert_eq!(index.len(), 32);
  let mut value = input.to_vec();
  let stages =
    (input.len().div_ceil(8).max(1)).next_power_of_two().ilog2() as usize;
  for (stage, bit) in index.iter().enumerate().take(stages) {
    let distance = 8usize << stage;
    value = (0..value.len())
      .map(|position| {
        let source = if right {
          position.checked_add(distance)
        } else {
          position.checked_sub(distance)
        };
        let shifted =
          source.and_then(|source| value.get(source)).copied().unwrap_or(zero);
        let delta = b.product_of_parities(&[*bit], &[value[position], shifted]);
        b.xor(&[value[position], delta], one)
      })
      .collect();
  }
  let high = any(b, one, &index[stages..]);
  let low = not(b, one, high);
  value.iter().map(|bit| b.and(low, *bit)).collect()
}

fn buffer(
  b: &mut BooleanR1csBuilder,
  one: usize,
  zero: usize,
  violations: &mut Vec<usize>,
  capacity: ByteCapacity,
  base: usize,
) -> (Vec<usize>, Vec<usize>) {
  let length: Vec<_> = (base..base + 32).collect();
  require_zero(
    b,
    one,
    violations,
    one,
    &(base + 32..base + 128).collect::<Vec<_>>(),
  );
  let maximum = constant_bits(one, zero, (capacity.bytes() + 1) as u32);
  let in_range = subtract(b, one, zero, &length, &maximum).1;
  require(b, one, violations, one, in_range);
  let data: Vec<_> =
    (base + 128..base + 128 * capacity.record_words()).collect();
  for (byte, bits) in data.chunks(8).enumerate() {
    let boundary = constant_bits(one, zero, byte as u32);
    let live = subtract(b, one, zero, &boundary, &length).1;
    let padding = not(b, one, live);
    require_zero(b, one, violations, padding, bits);
  }
  (length, data)
}

fn build(gate: &BytePrimitiveGate) -> BooleanR1csPlan {
  let n = gate.input_count();
  let reserved = 128 * (n + gate.output_count());
  let columns = reserved + 16384 + 2048 * (gate.capacity.bytes() + 1);
  let mut b = BooleanR1csBuilder::new(
    columns.next_power_of_two().ilog2() as usize,
    reserved,
  );
  for bit in 0..128 * n {
    b.free_boolean_at(bit);
  }
  let one = b.alloc_constant_one();
  let zero = b.xor(&[one, one], one);
  let mut violations = Vec::new();
  let active = equal_constant(&mut b, one, &(32..64).collect::<Vec<_>>(), 2);
  let code: Vec<_> = (160..192).collect();
  let count: Vec<_> = (192..224).collect();
  let mut selected = vec![zero; 35];
  for opcode in gate.registry.opcodes() {
    let equal = equal_constant(&mut b, one, &code, u64::from(opcode));
    selected[opcode as usize] = b.and(active, equal);
  }
  let valid = b.xor(&selected, one);
  require(&mut b, one, &mut violations, active, valid);
  let byte = flags(&mut b, one, &selected, BYTE_PRIMITIVES);
  let scalar = not(&mut b, one, byte);
  let mut used = [zero; 3];
  for arity in 1..=3 {
    let codes: Vec<_> = BYTE_PRIMITIVES
      .iter()
      .copied()
      .filter(|opcode| primitive_arity(*opcode) == Some(arity))
      .collect();
    let flag = flags(&mut b, one, &selected, &codes);
    let correct = equal_constant(&mut b, one, &count, arity as u64);
    require(&mut b, one, &mut violations, flag, correct);
    if arity > gate.operands {
      violations.push(flag);
    }
    for target in used.iter_mut().take(arity) {
      *target = b.xor(&[*target, flag], one);
    }
  }
  let mut args = Vec::new();
  let mut tags = Vec::new();
  for (index, enabled) in used.iter().enumerate() {
    let raw = if index < gate.operands {
      (128 * (3 + 2 * index)..128 * (5 + 2 * index)).collect::<Vec<_>>()
    } else {
      vec![zero; 256]
    };
    let masked: Vec<_> = raw.iter().map(|bit| b.and(*enabled, *bit)).collect();
    tags.push(cell_with_byte_handles(
      &mut b,
      one,
      &mut violations,
      *enabled,
      &masked,
      gate.entries,
    ));
    let unused = not(&mut b, one, *enabled);
    let unused = b.and(byte, unused);
    require_zero(&mut b, one, &mut violations, unused, &raw);
    args.push(masked[128..].to_vec());
  }
  for index in 3..gate.operands {
    require_zero(
      &mut b,
      one,
      &mut violations,
      byte,
      &(128 * (3 + 2 * index)..128 * (5 + 2 * index)).collect::<Vec<_>>(),
    );
  }
  for (codes, argument, tag) in [
    (&[11][..], 0, 1),
    (&[19][..], 0, 2),
    (&[12, 20, 29, 30, 31, 32, 33, 34][..], 0, 5),
    (&[31, 33][..], 1, 5),
    (&[30, 32][..], 1, 1),
    (&[32][..], 2, 1),
  ] {
    let flag = flags(&mut b, one, &selected, codes);
    require(&mut b, one, &mut violations, flag, tags[argument][tag]);
  }
  let first = 128 * (3 + 2 * gate.operands);
  let second = first + 128 * gate.capacity.record_words();
  let (a_len, a) =
    buffer(&mut b, one, zero, &mut violations, gate.capacity, first);
  let (b_len, rhs) =
    buffer(&mut b, one, zero, &mut violations, gate.capacity, second);
  for (opcode, length) in [(12, 4), (20, 8)] {
    let correct = equal_constant(&mut b, one, &a_len, length);
    require(&mut b, one, &mut violations, selected[opcode], correct);
  }
  let in_range = subtract(&mut b, one, zero, &args[1][..32], &a_len).1;
  require(&mut b, one, &mut violations, selected[30], in_range);
  let (end, carry) = add(&mut b, one, zero, &args[1][..32], &args[2][..32]);
  violations.push(b.and(selected[32], carry));
  let past_end = subtract(&mut b, one, zero, &a_len, &end).1;
  violations.push(b.and(selected[32], past_end));
  let (appended_len, carry) = add(&mut b, one, zero, &a_len, &b_len);
  violations.push(b.and(selected[31], carry));
  let shifted = shift(&mut b, one, zero, &a, &args[1][..32], true);
  let appended = shift(&mut b, one, zero, &rhs, &a_len, false);
  let appended: Vec<_> =
    a.iter().zip(appended).map(|(a, bits)| b.xor(&[*a, bits], one)).collect();
  let lengths_equal = equal(&mut b, one, &a_len, &b_len);
  let data_equal = equal(&mut b, one, &a, &rhs);
  let same = b.and(lengths_equal, data_equal);
  let array = flags(&mut b, one, &selected, &[11, 19, 31, 32, 34]);
  let four = constant_bits(one, zero, 4);
  let eight = constant_bits(one, zero, 8);
  let thirty_two = constant_bits(one, zero, 32);
  let length = choose(
    &mut b,
    one,
    zero,
    &[
      (selected[11], &four),
      (selected[19], &eight),
      (selected[31], &appended_len),
      (selected[32], &args[2][..32]),
      (selected[34], &thirty_two),
    ],
    32,
  );
  let maximum = constant_bits(one, zero, (gate.capacity.bytes() + 1) as u32);
  let fits = subtract(&mut b, one, zero, &length, &maximum).1;
  require(&mut b, one, &mut violations, one, fits);
  let id: Vec<_> = (256..288).collect();
  require_zero(
    &mut b,
    one,
    &mut violations,
    one,
    &(288..384).collect::<Vec<_>>(),
  );
  let entries = constant_bits(one, zero, gate.entries as u32);
  let allocated = subtract(&mut b, one, zero, &id, &entries).1;
  require(&mut b, one, &mut violations, one, allocated);
  let payload = choose(
    &mut b,
    one,
    zero,
    &[
      (array, &id),
      (selected[12], &a[..32]),
      (selected[20], &a[..64]),
      (selected[29], &a_len),
      (selected[30], &shifted[..8]),
      (selected[33], &[same]),
    ],
    128,
  );
  let word = flags(&mut b, one, &selected, &[12, 29, 30]);
  let word_tag = constant_bits(one, zero, WORD32_TAG as u32);
  let field_tag = constant_bits(one, zero, FIELD_TAG as u32);
  let bool_tag = constant_bits(one, zero, BOOL_TAG as u32);
  let byte_tag = constant_bits(one, zero, BYTES_TAG as u32);
  let tag = choose(
    &mut b,
    one,
    zero,
    &[
      (word, &word_tag),
      (selected[20], &field_tag),
      (selected[33], &bool_tag),
      (array, &byte_tag),
    ],
    128,
  );
  let mut value = tag.clone();
  value.extend_from_slice(&payload);
  cell_with_byte_handles(
    &mut b,
    one,
    &mut violations,
    byte,
    &value,
    gate.entries,
  );
  let hash: Vec<_> = (128 * (n - 2)..128 * n).collect();
  let data = choose(
    &mut b,
    one,
    zero,
    &[
      (selected[11], &args[0][..32]),
      (selected[19], &args[0][..64]),
      (selected[31], &appended),
      (selected[32], &shifted),
      (selected[34], &hash),
    ],
    a.len(),
  );
  let mut record = vec![zero; 128];
  record[..32].copy_from_slice(&length);
  record[32] = array;
  for (position, bits) in data.chunks(8).enumerate() {
    let boundary = constant_bits(one, zero, position as u32);
    let live = subtract(&mut b, one, zero, &boundary, &length).1;
    record.extend(bits.iter().map(|bit| b.and(live, *bit)));
  }
  b.write_xor(128 * n, &[byte], one);
  for bit in 0..256 {
    let source = b.and(scalar, bit);
    b.write_xor(128 * (n + 1) + bit, &[source], one);
  }
  for (bit, source) in value.iter().enumerate() {
    b.write_xor(128 * (n + 3) + bit, &[*source], one);
  }
  for (bit, source) in record.iter().enumerate() {
    b.write_xor(128 * (n + 5) + bit, &[*source], one);
  }
  let violation = any(&mut b, one, &violations);
  b.write_xor(128 * (n + 5 + gate.capacity.record_words()), &[violation], one);
  b.finish()
}
