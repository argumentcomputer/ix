//! Constrained length, position, flags and padding for a fixed BLAKE3 block
//! schedule. Capacity is setup data; the actual byte length is a private wire.
//! Metadata and padding checks are not delegated to the host hash function.

use super::bits::{any, constant_bits, equal_constant, not, or, subtract};
use crate::{
  boolean::{
    BooleanR1csBuilder, BooleanR1csPlan, generate_boolean_witness_into,
    write_f128,
  },
  hash::{CHUNK_END, CHUNK_START, pack_params},
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

pub const MAX_HASH_CAPACITY: usize = 16 * 1024 * 1024;

#[derive(Clone, Debug)]
pub struct HashBlockGate {
  nu: usize,
  capacity: usize,
  plan: Arc<OnceLock<BooleanR1csPlan>>,
}

#[derive(Clone, Debug)]
pub struct HashBlockRow([F128; 6]);

impl HashBlockGate {
  pub fn new(nu: usize, capacity: usize) -> Result<Self> {
    ensure!((3..=20).contains(&nu), "hash block row-domain admission");
    ensure!(capacity <= MAX_HASH_CAPACITY, "hash byte capacity admission");
    Ok(Self { nu, capacity, plan: Arc::new(OnceLock::new()) })
  }
  pub fn blocks(&self) -> usize {
    self.capacity.div_ceil(64).max(1)
  }
  fn plan(&self) -> &BooleanR1csPlan {
    self.plan.get_or_init(|| build_plan(self.capacity))
  }
  pub fn r1cs(&self) -> BlockR1cs {
    self.plan().block_r1cs(self.nu)
  }
  pub fn generate_witness_into(
    &self,
    rows: &[HashBlockRow],
    mut dst: SlotWitnessDest<'_>,
  ) -> Vec<u8> {
    dst.elide_padding_writes = false;
    generate_boolean_witness_into(
      self.plan(),
      rows,
      self.nu,
      dst,
      |row, bits| {
        for (word, value) in row.0.iter().enumerate() {
          write_f128(bits, word * 128, *value);
        }
      },
    )
  }
}

impl CountedGate for HashBlockGate {
  fn input_count(&self) -> usize {
    6
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

impl GateType for HashBlockGate {
  type Row = HashBlockRow;
  type Hint = ();
  fn table(&self) -> TableType {
    let mut schema: Vec<_> = (0..6).map(IoWord::input).collect();
    schema.extend((6..9).map(IoWord::output));
    crate::boolean::table_from_block_r1cs(self.r1cs()).with_io_schema(schema)
  }
  fn eval(
    &self,
    inputs: &[F128],
    _: &(),
    outputs: &mut Vec<F128>,
  ) -> Self::Row {
    let row = HashBlockRow(inputs.try_into().expect("fixed hash block width"));
    outputs.extend(evaluate(self.capacity, &row));
    row
  }
  fn witness(&self, _: &[Self::Row], _: usize) -> SlotWitness {
    SlotWitness::DeferredToRows
  }
}

/// The fixed schedule binds the residual to a verifier-owned zero. Callers
/// provide the block position as a fixed wire, not as a trace-derived value.
#[derive(Clone, Copy, Debug)]
pub struct HashBlockSlot {
  slot: SlotId,
  zero: Wire,
}

impl HashBlockSlot {
  pub fn declare(b: &mut impl CircuitEmitter, gate: HashBlockGate) -> Self {
    Self { slot: b.slot(gate), zero: b.fixed_public_input(F128::ZERO) }
  }
  pub fn slot(&self) -> SlotId {
    self.slot
  }
  pub fn block(
    &self,
    b: &mut impl CircuitEmitter,
    length: Wire,
    index: Wire,
    message: [Wire; 4],
  ) -> (Wire, Wire) {
    let output = b.gate(
      self.slot,
      &[length, index, message[0], message[1], message[2], message[3]],
    );
    b.connect(output[2], self.zero);
    (output[0], output[1])
  }
}

fn evaluate(capacity: usize, row: &HashBlockRow) -> [F128; 3] {
  let length = row.0[0].lo as u32 as u64;
  let index = row.0[1].lo as u32 as u64;
  // Invalid wide indices still have a deterministic low-word result; their
  // range violation is constrained, so this cannot admit a wrapped offset.
  let offset = (index << 6) & u64::from(u32::MAX);
  let remaining = length.saturating_sub(offset);
  let block_len = remaining.min(64);
  let active = index == 0 || length > offset;
  let flags = if index & 15 == 0 { CHUNK_START } else { 0 }
    | if index & 15 == 15 || remaining <= 64 { CHUNK_END } else { 0 };
  let mut violation =
    row.0[..2].iter().any(|word| word.hi != 0 || word.lo >> 32 != 0)
      || length > capacity as u64
      || index >= capacity.div_ceil(64).max(1) as u64;
  for (word, value) in row.0[2..].iter().enumerate() {
    let packed = [value.lo.to_le_bytes(), value.hi.to_le_bytes()].concat();
    for (byte, value) in packed.iter().enumerate() {
      violation |= word * 16 + byte >= block_len as usize && *value != 0;
    }
  }
  [
    pack_params(index >> 4, block_len as u32, flags),
    F128::new(u64::from(active), 0),
    F128::new(u64::from(violation), 0),
  ]
}

fn build_plan(capacity: usize) -> BooleanR1csPlan {
  const PARAMS: usize = 6 * 128;
  const ACTIVE: usize = 7 * 128;
  const VIOLATION: usize = 8 * 128;
  let mut b = BooleanR1csBuilder::new(12, 9 * 128);
  for bit in 0..6 * 128 {
    b.free_boolean_at(bit);
  }
  let one = b.alloc_constant_one();
  let zero = b.xor(&[one, one], one);
  let length: Vec<_> = (0..32).collect();
  let index: Vec<_> = (128..160).collect();
  let mut offset = vec![zero; 6];
  offset.extend_from_slice(&index[..26]);
  let (difference, borrow) = subtract(&mut b, one, zero, &length, &offset);
  let not_borrow = not(&mut b, one, borrow);
  let mut violations: Vec<_> = (32..128).chain(160..256).collect();
  let maximum = constant_bits(one, zero, capacity as u32);
  let (_, length_too_large) = subtract(&mut b, one, zero, &maximum, &length);
  violations.push(length_too_large);
  let blocks = constant_bits(one, zero, capacity.div_ceil(64).max(1) as u32);
  let (_, index_in_range) = subtract(&mut b, one, zero, &index, &blocks);
  violations.push(not(&mut b, one, index_in_range));
  let first = equal_constant(&mut b, one, &index, 0);
  let nonzero = any(&mut b, one, &difference);
  let positive = b.and(not_borrow, nonzero);
  let active = or(&mut b, one, first, positive);
  b.write_xor(ACTIVE, &[active], one);

  let at_least_64 = any(&mut b, one, &difference[6..]);
  let under_64 = not(&mut b, one, at_least_64);
  let short = b.and(not_borrow, under_64);
  let mut block_len: Vec<_> =
    difference[..6].iter().map(|bit| b.and(short, *bit)).collect();
  block_len.push(b.and(not_borrow, at_least_64));
  for (bit, source) in block_len.iter().enumerate() {
    b.write_xor(PARAMS + 64 + bit, &[*source], one);
  }
  for (bit, source) in index[4..].iter().enumerate() {
    b.write_xor(PARAMS + bit, &[*source], one);
  }
  let start = equal_constant(&mut b, one, &index[..4], 0);
  let chunk_last = equal_constant(&mut b, one, &index[..4], 15);
  let upper = any(&mut b, one, &difference[7..]);
  let lower = any(&mut b, one, &difference[..6]);
  let extra = b.and(difference[6], lower);
  let greater_64 = or(&mut b, one, upper, extra);
  let within_64 = not(&mut b, one, greater_64);
  let final_block = or(&mut b, one, borrow, within_64);
  let end = or(&mut b, one, chunk_last, final_block);
  b.write_xor(PARAMS + 96, &[start], one);
  b.write_xor(PARAMS + 97, &[end], one);

  let counts: Vec<_> =
    (0..=64).map(|n| equal_constant(&mut b, one, &block_len, n)).collect();
  for byte in 0..64 {
    let live = b.xor(&counts[byte + 1..], one);
    let padding = not(&mut b, one, live);
    let nonzero =
      any(&mut b, one, &(256 + byte * 8..264 + byte * 8).collect::<Vec<_>>());
    violations.push(b.and(padding, nonzero));
  }
  let violation = any(&mut b, one, &violations);
  b.write_xor(VIOLATION, &[violation], one);
  b.finish()
}

/// ROOT output uses counter zero even when the selected chunk output retained
/// a chunk counter. Setting the ROOT bit is part of the circuit, not host advice.
#[derive(Clone, Copy, Debug)]
pub struct RootParamsGate {
  pub nu: usize,
}

#[derive(Clone, Copy, Debug)]
pub struct RootParamsRow(F128);

fn root_plan() -> &'static BooleanR1csPlan {
  static PLAN: OnceLock<BooleanR1csPlan> = OnceLock::new();
  PLAN.get_or_init(|| {
    let mut b = BooleanR1csBuilder::new(9, 256);
    for bit in 0..128 {
      b.free_boolean_at(bit);
    }
    let one = b.alloc_constant_one();
    for bit in 64..128 {
      b.write_xor(128 + bit, &[if bit == 99 { one } else { bit }], one);
    }
    b.finish()
  })
}

impl RootParamsGate {
  pub fn r1cs(&self) -> BlockR1cs {
    root_plan().block_r1cs(self.nu)
  }
  pub fn generate_witness_into(
    &self,
    rows: &[RootParamsRow],
    mut dst: SlotWitnessDest<'_>,
  ) -> Vec<u8> {
    dst.elide_padding_writes = false;
    generate_boolean_witness_into(
      root_plan(),
      rows,
      self.nu,
      dst,
      |row, bits| write_f128(bits, 0, row.0),
    )
  }
}
impl CountedGate for RootParamsGate {
  fn input_count(&self) -> usize {
    1
  }
  fn output_count(&self) -> usize {
    1
  }
  fn table_at(&self, nu: usize) -> TableType {
    Self { nu }.table()
  }
}
impl GateType for RootParamsGate {
  type Row = RootParamsRow;
  type Hint = ();
  fn table(&self) -> TableType {
    crate::boolean::table_from_block_r1cs(self.r1cs())
      .with_io_schema(vec![IoWord::input(0), IoWord::output(1)])
  }
  fn eval(
    &self,
    inputs: &[F128],
    _: &(),
    outputs: &mut Vec<F128>,
  ) -> Self::Row {
    assert_eq!(inputs.len(), 1);
    outputs.push(F128::new(0, inputs[0].hi | (8 << 32)));
    RootParamsRow(inputs[0])
  }
  fn witness(&self, _: &[Self::Row], _: usize) -> SlotWitness {
    SlotWitness::DeferredToRows
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::hash::pack_bytes;

  fn row(length: u32, index: u32) -> HashBlockRow {
    let offset = u64::from(index) * 64;
    let live = u64::from(length).saturating_sub(offset).min(64) as usize;
    let bytes: [u8; 64] =
      std::array::from_fn(|i| if i < live { (i * 17 + 1) as u8 } else { 0 });
    let words: [F128; 4] =
      std::array::from_fn(|i| pack_bytes(&bytes[i * 16..(i + 1) * 16]));
    HashBlockRow([
      F128::new(u64::from(length), 0),
      F128::new(u64::from(index), 0),
      words[0],
      words[1],
      words[2],
      words[3],
    ])
  }

  fn logical(gate: &HashBlockGate, row: &HashBlockRow) -> Vec<bool> {
    let mut bits = vec![false; gate.plan().k()];
    gate.plan().fill_row(&mut bits, |bits| {
      for (word, value) in row.0.iter().enumerate() {
        write_f128(bits, word * 128, *value);
      }
    });
    let mut expected = vec![false; 384];
    for (word, value) in evaluate(gate.capacity, row).iter().enumerate() {
      write_f128(&mut expected, word * 128, *value);
    }
    assert_eq!(&bits[768..1152], expected);
    bits
  }

  fn satisfies(r1cs: &BlockR1cs, bits: &[bool]) -> bool {
    let mut full = vec![false; r1cs.n()];
    full[..bits.len()].copy_from_slice(bits);
    r1cs.satisfies(&full)
  }

  fn rejected(gate: &HashBlockGate, r1cs: &BlockR1cs, row: &HashBlockRow) {
    let mut bits = logical(gate, row);
    assert!(satisfies(r1cs, &bits));
    assert!(bits[1024]);
    bits[1024] = false;
    assert!(!satisfies(r1cs, &bits));
  }

  #[test]
  fn lengths_positions_and_chunk_flags_match_at_all_boundaries() {
    for capacity in
      [0, 1, 63, 64, 65, 1023, 1024, 1025, 4097, MAX_HASH_CAPACITY]
    {
      let gate = HashBlockGate::new(3, capacity).unwrap();
      let r1cs = gate.r1cs();
      for length in [0, 1, 63, 64, 65, 1023, 1024, 1025, 2048, capacity] {
        if length > capacity {
          continue;
        }
        for index in [0, 1, 14, 15, 16, 17, 31, 32, gate.blocks() - 1] {
          if index >= gate.blocks() {
            continue;
          }
          let bits = logical(&gate, &row(length as u32, index as u32));
          assert!(satisfies(&r1cs, &bits));
          assert!(!bits[1024]);
        }
      }
    }
  }

  #[test]
  fn wide_metadata_and_every_nonzero_padding_bit_are_rejected_in_constraints() {
    let gate = HashBlockGate::new(3, 1025).unwrap();
    let r1cs = gate.r1cs();
    for length in [1026, 65536, 1 << 31, u32::MAX] {
      rejected(&gate, &r1cs, &row(length, 0));
    }
    for index in [17, 32, 1 << 26, 1 << 31, u32::MAX] {
      rejected(&gate, &r1cs, &row(1, index));
    }
    for word in 0..2 {
      for bit in 32..128 {
        let mut bad = row(1, 0);
        if bit < 64 {
          bad.0[word].lo |= 1 << bit;
        } else {
          bad.0[word].hi |= 1 << (bit - 64);
        }
        rejected(&gate, &r1cs, &bad);
      }
    }
    for index in [0, 16] {
      for bit in 0..512 {
        let mut bad = row(0, index);
        let word = 2 + bit / 128;
        if bit % 128 < 64 {
          bad.0[word].lo = 1 << (bit % 128);
        } else {
          bad.0[word].hi = 1 << (bit % 128 - 64);
        }
        rejected(&gate, &r1cs, &bad);
      }
    }
  }

  #[test]
  fn every_parameter_active_and_residual_bit_is_constrained() {
    let gate = HashBlockGate::new(3, 1025).unwrap();
    let r1cs = gate.r1cs();
    let good = logical(&gate, &row(1025, 16));
    for bit in 768..1152 {
      let mut bad = good.clone();
      bad[bit] ^= true;
      assert!(!satisfies(&r1cs, &bad));
    }
    let mut bad = good;
    bad[gate.plan().k() - 1] = true;
    assert!(!satisfies(&r1cs, &bad));
    assert!(HashBlockGate::new(3, MAX_HASH_CAPACITY + 1).is_err());
    assert!(HashBlockGate::new(2, 64).is_err());
    assert!(HashBlockGate::new(21, 64).is_err());
  }

  #[test]
  fn root_conversion_resets_counter_and_constrains_every_output_bit() {
    let gate = RootParamsGate { nu: 3 };
    let r1cs = gate.r1cs();
    for input in
      [F128::ZERO, pack_params(17, 1, 3), F128::new(u64::MAX, u64::MAX)]
    {
      let mut output = Vec::new();
      let row = gate.eval(&[input], &(), &mut output);
      let mut bits = vec![false; root_plan().k()];
      root_plan().fill_row(&mut bits, |bits| write_f128(bits, 0, row.0));
      let mut expected = vec![false; 128];
      write_f128(&mut expected, 0, output[0]);
      assert_eq!(&bits[128..256], expected);
      assert!(satisfies(&r1cs, &bits));
      for bit in 128..256 {
        let mut bad = bits.clone();
        bad[bit] ^= true;
        assert!(!satisfies(&r1cs, &bad));
      }
    }
  }

  #[test]
  fn both_hash_control_drivers_clear_recycled_padding_and_constant_stripes() {
    let gate = HashBlockGate::new(3, 1025).unwrap();
    for rows in [vec![], vec![row(0, 0)], vec![row(1025, 16); 3]] {
      crate::ixby::test_support::padding(
        gate.plan(),
        &rows,
        |row, bits| {
          for (word, value) in row.0.iter().enumerate() {
            write_f128(bits, word * 128, *value);
          }
        },
        |dst| gate.generate_witness_into(&rows, dst),
      );
    }
    let root = RootParamsGate { nu: 3 };
    for rows in [
      vec![],
      vec![RootParamsRow(F128::ZERO)],
      vec![RootParamsRow(pack_params(17, 64, 4)); 3],
    ] {
      crate::ixby::test_support::padding(
        root_plan(),
        &rows,
        |row, bits| write_f128(bits, 0, row.0),
        |dst| root.generate_witness_into(&rows, dst),
      );
    }
  }
}
