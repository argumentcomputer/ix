//! Constrained selector-based access to a bounded, canonically padded bank.
//!
//! The physical bank capacity is setup data. Its contents, live length, index,
//! and enable bit are wires and never select circuit topology. This is the
//! small-profile dynamic-access construction, not a scalable RAM argument.
//!
//! Control packing: index in bits 0..32, live length in 32..64, enable in bit
//! 64, and zeros in 65..128. Disabled reads require index zero and return zero.
//! Every cell outside the live prefix must be zero, even for a disabled read.
//! Enabled reads require index < live length <= capacity. All checks are in
//! the Boolean constraints; native evaluation only generates untrusted advice.

use anyhow::{Result, ensure};
use flock_prover::{
  circuit::builder::{GateType, SlotId, SlotWitness, Wire},
  field::F128,
  r1cs::BlockR1cs,
  schedule::{IoWord, TableType},
  union::SlotWitnessDest,
};
use std::sync::{Arc, OnceLock};

use crate::boolean::{
  BooleanR1csBuilder, BooleanR1csPlan, generate_boolean_witness_into,
  write_f128,
};
use crate::sizing::{CircuitEmitter, CountedGate};

const WORD_BITS: usize = 128;
const MAX_CAPACITY: usize = 32;

/// Capacity is explicit setup input, not an advice field or a gate wire.
#[derive(Clone, Debug)]
pub struct BankReadGate {
  nu: usize,
  capacity: usize,
  plan: Arc<OnceLock<BooleanR1csPlan>>,
}

#[derive(Clone, Debug)]
pub struct BankReadRow {
  control: F128,
  cells: Vec<F128>,
}

impl BankReadGate {
  pub fn new(nu: usize, capacity: usize) -> Result<Self> {
    ensure!((3..=20).contains(&nu), "bank row-domain admission");
    ensure!((1..=MAX_CAPACITY).contains(&capacity), "bank capacity admission");
    Ok(Self { nu, capacity, plan: Arc::new(OnceLock::new()) })
  }

  pub fn capacity(&self) -> usize {
    self.capacity
  }

  pub fn r1cs(&self) -> BlockR1cs {
    self.plan().block_r1cs(self.nu)
  }

  pub fn generate_witness_into(
    &self,
    rows: &[BankReadRow],
    mut dst: SlotWitnessDest<'_>,
  ) -> Vec<u8> {
    // The bounded interpreter contract uses canonical zero padding on every
    // invocation, including recycled buffers after a different execution.
    // Retaining the upstream elision hint made the second changed-access
    // proof fail zerocheck in the same process; the repeated-proof and poison
    // regressions pin this stronger initialization contract.
    dst.elide_padding_writes = false;
    generate_boolean_witness_into(self.plan(), rows, self.nu, dst, fill_free)
  }

  fn plan(&self) -> &BooleanR1csPlan {
    self.plan.get_or_init(|| build_plan(self.capacity))
  }
}

impl CountedGate for BankReadGate {
  fn input_count(&self) -> usize {
    self.capacity + 1
  }
  fn output_count(&self) -> usize {
    2
  }
  fn table_at(&self, nu: usize) -> TableType {
    let mut gate = self.clone();
    gate.nu = nu;
    gate.table()
  }
}

impl GateType for BankReadGate {
  type Row = BankReadRow;
  type Hint = ();

  fn table(&self) -> TableType {
    let mut schema: Vec<_> = (0..=self.capacity).map(IoWord::input).collect();
    schema.push(IoWord::output(self.capacity + 1));
    schema.push(IoWord::output(self.capacity + 2));
    crate::boolean::table_from_block_r1cs(self.r1cs()).with_io_schema(schema)
  }

  fn eval(
    &self,
    inputs: &[F128],
    _hint: &(),
    outputs: &mut Vec<F128>,
  ) -> Self::Row {
    assert_eq!(inputs.len(), self.capacity + 1, "fixed bank input width");
    let row = BankReadRow { control: inputs[0], cells: inputs[1..].to_vec() };
    let (selected, violation) = evaluate(&row);
    outputs.extend([selected, F128::new(u64::from(violation), 0)]);
    row
  }

  fn witness(&self, _rows: &[Self::Row], _nu: usize) -> SlotWitness {
    SlotWitness::DeferredToRows
  }
}

/// Interpreter call sites use this wrapper so no validity residual is dropped.
/// The zero word is verifier-owned; it is not supplied by the witness.
#[derive(Clone, Copy, Debug)]
pub struct BankReadSlot {
  slot: SlotId,
  zero: Wire,
  capacity: usize,
}

impl BankReadSlot {
  pub fn declare(
    builder: &mut impl CircuitEmitter,
    gate: BankReadGate,
  ) -> Self {
    let capacity = gate.capacity;
    let slot = builder.slot(gate);
    let zero = builder.fixed_public_input(F128::ZERO);
    Self { slot, zero, capacity }
  }

  pub fn slot(&self) -> SlotId {
    self.slot
  }

  pub fn read(
    &self,
    builder: &mut impl CircuitEmitter,
    control: Wire,
    cells: &[Wire],
  ) -> Wire {
    assert_eq!(cells.len(), self.capacity, "fixed bank wiring width");
    let mut inputs = Vec::with_capacity(self.capacity + 1);
    inputs.push(control);
    inputs.extend_from_slice(cells);
    let outputs = builder.gate(self.slot, &inputs);
    builder.connect(outputs[1], self.zero);
    outputs[0]
  }
}

pub fn control(index: u32, length: u32, enabled: bool) -> F128 {
  F128::new(u64::from(index) | (u64::from(length) << 32), u64::from(enabled))
}

fn fill_free(row: &BankReadRow, bits: &mut [bool]) {
  write_f128(bits, 0, row.control);
  for (index, value) in row.cells.iter().enumerate() {
    write_f128(bits, (index + 1) * WORD_BITS, *value);
  }
}

fn evaluate(row: &BankReadRow) -> (F128, bool) {
  let index = row.control.lo as u32 as usize;
  let length = (row.control.lo >> 32) as usize;
  let enabled = row.control.hi & 1 == 1;
  let selected = if enabled {
    row.cells.get(index).copied().unwrap_or(F128::ZERO)
  } else {
    F128::ZERO
  };
  let violation = row.control.hi & !1 != 0
    || length > row.cells.len()
    || (!enabled && index != 0)
    || (enabled && index >= length)
    || row.cells.iter().skip(length).any(|value| *value != F128::ZERO);
  (selected, violation)
}

fn equal_u32_constant(
  builder: &mut BooleanR1csBuilder,
  one: usize,
  base: usize,
  constant: usize,
) -> usize {
  let mut equal = one;
  for bit in 0..32 {
    equal = if constant & (1 << bit) != 0 {
      builder.and(equal, base + bit)
    } else {
      builder.product_of_parities(&[equal], &[base + bit, one])
    };
  }
  equal
}

fn any(builder: &mut BooleanR1csBuilder, one: usize, bits: &[usize]) -> usize {
  let mut none = one;
  for bit in bits {
    none = builder.product_of_parities(&[none], &[*bit, one]);
  }
  builder.xor(&[none, one], one)
}

fn build_plan(capacity: usize) -> BooleanR1csPlan {
  let reserved = (capacity + 3) * WORD_BITS;
  // Upper bound for this fixed synthesis, including all length/index bits,
  // padding checks and OR chains. Unallocated columns are constrained zero.
  let columns = reserved + 360 * capacity + 256;
  let k_log = columns.next_power_of_two().ilog2() as usize;
  let mut builder = BooleanR1csBuilder::new(k_log, reserved);
  for column in 0..(capacity + 1) * WORD_BITS {
    builder.free_boolean_at(column);
  }
  let one = builder.alloc_constant_one();
  let enabled = 64;
  let lengths: Vec<_> = (0..=capacity)
    .map(|length| equal_u32_constant(&mut builder, one, 32, length))
    .collect();
  let valid_length = builder.xor(&lengths, one);
  let mut violations: Vec<_> = (65..128).collect();
  violations.push(builder.xor(&[valid_length, one], one));

  let index_nonzero = any(&mut builder, one, &(0..32).collect::<Vec<_>>());
  let disabled = builder.xor(&[enabled, one], one);
  violations.push(builder.and(disabled, index_nonzero));

  let mut selected = Vec::with_capacity(capacity);
  let mut selected_live = Vec::with_capacity(capacity);
  for index in 0..capacity {
    let matches = equal_u32_constant(&mut builder, one, 0, index);
    let select = builder.and(enabled, matches);
    selected.push(select);
    // Exactly one length can match a full 32-bit word, so this parity is a
    // prefix mask, not an untrusted one-hot witness.
    let live = builder.xor(&lengths[index + 1..], one);
    selected_live.push(builder.and(select, live));
    let padding = builder.xor(&[live, one], one);
    let base = (index + 1) * WORD_BITS;
    let nonzero =
      any(&mut builder, one, &(base..base + WORD_BITS).collect::<Vec<_>>());
    violations.push(builder.and(padding, nonzero));
  }
  selected_live.push(enabled);
  violations.push(builder.xor(&selected_live, one));
  let selected_base = (capacity + 1) * WORD_BITS;
  for bit in 0..WORD_BITS {
    let products: Vec<_> = selected
      .iter()
      .enumerate()
      .map(|(index, mask)| builder.and(*mask, (index + 1) * WORD_BITS + bit))
      .collect();
    builder.write_xor(selected_base + bit, &products, one);
  }
  let violation = any(&mut builder, one, &violations);
  builder.write_xor((capacity + 2) * WORD_BITS, &[violation], one);
  builder.finish()
}

#[cfg(test)]
#[path = "access_proof_tests.rs"]
mod proof_tests;

#[cfg(test)]
mod tests {
  use super::*;

  fn row(
    capacity: usize,
    length: usize,
    index: u32,
    enabled: bool,
  ) -> BankReadRow {
    BankReadRow {
      control: control(index, length as u32, enabled),
      cells: (0..capacity)
        .map(|i| {
          if i < length {
            F128::new(11 + i as u64, 101 + i as u64)
          } else {
            F128::ZERO
          }
        })
        .collect(),
    }
  }

  fn logical(gate: &BankReadGate, row: &BankReadRow) -> Vec<bool> {
    let mut bits = vec![false; gate.plan().k()];
    gate.plan().fill_row(&mut bits, |bits| fill_free(row, bits));
    let (selected, violation) = evaluate(row);
    let mut expected = vec![false; 2 * WORD_BITS];
    write_f128(&mut expected, 0, selected);
    write_f128(&mut expected, WORD_BITS, F128::new(u64::from(violation), 0));
    assert_eq!(
      &bits[(gate.capacity + 1) * WORD_BITS..(gate.capacity + 3) * WORD_BITS],
      expected
    );
    bits
  }

  fn satisfies(gate: &BankReadGate, logical: &[bool]) -> bool {
    let r1cs = gate.r1cs();
    let mut witness = vec![false; r1cs.n()];
    witness[..logical.len()].copy_from_slice(logical);
    r1cs.satisfies(&witness)
  }

  fn assert_rejected(gate: &BankReadGate, row: &BankReadRow) {
    let mut bits = logical(gate, row);
    assert!(satisfies(gate, &bits)); // The residual is a computed output.
    assert!(bits[(gate.capacity + 2) * WORD_BITS]);
    bits[(gate.capacity + 2) * WORD_BITS] = false; // Verifier-owned zero pin.
    assert!(!satisfies(gate, &bits));
  }

  #[test]
  fn all_capacities_lengths_and_indices_match_checked_prefix_access() {
    for capacity in [1, 2, 3, 4, 7, 16, 32] {
      let gate = BankReadGate::new(3, capacity).unwrap();
      for length in 0..=capacity {
        for index in 0..length {
          let row = row(capacity, length, index as u32, true);
          let bits = logical(&gate, &row);
          assert!(satisfies(&gate, &bits));
          assert!(!bits[(capacity + 2) * WORD_BITS]);
          let mut expected = vec![false; WORD_BITS];
          write_f128(&mut expected, 0, row.cells[index]);
          assert_eq!(
            &bits[(capacity + 1) * WORD_BITS..(capacity + 2) * WORD_BITS],
            expected
          );
        }
        let row = row(capacity, length, 0, false);
        let bits = logical(&gate, &row);
        assert!(satisfies(&gate, &bits));
        assert!(
          bits[(capacity + 1) * WORD_BITS..(capacity + 3) * WORD_BITS]
            .iter()
            .all(|b| !b)
        );
      }
    }
  }

  #[test]
  fn hostile_metadata_and_padding_fail_even_with_recomputed_internal_advice() {
    let gate = BankReadGate::new(3, 4).unwrap();
    for index in [0, 1, 3, 4, 31, 32, 1 << 16, 1 << 31, u32::MAX] {
      assert_rejected(&gate, &row(4, 0, index, true));
    }
    for index in [2, 3, 4, 1 << 31, u32::MAX] {
      assert_rejected(&gate, &row(4, 2, index, true));
    }
    for length in [5, 32, 1 << 16, 1 << 31, u32::MAX as usize] {
      assert_rejected(&gate, &row(4, length, 0, true));
    }
    assert_rejected(&gate, &row(4, 2, 1, false));
    for bit in 1..64 {
      let mut bad = row(4, 2, 0, true);
      bad.control.hi |= 1 << bit;
      assert_rejected(&gate, &bad);
    }
    for enabled in [false, true] {
      for bit in 0..128 {
        let mut bad = row(4, 2, 0, enabled);
        bad.cells[3] = if bit < 64 {
          F128::new(1 << bit, 0)
        } else {
          F128::new(0, 1 << (bit - 64))
        };
        assert_rejected(&gate, &bad);
      }
    }
  }

  #[test]
  fn forged_outputs_and_nonzero_padding_columns_are_constrained() {
    let gate = BankReadGate::new(3, 3).unwrap();
    let row = row(3, 3, 2, true);
    let good = logical(&gate, &row);
    for bit in 0..128 {
      let mut bad = good.clone();
      bad[(gate.capacity + 1) * WORD_BITS + bit] ^= true;
      assert!(!satisfies(&gate, &bad));
    }
    for bit in [1, 63, 127] {
      let mut bad = good.clone();
      bad[(gate.capacity + 2) * WORD_BITS + bit] = true;
      assert!(!satisfies(&gate, &bad));
    }
    let mut bad = good;
    bad[gate.plan().k() - 1] = true;
    assert!(!satisfies(&gate, &bad));
  }

  #[test]
  fn setup_is_capacity_only_and_rejects_unsupported_bounds() {
    assert!(BankReadGate::new(3, 0).is_err());
    assert!(BankReadGate::new(3, 33).is_err());
    assert!(BankReadGate::new(2, 4).is_err());
    assert!(BankReadGate::new(21, 4).is_err());
    let first = BankReadGate::new(3, 4).unwrap();
    let second = BankReadGate::new(3, 4).unwrap();
    let a = first.r1cs();
    let b = second.r1cs();
    assert_eq!(a.k_log, b.k_log);
    assert_eq!(a.useful_bits, b.useful_bits);
    assert_eq!(a.a_0.rows, b.a_0.rows);
    assert_eq!(a.b_0.rows, b.b_0.rows);
  }

  #[test]
  fn census_preserves_capacity_without_materializing_tables() {
    use crate::sizing::CountingEmitter;
    use flock_prover::circuit::builder::ShapeBuilder;
    for capacity in [1, 3, 8, 32] {
      let gate = BankReadGate::new(3, capacity).unwrap();
      let mut count = CountingEmitter::new();
      let counted = BankReadSlot::declare(&mut count, gate.clone());
      let control = count.input();
      let cells: Vec<_> = (0..capacity).map(|_| count.input()).collect();
      let output = counted.read(&mut count, control, &cells);
      count.publish(output);
      assert!(gate.plan.get().is_none(), "count pass allocated a table");

      let mut builder = ShapeBuilder::new(3);
      let compiled = BankReadSlot::declare(&mut builder, gate.clone());
      let control = builder.input();
      let cells: Vec<_> = (0..capacity).map(|_| builder.input()).collect();
      let output = compiled.read(&mut builder, control, &cells);
      builder.publish(output);
      let shape = builder.finish().unwrap();
      count.ensure_matches(&shape).unwrap();
      let (registry, counts) = count.registry(3);
      assert_eq!(counts, shape.counts);
      assert_eq!(
        registry.types()[0].a_0.rows,
        shape.registry.types()[0].a_0.rows
      );
      assert_eq!(
        registry.types()[0].b_0.rows,
        shape.registry.types()[0].b_0.rows
      );
      assert_eq!(
        registry.types()[0].io_schema,
        shape.registry.types()[0].io_schema
      );
    }
  }

  #[test]
  fn in_place_witness_overwrites_poison_and_clears_all_unused_rows() {
    use crate::boolean::generate_boolean_witness;
    let gate = BankReadGate::new(3, 4).unwrap();
    for rows in [vec![], vec![row(4, 3, 2, true)], vec![row(4, 0, 0, false); 3]]
    {
      let expected = generate_boolean_witness(gate.plan(), &rows, 3, fill_free);
      let poison = F128::new(u64::MAX, u64::MAX);
      for elide_padding_writes in [false, true] {
        let mut z = vec![poison; expected.0.len()];
        let mut a = z.clone();
        let mut b = z.clone();
        let stripe = gate.generate_witness_into(
          &rows,
          SlotWitnessDest {
            z: &mut z,
            a: &mut a,
            b: &mut b,
            elide_padding_writes,
          },
        );
        assert_eq!((z.clone(), a, b, stripe), expected);
        for column in 0..gate.plan().k() / WORD_BITS {
          for unused in rows.len()..8 {
            assert_eq!(z[column * 8 + unused], F128::ZERO);
          }
        }
      }
    }
  }
}
