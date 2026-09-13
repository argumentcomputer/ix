//! Nat instructions are derived from fetched headers and authenticated
//! magnitude reads. `caseNat` appends its predecessor before the existing
//! ordered-frame branch step; it consumes no extra VM transition.
use super::{NatCapacity, arithmetic, bits::Synthesis, canonical_magnitude};
use crate::{
  boolean::{BooleanR1csPlan, generate_boolean_witness_into},
  ixby::{
    bits::{add, constant_bits, evaluate_words, fill_words, subtract},
    byte_value::ByteCapacity,
    control::ControlCapacities,
    decode::PrimitiveSet,
    value::{BOOL_TAG, NAT_TAG},
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
pub(crate) struct NatDispatchGate {
  nu: usize,
  pub capacity: NatCapacity,
  pub bytes: ByteCapacity,
  pub control: ControlCapacities,
  pub operands: usize,
  entries: usize,
  registry: PrimitiveSet,
  plan: Arc<OnceLock<BooleanR1csPlan>>,
}

#[derive(Clone, Debug)]
pub(crate) struct NatDispatchRow(pub Vec<F128>);

impl NatDispatchGate {
  pub(crate) fn new(
    nu: usize,
    values: (NatCapacity, ByteCapacity),
    control: ControlCapacities,
    operands: usize,
    entries: usize,
    registry: PrimitiveSet,
  ) -> Result<Self> {
    ensure!((3..=20).contains(&nu), "Nat row-domain admission");
    ensure!((1..=4).contains(&operands), "Nat operand capacity");
    ensure!((1..=16).contains(&control.locals), "Nat local capacity");
    ensure!(values.0.bytes() <= values.1.bytes(), "Nat magnitude arena width");
    crate::ixby::byte_value::validate_entries(entries)?;
    Ok(Self {
      nu,
      capacity: values.0,
      bytes: values.1,
      control,
      operands,
      entries,
      registry,
      plan: Arc::new(OnceLock::new()),
    })
  }
  pub(crate) fn plan(&self) -> &BooleanR1csPlan {
    self.plan.get_or_init(|| build(self))
  }
  pub(crate) fn r1cs(&self) -> BlockR1cs {
    self.plan().block_r1cs(self.nu)
  }
  pub(crate) fn generate_witness_into(
    &self,
    rows: &[NatDispatchRow],
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
  /// Outputs: updated frame, action headers, non-Nat evaluation headers,
  /// normalized arguments, primitive-result flag, arena-result flag, result
  /// cell, new magnitude record, residual.
  pub(crate) fn result_word(&self) -> usize {
    self.control.frame_words() + 6 + 2 * self.operands
  }
}

impl CountedGate for NatDispatchGate {
  fn input_count(&self) -> usize {
    self.control.frame_words()
      + 3
      + 2 * self.operands
      + 2 * self.bytes.record_words()
  }
  fn output_count(&self) -> usize {
    self.control.frame_words()
      + 9
      + 2 * self.operands
      + self.bytes.record_words()
  }
  fn table_at(&self, nu: usize) -> TableType {
    let mut gate = self.clone();
    gate.nu = nu;
    gate.table()
  }
}
impl GateType for NatDispatchGate {
  type Row = NatDispatchRow;
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
  fn eval(
    &self,
    inputs: &[F128],
    _: &(),
    outputs: &mut Vec<F128>,
  ) -> Self::Row {
    assert_eq!(inputs.len(), self.input_count());
    outputs.extend(evaluate_words(self.plan(), inputs, self.output_count()));
    NatDispatchRow(inputs.to_vec())
  }
  fn witness(&self, _: &[Self::Row], _: usize) -> SlotWitness {
    SlotWitness::DeferredToRows
  }
}

fn build(gate: &NatDispatchGate) -> BooleanR1csPlan {
  let bits = gate.capacity.bits().max(1);
  let mut s = Synthesis::new(
    gate.input_count(),
    gate.output_count(),
    32768
      + 40 * bits * bits
      + 2048 * (gate.bytes.bytes() + gate.control.locals),
  );
  let frame: Vec<_> = (0..128 * gate.control.frame_words()).collect();
  let header_base = frame.len();
  let headers: Vec<_> = (header_base..header_base + 256).collect();
  let allocation: Vec<_> = (header_base + 256..header_base + 384).collect();
  let args_base = header_base + 384;
  let args: Vec<_> = (args_base..args_base + 256 * gate.operands).collect();
  let first_base = args_base + args.len();
  let width = 128 * gate.bytes.record_words();
  let first: Vec<_> = (first_base..first_base + width).collect();
  let second: Vec<_> = (first_base + width..first_base + 2 * width).collect();
  let primitive = s.eq_const(&headers[32..64], 2);
  let case = s.eq_const(&headers[32..64], 10);
  let admitted = std::array::from_fn(|i| gate.registry.contains(35 + i as u8));
  let selected: [usize; 7] = std::array::from_fn(|i| {
    if !admitted[i] {
      return s.zero;
    }
    let code = s.eq_const(&headers[160..192], (35 + i) as u64);
    s.and(primitive, code)
  });
  let nat = s.sum(&selected);
  let handled = s.sum(&[nat, case]);
  let arity = s.eq_const(&headers[192..224], 2);
  s.require(nat, arity);
  let arity = s.eq_const(&headers[192..224], 1);
  s.require(case, arity);
  if gate.operands < 2 {
    s.violations.push(nat);
  }
  for (index, buffer) in [&first, &second].into_iter().enumerate() {
    let live = if index == 0 { handled } else { nat };
    let cell = if index < gate.operands {
      args[256 * index..256 * (index + 1)].to_vec()
    } else {
      vec![s.zero; 256]
    };
    let tag = s.eq_const(&cell[..64], NAT_TAG);
    s.require(live, tag);
    s.require_zero(live, &cell[64..128]);
    s.require_zero(live, &cell[160..]);
    let limit = constant_bits(s.one, s.zero, gate.entries as u32);
    let fits = subtract(&mut s.b, s.one, s.zero, &cell[128..160], &limit).1;
    s.require(live, fits);
    s.require_zero(s.one, &buffer[32..128]);
    canonical_magnitude(
      &mut s.b,
      s.one,
      s.zero,
      &mut s.violations,
      live,
      gate.capacity,
      buffer,
    );
    // No higher data can be hidden past an understated length.
    for (byte, data) in buffer[128..].chunks(8).enumerate() {
      let boundary = constant_bits(s.one, s.zero, byte as u32);
      let present =
        subtract(&mut s.b, s.one, s.zero, &boundary, &buffer[..32]).1;
      let padding = s.not(present);
      let padding = s.and(live, padding);
      s.require_zero(padding, data);
    }
  }
  for index in 1..gate.operands {
    s.require_zero(case, &args[256 * index..256 * (index + 1)]);
  }
  for index in 2..gate.operands {
    s.require_zero(nat, &args[256 * index..256 * (index + 1)]);
  }
  s.require_zero(s.one, &allocation[32..]);
  let limit = constant_bits(s.one, s.zero, gate.entries as u32);
  let fits = subtract(&mut s.b, s.one, s.zero, &allocation[..32], &limit).1;
  s.require(s.one, fits);
  let result = arithmetic::evaluate(
    &mut s,
    &first[128..128 + bits],
    &second[128..128 + bits],
    &selected,
    admitted,
  );
  let successor = s.and(case, result.nonzero);
  let zero_case = s.not(result.nonzero);
  let zero_case = s.and(case, zero_case);
  let number = s.sum(&selected[..5]);
  let boolean = s.sum(&selected[5..]);
  let stored = s.sum(&[number, successor]);
  let magnitude =
    s.choose(&[(s.one, &result.magnitude), (successor, &result.predecessor)]);
  s.require_zero(stored, &magnitude[gate.capacity.bits()..]);
  let length = arithmetic::magnitude_length(&mut s, &magnitude);
  let mut record = vec![s.zero; width];
  record[..32].copy_from_slice(&length);
  record[32] = stored;
  record[128..128 + bits].copy_from_slice(&magnitude);
  let nat_tag = s.constant(128, NAT_TAG);
  let bool_tag = s.constant(128, BOOL_TAG);
  let tag = s.choose(&[(number, &nat_tag), (boolean, &bool_tag)]);
  let mut cell = tag;
  let mut comparison = vec![s.zero; 128];
  comparison[0] = result.comparison;
  cell.extend(s.choose(&[(number, &allocation), (s.one, &comparison)]));

  let mut next_frame = frame.clone();
  let mut increment = vec![s.zero; 32];
  increment[0] = successor;
  let (length, carry) =
    add(&mut s.b, s.one, s.zero, &frame[64..96], &increment);
  let bad = s.and(case, carry);
  s.violations.push(bad);
  let maximum = constant_bits(s.one, s.zero, (gate.control.locals + 1) as u32);
  let fits = subtract(&mut s.b, s.one, s.zero, &length, &maximum).1;
  s.require(case, fits);
  next_frame[64..96].copy_from_slice(&length);
  let mut predecessor = nat_tag;
  predecessor.extend_from_slice(&allocation);
  for local in 0..gate.control.locals {
    let matched = s.eq_const(&frame[64..96], local as u64);
    let append = s.and(successor, matched);
    for (bit, source) in predecessor.iter().enumerate() {
      let position = 128 + 256 * local + bit;
      // Initial/control constraints require unused frame cells to be zero.
      let added = s.and(append, *source);
      next_frame[position] = s.sum(&[next_frame[position], added]);
    }
  }
  let mut branch_headers = headers.clone();
  branch_headers[32..64].copy_from_slice(&s.constant(32, 6));
  branch_headers[128..256].copy_from_slice(&s.constant(128, 0));
  // A branch has exactly one already resolved Bool argument.
  branch_headers[192..224].copy_from_slice(&s.constant(32, 1));
  let action_headers = s.mux(case, &branch_headers, &headers);
  let not_nat = s.not(nat);
  let evaluation_headers = s.mask(not_nat, &action_headers);
  let mut branch_args = vec![s.zero; args.len()];
  branch_args[..128].copy_from_slice(&bool_tag);
  branch_args[128] = zero_case;
  let normalized_args = s.mux(case, &branch_args, &args);
  let mut output = next_frame;
  output.extend(action_headers);
  output.extend(evaluation_headers);
  output.extend(normalized_args);
  output.extend(s.constant(128, 0));
  let flag_word = gate.result_word() - 2;
  output[128 * flag_word] = nat;
  output.extend(s.constant(128, 0));
  output[128 * (flag_word + 1)] = handled;
  output.extend(cell);
  output.extend(record);
  assert_eq!(output.len(), 128 * (gate.output_count() - 1));
  s.write(128 * gate.input_count(), &output);
  s.finish(128 * (gate.input_count() + gate.output_count() - 1))
}
