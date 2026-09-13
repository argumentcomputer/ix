//! Untrusted typed row generation. Every unique table has one driver, sorted
//! in verifier-owned registry order, including every padding cell on reuse.

use super::{ByteCommitmentSlots, CompiledExec, ScalarMachineSlots};
use crate::{
  blake3_backend::Blake3CompressionSlots,
  extension::{self, GoldilocksLaneRepackGate},
  goldilocks::{self, CanonicalGoldilocksQuadGate, GoldilocksAddPairGate},
  hash::Blake3Gate,
  ixby::{
    byte_value::{BytePrimitiveGate, ByteReadGate},
    control::ControlStepGate,
    decode::{
      InputDecodeGate, OperandResolveGate, ProgramDecodeGate, ProgramFetchGate,
    },
    hash_control::{HashBlockGate, RootParamsGate},
    length::CheckedLengthAddGate,
    machine::{ActionAssembleGate, InitialStateGate, OutputEncodeGate},
    nat_value::NatDispatchGate,
    object_value::ObjectDispatchGate,
    primitive::{PrimitiveFinishGate, PrimitivePrepareGate},
    select::SelectWordsGate,
  },
  multiplication::{self, GoldilocksMulPairGate},
  packed_blake3::PackedWordGate,
};
use anyhow::{Result, ensure};
use flock_prover::{
  circuit::builder::{CircuitShape, CircuitWitness},
  prover::UnionSlotProverInput,
  r1cs::BlockR1cs,
  r1cs_hashes::blake3 as flock_blake3,
};

pub(super) fn tables(
  m: &ScalarMachineSlots,
  h: &ByteCommitmentSlots,
  shape: &CircuitShape,
  nu: usize,
) -> Result<Vec<BlockR1cs>> {
  let p = &m.primitive_slots;
  let common = &h.hashes()[0];
  let mut tables = vec![
    (m.program_slot.slot(), m.program_gate.r1cs()),
    (m.input_slot.slot(), m.input_gate.r1cs()),
    (m.fetch_slot.slot(), m.fetch_gate.r1cs()),
    (m.operand_slot.slot(), m.operand_gate.r1cs()),
    (p.prepare, m.primitive_gate.r1cs()),
    (p.finish, p.finish_gate.r1cs()),
    (p.arithmetic.add, goldilocks::build_goldilocks_add_r1cs(nu)),
    (p.arithmetic.mul, multiplication::build_goldilocks_mul_r1cs(nu)),
    (p.arithmetic.canonical, goldilocks::build_canonical_quad_r1cs(nu)),
    (p.arithmetic.repack, extension::build_lane_repack_r1cs(nu)),
    (m.action_slot.slot(), m.action_gate.r1cs()),
    (m.control_slot.slot(), m.control_gate.r1cs()),
    (m.initial_slot.slot(), m.initial_gate.r1cs()),
    (m.output_slot.slot(), m.output_gate.r1cs()),
    (common.select_slot(), common.select_gate().r1cs()),
    (common.root_slot(), common.root_gate().r1cs()),
    (h.length_slot().slot(), h.length_gate().r1cs()),
  ];
  tables.extend(common.compression().tables());
  if let Some(objects) = &m.objects {
    tables.push((objects.slot, objects.gate.r1cs()));
  }
  if let Some(nats) = &m.nats {
    tables.push((nats.slot, nats.gate.r1cs()));
  }
  if let Some(bytes) = &m.bytes {
    tables.extend([
      (bytes.read_slot.slot(), bytes.read_gate.r1cs()),
      (bytes.primitive_slot, bytes.primitive_gate.r1cs()),
      (bytes.select_slot.slot(), bytes.select_gate.r1cs()),
      (bytes.hash.block_slot(), bytes.hash.block_gate().r1cs()),
    ]);
  }
  tables.extend(
    h.hashes().iter().map(|hash| (hash.block_slot(), hash.block_gate().r1cs())),
  );
  tables.sort_by_key(|(slot, _)| shape.registry_slot(*slot));
  ensure!(tables.len() == shape.counts.len(), "Exec table coverage");
  for (index, (slot, r1cs)) in tables.iter().enumerate() {
    ensure!(shape.registry_slot(*slot) == index, "Exec table order/uniqueness");
    let ty = &shape.registry.types()[index];
    ensure!(
      r1cs.m == nu + ty.k_log
        && r1cs.k_log == ty.k_log
        && r1cs.useful_bits == ty.useful_bits
        && r1cs.const_pin == ty.const_pin,
      "Exec table geometry"
    );
    for (matrix, expected) in
      [(&r1cs.a_0, &ty.a_0), (&r1cs.b_0, &ty.b_0), (&r1cs.c_0, &ty.c_0)]
    {
      ensure!(
        matrix.num_rows == expected.num_rows
          && matrix.num_cols == expected.num_cols
          && matrix.rows == expected.rows,
        "Exec prover/verifier matrix mismatch"
      );
    }
  }
  Ok(tables.into_iter().map(|(_, table)| table).collect())
}

pub(super) fn drivers<'a>(
  compiled: &'a CompiledExec,
  witness: &'a CircuitWitness,
) -> Vec<UnionSlotProverInput<'a>> {
  let m = &compiled.machine;
  let h = &compiled.commitments;
  let common = &h.hashes()[0];
  let nu = compiled.nu;
  let mut drivers = Vec::new();
  macro_rules! gate {
    ($slot:expr, $ty:ty, $gate:expr) => {{
      let slot = $slot;
      let gate = $gate;
      let rows = witness.rows::<$ty>(slot);
      drivers.push((
        slot,
        UnionSlotProverInput::in_place(
          move |dst| gate.generate_witness_into(rows, dst),
          compiled.tables[compiled.shape.registry_slot(slot)]
            .csc_lincheck_circuit(),
        ),
      ));
    }};
  }
  macro_rules! native {
    ($slot:expr, $ty:ty, $generate:path) => {{
      let slot = $slot;
      let rows = witness.rows::<$ty>(slot);
      drivers.push((
        slot,
        UnionSlotProverInput::in_place(
          move |mut dst| {
            dst.elide_padding_writes = false;
            $generate(rows, nu, dst)
          },
          compiled.tables[compiled.shape.registry_slot(slot)]
            .csc_lincheck_circuit(),
        ),
      ));
    }};
  }
  gate!(m.program_slot.slot(), ProgramDecodeGate, &m.program_gate);
  gate!(m.input_slot.slot(), InputDecodeGate, &m.input_gate);
  gate!(m.fetch_slot.slot(), ProgramFetchGate, &m.fetch_gate);
  gate!(m.operand_slot.slot(), OperandResolveGate, &m.operand_gate);
  gate!(m.primitive_slots.prepare, PrimitivePrepareGate, &m.primitive_gate);
  gate!(
    m.primitive_slots.finish,
    PrimitiveFinishGate,
    &m.primitive_slots.finish_gate
  );
  gate!(m.action_slot.slot(), ActionAssembleGate, &m.action_gate);
  gate!(m.control_slot.slot(), ControlStepGate, &m.control_gate);
  gate!(m.initial_slot.slot(), InitialStateGate, &m.initial_gate);
  gate!(m.output_slot.slot(), OutputEncodeGate, &m.output_gate);
  if let Some(objects) = &m.objects {
    gate!(objects.slot, ObjectDispatchGate, &objects.gate);
  }
  if let Some(nats) = &m.nats {
    gate!(nats.slot, NatDispatchGate, &nats.gate);
  }
  let a = &m.primitive_slots.arithmetic;
  native!(
    a.add,
    GoldilocksAddPairGate,
    goldilocks::generate_goldilocks_add_witness_into
  );
  native!(
    a.mul,
    GoldilocksMulPairGate,
    multiplication::generate_goldilocks_mul_witness_into
  );
  native!(
    a.canonical,
    CanonicalGoldilocksQuadGate,
    goldilocks::generate_canonical_quad_witness_into
  );
  native!(
    a.repack,
    GoldilocksLaneRepackGate,
    extension::generate_lane_repack_witness_into
  );
  match common.compression() {
    Blake3CompressionSlots::LegacyOptionF { slot, .. } => {
      native!(
        *slot,
        Blake3Gate,
        flock_blake3::generate_witness_batch_major_partial_into
      );
    },
    Blake3CompressionSlots::PackedWordsV0(packed) => {
      for (word_gate, slot) in packed.gates() {
        gate!(*slot, PackedWordGate, word_gate);
      }
    },
  }
  gate!(common.select_slot(), SelectWordsGate, common.select_gate());
  gate!(common.root_slot(), RootParamsGate, common.root_gate());
  gate!(h.length_slot().slot(), CheckedLengthAddGate, h.length_gate());
  for hash in h.hashes() {
    gate!(hash.block_slot(), HashBlockGate, hash.block_gate());
  }
  if let Some(bytes) = &m.bytes {
    gate!(bytes.read_slot.slot(), ByteReadGate, &bytes.read_gate);
    gate!(bytes.primitive_slot, BytePrimitiveGate, &bytes.primitive_gate);
    gate!(bytes.select_slot.slot(), SelectWordsGate, &bytes.select_gate);
    gate!(bytes.hash.block_slot(), HashBlockGate, bytes.hash.block_gate());
  }
  drivers.sort_by_key(|(slot, _)| compiled.shape.registry_slot(*slot));
  assert_eq!(drivers.len(), compiled.shape.counts.len());
  for (index, (slot, _)) in drivers.iter().enumerate() {
    assert_eq!(compiled.shape.registry_slot(*slot), index);
  }
  drivers.into_iter().map(|(_, driver)| driver).collect()
}
