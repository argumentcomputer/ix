use super::*;
use crate::{
  extension::{self, GoldilocksLaneRepackGate},
  goldilocks::{self, CanonicalGoldilocksQuadGate, GoldilocksAddPairGate},
  hash::Blake3Gate,
  ixby::{
    auth_memory::{MemoryGate, multi::MultiGate},
    decode::PrimitiveSet,
    execution_order::OrderGate,
    ixbf_decode::paged::proof_support::{Driver, driver},
    memory_log::{AuditGate, BooleanSwitchGate, RecordPackingGate},
    paged_code::CodeGate,
    paged_frame::FrameGate,
    paged_nat::Nat128Gate,
    paged_primitive::PrimitiveRouteGate,
    primitive::{PrimitiveFinishGate, PrimitivePrepareGate},
    select::SelectWordsGate,
    wide_fuel::Fuel64StepGate,
  },
  multiplication::{self, GoldilocksMulPairGate},
};
use anyhow::{Result, ensure};
use flock_prover::{
  circuit::builder::CircuitShape, r1cs_hashes::blake3 as flock_blake3,
};
pub(super) fn drivers(
  emission: &BatchEmission,
  shape: &CircuitShape,
) -> Result<Vec<Box<dyn Driver>>> {
  let nu = emission.class.nu();
  let mut result = Vec::new();
  for (slot, gate) in emission.execution.gates() {
    result.push(driver(
      slot,
      gate.clone(),
      gate.r1cs(),
      MicroGate::generate_witness_into,
    ));
  }
  for (slot, gate) in emission.execution.code.gates() {
    result.push(driver(
      slot,
      gate.clone(),
      gate.r1cs(),
      |g: &CodeGate, r, d| g.generate_witness_into(r, d),
    ));
  }
  let (slot, gate) = emission.execution.frame.frame_gate();
  result.push(driver(
    slot,
    gate.clone(),
    gate.r1cs(),
    |g: &FrameGate, r, d| g.generate_witness_into(r, d),
  ));
  let (slot, gate) = emission.execution.frame.fuel_gate();
  result.push(driver(
    slot,
    gate.clone(),
    gate.r1cs(),
    |g: &Fuel64StepGate, r, d| g.generate_witness_into(r, d),
  ));
  let (slot, gate) = emission.execution.numeric.route_gate();
  result.push(driver(
    slot,
    gate.clone(),
    gate.r1cs(),
    |g: &PrimitiveRouteGate, r, d| g.generate_witness_into(r, d),
  ));
  let (slot, gate) = emission.execution.numeric.nat.gate();
  result.push(driver(
    slot,
    gate.clone(),
    gate.r1cs(),
    |g: &Nat128Gate, r, d| g.generate_witness_into(r, d),
  ));
  let scalar = &emission.execution.numeric.scalar;
  let gate = PrimitivePrepareGate::new(
    nu,
    2,
    PrimitiveSet::crypto().crypto_scalar_subset(),
  )
  .unwrap();
  result.push(driver(
    scalar.prepare,
    gate.clone(),
    gate.r1cs(),
    |g: &PrimitivePrepareGate, r, d| g.generate_witness_into(r, d),
  ));
  result.push(driver(
    scalar.finish,
    scalar.finish_gate.clone(),
    scalar.finish_gate.r1cs(),
    |g: &PrimitiveFinishGate, r, d| g.generate_witness_into(r, d),
  ));
  let gate = SelectWordsGate::new(nu, 2).unwrap();
  result.push(driver(
    emission.execution.numeric.select_slot(),
    gate.clone(),
    gate.r1cs(),
    |g: &SelectWordsGate, r, d| g.generate_witness_into(r, d),
  ));
  let a = &scalar.arithmetic;
  result.push(driver(
    a.add,
    GoldilocksAddPairGate { nu },
    goldilocks::build_goldilocks_add_r1cs(nu),
    |g: &GoldilocksAddPairGate, r, d| {
      goldilocks::generate_goldilocks_add_witness_into(r, g.nu, d)
    },
  ));
  result.push(driver(
    a.mul,
    GoldilocksMulPairGate { nu },
    multiplication::build_goldilocks_mul_r1cs(nu),
    |g: &GoldilocksMulPairGate, r, d| {
      multiplication::generate_goldilocks_mul_witness_into(r, g.nu, d)
    },
  ));
  result.push(driver(
    a.canonical,
    CanonicalGoldilocksQuadGate { nu },
    goldilocks::build_canonical_quad_r1cs(nu),
    |g: &CanonicalGoldilocksQuadGate, r, d| {
      goldilocks::generate_canonical_quad_witness_into(r, g.nu, d)
    },
  ));
  result.push(driver(
    a.repack,
    GoldilocksLaneRepackGate { nu },
    extension::build_lane_repack_r1cs(nu),
    |g: &GoldilocksLaneRepackGate, r, d| {
      extension::generate_lane_repack_witness_into(r, g.nu, d)
    },
  ));
  for (slot, gate) in
    emission.order.gates().chain([emission.memory.prepare_gate()])
  {
    result.push(driver(
      slot,
      gate.clone(),
      gate.r1cs(),
      OrderGate::generate_witness_into,
    ));
  }
  let log = emission.memory.log();
  for permutation in [
    Some(emission.order.permutation()),
    Some(log.permutation()),
    emission.tree.as_ref().map(|tree| tree.permutation()),
  ]
  .into_iter()
  .flatten()
  {
    for (slot, gate) in permutation.packing_gates() {
      result.push(driver(
        slot,
        gate.clone(),
        gate.r1cs(),
        RecordPackingGate::generate_witness_into,
      ));
    }
    if let Some((slot, gate)) = permutation.boolean_gate() {
      result.push(driver(
        slot,
        gate.clone(),
        gate.r1cs(),
        BooleanSwitchGate::generate_witness_into,
      ));
    }
  }
  for (slot, gate) in log.memory().gates() {
    result.push(driver(
      slot,
      gate.clone(),
      gate.r1cs(),
      |g: &MemoryGate, r, d| g.generate_witness_into(r, d),
    ));
  }
  if let Some(tree) = &emission.tree {
    for (slot, gate) in tree.gates() {
      result.push(driver(
        slot,
        gate.clone(),
        gate.r1cs(),
        |g: &MultiGate, r, d| g.generate_witness_into(r, d),
      ));
    }
  }
  let (slot, gate) = log.audit_gate();
  result.push(driver(
    slot,
    gate.clone(),
    gate.r1cs(),
    |g: &AuditGate, r, d| g.generate_witness_into(r, d),
  ));
  for (slot, table) in log.memory().compression().tables() {
    result.push(driver(
      slot,
      Blake3Gate { nu },
      table,
      |g: &Blake3Gate, rows, dst| {
        flock_blake3::generate_witness_batch_major_partial_into(rows, g.nu, dst)
      },
    ));
  }
  result.sort_by_key(|d| shape.registry_slot(d.slot()));
  ensure!(
    result.len() == shape.registry.boolean_types().len(),
    "execution driver registry length"
  );
  for (i, d) in result.iter().enumerate() {
    ensure!(
      shape.registry_slot(d.slot()) == i,
      "execution driver registry order"
    );
    d.validate(shape)?;
  }
  Ok(result)
}
