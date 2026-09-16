use anyhow::{Result, ensure};
use flock_prover::{
  circuit::builder::{CircuitShape, CircuitWitness, GateType, SlotId},
  prover::UnionSlotProverInput,
  r1cs::{BlockR1cs, SparseBinaryMatrix},
  union::SlotWitnessDest,
};
pub(in crate::ixby) trait Driver: Send + Sync {
  fn slot(&self) -> SlotId;
  fn validate(&self, shape: &CircuitShape) -> Result<()>;
  fn prover<'a>(
    &'a self,
    witness: &'a CircuitWitness,
  ) -> UnionSlotProverInput<'a>;
}
type Generate<G> =
  fn(&G, &[<G as GateType>::Row], SlotWitnessDest<'_>) -> Vec<u8>;
struct TypedDriver<G: GateType> {
  slot: SlotId,
  gate: G,
  table: BlockR1cs,
  generate: Generate<G>,
}
impl<G> Driver for TypedDriver<G>
where
  G: GateType<Hint = ()> + Send + Sync + 'static,
  G::Row: Clone + Send + Sync + 'static,
{
  fn slot(&self) -> SlotId {
    self.slot
  }
  fn validate(&self, shape: &CircuitShape) -> Result<()> {
    let expected = &shape.registry.types()[shape.registry_slot(self.slot)];
    let actual = &self.table;
    let gate = self.gate.table();
    let equal = |a: &SparseBinaryMatrix, b: &SparseBinaryMatrix| {
      a.num_rows == b.num_rows && a.num_cols == b.num_cols && a.rows == b.rows
    };
    ensure!(
      !expected.is_element()
        && actual.k_log == expected.k_log
        && actual.useful_bits == expected.useful_bits
        && actual.const_pin == expected.const_pin
        && actual.n_log() == shape.registry.nu()
        && equal(&actual.a_0, &expected.a_0)
        && equal(&actual.b_0, &expected.b_0)
        && equal(&actual.c_0, &expected.c_0)
        && !gate.is_element()
        && gate.k_log == expected.k_log
        && gate.useful_bits == expected.useful_bits
        && gate.const_pin == expected.const_pin
        && gate.io_schema == expected.io_schema
        && equal(&gate.a_0, &expected.a_0)
        && equal(&gate.b_0, &expected.b_0)
        && equal(&gate.c_0, &expected.c_0),
      "paged prover table {} differs from compiled verifier registry: capacity={} block_metadata={} block_matrices={} gate_metadata={} gate_schema={} gate_matrices={}",
      std::any::type_name::<G>(),
      actual.n_log() == shape.registry.nu(),
      actual.k_log == expected.k_log
        && actual.useful_bits == expected.useful_bits
        && actual.const_pin == expected.const_pin,
      equal(&actual.a_0, &expected.a_0)
        && equal(&actual.b_0, &expected.b_0)
        && equal(&actual.c_0, &expected.c_0),
      gate.k_log == expected.k_log
        && gate.useful_bits == expected.useful_bits
        && gate.const_pin == expected.const_pin,
      gate.io_schema == expected.io_schema,
      equal(&gate.a_0, &expected.a_0)
        && equal(&gate.b_0, &expected.b_0)
        && equal(&gate.c_0, &expected.c_0)
    );
    Ok(())
  }
  fn prover<'a>(
    &'a self,
    witness: &'a CircuitWitness,
  ) -> UnionSlotProverInput<'a> {
    let rows = witness.rows::<G>(self.slot);
    UnionSlotProverInput::in_place(
      move |dst| (self.generate)(&self.gate, rows, dst),
      self.table.csc_lincheck_circuit(),
    )
  }
}
pub(in crate::ixby) fn driver<G>(
  slot: SlotId,
  gate: G,
  table: BlockR1cs,
  generate: Generate<G>,
) -> Box<dyn Driver>
where
  G: GateType<Hint = ()> + Send + Sync + 'static,
  G::Row: Clone + Send + Sync + 'static,
{
  Box::new(TypedDriver { slot, gate, table, generate })
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::{
    ixby::ixbf_decode::{GrammarKind, GrammarStepGate},
    sizing::CountedGate,
  };
  use flock_prover::circuit::builder::ShapeBuilder;
  #[test]
  fn prover_driver_rejects_a_different_grammar_before_proving() {
    let input = GrammarStepGate::new(3, GrammarKind::Input).unwrap();
    let program = GrammarStepGate::new(3, GrammarKind::Program).unwrap();
    let mut b = ShapeBuilder::new(3);
    let slot = b.slot(input.clone());
    let values =
      (0..input.input_count()).map(|_| b.input()).collect::<Vec<_>>();
    b.gate(slot, &values);
    let shape = b.finish().unwrap();
    driver(
      slot,
      input.clone(),
      input.r1cs(),
      GrammarStepGate::generate_witness_into,
    )
    .validate(&shape)
    .unwrap();
    assert!(
      driver(
        slot,
        program.clone(),
        program.r1cs(),
        GrammarStepGate::generate_witness_into
      )
      .validate(&shape)
      .is_err()
    );
    assert!(
      driver(
        slot,
        program,
        input.r1cs(),
        GrammarStepGate::generate_witness_into
      )
      .validate(&shape)
      .is_err()
    );
  }
}
