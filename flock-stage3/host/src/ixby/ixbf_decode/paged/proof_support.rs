use flock_prover::{
  circuit::builder::{CircuitWitness, GateType, SlotId},
  prover::UnionSlotProverInput,
  r1cs::BlockR1cs,
  union::SlotWitnessDest,
};
pub(super) trait Driver: Send + Sync {
  fn slot(&self) -> SlotId;
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
pub(super) fn driver<G>(
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
