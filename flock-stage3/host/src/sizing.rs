//! Count the same constraint emission used for compilation, without building
//! R1CS tables, wire classes, or capacity-sized permutation buffers.
//!
//! Counting wires are opaque placeholders: the emitter must not branch on wire
//! identity or inspect wire values. Native witness-dependent branches still
//! run normally in both passes. The finished circuit's counts and schemas are
//! checked against the count pass before it can be used.

use anyhow::{Result, bail};
use flock_prover::{
  circuit::builder::{
    CircuitShape, GateType, ShapeBuilder, SlotId, SlotWitness, Wire,
  },
  field::F128,
  r1cs::SparseBinaryMatrix,
  schedule::{IoDirection, IoWord, TableClass, TableType},
};

/// Cheap arity metadata, checked against every finished production table.
pub(crate) trait CountedGate: GateType {
  const INPUTS: usize;
  const OUTPUTS: usize;
}

macro_rules! counted_gates {
  ($($gate:ty => ($inputs:literal, $outputs:literal)),+ $(,)?) => {
    $(impl CountedGate for $gate {
      const INPUTS: usize = $inputs;
      const OUTPUTS: usize = $outputs;
    })+
  };
}

counted_gates! {
  crate::binding::Blake3Gate => (7, 4),
  crate::merkle::DigestOrderGate => (5, 4),
  crate::goldilocks::GoldilocksAddPairGate => (2, 3),
  crate::multiplication::GoldilocksMulPairGate => (2, 4),
  crate::extension::GoldilocksLaneRepackGate => (2, 4),
  crate::goldilocks::CanonicalGoldilocksQuadGate => (2, 1),
  crate::equality::F128EqualityGate => (2, 1),
  crate::transcript::HashSampleGate => (1, 1),
  crate::transcript::GoldilocksSampleGate => (4, 9),
  crate::transcript::U64SplitGate => (1, 2),
  crate::window::ByteWindowGate => (3, 1),
}

/// The gate-emission subset shared by the real builder and the census pass.
pub(crate) trait CircuitEmitter {
  fn slot<G>(&mut self, gate: G) -> SlotId
  where
    G: CountedGate + Send + Sync + 'static,
    G::Row: Send + 'static,
    G::Hint: 'static;
  fn input(&mut self) -> Wire;
  fn public_input(&mut self) -> Wire;
  fn fixed_public_input(&mut self, value: F128) -> Wire;
  fn gate(&mut self, slot: SlotId, inputs: &[Wire]) -> Vec<Wire>;
  fn publish(&mut self, wire: Wire);
  fn connect(&mut self, first: Wire, second: Wire);
}

impl CircuitEmitter for ShapeBuilder {
  fn slot<G>(&mut self, gate: G) -> SlotId
  where
    G: CountedGate + Send + Sync + 'static,
    G::Row: Send + 'static,
    G::Hint: 'static,
  {
    self.slot(gate)
  }
  fn input(&mut self) -> Wire {
    self.input()
  }
  fn public_input(&mut self) -> Wire {
    self.public_input()
  }
  fn fixed_public_input(&mut self, value: F128) -> Wire {
    self.fixed_public_input(value)
  }
  fn gate(&mut self, slot: SlotId, inputs: &[Wire]) -> Vec<Wire> {
    self.gate(slot, inputs)
  }
  fn publish(&mut self, wire: Wire) {
    self.publish(wire);
  }
  fn connect(&mut self, first: Wire, second: Wire) {
    self.connect(first, second);
  }
}

struct SlotCount {
  id: SlotId,
  name: &'static str,
  inputs: usize,
  outputs: usize,
  rows: usize,
}

pub(crate) struct CountingEmitter {
  // Upstream IDs have private constructors. This builder only allocates IDs;
  // it never emits a gate, evaluates a witness, or finishes a circuit.
  ids: ShapeBuilder,
  placeholder: Wire,
  slots: Vec<SlotCount>,
}

impl CountingEmitter {
  /// Capacity checks in the shared emitter must not truncate the count pass.
  /// No allocation uses this capacity: all real work is admitted afterwards.
  pub(crate) const COUNT_NU: usize = usize::BITS as usize - 1;

  pub(crate) fn new() -> Self {
    let mut ids = ShapeBuilder::new(0);
    let placeholder = ids.input();
    Self { ids, placeholder, slots: Vec::new() }
  }

  pub(crate) fn required_nu(&self, minimum: usize) -> Result<usize> {
    let rows = self.slots.iter().map(|slot| slot.rows).max().unwrap_or(0);
    let capacity =
      rows.max(1).checked_next_power_of_two().ok_or_else(|| {
        anyhow::anyhow!("Stage 3 exact table row count overflow")
      })?;
    Ok((capacity.ilog2() as usize).max(minimum))
  }

  pub(crate) fn table_rows(
    &self,
  ) -> impl Iterator<Item = (&'static str, usize)> {
    self.slots.iter().map(|slot| (slot.name, slot.rows))
  }

  pub(crate) fn ensure_matches(&self, shape: &CircuitShape) -> Result<()> {
    if self.slots.len() != shape.counts.len() {
      bail!("Stage 3 counting/compiled slot counts disagree");
    }
    for slot in &self.slots {
      let index = shape.registry_slot(slot.id);
      let schema = &shape.registry.types()[index].io_schema;
      let inputs = schema.iter().filter(|io| io.dir == IoDirection::In).count();
      if shape.counts[index] != slot.rows
        || inputs != slot.inputs
        || schema.len() - inputs != slot.outputs
      {
        bail!("Stage 3 counting/compiled table {index} disagrees");
      }
    }
    Ok(())
  }
}

impl CircuitEmitter for CountingEmitter {
  fn slot<G>(&mut self, _gate: G) -> SlotId
  where
    G: CountedGate + Send + Sync + 'static,
    G::Row: Send + 'static,
    G::Hint: 'static,
  {
    let id = self.ids.slot(IdOnlyGate);
    self.slots.push(SlotCount {
      id,
      name: std::any::type_name::<G>().rsplit("::").next().unwrap(),
      inputs: G::INPUTS,
      outputs: G::OUTPUTS,
      rows: 0,
    });
    id
  }
  fn input(&mut self) -> Wire {
    self.placeholder
  }
  fn public_input(&mut self) -> Wire {
    self.placeholder
  }
  fn fixed_public_input(&mut self, _value: F128) -> Wire {
    self.placeholder
  }
  fn gate(&mut self, slot: SlotId, inputs: &[Wire]) -> Vec<Wire> {
    let count = self.slots.iter_mut().find(|count| count.id == slot).unwrap();
    assert_eq!(inputs.len(), count.inputs, "counted gate input arity");
    // Saturation is fail-closed: required_nu rejects usize::MAX, including
    // when the emitter goes on to make more calls after an overflow.
    count.rows = count.rows.saturating_add(1);
    vec![self.placeholder; count.outputs]
  }
  fn publish(&mut self, _wire: Wire) {}
  fn connect(&mut self, _first: Wire, _second: Wire) {}
}

/// An ID allocator token, not a circuit table. It cannot escape this module
/// through CountingEmitter and its builder is never finished.
struct IdOnlyGate;

impl GateType for IdOnlyGate {
  type Row = ();
  type Hint = ();

  fn table(&self) -> TableType {
    let empty =
      || SparseBinaryMatrix { num_rows: 0, num_cols: 0, rows: Vec::new() };
    TableType {
      k_log: 0,
      useful_bits: 0,
      a_0: empty(),
      b_0: empty(),
      c_0: empty(),
      const_pin: None,
      class: TableClass::Boolean,
      io_schema: vec![IoWord::input(0)],
    }
  }

  fn eval(&self, _: &[F128], _: &(), _: &mut Vec<F128>) {
    unreachable!("counting IDs cannot evaluate a circuit")
  }

  fn witness(&self, _: &[()], _: usize) -> SlotWitness {
    unreachable!("counting IDs cannot produce a witness")
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::goldilocks::CanonicalGoldilocksQuadGate;

  #[test]
  fn capacity_uses_the_largest_table_and_checks_rounding_overflow() {
    let mut count = CountingEmitter::new();
    for _ in 0..2 {
      count.slot(CanonicalGoldilocksQuadGate { nu: 10 });
    }
    assert_eq!(count.required_nu(10).unwrap(), 10);
    for (rows, nu) in [(1023, 10), (1024, 10), (1025, 11)] {
      for slot in &mut count.slots {
        slot.rows = rows;
      }
      assert_eq!(count.required_nu(10).unwrap(), nu);
    }
    count.slots[0].rows = usize::MAX;
    assert!(count.required_nu(10).is_err());
  }

  #[test]
  fn compiled_count_and_schema_drift_are_rejected() {
    let mut count = CountingEmitter::new();
    let mut real = ShapeBuilder::new(10);
    fn emit(builder: &mut impl CircuitEmitter) {
      let slot = builder.slot(CanonicalGoldilocksQuadGate { nu: 10 });
      let input = builder.fixed_public_input(F128::ZERO);
      builder.gate(slot, &[input, input]);
    }
    emit(&mut count);
    emit(&mut real);
    assert_eq!(
      count.table_rows().collect::<Vec<_>>(),
      vec![("CanonicalGoldilocksQuadGate", 1)],
    );
    let shape = real.finish().unwrap();
    count.ensure_matches(&shape).unwrap();
    count.slots[0].rows += 1;
    assert!(count.ensure_matches(&shape).is_err());
    count.slots[0].rows -= 1;
    count.slots[0].outputs += 1;
    assert!(count.ensure_matches(&shape).is_err());
  }
}
