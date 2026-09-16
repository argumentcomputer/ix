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
  schedule::{IoDirection, IoWord, Registry, TableClass, TableType},
};

/// Cheap arity metadata, checked against every finished production table.
pub trait CountedGate: GateType {
  fn input_count(&self) -> usize;
  fn output_count(&self) -> usize;
  /// Preserve setup-owned gate parameters while changing only the row domain.
  fn table_at(&self, nu: usize) -> TableType;
}

macro_rules! counted_gates {
  ($($gate:ty => ($inputs:literal, $outputs:literal)),+ $(,)?) => {
    $(impl CountedGate for $gate {
      fn input_count(&self) -> usize { $inputs }
      fn output_count(&self) -> usize { $outputs }
      fn table_at(&self, nu: usize) -> TableType { Self { nu }.table() }
    })+
  };
}

counted_gates! {
  crate::hash::Blake3Gate => (7, 4),
  crate::conformance::merkle::DigestOrderGate => (5, 4),
  crate::goldilocks::GoldilocksAddPairGate => (2, 3),
  crate::multiplication::GoldilocksMulPairGate => (2, 4),
  crate::extension::GoldilocksLaneRepackGate => (2, 4),
  crate::goldilocks::CanonicalGoldilocksQuadGate => (2, 1),
  crate::equality::F128EqualityGate => (2, 1),
  crate::window::ByteWindowGate => (3, 1),
}

/// The gate-emission subset shared by the real builder and the census pass.
pub trait CircuitEmitter {
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
  table_at: Box<dyn Fn(usize) -> TableType + Send + Sync>,
}

pub struct CountingEmitter {
  // Upstream IDs have private constructors. This builder only allocates IDs;
  // it never emits a gate, evaluates a witness, or finishes a circuit.
  ids: ShapeBuilder,
  placeholder: Wire,
  slots: Vec<SlotCount>,
}

impl Default for CountingEmitter {
  fn default() -> Self {
    Self::new()
  }
}

impl CountingEmitter {
  /// Capacity checks in the shared emitter must not truncate the count pass.
  /// No allocation uses this capacity: all real work is admitted afterwards.
  pub const COUNT_NU: usize = usize::BITS as usize - 1;

  pub fn new() -> Self {
    let mut ids = ShapeBuilder::new(0);
    let placeholder = ids.input();
    Self { ids, placeholder, slots: Vec::new() }
  }

  pub fn required_nu(&self, minimum: usize) -> Result<usize> {
    let rows = self.slots.iter().map(|slot| slot.rows).max().unwrap_or(0);
    let capacity =
      rows.max(1).checked_next_power_of_two().ok_or_else(|| {
        anyhow::anyhow!("Stage 3 exact table row count overflow")
      })?;
    Ok((capacity.ilog2() as usize).max(minimum))
  }

  pub fn table_rows(&self) -> impl Iterator<Item = (&'static str, usize)> {
    self.slots.iter().map(|slot| (slot.name, slot.rows))
  }

  pub fn ensure_matches(&self, shape: &CircuitShape) -> Result<()> {
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

  /// Materialize only the small inner tables, not the circuit's wiring or
  /// capacity-sized permutation. This lets V2 validate the exact effective
  /// PCS configuration before allocating a compiled verifier.
  pub fn registry(&self, nu: usize) -> (Registry, Vec<usize>) {
    let mut tables: Vec<_> =
      self.slots.iter().map(|slot| ((slot.table_at)(nu), slot.rows)).collect();
    tables.sort_by_key(|(table, _)| {
      (table.is_element(), std::cmp::Reverse(table.k_log))
    });
    let (types, counts) = tables.into_iter().unzip();
    (Registry::new(types, nu), counts)
  }
}

impl CircuitEmitter for CountingEmitter {
  fn slot<G>(&mut self, gate: G) -> SlotId
  where
    G: CountedGate + Send + Sync + 'static,
    G::Row: Send + 'static,
    G::Hint: 'static,
  {
    let id = self.ids.slot(IdOnlyGate);
    self.slots.push(SlotCount {
      id,
      name: std::any::type_name::<G>().rsplit("::").next().unwrap(),
      inputs: gate.input_count(),
      outputs: gate.output_count(),
      rows: 0,
      table_at: Box::new(move |nu| gate.table_at(nu)),
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

  #[test]
  #[ignore = "exact per-table execution cost census; materializes inner matrices"]
  fn paged_execution_table_costs() {
    use crate::ixby::paged_exec::{BatchClass, emit_batch};
    use flock_prover::union::UnionInstance;
    for class in [
      BatchClass::SharedCompact,
      BatchClass::Shared,
      BatchClass::SharedCompactBoolean,
      BatchClass::SharedBoolean,
      BatchClass::Shared1024,
      BatchClass::SharedCompactPacked,
      BatchClass::SharedPacked1024,
    ] {
      let mut count = CountingEmitter::new();
      let _ = emit_batch(&mut count, class).unwrap();
      let mut totals = std::collections::BTreeMap::new();
      for slot in &count.slots {
        let table = (slot.table_at)(class.nu());
        let columns =
          table.useful_bits.div_ceil(128).min(1 << (table.k_log - 7));
        let words = slot.rows * columns;
        let entry = totals.entry(slot.name).or_insert((0usize, 0usize));
        entry.0 += slot.rows;
        entry.1 += words;
      }
      let (registry, rows) = count.registry(class.nu());
      let union = UnionInstance::new(&registry, rows);
      assert_eq!(
        totals.values().map(|(_, words)| words).sum::<usize>(),
        union.dense_words()
      );
      let mut totals: Vec<_> = totals.into_iter().collect();
      totals.sort_by_key(|(_, (_, words))| std::cmp::Reverse(*words));
      for (name, (rows, words)) in totals {
        eprintln!("execution_cost,{class:?},{name},{rows},{words}");
      }
      eprintln!(
        "execution_cost_total,{class:?},dense_words={},padded_words={},boolean_words={},m_total={},dense_m={}",
        union.dense_words(),
        union.packed_len(),
        union.boolean_packed_len(),
        union.m_total(),
        union.dense_m()
      );
    }
  }
}
