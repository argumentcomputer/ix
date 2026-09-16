use super::*;
use crate::{
  ixby::auth_memory::{MemoryAccessSlots, MemoryDepth, MemoryOpeningWires},
  sizing::{CircuitEmitter, CountedGate},
};
use anyhow::Result;
use flock_prover::{
  circuit::builder::{SlotId, Wire},
  field::F128,
};

/// These must be the caller's actual machine-access wires. The write flag is
/// constrained Boolean; time is assigned from position in this ordered list.
#[derive(Clone, Copy)]
pub struct AccessWires {
  pub address: Wire,
  pub write: Wire,
  pub value: [Wire; 2],
}
/// One opening and final value per distinct touched cell. Extra untouched
/// cells are permitted, but duplicate addresses and unbacked accesses reject.
pub struct BoundaryWires {
  pub address: Wire,
  pub opening: MemoryOpeningWires,
  pub final_value: [Wire; 2],
}

pub struct MemoryLogSlots {
  permutation: PermutationSlots,
  audit: (SlotId, AuditGate),
  memory: MemoryAccessSlots,
  kinds: [Wire; 5],
  zero: Wire,
  one: Wire,
  last: Wire,
  residual: Wire,
}
impl MemoryLogSlots {
  pub fn declare(
    b: &mut impl CircuitEmitter,
    nu: usize,
    depth: MemoryDepth,
  ) -> Result<Self> {
    let permutation = PermutationSlots::declare(b, RECORD_WORDS)?;
    let gate = AuditGate::new(nu)?;
    let audit = (b.slot(gate.clone()), gate);
    let memory = MemoryAccessSlots::declare(b, nu, depth)?;
    Ok(Self {
      permutation,
      audit,
      memory,
      kinds: std::array::from_fn(|i| {
        b.fixed_public_input(F128::new(i as u64, 0))
      }),
      zero: b.fixed_public_input(F128::ZERO),
      one: b.fixed_public_input(F128::ONE),
      last: b.fixed_public_input(F128::new(u64::MAX, 0)),
      residual: b.fixed_public_input(F128::ZERO),
    })
  }
  pub fn memory(&self) -> &MemoryAccessSlots {
    &self.memory
  }
  pub fn permutation(&self) -> &PermutationSlots {
    &self.permutation
  }
  pub fn audit_gate(&self) -> (SlotId, &AuditGate) {
    (self.audit.0, &self.audit.1)
  }
  pub fn plan(accesses: usize, cells: usize) -> Result<PermutationPlan> {
    let rows = accesses
      .checked_add(
        cells
          .checked_mul(2)
          .ok_or_else(|| anyhow::anyhow!("memory cell count overflow"))?,
      )
      .and_then(|v| v.max(1).checked_next_power_of_two())
      .ok_or_else(|| anyhow::anyhow!("memory log count overflow"))?;
    PermutationPlan::new(rows)
  }
  /// Authenticate one old/new path pair per distinct address, prove an exact
  /// permutation of the complete access records, and audit their order/value
  /// continuity. The caller must bind both returned and initial roots to the
  /// same machine boundary. No native memory verdict participates.
  pub fn check(
    &self,
    b: &mut impl CircuitEmitter,
    initial_root: [Wire; 2],
    accesses: &[AccessWires],
    cells: &[BoundaryWires],
    switches: &[Wire],
  ) -> [Wire; 2] {
    let plan = Self::plan(accesses.len(), cells.len()).unwrap();
    assert_eq!(switches.len(), plan.switches());
    let (switch_slot, switch_gate) = self.permutation.gate();
    let mut records = Vec::with_capacity(plan.lanes());
    for (batch_index, batch) in
      accesses.chunks(switch::SWITCHES_PER_ROW).enumerate()
    {
      let mut input = Vec::with_capacity(switch_gate.input_count());
      for (i, access) in batch.iter().enumerate() {
        let clock = batch_index * switch::SWITCHES_PER_ROW + i + 1;
        let clock = b.fixed_public_input(F128::new(clock as u64, 0));
        input.push(access.write);
        for kind in [READ, WRITE] {
          input.extend([
            access.address,
            clock,
            self.kinds[kind as usize],
            access.value[0],
            access.value[1],
          ]);
        }
      }
      input.resize(switch_gate.input_count(), self.zero);
      let output = b.gate(switch_slot, &input);
      records.extend(
        output
          .as_chunks::<{ 2 * RECORD_WORDS }>()
          .0
          .iter()
          .take(batch.len())
          .map(|record| record[..RECORD_WORDS].to_vec()),
      );
    }
    let mut root = initial_root;
    for cell in cells {
      root = self.memory.replace(
        b,
        root,
        cell.address,
        &cell.opening,
        cell.final_value,
      );
      records.push(vec![
        cell.address,
        self.zero,
        self.kinds[SEED as usize],
        cell.opening.value[0],
        cell.opening.value[1],
      ]);
      records.push(vec![
        cell.address,
        self.last,
        self.kinds[SEAL as usize],
        cell.final_value[0],
        cell.final_value[1],
      ]);
    }
    let padding = vec![
      self.zero,
      self.zero,
      self.kinds[PAD as usize],
      self.zero,
      self.zero,
    ];
    records.resize(plan.lanes(), padding.clone());
    let sorted = self.permutation.permute(b, plan, &records, switches);
    let mut previous = &padding;
    for (i, current) in sorted.iter().enumerate() {
      let mut input = previous.clone();
      input.extend_from_slice(current);
      input.push(if i == 0 { self.one } else { self.zero });
      input.push(if i + 1 == sorted.len() { self.one } else { self.zero });
      let output = b.gate(self.audit.0, &input);
      b.connect(output[0], self.residual);
      previous = current;
    }
    root
  }
}
