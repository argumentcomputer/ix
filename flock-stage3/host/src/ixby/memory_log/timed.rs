use super::{AccessWires, BoundaryWires, MemoryLogSlots, RoutingKind};
use crate::{
  ixby::{
    auth_memory::{
      MemoryDepth,
      multi::{MultiMemorySlots, MultiProofWires},
    },
    execution_order::{OrderGate, OrderKind},
  },
  sizing::CircuitEmitter,
};
use anyhow::Result;
use flock_prover::{
  circuit::builder::{SlotId, Wire},
  field::F128,
};

/// `enabled` and `clock` must be the same wires consumed by StateChainSlots.
/// Assign distinct fixed ordinals within each semantic row (at most 32).
#[derive(Clone, Copy)]
pub struct TimedAccessWires {
  pub enabled: Wire,
  pub clock: Wire,
  pub ordinal: u8,
  pub access: AccessWires,
}
pub struct TimedMemoryLogSlots {
  log: MemoryLogSlots,
  prepare: (SlotId, OrderGate),
  residual: Wire,
}
impl TimedMemoryLogSlots {
  pub fn declare(
    b: &mut impl CircuitEmitter,
    nu: usize,
    depth: MemoryDepth,
  ) -> Result<Self> {
    Self::declare_with_routing(b, nu, depth, RoutingKind::Element)
  }
  pub fn declare_with_routing(
    b: &mut impl CircuitEmitter,
    nu: usize,
    depth: MemoryDepth,
    routing: RoutingKind,
  ) -> Result<Self> {
    let prepare = OrderGate::new(nu, OrderKind::Access)?;
    Ok(Self {
      log: MemoryLogSlots::declare_with_routing(b, nu, depth, routing)?,
      prepare: (b.slot(prepare.clone()), prepare),
      residual: b.fixed_public_input(F128::ZERO),
    })
  }
  pub fn log(&self) -> &MemoryLogSlots {
    &self.log
  }
  pub fn prepare_gate(&self) -> (SlotId, &OrderGate) {
    (self.prepare.0, &self.prepare.1)
  }
  pub fn check(
    &self,
    b: &mut impl CircuitEmitter,
    root: [Wire; 2],
    accesses: &[TimedAccessWires],
    cells: &[BoundaryWires],
    switches: &[Wire],
  ) -> [Wire; 2] {
    let records = self.records(b, accesses);
    self.log.check_records(b, root, records, cells, switches)
  }
  pub fn check_shared(
    &self,
    b: &mut impl CircuitEmitter,
    tree: &MultiMemorySlots,
    roots: [[Wire; 2]; 2],
    accesses: &[TimedAccessWires],
    proof: &MultiProofWires,
    switches: &[Wire],
  ) {
    let records = self.records(b, accesses);
    self.log.check_shared_records(b, tree, roots, records, proof, switches);
  }
  fn records(
    &self,
    b: &mut impl CircuitEmitter,
    accesses: &[TimedAccessWires],
  ) -> Vec<Vec<Wire>> {
    accesses
      .iter()
      .map(|request| {
        assert!(request.ordinal < 32);
        let a = request.access;
        let ordinal =
          b.fixed_public_input(F128::new(u64::from(request.ordinal), 0));
        let output = b.gate(
          self.prepare.0,
          &[
            request.enabled,
            request.clock,
            ordinal,
            a.address,
            a.write,
            a.value[0],
            a.value[1],
          ],
        );
        b.connect(output[5], self.residual);
        output[..5].to_vec()
      })
      .collect()
  }
}
