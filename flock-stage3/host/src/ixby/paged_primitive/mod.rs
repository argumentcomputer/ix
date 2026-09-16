//! Functional primitive tags are routed from actual packed instruction wires.
//! Numeric operations reuse the existing Word32/Goldilocks/extension tables
//! and the immediate Nat128 table. Byte requests are returned for the paged
//! byte engine; they cannot be interpreted as a completed numeric result.
mod gate;
#[cfg(test)]
mod tests;
use crate::{
  ixby::{
    decode::PrimitiveSet,
    paged_nat::Nat128Slot,
    primitive::{PrimitivePrepareGate, ScalarPrimitiveSlots},
    select::{SelectWordsGate, SelectWordsSlot},
  },
  sizing::CircuitEmitter,
};
use anyhow::Result;
use flock_prover::{
  circuit::builder::{SlotId, Wire},
  field::F128,
};
pub use gate::{PrimitiveRouteGate, PrimitiveRouteRow};

pub struct NumericSlots {
  route: (SlotId, PrimitiveRouteGate),
  pub nat: Nat128Slot,
  pub scalar: ScalarPrimitiveSlots,
  select: SelectWordsSlot,
  zero: Wire,
}
pub struct PrimitiveResultWires {
  pub value: [Wire; 2],
  /// Zero means no byte request; otherwise the functional primitive tag + 1.
  pub byte_code: Wire,
  pub byte_arguments: [Wire; 6],
}
impl NumericSlots {
  pub fn declare(b: &mut impl CircuitEmitter, nu: usize) -> Result<Self> {
    let gate = PrimitiveRouteGate::new(nu)?;
    Ok(Self {
      route: (b.slot(gate.clone()), gate),
      nat: Nat128Slot::declare(b, nu)?,
      scalar: ScalarPrimitiveSlots::declare(
        b,
        PrimitivePrepareGate::new(
          nu,
          2,
          PrimitiveSet::crypto().crypto_scalar_subset(),
        )?,
      ),
      select: SelectWordsSlot::declare(b, SelectWordsGate::new(nu, 2)?),
      zero: b.fixed_public_input(F128::ZERO),
    })
  }
  pub fn route_gate(&self) -> (SlotId, &PrimitiveRouteGate) {
    (self.route.0, &self.route.1)
  }
  pub fn select_slot(&self) -> SlotId {
    self.select.slot()
  }
  pub fn evaluate(
    &self,
    b: &mut impl CircuitEmitter,
    enabled: Wire,
    header: Wire,
    arguments: [Wire; 6],
  ) -> PrimitiveResultWires {
    let input =
      [enabled, header].into_iter().chain(arguments).collect::<Vec<_>>();
    let r = b.gate(self.route.0, &input);
    b.connect(r[19], self.zero);
    let nat = self.nat.evaluate(b, r[1], [r[2], r[3]], [r[4], r[5]]);
    let scalar = self.scalar.evaluate(b, &[r[6], r[7]], &r[8..12]);
    let selected = self.select.select(b, r[0], &nat, &scalar);
    PrimitiveResultWires {
      value: selected.try_into().unwrap(),
      byte_code: r[12],
      byte_arguments: r[13..19].try_into().unwrap(),
    }
  }
  pub fn finish_canonical(&self, b: &mut impl CircuitEmitter) {
    self.scalar.finish_canonical(b);
  }
}
