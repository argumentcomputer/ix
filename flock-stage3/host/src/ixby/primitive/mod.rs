//! Runtime scalar opcode dispatch. Setup depends only on the approved opcode
//! registry and operand capacity. Word operations and typed dispatch are
//! Boolean constraints; base/extension arithmetic uses the shared canonical
//! Goldilocks tables. An inverse is untrusted advice, constrained by its full
//! extension product and by the reference inverse-zero convention.

mod finish;
mod prepare;
pub mod registry;
#[cfg(test)]
pub(crate) mod tests;
mod word;
#[cfg(test)]
mod word_tests;

pub use finish::{PrimitiveFinishGate, PrimitiveFinishRow};
pub use prepare::{PrimitivePrepareGate, PrimitivePrepareRow};

use crate::{extension::GoldilocksCircuitSlots, sizing::CircuitEmitter};
use flock_prover::{
  circuit::builder::{SlotId, Wire},
  field::F128,
};

/// One fixed arithmetic/dispatch network per emitted machine transition.
pub struct ScalarPrimitiveSlots {
  pub prepare: SlotId,
  pub finish: SlotId,
  pub finish_gate: PrimitiveFinishGate,
  pub arithmetic: GoldilocksCircuitSlots,
  zero: Wire,
  operands: usize,
}

impl ScalarPrimitiveSlots {
  pub fn declare(
    b: &mut impl CircuitEmitter,
    gate: PrimitivePrepareGate,
  ) -> Self {
    let operands = gate.operands();
    let nu = gate.nu();
    let finish_gate = PrimitiveFinishGate::new(nu).unwrap();
    Self {
      prepare: b.slot(gate),
      finish: b.slot(finish_gate.clone()),
      finish_gate,
      arithmetic: GoldilocksCircuitSlots::declare(b, nu),
      zero: b.fixed_public_input(F128::ZERO),
      operands,
    }
  }

  /// `headers` and `arguments` must be the fetched block headers and resolved
  /// operand wires, not a separately supplied host description of an opcode.
  pub fn evaluate(
    &self,
    b: &mut impl CircuitEmitter,
    headers: &[Wire; 2],
    arguments: &[Wire],
  ) -> [Wire; 2] {
    assert_eq!(arguments.len(), 2 * self.operands);
    let mut input = headers.to_vec();
    input.extend_from_slice(arguments);
    let p = b.gate(self.prepare, &input);
    b.connect(p[7], self.zero);
    let sum = self.arithmetic.add(b, p[2], p[3]);
    let product = self.arithmetic.ext2_mul(b, p[2], p[3]);
    let result =
      b.gate(self.finish, &[p[0], p[1], p[6], sum, product, p[4], p[5]]);
    b.connect(result[2], self.zero);
    [result[0], result[1]]
  }

  pub fn finish_canonical(&self, b: &mut impl CircuitEmitter) {
    self.arithmetic.finish_canonical(b);
  }
}
