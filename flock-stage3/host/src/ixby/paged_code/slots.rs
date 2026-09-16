use super::*;
use crate::{ixby::memory_log::AccessWires, sizing::CircuitEmitter};
use anyhow::Result;
use flock_prover::{
  circuit::builder::{SlotId, Wire},
  field::F128,
};

pub struct CodeReadWires {
  pub access: AccessWires,
  pub value: [Wire; 2],
}
pub struct OperandReadWires {
  pub accesses: [AccessWires; 2],
  pub value: [Wire; 2],
}
pub struct CodeSlots {
  gates: [(SlotId, CodeGate); 5],
  zero: Wire,
}
impl CodeSlots {
  pub fn declare(b: &mut impl CircuitEmitter, nu: usize) -> Result<Self> {
    let mut gates = Vec::new();
    for kind in [
      CodeGateKind::Block,
      CodeGateKind::Operand,
      CodeGateKind::Function,
      CodeGateKind::Alternative,
      CodeGateKind::Constructor,
    ] {
      let gate = CodeGate::new(nu, kind)?;
      gates.push((b.slot(gate.clone()), gate));
    }
    Ok(Self {
      gates: gates.try_into().ok().unwrap(),
      zero: b.fixed_public_input(F128::ZERO),
    })
  }
  pub fn gates(&self) -> impl Iterator<Item = (SlotId, &CodeGate)> {
    self.gates.iter().map(|(slot, gate)| (*slot, gate))
  }
  fn read(
    &self,
    b: &mut impl CircuitEmitter,
    at: usize,
    input: &[Wire],
  ) -> CodeReadWires {
    let out = b.gate(self.gates[at].0, input);
    b.connect(out[4], self.zero);
    CodeReadWires {
      access: AccessWires {
        address: out[0],
        write: out[1],
        value: [out[2], out[3]],
      },
      value: [out[2], out[3]],
    }
  }
  pub fn block(
    &self,
    b: &mut impl CircuitEmitter,
    enabled: Wire,
    frame: Wire,
    cell: [Wire; 2],
  ) -> CodeReadWires {
    self.read(b, 0, &[enabled, frame, cell[0], cell[1]])
  }
  pub fn function(
    &self,
    b: &mut impl CircuitEmitter,
    enabled: Wire,
    function: Wire,
    cell: [Wire; 2],
  ) -> CodeReadWires {
    self.read(b, 2, &[enabled, function, cell[0], cell[1]])
  }
  pub fn constructor(
    &self,
    b: &mut impl CircuitEmitter,
    enabled: Wire,
    constructor: Wire,
    cell: [Wire; 2],
  ) -> CodeReadWires {
    self.read(b, 4, &[enabled, constructor, cell[0], cell[1]])
  }
  #[allow(clippy::too_many_arguments)]
  pub fn alternative(
    &self,
    b: &mut impl CircuitEmitter,
    enabled: Wire,
    frame: Wire,
    index: Wire,
    count: Wire,
    cell: [Wire; 2],
  ) -> CodeReadWires {
    self.read(b, 3, &[enabled, frame, index, count, cell[0], cell[1]])
  }
  #[allow(clippy::too_many_arguments)]
  pub fn operand(
    &self,
    b: &mut impl CircuitEmitter,
    enabled: Wire,
    frame: Wire,
    index: Wire,
    count: Wire,
    cell: [Wire; 2],
    local: [Wire; 2],
  ) -> OperandReadWires {
    let out = b.gate(
      self.gates[1].0,
      &[enabled, frame, index, count, cell[0], cell[1], local[0], local[1]],
    );
    b.connect(out[10], self.zero);
    OperandReadWires {
      accesses: std::array::from_fn(|i| {
        let at = i * 4;
        AccessWires {
          address: out[at],
          write: out[at + 1],
          value: [out[at + 2], out[at + 3]],
        }
      }),
      value: [out[8], out[9]],
    }
  }
}
