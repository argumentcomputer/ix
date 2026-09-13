use flock_prover::field::F128;
use ix_stage4_trace::{
  F128AlgebraTraceV1, F128EqualityV1, F128InputSourceV1 as Source,
  F128OperationV1 as Operation, F128ReferenceV1 as Reference,
  F128VerifierPhaseV1 as Phase,
};

#[derive(Clone, Copy)]
pub(super) struct Symbol(pub(super) Reference);

pub(super) struct Algebra {
  pub(super) trace: F128AlgebraTraceV1,
  phase: Phase,
}

impl Algebra {
  pub(super) fn new(phase: Phase) -> Self {
    Self { trace: F128AlgebraTraceV1::default(), phase }
  }
  pub(super) fn set_phase(&mut self, phase: Phase) {
    self.phase = phase;
  }
  pub(super) fn constant(&self, value: F128) -> Symbol {
    Symbol(Reference::Input(Source::Constant(encode(value))))
  }
  pub(super) fn input(&self, source: Source) -> Symbol {
    Symbol(Reference::Input(source))
  }
  pub(super) fn op(&mut self, operation: Operation) -> Symbol {
    let result =
      Symbol(Reference::Operation(self.trace.operations.len() as u64));
    self.trace.operations.push(operation);
    result
  }
  pub(super) fn add(&mut self, left: Symbol, right: Symbol) -> Symbol {
    self.op(Operation::Add { phase: self.phase, left: left.0, right: right.0 })
  }
  pub(super) fn mul(&mut self, left: Symbol, right: Symbol) -> Symbol {
    self.op(Operation::Multiply {
      phase: self.phase,
      left: left.0,
      right: right.0,
    })
  }
  pub(super) fn inv(&mut self, value: Symbol) -> Symbol {
    self.op(Operation::Inverse { phase: self.phase, value: value.0 })
  }
  pub(super) fn equal(&mut self, left: Symbol, right: Symbol) {
    self.trace.equalities.push(F128EqualityV1 {
      phase: self.phase,
      left: left.0,
      right: right.0,
    });
  }
}

pub(super) struct Addresses {
  pub(super) observed: u64,
  pub(super) challenges: u64,
}

impl Addresses {
  pub(super) fn observe(&mut self) -> Symbol {
    let result = Symbol(Reference::Input(Source::ObservedValue(self.observed)));
    self.observed += 1;
    result
  }
  pub(super) fn challenge(&mut self) -> Symbol {
    let result = Symbol(Reference::Input(Source::Challenge(self.challenges)));
    self.challenges += 1;
    result
  }
}

pub(super) fn encode(value: F128) -> [u8; 16] {
  let mut bytes = [0; 16];
  bytes[..8].copy_from_slice(&value.lo.to_le_bytes());
  bytes[8..].copy_from_slice(&value.hi.to_le_bytes());
  bytes
}
