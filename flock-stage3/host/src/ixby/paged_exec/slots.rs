use super::*;
use crate::{
  blake3_backend::Blake3CompressionSlots,
  ixby::{
    memory_log::AccessWires, paged_code::CodeSlots, paged_frame::FrameSlots,
    paged_primitive::NumericSlots,
  },
  sizing::CircuitEmitter,
};
use anyhow::Result;
use flock_prover::{
  circuit::builder::{SlotId, Wire},
  field::F128,
};

pub struct ExecutionSlots {
  micro: Vec<(SlotId, MicroGate)>,
  pub code: CodeSlots,
  pub frame: FrameSlots,
  pub numeric: NumericSlots,
  pub(super) zero: Wire,
  pub(super) compression: Blake3CompressionSlots,
  pub(super) hash_iv: [Wire; 2],
}
pub struct StepWires {
  pub state: [Wire; STATE_WORDS],
  pub accesses: Vec<AccessWires>,
}
impl ExecutionSlots {
  pub fn declare(
    b: &mut impl CircuitEmitter,
    nu: usize,
    compression: &Blake3CompressionSlots,
  ) -> Result<Self> {
    let mut micro = Vec::new();
    for kind in MicroKind::ALL {
      let gate = MicroGate::new(nu, kind)?;
      micro.push((b.slot(gate.clone()), gate));
    }
    Ok(Self {
      micro,
      code: CodeSlots::declare(b, nu)?,
      frame: FrameSlots::declare(b, nu)?,
      numeric: NumericSlots::declare(b, nu)?,
      zero: b.fixed_public_input(F128::ZERO),
      compression: compression.clone(),
      hash_iv: crate::hash::pack8(&crate::hash::IV)
        .map(|w| b.fixed_public_input(w)),
    })
  }
  pub fn gates(&self) -> impl Iterator<Item = (SlotId, &MicroGate)> {
    self.micro.iter().map(|(s, g)| (*s, g))
  }
  pub(super) fn gate(
    &self,
    b: &mut impl CircuitEmitter,
    kind: MicroKind,
    input: &[Wire],
  ) -> Vec<Wire> {
    let (slot, _) = self.micro.iter().find(|(_, g)| g.kind() == kind).unwrap();
    let out = b.gate(*slot, input);
    b.connect(*out.last().unwrap(), self.zero);
    out[..out.len() - 1].to_vec()
  }
  /// Packed static words: (locals, continuations), (fuel budget, zero),
  /// (Nat bits, byte-array byte limit). Source admission must derive these
  /// exact values from the original program's semantic limits.
  pub fn parameters(&self, b: &mut impl CircuitEmitter, parameters: [Wire; 3]) {
    self.gate(b, MicroKind::Parameters, &parameters);
  }
  pub fn finish_canonical(&self, b: &mut impl CircuitEmitter) {
    self.numeric.finish_canonical(b);
  }
  #[allow(clippy::too_many_arguments)]
  pub(super) fn complete(
    &self,
    b: &mut impl CircuitEmitter,
    enabled: Wire,
    state: [Wire; STATE_WORDS],
    action: [Wire; 5],
    reply: [Wire; 2],
    parameters: [Wire; 3],
    mut accesses: Vec<AccessWires>,
  ) -> StepWires {
    let prefix = [enabled].into_iter().chain(state).collect::<Vec<_>>();
    let request = self.gate(
      b,
      MicroKind::FrameRequest,
      &prefix.iter().copied().chain([parameters[1]]).collect::<Vec<_>>(),
    );
    let step = self.frame.step(
      b,
      request[..5].try_into().unwrap(),
      action,
      reply,
      parameters[0],
      request[5],
      parameters[1],
    );
    let after = self.gate(
      b,
      MicroKind::Complete,
      &prefix
        .into_iter()
        .chain(step.state)
        .chain([step.fuel])
        .collect::<Vec<_>>(),
    );
    accesses.extend(step.accesses);
    StepWires { state: after.try_into().unwrap(), accesses }
  }
  /// Clock and enabled are subsequently passed unchanged to the state-chain
  /// and timed-memory consumers. `advice` consists only of memory replies.
  #[allow(clippy::too_many_arguments)]
  pub fn step(
    &self,
    b: &mut impl CircuitEmitter,
    chip: Chip,
    enabled: Wire,
    state: [Wire; STATE_WORDS],
    advice: &[Wire],
    parameters: [Wire; 3],
  ) -> StepWires {
    assert_eq!(advice.len(), chip.advice_words());
    let prefix = [enabled].into_iter().chain(state).collect::<Vec<_>>();
    let append = |values: &[Wire]| {
      prefix.iter().copied().chain(values.iter().copied()).collect::<Vec<_>>()
    };
    match chip {
      Chip::CollectionStart
      | Chip::ArrayStep
      | Chip::ArrayAscend
      | Chip::CollectionFinish
      | Chip::BuilderNode
      | Chip::BuilderCopy
      | Chip::BuilderEmit => {
        self.collection_step(b, chip, enabled, state, advice, parameters)
      },
      Chip::Fetch => {
        let read =
          self.code.block(b, enabled, state[0], advice.try_into().unwrap());
        let after = self.gate(b, MicroKind::Fetch, &append(&read.value));
        StepWires {
          state: after.try_into().unwrap(),
          accesses: vec![read.access],
        }
      },
      Chip::Resolve => {
        let request = self.gate(b, MicroKind::ResolveRequest, &prefix);
        let read = self.code.operand(
          b,
          enabled,
          state[0],
          request[0],
          request[1],
          advice[..2].try_into().unwrap(),
          advice[2..].try_into().unwrap(),
        );
        let after =
          self.gate(b, MicroKind::ResolveFinish, &append(&read.value));
        let mut accesses = read.accesses.to_vec();
        let at = STATE_WORDS;
        accesses.push(AccessWires {
          address: after[at],
          write: after[at + 1],
          value: [after[at + 2], after[at + 3]],
        });
        StepWires { state: after[..STATE_WORDS].try_into().unwrap(), accesses }
      },
      Chip::Numeric | Chip::Control => {
        let count = if chip == Chip::Numeric { 3 } else { 1 };
        let records = self.gate(b, MicroKind::Scratch(count), &append(advice));
        let accesses = records
          .as_chunks::<4>()
          .0
          .iter()
          .map(|r| AccessWires {
            address: r[0],
            write: r[1],
            value: [r[2], r[3]],
          })
          .collect();
        let (value, kind) = if chip == Chip::Numeric {
          let result = self.numeric.evaluate(
            b,
            enabled,
            state[HEADER],
            advice.try_into().unwrap(),
          );
          b.connect(result.byte_code, self.zero);
          (result.value, MicroKind::NumericAction)
        } else {
          (advice.try_into().unwrap(), MicroKind::ControlAction)
        };
        let action = self.gate(b, kind, &append(&value));
        self.complete(
          b,
          enabled,
          state,
          action.try_into().unwrap(),
          [self.zero; 2],
          parameters,
          accesses,
        )
      },
      Chip::Call => {
        let reference = self.gate(b, MicroKind::CallReference, &prefix)[0];
        let read =
          self.code.function(b, enabled, reference, advice.try_into().unwrap());
        let action = self.gate(b, MicroKind::CallAction, &append(&read.value));
        self.complete(
          b,
          enabled,
          state,
          action.try_into().unwrap(),
          [self.zero; 2],
          parameters,
          vec![read.access],
        )
      },
      Chip::Resume => {
        self.gate(b, MicroKind::Resume, &prefix);
        self.complete(
          b,
          enabled,
          state,
          [self.zero; 5],
          advice.try_into().unwrap(),
          parameters,
          Vec::new(),
        )
      },
      Chip::ByteStart
      | Chip::ByteRead
      | Chip::ByteAppend
      | Chip::ByteEq
      | Chip::ByteFinish
      | Chip::ByteEmit
      | Chip::HashBlock
      | Chip::HashCombine
      | Chip::HashPush
      | Chip::HashSkip => {
        self.byte_step(b, chip, enabled, state, advice, parameters)
      },
      _ => self.object_step(b, chip, enabled, state, advice, parameters),
    }
  }
}
