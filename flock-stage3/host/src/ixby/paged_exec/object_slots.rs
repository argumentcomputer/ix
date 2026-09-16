use super::*;
use crate::{ixby::memory_log::AccessWires, sizing::CircuitEmitter};
use flock_prover::circuit::builder::Wire;

impl ExecutionSlots {
  #[allow(clippy::too_many_arguments)]
  pub(super) fn object_step(
    &self,
    b: &mut impl CircuitEmitter,
    chip: Chip,
    enabled: Wire,
    state: [Wire; STATE_WORDS],
    advice: &[Wire],
    parameters: [Wire; 3],
  ) -> StepWires {
    let prefix = [enabled].into_iter().chain(state).collect::<Vec<_>>();
    let append = |values: &[Wire]| {
      prefix.iter().copied().chain(values.iter().copied()).collect::<Vec<_>>()
    };
    let read =
      |address, value| AccessWires { address, write: self.zero, value };
    let invoke = |b: &mut _, kind, input: &[Wire]| {
      self.gate(b, MicroKind::Object(kind), input)
    };
    match chip {
      Chip::Construct | Chip::Closure => {
        let reference = invoke(b, ObjectKind::Reference, &prefix)[0];
        let reply = advice.try_into().unwrap();
        let (loaded, kind) = if chip == Chip::Construct {
          (
            self.code.constructor(b, enabled, reference, reply),
            ObjectKind::Construct,
          )
        } else {
          (
            self.code.function(b, enabled, reference, reply),
            ObjectKind::Closure,
          )
        };
        let after = invoke(b, kind, &append(&loaded.value));
        StepWires {
          state: after.try_into().unwrap(),
          accesses: vec![loaded.access],
        }
      },
      Chip::ApplyInstruction | Chip::Project | Chip::Case => {
        let request = invoke(b, ObjectKind::OperandRequest, &prefix);
        let value: [Wire; 2] = advice[..2].try_into().unwrap();
        let mut accesses = vec![read(request[0], value)];
        if chip == Chip::ApplyInstruction {
          let after = invoke(b, ObjectKind::ApplyInstruction, &append(&value));
          return StepWires { state: after.try_into().unwrap(), accesses };
        }
        let (input, kind) = if chip == Chip::Project {
          let address =
            invoke(b, ObjectKind::ProjectRequest, &append(&value))[0];
          let field: [Wire; 2] = advice[2..].try_into().unwrap();
          accesses.push(read(address, field));
          (append(&advice[..4]), ObjectKind::ProjectAction)
        } else {
          let alt = self.code.alternative(
            b,
            enabled,
            state[0],
            advice[2],
            request[1],
            advice[3..].try_into().unwrap(),
          );
          accesses.push(alt.access);
          (
            append(&value.into_iter().chain(alt.value).collect::<Vec<_>>()),
            ObjectKind::CaseAction,
          )
        };
        let action = invoke(b, kind, &input);
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
      Chip::Apply => {
        let request = invoke(b, ObjectKind::ApplyRequest, &prefix);
        let loaded = self.code.function(
          b,
          request[0],
          request[1],
          advice.try_into().unwrap(),
        );
        let after = invoke(b, ObjectKind::ApplyStart, &append(&loaded.value));
        StepWires {
          state: after.try_into().unwrap(),
          accesses: vec![loaded.access],
        }
      },
      Chip::StoreCopy => {
        let out = invoke(b, ObjectKind::StoreCopy, &append(advice));
        let accesses = out[STATE_WORDS..]
          .as_chunks::<4>()
          .0
          .iter()
          .map(|r| AccessWires {
            address: r[0],
            write: r[1],
            value: [r[2], r[3]],
          })
          .collect();
        StepWires { state: out[..STATE_WORDS].try_into().unwrap(), accesses }
      },
      Chip::StoreFinish => {
        let action = invoke(b, ObjectKind::StoreFinish, &prefix);
        self.complete(
          b,
          enabled,
          state,
          action.try_into().unwrap(),
          [self.zero; 2],
          parameters,
          Vec::new(),
        )
      },
      _ => unreachable!(),
    }
  }
}
