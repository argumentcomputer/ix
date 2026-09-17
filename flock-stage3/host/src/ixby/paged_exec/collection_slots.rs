use super::*;
use crate::{ixby::memory_log::AccessWires, sizing::CircuitEmitter};
use flock_prover::circuit::builder::Wire;
fn records(words: &[Wire]) -> Vec<AccessWires> {
  words
    .as_chunks::<4>()
    .0
    .iter()
    .map(|r| AccessWires { address: r[0], write: r[1], value: [r[2], r[3]] })
    .collect()
}
impl ExecutionSlots {
  #[allow(clippy::too_many_arguments)]
  pub(super) fn collection_step(
    &self,
    b: &mut impl CircuitEmitter,
    chip: Chip,
    enabled: Wire,
    state: [Wire; STATE_WORDS],
    advice: &[Wire],
    parameters: [Wire; 3],
  ) -> StepWires {
    let prefix = [enabled].into_iter().chain(state).collect::<Vec<_>>();
    let append =
      |extra: &[Wire]| prefix.iter().chain(extra).copied().collect::<Vec<_>>();
    let invoke = |b: &mut _, kind, input: &[Wire]| {
      self.gate(b, MicroKind::Collection(kind), input)
    };
    match chip {
      Chip::CollectionStart => {
        let scratch = self.gate(b, MicroKind::Scratch(3), &append(advice));
        let extra =
          advice.iter().copied().chain([parameters[2]]).collect::<Vec<_>>();
        let out = invoke(b, CollectionKind::Start, &append(&extra));
        let mut accesses = records(&scratch);
        accesses.extend(records(&out[STATE_WORDS..]));
        StepWires { state: out[..STATE_WORDS].try_into().unwrap(), accesses }
      },
      Chip::ArrayStep | Chip::ArrayAscend | Chip::BuilderNode => {
        let (request, step) = match chip {
          Chip::ArrayStep => {
            (CollectionKind::ArrayRequest, CollectionKind::ArrayStep)
          },
          Chip::ArrayAscend => {
            (CollectionKind::AscendRequest, CollectionKind::Ascend)
          },
          _ => (CollectionKind::BuilderRequest, CollectionKind::BuilderNode),
        };
        let addresses = invoke(b, request, &prefix);
        let mut accesses = addresses
          .into_iter()
          .zip(advice.as_chunks::<2>().0)
          .map(|(address, value)| AccessWires {
            address,
            write: self.zero,
            value: *value,
          })
          .collect::<Vec<_>>();
        let out = invoke(b, step, &append(advice));
        accesses.extend(records(&out[STATE_WORDS..]));
        StepWires { state: out[..STATE_WORDS].try_into().unwrap(), accesses }
      },
      Chip::BuilderCopy => {
        let request = invoke(b, CollectionKind::CopyRequest, &prefix);
        let (data, accesses) = self.byte_window(b, &prefix, &request, advice);
        let out = invoke(b, CollectionKind::Copy, &append(&data));
        StepWires { state: out.try_into().unwrap(), accesses }
      },
      Chip::BuilderEmit => {
        let out = invoke(b, CollectionKind::Emit, &prefix);
        StepWires {
          state: out[..STATE_WORDS].try_into().unwrap(),
          accesses: records(&out[STATE_WORDS..]),
        }
      },
      Chip::CollectionFinish => {
        let action = invoke(b, CollectionKind::Finish, &prefix);
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
