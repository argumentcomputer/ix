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
  fn byte_window(
    &self,
    b: &mut impl CircuitEmitter,
    prefix: &[Wire],
    request: &[Wire],
    reply: &[Wire],
  ) -> (Vec<Wire>, Vec<AccessWires>) {
    let input =
      prefix.iter().chain(request).chain(reply).copied().collect::<Vec<_>>();
    let out = self.gate(b, MicroKind::Byte(ByteKind::Window), &input);
    (out[..4].to_vec(), records(&out[4..]))
  }
  #[allow(clippy::too_many_arguments)]
  pub(super) fn byte_step(
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
      self.gate(b, MicroKind::Byte(kind), input)
    };
    match chip {
      Chip::ByteStart => {
        let access = self.gate(b, MicroKind::Scratch(3), &append(advice));
        let extra =
          advice.iter().copied().chain([parameters[2]]).collect::<Vec<_>>();
        let after = invoke(b, ByteKind::Start, &append(&extra));
        StepWires {
          state: after.try_into().unwrap(),
          accesses: records(&access),
        }
      },
      Chip::ByteRead => {
        let request = invoke(b, ByteKind::ReadRequest, &prefix);
        let (data, accesses) = self.byte_window(b, &prefix, &request, advice);
        let after = invoke(b, ByteKind::ReadFinish, &append(&data));
        StepWires { state: after.try_into().unwrap(), accesses }
      },
      Chip::ByteAppend | Chip::ByteEq => {
        let (request, finish) = if chip == Chip::ByteAppend {
          (ByteKind::AppendRequest, ByteKind::AppendFinish)
        } else {
          (ByteKind::EqRequest, ByteKind::EqFinish)
        };
        let request = invoke(b, request, &prefix);
        let (a, mut accesses) =
          self.byte_window(b, &prefix, &request[..2], &advice[..6]);
        let (data_b, access_b) =
          self.byte_window(b, &prefix, &request[2..], &advice[6..]);
        accesses.extend(access_b);
        let data = a.into_iter().chain(data_b).collect::<Vec<_>>();
        let after = invoke(b, finish, &append(&data));
        accesses.extend(records(&after[STATE_WORDS..]));
        StepWires { state: after[..STATE_WORDS].try_into().unwrap(), accesses }
      },
      Chip::ByteFinish => {
        let action = invoke(b, ByteKind::Finish, &prefix);
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
      Chip::ByteEmit | Chip::HashPush | Chip::HashSkip => {
        let kind = match chip {
          Chip::ByteEmit => ByteKind::Emit,
          Chip::HashPush => ByteKind::HashPush,
          _ => ByteKind::HashSkip,
        };
        let out = invoke(b, kind, &prefix);
        StepWires {
          state: out[..STATE_WORDS].try_into().unwrap(),
          accesses: records(&out[STATE_WORDS..]),
        }
      },
      Chip::HashBlock => {
        let request = invoke(b, ByteKind::HashRequest, &prefix);
        let (data, accesses) =
          self.byte_window(b, &prefix, &request[..2], advice);
        let hash = self.compression.compress(
          b,
          [
            request[2], request[3], data[0], data[1], data[2], data[3],
            request[4],
          ],
        );
        let after = invoke(b, ByteKind::HashFinish, &append(&hash[..2]));
        StepWires { state: after.try_into().unwrap(), accesses }
      },
      Chip::HashCombine => {
        let request = invoke(b, ByteKind::HashMergeRequest, &prefix);
        let hash = self.compression.compress(
          b,
          [
            self.hash_iv[0],
            self.hash_iv[1],
            advice[0],
            advice[1],
            state[bytes::CV],
            state[bytes::CV + 1],
            request[1],
          ],
        );
        let after = invoke(b, ByteKind::HashMergeFinish, &append(&hash[..2]));
        StepWires {
          state: after.try_into().unwrap(),
          accesses: vec![AccessWires {
            address: request[0],
            write: self.zero,
            value: advice.try_into().unwrap(),
          }],
        }
      },
      _ => unreachable!(),
    }
  }
}
