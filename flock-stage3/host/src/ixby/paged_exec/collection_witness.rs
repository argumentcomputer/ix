use super::witness::records;
use super::*;
use crate::ixby::{
  memory_log::{AccessAdvice, MemoryBatch},
  paged_frame::SCRATCH,
};
use anyhow::Result;
impl NativeMachine {
  pub(super) fn collection_step(
    &self,
    chip: Chip,
    before: [F128; STATE_WORDS],
    memory: &MemoryBatch<'_>,
  ) -> Result<(Vec<F128>, [F128; STATE_WORDS], Vec<AccessAdvice>)> {
    let prefix = [F128::ONE].into_iter().chain(before).collect::<Vec<_>>();
    let append =
      |extra: &[F128]| prefix.iter().chain(extra).copied().collect::<Vec<_>>();
    let invoke =
      |kind, input: &[F128]| self.micro(MicroKind::Collection(kind), input);
    let mut accesses = Vec::new();
    let advice;
    let out;
    match chip {
      Chip::CollectionStart => {
        let count = (before[HEADER].lo >> 32) as u8 as usize;
        advice = (0..3)
          .map(|i| {
            if i < count {
              memory.value(SCRATCH + i as u64)
            } else {
              Ok([F128::ZERO; 2])
            }
          })
          .collect::<Result<Vec<_>>>()?
          .into_iter()
          .flatten()
          .collect::<Vec<_>>();
        accesses.extend(records(
          &self.micro(MicroKind::Scratch(3), &append(&advice))?,
        ));
        let args = advice
          .iter()
          .copied()
          .chain([self.parameters[2]])
          .collect::<Vec<_>>();
        out = invoke(CollectionKind::Start, &append(&args))?;
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
        let mut values = Vec::new();
        for address in invoke(request, &prefix)? {
          let value = memory.value(address.lo)?;
          values.extend(value);
          accesses.push(AccessAdvice {
            address: address.lo,
            write: false,
            value,
          });
        }
        advice = values;
        out = invoke(step, &append(&advice))?;
      },
      Chip::BuilderCopy => {
        let request = invoke(CollectionKind::CopyRequest, &prefix)?;
        let (data, replies, reads) =
          self.byte_window(memory, &prefix, &request)?;
        advice = replies;
        accesses.extend(reads);
        out = invoke(CollectionKind::Copy, &append(&data))?;
      },
      Chip::BuilderEmit => {
        advice = Vec::new();
        out = invoke(CollectionKind::Emit, &prefix)?;
      },
      Chip::CollectionFinish => {
        let action = invoke(CollectionKind::Finish, &prefix)?;
        let after =
          self.complete(&prefix, &action, [F128::ZERO; 2], &mut accesses)?;
        return Ok((Vec::new(), after, accesses));
      },
      _ => unreachable!(),
    }
    accesses.extend(records(&out[STATE_WORDS..]));
    Ok((advice, out[..STATE_WORDS].try_into().unwrap(), accesses))
  }
}
