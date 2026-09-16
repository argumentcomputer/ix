//! Native advice generation. Every result is checked by the separately
//! compiled gate tables and by authenticated memory/state constraints.
use super::*;
use crate::{
  extension::goldilocks_ext2_mul,
  goldilocks::goldilocks_add,
  hash::{Blake3Gate, IV, pack8},
  ixby::{
    auth_memory::SparseMemory,
    decode::PrimitiveSet,
    memory_log::{AccessAdvice, MemoryBatch},
    paged_code::{
      CONSTRUCTORS, CodeGate, CodeGateKind, FUNCTIONS, block_address,
    },
    paged_frame::{CONTINUATIONS, FrameGate, LOCALS, Phase, SCRATCH},
    paged_nat::Nat128Gate,
    paged_primitive::PrimitiveRouteGate,
    primitive::{PrimitiveFinishGate, PrimitivePrepareGate},
  },
};
use anyhow::{Context, Result, bail, ensure};
use flock_prover::circuit::builder::GateType;

pub struct RowAdvice {
  pub chip: Chip,
  pub clock: u64,
  pub before: [F128; STATE_WORDS],
  pub after: [F128; STATE_WORDS],
  pub advice: Vec<F128>,
  pub accesses: Vec<AccessAdvice>,
}
pub struct NativeMachine {
  pub state: [F128; STATE_WORDS],
  pub clock: u64,
  pub parameters: [F128; 3],
  micro: Vec<MicroGate>,
  code: Vec<CodeGate>,
  frame: FrameGate,
  route: PrimitiveRouteGate,
  nat: Nat128Gate,
  prepare: PrimitivePrepareGate,
  finish: PrimitiveFinishGate,
  #[cfg(test)]
  pub(super) compare_native_advice: bool,
}
fn run<G: GateType<Hint = ()>>(gate: &G, input: &[F128]) -> Result<Vec<F128>> {
  let mut output = Vec::new();
  gate.eval(input, &(), &mut output);
  ensure!(
    output.last() == Some(&F128::ZERO),
    "native advice violates gate relation"
  );
  output.pop();
  Ok(output)
}
fn records(words: &[F128]) -> Vec<AccessAdvice> {
  words
    .as_chunks::<4>()
    .0
    .iter()
    .map(|r| AccessAdvice {
      address: r[0].lo,
      write: r[1] == F128::ONE,
      value: [r[2], r[3]],
    })
    .collect()
}
impl NativeMachine {
  pub fn new(
    state: [F128; STATE_WORDS],
    clock: u64,
    parameters: [F128; 3],
  ) -> Result<Self> {
    let machine = Self {
      state,
      clock,
      parameters,
      micro: MicroKind::ALL
        .into_iter()
        .map(|k| MicroGate::new(3, k))
        .collect::<Result<_>>()?,
      code: [
        CodeGateKind::Block,
        CodeGateKind::Operand,
        CodeGateKind::Function,
        CodeGateKind::Constructor,
        CodeGateKind::Alternative,
      ]
      .into_iter()
      .map(|k| CodeGate::new(3, k))
      .collect::<Result<_>>()?,
      frame: FrameGate::new(3)?,
      route: PrimitiveRouteGate::new(3)?,
      nat: Nat128Gate::new(3)?,
      prepare: PrimitivePrepareGate::new(
        3,
        2,
        PrimitiveSet::crypto().crypto_scalar_subset(),
      )?,
      finish: PrimitiveFinishGate::new(3)?,
      #[cfg(test)]
      compare_native_advice: true,
    };
    machine.micro(MicroKind::Parameters, &parameters)?;
    Ok(machine)
  }
  fn micro(&self, kind: MicroKind, input: &[F128]) -> Result<Vec<F128>> {
    let gate = self.micro.iter().find(|g| g.kind() == kind).unwrap();
    if let Some(out) = fast_advice::micro(kind, input) {
      #[cfg(test)]
      if self.compare_native_advice {
        ensure!(
          out == run(gate, input)?,
          "native {kind:?} advice differs from Boolean plan"
        );
      }
      return Ok(out);
    }
    run(gate, input).with_context(|| format!("execution {kind:?}"))
  }
  fn code(&self, index: usize, input: &[F128]) -> Result<Vec<F128>> {
    let gate = &self.code[index];
    if let Some(out) = fast_advice::code(gate.kind(), input) {
      #[cfg(test)]
      if self.compare_native_advice {
        ensure!(
          out == run(gate, input)?,
          "native {:?} advice differs from Boolean plan",
          gate.kind()
        );
      }
      return Ok(out);
    }
    run(gate, input)
  }
  pub fn next_chip(&self) -> Result<Option<Chip>> {
    Ok(Some(match self.state[CONTROL].lo as u8 {
      0 => match self.state[0].lo as u8 {
        x if x == Phase::Eval as u8 => Chip::Fetch,
        x if x == Phase::Return as u8 || x == Phase::Copy as u8 => Chip::Resume,
        x if x == Phase::Halted as u8 => return Ok(None),
        x if x == Phase::Apply as u8 => Chip::Apply,
        p => bail!("pending implementation: paged frame phase {p}"),
      },
      1 => Chip::Resolve,
      2 => {
        let h = self.state[HEADER];
        let instruction = (h.lo >> 8) as u8;
        let op = (h.lo >> 16) as u8;
        match (instruction, op) {
          (0, 1) => {
            if bytes::is_byte((h.lo >> 24) as u8) {
              Chip::ByteStart
            } else {
              Chip::Numeric
            }
          },
          (0, 0) | (1 | 6 | 7, _) => Chip::Control,
          (0, 5 | 6) | (2 | 3, _) => Chip::Call,
          (0, 2) => Chip::Construct,
          (0, 3) => Chip::Project,
          (0, 4) => Chip::Closure,
          (0, 7) | (4, _) => Chip::ApplyInstruction,
          (5, _) => Chip::Case,
          _ => bail!(
            "pending implementation: paged instruction {instruction}, operation {op}"
          ),
        }
      },
      3 => {
        let control = self.state[CONTROL].lo;
        if ((control >> 8) as u8) < (control >> 16) as u8 {
          Chip::StoreCopy
        } else {
          Chip::StoreFinish
        }
      },
      4 => Chip::ByteFinish,
      5 => Chip::ByteRead,
      6 => Chip::ByteAppend,
      7 => Chip::ByteEq,
      8 => Chip::HashBlock,
      9 => {
        let control = self.state[bytes::MERGE_CONTROL];
        ensure!(control.lo <= 26, "BLAKE3 merge level");
        if self.state[bytes::MERGE_MASK].lo & (1 << control.lo) != 0 {
          Chip::HashCombine
        } else if control.hi == 1 {
          Chip::HashSkip
        } else {
          Chip::HashPush
        }
      },
      10 => Chip::ByteEmit,
      p => bail!("pending implementation: paged micro phase {p}"),
    }))
  }
  fn numeric(&self, header: F128, args: &[F128]) -> Result<[F128; 2]> {
    let r = run(
      &self.route,
      &[F128::ONE, header]
        .into_iter()
        .chain(args.iter().copied())
        .collect::<Vec<_>>(),
    )?;
    ensure!(
      r[12] == F128::ZERO,
      "pending implementation: paged byte primitive {}",
      r[12].lo
    );
    let n = run(&self.nat, &r[1..6])?;
    let p = run(&self.prepare, &r[6..12])?;
    let sum = F128::new(
      goldilocks_add(p[2].lo, p[3].lo),
      goldilocks_add(p[2].hi, p[3].hi),
    );
    let product = goldilocks_ext2_mul(p[2], p[3]);
    let value =
      run(&self.finish, &[p[0], p[1], p[6], sum, product, p[4], p[5]])?;
    Ok(if r[0] == F128::ONE {
      n.try_into().unwrap()
    } else {
      value.try_into().unwrap()
    })
  }
  fn byte_window(
    &self,
    memory: &MemoryBatch<'_>,
    prefix: &[F128],
    request: &[F128],
  ) -> Result<(Vec<F128>, Vec<F128>, Vec<AccessAdvice>)> {
    let pointer = request[0].lo;
    let count = request[1].lo;
    let n = ((pointer & 31) + count).div_ceil(32);
    ensure!(n <= 3, "byte window cell count");
    let mut advice = Vec::new();
    for i in 0..3 {
      advice.extend(if i < n {
        memory.value((pointer >> 5) + i)?
      } else {
        [F128::ZERO; 2]
      });
    }
    let input =
      prefix.iter().chain(request).chain(&advice).copied().collect::<Vec<_>>();
    let out = self.micro(MicroKind::Byte(ByteKind::Window), &input)?;
    Ok((out[..4].to_vec(), advice, records(&out[4..])))
  }
  fn compress(input: [F128; 7]) -> [F128; 2] {
    let mut out = Vec::new();
    Blake3Gate { nu: 3 }.eval(&input, &(), &mut out);
    out[..2].try_into().unwrap()
  }
  fn complete(
    &self,
    prefix: &[F128],
    action: &[F128],
    reply: [F128; 2],
    accesses: &mut Vec<AccessAdvice>,
  ) -> Result<[F128; STATE_WORDS]> {
    let frame = run(
      &self.frame,
      &self.state[..5]
        .iter()
        .copied()
        .chain(action.iter().copied())
        .chain(reply)
        .chain([self.parameters[0]])
        .collect::<Vec<_>>(),
    )?;
    accesses.extend(records(&frame[5..17]));
    let fuel = self.state[FUEL];
    let fuel = if frame[17] == F128::new(2, 0) {
      fuel
    } else {
      ensure!(
        fuel.lo > 0 && fuel.hi < self.parameters[1].lo,
        "execution fuel exhausted"
      );
      F128::new(fuel.lo - 1, fuel.hi + 1)
    };
    let after = self.micro(
      MicroKind::Complete,
      &prefix
        .iter()
        .copied()
        .chain(frame[..5].iter().copied())
        .chain([fuel])
        .collect::<Vec<_>>(),
    )?;
    Ok(after.try_into().unwrap())
  }
  pub fn preview(&self, memory: &MemoryBatch<'_>) -> Result<RowAdvice> {
    let chip = self
      .next_chip()?
      .ok_or_else(|| anyhow::anyhow!("execution already halted"))?;
    let before = self.state;
    let prefix = [F128::ONE].into_iter().chain(before).collect::<Vec<_>>();
    let append = |values: &[F128]| {
      prefix.iter().copied().chain(values.iter().copied()).collect::<Vec<_>>()
    };
    let function = (before[0].lo >> 8) as u16;
    let block = (before[0].lo >> 24) as u8;
    let depth = before[0].lo >> 48;
    let mut accesses = Vec::new();
    let advice;
    let after;
    match chip {
      Chip::Fetch => {
        let cell = memory.value(block_address(function, block))?;
        advice = cell.to_vec();
        let read = self.code(0, &[F128::ONE, before[0], cell[0], cell[1]])?;
        accesses.extend(records(&read));
        after =
          self.micro(MicroKind::Fetch, &append(&cell))?.try_into().unwrap();
      },
      Chip::Resolve => {
        let request = self.micro(MicroKind::ResolveRequest, &prefix)?;
        let cell =
          memory.value(block_address(function, block) + 1 + request[0].lo)?;
        let local = if cell[0] == F128::ZERO {
          memory.value(LOCALS + depth * 128 + cell[1].lo)?
        } else {
          [F128::ZERO; 2]
        };
        advice = cell.into_iter().chain(local).collect();
        let read = self.code(
          1,
          &[
            F128::ONE,
            before[0],
            request[0],
            request[1],
            cell[0],
            cell[1],
            local[0],
            local[1],
          ],
        )?;
        accesses.extend(records(&read[..8]));
        let out =
          self.micro(MicroKind::ResolveFinish, &append(&read[8..10]))?;
        accesses.extend(records(&out[STATE_WORDS..]));
        after = out[..STATE_WORDS].try_into().unwrap();
      },
      Chip::Numeric | Chip::Control => {
        let n = if chip == Chip::Numeric { 3 } else { 1 };
        let count = (before[HEADER].lo >> 32) as u8 as usize;
        advice = (0..n)
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
        let out = self.micro(MicroKind::Scratch(n), &append(&advice))?;
        accesses.extend(records(&out));
        let (value, kind) = if chip == Chip::Numeric {
          (self.numeric(before[HEADER], &advice)?, MicroKind::NumericAction)
        } else {
          (advice[..2].try_into().unwrap(), MicroKind::ControlAction)
        };
        let action = self.micro(kind, &append(&value))?;
        after =
          self.complete(&prefix, &action, [F128::ZERO; 2], &mut accesses)?;
      },
      Chip::Call => {
        let reference = self.micro(MicroKind::CallReference, &prefix)?[0];
        let cell = memory.value(FUNCTIONS + reference.lo)?;
        advice = cell.to_vec();
        let read = self.code(2, &[F128::ONE, reference, cell[0], cell[1]])?;
        accesses.extend(records(&read));
        let action = self.micro(MicroKind::CallAction, &append(&cell))?;
        after =
          self.complete(&prefix, &action, [F128::ZERO; 2], &mut accesses)?;
      },
      Chip::Resume => {
        self.micro(MicroKind::Resume, &prefix)?;
        let address = if before[0].lo as u8 == Phase::Copy as u8 {
          before[1].lo + (before[0].hi & 255)
        } else if depth == 0 {
          0
        } else {
          CONTINUATIONS + depth - 1
        };
        let cell = memory.value(address)?;
        advice = cell.to_vec();
        after =
          self.complete(&prefix, &[F128::ZERO; 5], cell, &mut accesses)?;
      },
      Chip::Construct | Chip::Closure => {
        let reference =
          self.micro(MicroKind::Object(ObjectKind::Reference), &prefix)?[0];
        let (at, address, kind) = if chip == Chip::Construct {
          (3, CONSTRUCTORS + 3 * reference.lo + 2, ObjectKind::Construct)
        } else {
          (2, FUNCTIONS + reference.lo, ObjectKind::Closure)
        };
        let cell = memory.value(address)?;
        advice = cell.to_vec();
        let read = self.code(at, &[F128::ONE, reference, cell[0], cell[1]])?;
        accesses.extend(records(&read));
        after = self
          .micro(MicroKind::Object(kind), &append(&cell))?
          .try_into()
          .unwrap();
      },
      Chip::ApplyInstruction | Chip::Project | Chip::Case => {
        let request =
          self.micro(MicroKind::Object(ObjectKind::OperandRequest), &prefix)?;
        let value = memory.value(request[0].lo)?;
        accesses.push(AccessAdvice {
          address: request[0].lo,
          write: false,
          value,
        });
        if chip == Chip::ApplyInstruction {
          advice = value.to_vec();
          after = self
            .micro(
              MicroKind::Object(ObjectKind::ApplyInstruction),
              &append(&value),
            )?
            .try_into()
            .unwrap();
        } else {
          let action = if chip == Chip::Project {
            let address = self.micro(
              MicroKind::Object(ObjectKind::ProjectRequest),
              &append(&value),
            )?[0];
            let field = memory.value(address.lo)?;
            accesses.push(AccessAdvice {
              address: address.lo,
              write: false,
              value: field,
            });
            advice = value.into_iter().chain(field).collect::<Vec<_>>();
            self.micro(
              MicroKind::Object(ObjectKind::ProjectAction),
              &append(&advice),
            )?
          } else {
            let mut selected = None;
            for i in 0..request[1].lo {
              let alt =
                memory.value(block_address(function, block) + 128 + i)?;
              if alt[0].lo as u8 as u64 == value[0].hi {
                selected = Some((F128::new(i, 0), alt));
                break;
              }
            }
            let (index, alt) = selected.ok_or_else(|| {
              anyhow::anyhow!("constructor alternative missing")
            })?;
            let read = self.code(
              4,
              &[F128::ONE, before[0], index, request[1], alt[0], alt[1]],
            )?;
            accesses.extend(records(&read));
            advice =
              value.into_iter().chain([index]).chain(alt).collect::<Vec<_>>();
            self.micro(
              MicroKind::Object(ObjectKind::CaseAction),
              &append(&value.into_iter().chain(alt).collect::<Vec<_>>()),
            )?
          };
          after =
            self.complete(&prefix, &action, [F128::ZERO; 2], &mut accesses)?;
        }
      },
      Chip::Apply => {
        let request =
          self.micro(MicroKind::Object(ObjectKind::ApplyRequest), &prefix)?;
        let cell = if request[0] == F128::ONE {
          memory.value(FUNCTIONS + request[1].lo)?
        } else {
          [F128::ZERO; 2]
        };
        advice = cell.to_vec();
        let read = self.code(2, &[request[0], request[1], cell[0], cell[1]])?;
        accesses.extend(records(&read));
        after = self
          .micro(MicroKind::Object(ObjectKind::ApplyStart), &append(&cell))?
          .try_into()
          .unwrap();
      },
      Chip::StoreCopy => {
        let address =
          self.micro(MicroKind::Object(ObjectKind::StoreRequest), &prefix)?[0];
        let cell = memory.value(address.lo)?;
        advice = cell.to_vec();
        let out = self
          .micro(MicroKind::Object(ObjectKind::StoreCopy), &append(&cell))?;
        after = out[..STATE_WORDS].try_into().unwrap();
        accesses.extend(records(&out[STATE_WORDS..]));
      },
      Chip::StoreFinish => {
        advice = Vec::new();
        let action =
          self.micro(MicroKind::Object(ObjectKind::StoreFinish), &prefix)?;
        after =
          self.complete(&prefix, &action, [F128::ZERO; 2], &mut accesses)?;
      },
      Chip::ByteStart => {
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
        let out = self.micro(MicroKind::Scratch(3), &append(&advice))?;
        accesses.extend(records(&out));
        let args = advice
          .iter()
          .copied()
          .chain([self.parameters[2]])
          .collect::<Vec<_>>();
        after = self
          .micro(MicroKind::Byte(ByteKind::Start), &append(&args))?
          .try_into()
          .unwrap();
      },
      Chip::ByteRead | Chip::HashBlock => {
        let kind = if chip == Chip::ByteRead {
          ByteKind::ReadRequest
        } else {
          ByteKind::HashRequest
        };
        let request = self.micro(MicroKind::Byte(kind), &prefix)?;
        let (data, replies, reads) =
          self.byte_window(memory, &prefix, &request[..2])?;
        advice = replies;
        accesses.extend(reads);
        let (kind, value) = if chip == Chip::ByteRead {
          (ByteKind::ReadFinish, data)
        } else {
          (
            ByteKind::HashFinish,
            Self::compress([
              request[2], request[3], data[0], data[1], data[2], data[3],
              request[4],
            ])
            .to_vec(),
          )
        };
        after = self
          .micro(MicroKind::Byte(kind), &append(&value))?
          .try_into()
          .unwrap();
      },
      Chip::ByteAppend | Chip::ByteEq => {
        let (request, finish) = if chip == Chip::ByteAppend {
          (ByteKind::AppendRequest, ByteKind::AppendFinish)
        } else {
          (ByteKind::EqRequest, ByteKind::EqFinish)
        };
        let request = self.micro(MicroKind::Byte(request), &prefix)?;
        let (a, replies_a, reads_a) =
          self.byte_window(memory, &prefix, &request[..2])?;
        let (b, replies_b, reads_b) =
          self.byte_window(memory, &prefix, &request[2..])?;
        advice = replies_a.into_iter().chain(replies_b).collect();
        accesses.extend(reads_a);
        accesses.extend(reads_b);
        let data = a.into_iter().chain(b).collect::<Vec<_>>();
        let out = self.micro(MicroKind::Byte(finish), &append(&data))?;
        after = out[..STATE_WORDS].try_into().unwrap();
        accesses.extend(records(&out[STATE_WORDS..]));
      },
      Chip::ByteFinish => {
        advice = Vec::new();
        let action = self.micro(MicroKind::Byte(ByteKind::Finish), &prefix)?;
        after =
          self.complete(&prefix, &action, [F128::ZERO; 2], &mut accesses)?;
      },
      Chip::ByteEmit | Chip::HashPush | Chip::HashSkip => {
        advice = Vec::new();
        let kind = match chip {
          Chip::ByteEmit => ByteKind::Emit,
          Chip::HashPush => ByteKind::HashPush,
          _ => ByteKind::HashSkip,
        };
        let out = self.micro(MicroKind::Byte(kind), &prefix)?;
        after = out[..STATE_WORDS].try_into().unwrap();
        accesses.extend(records(&out[STATE_WORDS..]));
      },
      Chip::HashCombine => {
        let request =
          self.micro(MicroKind::Byte(ByteKind::HashMergeRequest), &prefix)?;
        let cell = memory.value(request[0].lo)?;
        advice = cell.to_vec();
        accesses.push(AccessAdvice {
          address: request[0].lo,
          write: false,
          value: cell,
        });
        let iv = pack8(&IV);
        let digest = Self::compress([
          iv[0],
          iv[1],
          cell[0],
          cell[1],
          before[bytes::CV],
          before[bytes::CV + 1],
          request[1],
        ]);
        after = self
          .micro(MicroKind::Byte(ByteKind::HashMergeFinish), &append(&digest))?
          .try_into()
          .unwrap();
      },
    }
    ensure!(accesses.len() == chip.accesses(), "native access count");
    Ok(RowAdvice { chip, clock: self.clock, before, after, advice, accesses })
  }
  pub fn commit(
    &mut self,
    memory: &mut MemoryBatch<'_>,
    row: &RowAdvice,
  ) -> Result<()> {
    ensure!(
      row.clock == self.clock && row.before == self.state,
      "stale execution preview"
    );
    let clock = self
      .clock
      .checked_add(1)
      .ok_or_else(|| anyhow::anyhow!("execution clock exhausted"))?;
    for access in &row.accesses {
      if access.write {
        memory.write(access.address, access.value)?;
      } else {
        ensure!(
          memory.read(access.address)? == access.value,
          "native memory reply mismatch"
        );
      }
    }
    self.state = row.after;
    self.clock = clock;
    Ok(())
  }
  pub fn step(&mut self, memory: &mut MemoryBatch<'_>) -> Result<RowAdvice> {
    let row = self.preview(memory)?;
    self.commit(memory, &row)?;
    Ok(row)
  }
  /// Stop before exceeding any fixed circuit quota. A suspended instruction
  /// is carried in the complete public boundary state, including its copy job.
  pub fn batch(
    &mut self,
    class: BatchClass,
    memory: &mut SparseMemory,
  ) -> Result<Option<BatchAdvice>> {
    if self.next_chip()?.is_none() {
      return Ok(None);
    }
    let mut memory = MemoryBatch::new(memory);
    let mut counts = [0; Chip::ALL.len()];
    let quotas = class.quotas();
    let mut rows = Vec::new();
    while let Some(chip) = self.next_chip()? {
      if counts[chip as usize] == quotas[chip as usize] {
        break;
      }
      let row = self.preview(&memory)?;
      if memory.prospective_cells(&row.accesses) > class.cells() {
        break;
      }
      if class
        .shared_memory()
        .is_some_and(|capacity| !memory.fits_shared(&row.accesses, capacity))
      {
        break;
      }
      self.commit(&mut memory, &row)?;
      counts[chip as usize] += 1;
      rows.push(row);
    }
    ensure!(
      !rows.is_empty(),
      "batch class cannot admit the next execution step"
    );
    let advice = if let Some(capacity) = class.shared_memory() {
      let (memory, tree) = memory.finish_shared(capacity)?;
      BatchAdvice::new_shared(class, self.parameters, &rows, &memory, &tree)?
    } else {
      let memory = memory.finish_padded(class.cells())?;
      BatchAdvice::new(class, self.parameters, &rows, &memory)?
    };
    Ok(Some(advice))
  }
}
