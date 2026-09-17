//! Native advice generation. Every result is checked by the separately
//! compiled gate tables and by authenticated memory/state constraints.
use super::*;
use crate::{
  extension::goldilocks_ext2_mul,
  goldilocks::goldilocks_add,
  hash::{Blake3Gate, IV, pack8},
  ixby::{
    auth_memory::SparseMemory,
    memory_log::{AccessAdvice, MemoryBatch},
    paged_code::{
      CONSTRUCTORS, CodeGate, CodeGateKind, FUNCTIONS, block_address,
    },
    paged_frame::{CONTINUATIONS, FrameGate, LOCALS, Phase, SCRATCH},
    paged_nat::Nat128Gate,
    paged_primitive::PrimitiveRouteGate,
    primitive::registry::PrimitiveSet,
    primitive::{PrimitiveFinishGate, PrimitivePrepareGate},
  },
};
use anyhow::{Context, Result, bail, ensure};
use flock_prover::circuit::builder::GateType;

#[derive(Clone, Debug)]
pub struct RowAdvice {
  pub chip: Chip,
  /// Original microstep clock; a fused row advances by `chip.span()`.
  pub clock: u64,
  pub before: [F128; STATE_WORDS],
  pub after: [F128; STATE_WORDS],
  pub advice: Vec<F128>,
  pub accesses: Vec<AccessAdvice>,
}
impl RowAdvice {
  pub fn end_clock(&self) -> Result<u64> {
    self
      .clock
      .checked_add(u64::from(self.chip.span()))
      .ok_or_else(|| anyhow::anyhow!("execution clock exhausted"))
  }
}

#[derive(Clone)]
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
pub(super) fn records(words: &[F128]) -> Vec<AccessAdvice> {
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
  pub(super) fn micro(
    &self,
    kind: MicroKind,
    input: &[F128],
  ) -> Result<Vec<F128>> {
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
    Ok(Some(match self.state[CONTROL].lo & 255 {
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
            if collections::is_collection((h.lo >> 24) as u8) {
              Chip::CollectionStart
            } else if bytes::is_byte((h.lo >> 24) as u8) {
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
      collections::ARRAY_DOWN => Chip::ArrayStep,
      collections::ARRAY_UP => Chip::ArrayAscend,
      collections::FINISH => Chip::CollectionFinish,
      collections::BUILDER_NODE => Chip::BuilderNode,
      collections::BUILDER_COPY => Chip::BuilderCopy,
      collections::BUILDER_EMIT => Chip::BuilderEmit,
      p => bail!("pending implementation: paged micro phase {p}"),
    }))
  }
  fn numeric(&self, header: F128, args: &[F128]) -> Result<[F128; 2]> {
    if let Some(p) = numeric_native::primitive(header, args) {
      let opcode = p.opcode();
      let direct = if matches!(opcode, 0..=6 | 45..=48) {
        let control = if opcode <= 6 { opcode + 1 } else { opcode - 37 };
        let input = [
          F128::new(u64::from(control), 0),
          args[0],
          args[1],
          args[2],
          args[3],
        ];
        Some(run(&self.nat, &input)?.try_into().unwrap())
      } else {
        numeric_native::scalar(p, args)
      };
      if let Some(value) = direct {
        #[cfg(test)]
        if self.compare_native_advice {
          ensure!(
            value == self.numeric_reference(header, args)?,
            "native {p:?} advice differs from Boolean plans"
          );
        }
        return Ok(value);
      }
    }
    self.numeric_reference(header, args)
  }
  fn numeric_reference(
    &self,
    header: F128,
    args: &[F128],
  ) -> Result<[F128; 2]> {
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
  pub(super) fn byte_window(
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
  pub(super) fn complete(
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
      Chip::FusedControl
      | Chip::FusedNumeric
      | Chip::CopyPair
      | Chip::FusedCall0
      | Chip::FusedCall1
      | Chip::FusedCall2
      | Chip::FusedCall3
      | Chip::FusedCall4 => {
        unreachable!("fused rows are selected by preview_for_class")
      },
      Chip::CollectionStart
      | Chip::ArrayStep
      | Chip::ArrayAscend
      | Chip::CollectionFinish
      | Chip::BuilderNode
      | Chip::BuilderCopy
      | Chip::BuilderEmit => {
        let (values, next, records) =
          self.collection_step(chip, before, memory)?;
        advice = values;
        after = next;
        accesses = records;
      },
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
    let clock = row.end_clock()?;
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
  /// Select only setup-authorized fusions. An exact stop inside a potential
  /// fusion falls back to the original single-step relation.
  pub fn preview_for_class(
    &self,
    class: BatchClass,
    memory: &MemoryBatch<'_>,
    end_clock: u64,
  ) -> Result<RowAdvice> {
    if class.fused()
      && let Some(chip) = self.fused_chip(memory)?
      && self
        .clock
        .checked_add(u64::from(chip.span()))
        .is_some_and(|end| end <= end_clock)
    {
      return self.preview_fused(chip, memory);
    }
    self.preview(memory)
  }
  fn fused_chip(&self, memory: &MemoryBatch<'_>) -> Result<Option<Chip>> {
    if self.state[CONTROL] != F128::ZERO {
      return Ok(None);
    }
    let frame = self.state[0];
    if frame.lo as u8 == Phase::Copy as u8 {
      let index = frame.hi & 255;
      let count = (frame.hi >> 8) & 255;
      return Ok(
        count.checked_sub(index).filter(|n| *n >= 2).map(|_| Chip::CopyPair),
      );
    }
    if frame.lo as u8 != Phase::Eval as u8 {
      return Ok(None);
    }
    let header = memory
      .value(block_address((frame.lo >> 8) as u16, (frame.lo >> 24) as u8))?[0];
    let instruction = (header.lo >> 8) as u8;
    let operation = (header.lo >> 16) as u8;
    let primitive = (header.lo >> 24) as u8;
    let count = (header.lo >> 32) as u8;
    Ok(match (instruction, operation, count) {
      (0, 5 | 6, 0..=4) | (2 | 3, _, 0..=4) => {
        Some(Chip::FUSED_CALLS[count as usize])
      },
      (0, 0, 1) | (1 | 6 | 7, _, 1) => Some(Chip::FusedControl),
      (0, 1, 2)
        if !collections::is_collection(primitive)
          && !bytes::is_byte(primitive) =>
      {
        Some(Chip::FusedNumeric)
      },
      _ => None,
    })
  }
  fn preview_fused(
    &self,
    chip: Chip,
    memory: &MemoryBatch<'_>,
  ) -> Result<RowAdvice> {
    let mut view = self.clone();
    let mut advice = Vec::new();
    let mut accesses = Vec::new();
    let call_arity = chip.call_arity();
    let mut operands = Vec::new();
    let components = if chip == Chip::CopyPair {
      vec![Chip::Resume, Chip::Resume]
    } else if let Some(arity) = call_arity {
      std::iter::once(Chip::Fetch)
        .chain(std::iter::repeat_n(Chip::Resolve, arity))
        .collect()
    } else if chip == Chip::FusedControl {
      vec![Chip::Fetch, Chip::Resolve]
    } else {
      vec![Chip::Fetch, Chip::Resolve, Chip::Resolve]
    };
    for &expected in &components {
      let row = view.preview(memory)?;
      ensure!(row.chip == expected, "fused execution phase");
      if chip == Chip::CopyPair {
        let unused = row.accesses[1];
        ensure!(
          unused.address == 0
            && !unused.write
            && unused.value == [F128::ZERO; 2],
          "fused copy continuation"
        );
        accesses.extend([row.accesses[0], row.accesses[2]]);
      } else {
        if row.chip == Chip::Resolve {
          operands.extend(row.accesses[2].value);
        }
        accesses.extend(row.accesses.iter().copied());
      }
      advice.extend(row.advice);
      view.state = row.after;
      view.clock = row.clock + 1;
    }
    if let Some(arity) = call_arity {
      let row = view.preview(memory)?;
      ensure!(row.chip == Chip::Call, "fused call phase");
      for i in [1, 3] {
        let unused = row.accesses[i];
        ensure!(
          unused.address == 0
            && !unused.write
            && unused.value == [F128::ZERO; 2],
          "fused call unused event"
        );
      }
      accesses.extend([row.accesses[0], row.accesses[2]]);
      advice.extend(row.advice);
      view.state = row.after;
      ensure!(operands.len() == 2 * arity, "fused call arity");
      for (i, reply) in operands.as_chunks::<2>().0.iter().enumerate() {
        let prefix =
          [F128::ONE].into_iter().chain(view.state).collect::<Vec<_>>();
        view.micro(MicroKind::Resume, &prefix)?;
        let mut copied = Vec::new();
        view.state =
          view.complete(&prefix, &[F128::ZERO; 5], *reply, &mut copied)?;
        ensure!(
          copied[0].address == SCRATCH + i as u64
            && !copied[0].write
            && copied[0].value == *reply,
          "fused argument forwarding"
        );
        let unused = copied[1];
        ensure!(
          unused.address == 0
            && !unused.write
            && unused.value == [F128::ZERO; 2],
          "fused call copy continuation"
        );
        accesses.push(copied[2]);
      }
    } else if chip != Chip::CopyPair {
      operands.resize(6, F128::ZERO);
      let numeric = chip == Chip::FusedNumeric;
      let count = if numeric { 3 } else { 1 };
      let prefix =
        [F128::ONE].into_iter().chain(view.state).collect::<Vec<_>>();
      view.micro(
        MicroKind::Scratch(count),
        &prefix
          .iter()
          .copied()
          .chain(operands[..2 * count].iter().copied())
          .collect::<Vec<_>>(),
      )?;
      let (value, kind) = if numeric {
        (view.numeric(view.state[HEADER], &operands)?, MicroKind::NumericAction)
      } else {
        ([operands[0], operands[1]], MicroKind::ControlAction)
      };
      let action = view.micro(
        kind,
        &prefix.iter().copied().chain(value).collect::<Vec<_>>(),
      )?;
      view.state =
        view.complete(&prefix, &action, [F128::ZERO; 2], &mut accesses)?;
    }
    ensure!(
      advice.len() == chip.advice_words() && accesses.len() == chip.accesses(),
      "fused execution width"
    );
    Ok(RowAdvice {
      chip,
      clock: self.clock,
      before: self.state,
      after: view.state,
      advice,
      accesses,
    })
  }
  /// Stop before exceeding any fixed circuit quota. A suspended instruction
  /// is carried in the complete public boundary state, including its copy job.
  pub fn batch(
    &mut self,
    class: BatchClass,
    memory: &mut SparseMemory,
  ) -> Result<Option<BatchAdvice>> {
    self.batch_until(class, memory, u64::MAX)
  }
  /// End at an exact original microstep clock, or earlier at fixed quotas.
  /// Fusion falls back to single steps when the stop lies inside a macro.
  /// Padding and the authenticated boundary relation are identical to batch().
  pub fn batch_until(
    &mut self,
    class: BatchClass,
    memory: &mut SparseMemory,
    end_clock: u64,
  ) -> Result<Option<BatchAdvice>> {
    ensure!(
      end_clock >= self.clock,
      "execution boundary precedes current clock"
    );
    if end_clock == self.clock {
      return Ok(None);
    }
    if self.next_chip()?.is_none() {
      return Ok(None);
    }
    let mut memory = MemoryBatch::new(memory);
    if class.fused() {
      // Dummy reads may be omitted only with the reserved cell authenticated
      // as zero. The fused circuit pins its first boundary leaf independently.
      memory.include_cell(0)?;
      ensure!(
        memory.value(0)? == [F128::ZERO; 2],
        "reserved execution cell must be zero"
      );
    }
    let mut counts = [0; Chip::COUNT];
    let mut quotas = [0; Chip::COUNT];
    for (chip, quota) in class.chip_quotas() {
      quotas[chip as usize] = quota;
    }
    let mut rows = Vec::new();
    while self.next_chip()?.is_some() {
      if self.clock == end_clock {
        break;
      }
      let mut row = self.preview_for_class(class, &memory, end_clock)?;
      let fits = |row: &RowAdvice| {
        counts[row.chip as usize] < quotas[row.chip as usize]
          && memory.prospective_cells(&row.accesses) <= class.cells()
          && class
            .shared_memory()
            .is_none_or(|capacity| memory.fits_shared(&row.accesses, capacity))
      };
      let mut admitted = fits(&row);
      if !admitted && rows.is_empty() && row.chip.span() > 1 {
        // Tiny classes may fit each original step but not its entire fused
        // memory footprint. Preserve their ability to make progress.
        row = self.preview(&memory)?;
        admitted = fits(&row);
      }
      if !admitted {
        break;
      }
      self.commit(&mut memory, &row)?;
      counts[row.chip as usize] += 1;
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

#[cfg(test)]
mod native_tests {
  use super::*;
  use crate::{
    goldilocks::GOLDILOCKS_MODULUS as P,
    ixby::{ixbf::Primitive, paged_code::Header},
  };

  #[test]
  fn numeric_advice_matches_boolean_plans_at_integer_and_field_boundaries() {
    let machine = NativeMachine::new(
      [F128::ZERO; STATE_WORDS],
      0,
      [F128::new(4096, 4096), F128::new(16_000_000_000, 0), F128::new(4096, 0)],
    )
    .unwrap();
    let values = [
      0u128,
      1,
      2,
      7,
      31,
      32,
      33,
      255,
      u32::MAX as u128,
      (1u128 << 32),
      P as u128 - 1,
      P as u128,
      u64::MAX as u128,
      (1u128 << 65) + 3,
      u128::MAX,
    ];
    for p in Primitive::ALL {
      let code = p.opcode();
      if !matches!(code, 0..=6 | 10..=20 | 23..=28 | 31..=38 | 45..=48) {
        continue;
      }
      for (i, &a) in values.iter().enumerate() {
        for &b in &[0, 1, values[(i + 3) % values.len()]] {
          let tag = match code {
            0..=6 | 45 | 48 => 8,
            10..=23 | 46 => 2,
            24..=28 | 36 | 47 => 3,
            _ => 4,
          };
          let value = |n: u128| match tag {
            2 => F128::new(u64::from(n as u32), 0),
            3 => F128::new((n % u128::from(P)) as u64, 0),
            4 => F128::new((n as u64) % P, ((n >> 64) as u64) % P),
            _ => F128::new(n as u64, (n >> 64) as u64),
          };
          let mut args = [F128::ZERO; 6];
          args[..2].copy_from_slice(&[F128::new(tag, 0), value(a)]);
          if p.arity() == 2 {
            args[2..4].copy_from_slice(&[F128::new(tag, 0), value(b)]);
          }
          let h = Header {
            operation: 1,
            primitive: code,
            operands: p.arity() as u8,
            arguments: p.arity() as u8,
            ..Header::default()
          }
          .words()[0];
          let expected = machine.numeric_reference(h, &args);
          let actual = machine.numeric(h, &args);
          match (expected, actual) {
            (Ok(a), Ok(b)) => assert_eq!(a, b, "{p:?}"),
            (Err(_), Err(_)) => {},
            (a, b) => panic!("numeric mismatch {p:?}: {a:?} / {b:?}"),
          }
        }
      }
    }
  }
}
