//! Native advice generation. Every result is checked by the separately
//! compiled gate tables and by authenticated memory/state constraints.
use super::*;
use crate::{
  extension::goldilocks_ext2_mul,
  goldilocks::goldilocks_add,
  ixby::{
    decode::PrimitiveSet,
    memory_log::{AccessAdvice, MemoryBatch},
    paged_code::{CodeGate, CodeGateKind, FUNCTIONS, block_address},
    paged_frame::{CONTINUATIONS, FrameGate, LOCALS, Phase, SCRATCH},
    paged_nat::Nat128Gate,
    paged_primitive::PrimitiveRouteGate,
    primitive::{PrimitiveFinishGate, PrimitivePrepareGate},
  },
};
use anyhow::{Result, bail, ensure};
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
    };
    machine.micro(MicroKind::Parameters, &parameters)?;
    Ok(machine)
  }
  fn micro(&self, kind: MicroKind, input: &[F128]) -> Result<Vec<F128>> {
    run(self.micro.iter().find(|g| g.kind() == kind).unwrap(), input)
  }
  pub fn next_chip(&self) -> Result<Option<Chip>> {
    Ok(Some(match self.state[CONTROL].lo as u8 {
      0 => match self.state[0].lo as u8 {
        x if x == Phase::Eval as u8 => Chip::Fetch,
        x if x == Phase::Return as u8 || x == Phase::Copy as u8 => Chip::Resume,
        x if x == Phase::Halted as u8 => return Ok(None),
        p => bail!("pending implementation: paged frame phase {p}"),
      },
      1 => Chip::Resolve,
      2 => {
        let h = self.state[HEADER];
        let instruction = (h.lo >> 8) as u8;
        let op = (h.lo >> 16) as u8;
        match (instruction, op) {
          (0, 1) => Chip::Numeric,
          (0, 0) | (1 | 6 | 7, _) => Chip::Control,
          (0, 5 | 6) | (2 | 3, _) => Chip::Call,
          _ => bail!(
            "pending implementation: paged instruction {instruction}, operation {op}"
          ),
        }
      },
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
  pub fn step(&mut self, memory: &mut MemoryBatch<'_>) -> Result<RowAdvice> {
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
        let read =
          run(&self.code[0], &[F128::ONE, before[0], cell[0], cell[1]])?;
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
        let read = run(
          &self.code[1],
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
        let read =
          run(&self.code[2], &[F128::ONE, reference, cell[0], cell[1]])?;
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
    }
    ensure!(accesses.len() == chip.accesses(), "native access count");
    for access in &accesses {
      if access.write {
        memory.write(access.address, access.value)?;
      } else {
        ensure!(
          memory.read(access.address)? == access.value,
          "native memory reply mismatch"
        );
      }
    }
    let row =
      RowAdvice { chip, clock: self.clock, before, after, advice, accesses };
    self.state = after;
    self.clock = self
      .clock
      .checked_add(1)
      .ok_or_else(|| anyhow::anyhow!("execution clock exhausted"))?;
    Ok(row)
  }
}
