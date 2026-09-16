use super::*;
use crate::{
  ixby::{
    auth_memory::{MemoryDepth, MemoryOpeningWires},
    execution_order::{
      self, BoundaryWires as StateBoundary, StateChainSlots, TransitionWires,
    },
    io::{InputLayout, LayoutEmitter, PublicLayout},
    memory_log::{
      BoundaryWires, MemoryBatchAdvice, MemoryLogSlots, TimedAccessWires,
      TimedMemoryLogSlots,
    },
  },
  sizing::CircuitEmitter,
};
use anyhow::{Result, ensure};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BatchClass {
  Small,
  Objects,
  Compact,
}
impl BatchClass {
  pub fn quotas(self) -> [usize; 14] {
    match self {
      Self::Small => [6, 8, 2, 3, 2, 4, 0, 0, 0, 0, 0, 0, 0, 0],
      Self::Objects => [24, 40, 8, 16, 2, 32, 4, 8, 8, 4, 4, 12, 48, 32],
      Self::Compact => [2, 4, 1, 2, 1, 3, 1, 1, 1, 1, 1, 1, 2, 2],
    }
  }
  pub fn cells(self) -> usize {
    match self {
      Self::Small => 24,
      Self::Objects => 96,
      Self::Compact => 16,
    }
  }
  pub fn nu(self) -> usize {
    match self {
      Self::Small => 11,
      Self::Objects => 13,
      Self::Compact => 11,
    }
  }
  pub fn transitions(self) -> usize {
    self.quotas().iter().sum()
  }
  pub fn accesses(self) -> usize {
    self
      .quotas()
      .into_iter()
      .zip(Chip::ALL)
      .map(|(n, c)| n * c.accesses())
      .sum()
  }
}
pub struct BatchEmission {
  pub class: BatchClass,
  pub execution: ExecutionSlots,
  pub order: StateChainSlots,
  pub memory: TimedMemoryLogSlots,
  pub inputs: InputLayout,
  pub public: PublicLayout,
}
pub fn emit_batch(
  b: &mut impl CircuitEmitter,
  class: BatchClass,
) -> Result<BatchEmission> {
  let mut b = LayoutEmitter::new(b);
  let nu = class.nu();
  let execution = ExecutionSlots::declare(&mut b, nu)?;
  let order = StateChainSlots::declare(&mut b, nu, STATE_WORDS)?;
  let memory = TimedMemoryLogSlots::declare(&mut b, nu, MemoryDepth::new(40)?)?;
  let parameters = std::array::from_fn(|_| {
    let w = b.input();
    b.publish(w);
    w
  });
  execution.parameters(&mut b, parameters);
  let initial_clock = b.input();
  b.publish(initial_clock);
  let initial_state = (0..STATE_WORDS)
    .map(|_| {
      let w = b.input();
      b.publish(w);
      w
    })
    .collect();
  let initial_root = std::array::from_fn(|_| {
    let w = b.input();
    b.publish(w);
    w
  });
  let final_clock = b.input();
  b.publish(final_clock);
  let final_state = (0..STATE_WORDS)
    .map(|_| {
      let w = b.input();
      b.publish(w);
      w
    })
    .collect();
  let mut transitions = Vec::new();
  let mut accesses = Vec::new();
  for (chip, count) in Chip::ALL.into_iter().zip(class.quotas()) {
    for _ in 0..count {
      let enabled = b.input();
      let clock = b.input();
      let before = std::array::from_fn(|_| b.input());
      let advice =
        (0..chip.advice_words()).map(|_| b.input()).collect::<Vec<_>>();
      let step =
        execution.step(&mut b, chip, enabled, before, &advice, parameters);
      transitions.push(TransitionWires {
        enabled,
        clock,
        before: before.to_vec(),
        after: step.state.to_vec(),
      });
      accesses.extend(step.accesses.into_iter().enumerate().map(
        |(ordinal, access)| TimedAccessWires {
          enabled,
          clock,
          ordinal: ordinal as u8,
          access,
        },
      ));
    }
  }
  execution.finish_canonical(&mut b);
  let switches = (0..StateChainSlots::plan(class.transitions())?.switches())
    .map(|_| b.input())
    .collect::<Vec<_>>();
  order.check(
    &mut b,
    StateBoundary { clock: initial_clock, state: initial_state },
    StateBoundary { clock: final_clock, state: final_state },
    &transitions,
    &switches,
  );
  let cells = (0..class.cells())
    .map(|_| BoundaryWires {
      address: b.input(),
      opening: MemoryOpeningWires {
        value: std::array::from_fn(|_| b.input()),
        siblings: (0..40).map(|_| std::array::from_fn(|_| b.input())).collect(),
      },
      final_value: std::array::from_fn(|_| b.input()),
    })
    .collect::<Vec<_>>();
  let switches = (0..MemoryLogSlots::plan(class.accesses(), class.cells())?
    .switches())
    .map(|_| b.input())
    .collect::<Vec<_>>();
  for w in memory.check(&mut b, initial_root, &accesses, &cells, &switches) {
    b.publish(w);
  }
  let (inputs, public) = b.finish();
  Ok(BatchEmission { class, execution, order, memory, inputs, public })
}

pub struct BatchAdvice {
  pub private: Vec<F128>,
  pub expected: Vec<F128>,
}
impl BatchAdvice {
  pub fn new(
    class: BatchClass,
    parameters: [F128; 3],
    rows: &[RowAdvice],
    memory: &MemoryBatchAdvice,
  ) -> Result<Self> {
    ensure!(!rows.is_empty(), "execution batch must make progress");
    ensure!(
      memory.boundaries.len() == class.cells(),
      "execution boundary quota"
    );
    let start = &rows[0];
    let end = rows.last().unwrap();
    let mut private = parameters.to_vec();
    private.push(F128::new(start.clock, 0));
    private.extend(start.before);
    private.extend(memory.initial_root);
    private.push(F128::new(
      end
        .clock
        .checked_add(1)
        .ok_or_else(|| anyhow::anyhow!("execution clock overflow"))?,
      0,
    ));
    private.extend(end.after);
    let mut expected = private.clone();
    expected.extend(memory.final_root);
    let mut offsets = Vec::with_capacity(rows.len());
    let mut offset = 0;
    for (i, row) in rows.iter().enumerate() {
      if i > 0 {
        ensure!(
          rows[i - 1].clock.checked_add(1) == Some(row.clock)
            && rows[i - 1].after == row.before,
          "native execution discontinuity"
        );
      }
      offsets.push(offset);
      offset += row.accesses.len();
    }
    ensure!(offset == memory.accesses.len(), "execution memory event count");
    let record = |clock: u64, kind: u64, state: &[F128]| {
      [F128::new(clock, 0), F128::new(kind, 0)]
        .into_iter()
        .chain(state.iter().copied())
        .collect::<Vec<_>>()
    };
    let mut pad = vec![F128::ZERO; STATE_WORDS + 2];
    pad[1] = F128::new(execution_order::PAD, 0);
    let mut state_records = Vec::new();
    let mut memory_order = Vec::new();
    for (chip, quota) in Chip::ALL.into_iter().zip(class.quotas()) {
      let matching = rows
        .iter()
        .enumerate()
        .filter(|(_, r)| r.chip == chip)
        .collect::<Vec<_>>();
      ensure!(matching.len() <= quota, "execution chip quota");
      for position in 0..quota {
        if let Some(&(index, row)) = matching.get(position) {
          private.extend([F128::ONE, F128::new(row.clock, 0)]);
          private.extend(row.before);
          private.extend(&row.advice);
          state_records.extend([
            record(row.clock, execution_order::BEFORE, &row.before),
            record(row.clock + 1, execution_order::AFTER, &row.after),
          ]);
          memory_order.extend((0..chip.accesses()).map(|ordinal| {
            Some((offsets[index] + ordinal, row.clock, ordinal as u8))
          }));
        } else {
          private.resize(
            private.len() + 2 + STATE_WORDS + chip.advice_words(),
            F128::ZERO,
          );
          state_records.extend([pad.clone(), pad.clone()]);
          memory_order.resize(memory_order.len() + chip.accesses(), None);
        }
      }
    }
    state_records.extend([
      record(start.clock, execution_order::SEED, &start.before),
      record(end.clock + 1, execution_order::SEAL, &end.after),
    ]);
    state_records
      .resize(StateChainSlots::plan(class.transitions())?.lanes(), pad);
    private.extend(execution_order::routing(&state_records)?);
    private.extend(memory.boundary_words());
    private.extend(memory.timed_switches(&memory_order)?);
    Ok(Self { private, expected })
  }
}
