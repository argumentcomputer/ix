use super::*;
use crate::{
  ixby::{
    auth_memory::{
      MemoryDepth, MemoryOpeningWires,
      multi::{MultiAdvice, MultiCapacity, MultiMemorySlots, MultiProofWires},
    },
    execution_order::{
      self, BoundaryWires as StateBoundary, StateChainSlots, TransitionWires,
    },
    io::{InputLayout, LayoutEmitter, PublicLayout},
    memory_log::{
      BoundaryWires, MemoryBatchAdvice, MemoryLogSlots, RecordLayout,
      RoutingKind, TimedAccessWires, TimedMemoryLogSlots,
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
  Bytes,
  SharedCompact,
  Shared,
  SharedCompactBoolean,
  SharedBoolean,
  /// 1,024 fetch slots, with separate bounds for other instruction families.
  Shared1024,
  SharedCompactPacked,
  SharedPacked1024,
  SharedCompactLinked,
  SharedLinked1024,
  /// Measured workload-specific quotas; all use shared memory and exact
  /// packed state linking. Every family retains a positive fallback quota.
  Arithmetic768,
  Arithmetic3072,
  /// 4K fetch prototype. Larger leaves need not be faster per useful step.
  Arithmetic4096,
  Arrays768,
  Builders768,
  Mixed3072,
  /// Runtime-v2 CSLib phases, including bounded byte-builder copy capacity.
  Cslib2048,
  /// Fused instruction/copy rows with original microstep clocks.
  FusedCompact,
  CslibFused,
}
impl BatchClass {
  pub const ALL: [Self; 22] = [
    Self::Small,
    Self::Objects,
    Self::Compact,
    Self::Bytes,
    Self::SharedCompact,
    Self::Shared,
    Self::SharedCompactBoolean,
    Self::SharedBoolean,
    Self::Shared1024,
    Self::SharedCompactPacked,
    Self::SharedPacked1024,
    Self::SharedCompactLinked,
    Self::SharedLinked1024,
    Self::Arithmetic768,
    Self::Arithmetic3072,
    Self::Arithmetic4096,
    Self::Arrays768,
    Self::Builders768,
    Self::Mixed3072,
    Self::Cslib2048,
    Self::FusedCompact,
    Self::CslibFused,
  ];
  pub fn name(self) -> &'static str {
    match self {
      Self::Small => "small",
      Self::Objects => "objects",
      Self::Compact => "compact",
      Self::Bytes => "bytes",
      Self::SharedCompact => "shared-compact",
      Self::Shared => "shared",
      Self::SharedCompactBoolean => "shared-compact-boolean",
      Self::SharedBoolean => "shared-boolean",
      Self::Shared1024 => "shared-1024",
      Self::SharedCompactPacked => "shared-compact-packed",
      Self::SharedPacked1024 => "shared-packed-1024",
      Self::SharedCompactLinked => "shared-compact-linked",
      Self::SharedLinked1024 => "shared-linked-1024",
      Self::Arithmetic768 => "arithmetic-768",
      Self::Arithmetic3072 => "arithmetic-3072",
      Self::Arithmetic4096 => "arithmetic-4096",
      Self::Arrays768 => "arrays-768",
      Self::Builders768 => "builders-768",
      Self::Mixed3072 => "mixed-3072",
      Self::Cslib2048 => "cslib-2048",
      Self::FusedCompact => "fused-compact",
      Self::CslibFused => "cslib-fused",
    }
  }
  pub fn from_name(name: &str) -> Result<Self> {
    Self::ALL
      .into_iter()
      .find(|class| class.name() == name)
      .ok_or_else(|| anyhow::anyhow!("unknown execution class {name}"))
  }
  pub fn transcript_domain(self) -> &'static [u8] {
    match self {
      Self::Small => b"IxBy/Flock/paged-execution:small:v4",
      Self::Objects => b"IxBy/Flock/paged-execution:objects:v3",
      Self::Compact => b"IxBy/Flock/paged-execution:compact:v3",
      Self::Bytes => b"IxBy/Flock/paged-execution:bytes:v2",
      Self::SharedCompact => b"IxBy/Flock/paged-execution:shared-compact:v2",
      Self::Shared => b"IxBy/Flock/paged-execution:shared:v2",
      Self::SharedCompactBoolean => {
        b"IxBy/Flock/paged-execution:shared-compact-boolean:v2"
      },
      Self::SharedBoolean => b"IxBy/Flock/paged-execution:shared-boolean:v2",
      Self::Shared1024 => b"IxBy/Flock/paged-execution:shared-1024:v3",
      Self::SharedCompactPacked => {
        b"IxBy/Flock/paged-execution:shared-compact-packed:v2"
      },
      Self::SharedPacked1024 => {
        b"IxBy/Flock/paged-execution:shared-packed-1024:v3"
      },
      Self::SharedCompactLinked => {
        b"IxBy/Flock/paged-execution:shared-compact-linked:v2"
      },
      Self::SharedLinked1024 => {
        b"IxBy/Flock/paged-execution:shared-linked-1024:v3"
      },
      Self::Arithmetic768 => b"IxBy/Flock/paged-execution:arithmetic-768:v0",
      Self::Arithmetic3072 => b"IxBy/Flock/paged-execution:arithmetic-3072:v0",
      Self::Arithmetic4096 => b"IxBy/Flock/paged-execution:arithmetic-4096:v0",
      Self::Arrays768 => b"IxBy/Flock/paged-execution:arrays-768:v0",
      Self::Builders768 => b"IxBy/Flock/paged-execution:builders-768:v0",
      Self::Mixed3072 => b"IxBy/Flock/paged-execution:mixed-3072:v0",
      Self::Cslib2048 => b"IxBy/Flock/paged-execution:cslib-2048:v0",
      Self::FusedCompact => b"IxBy/Flock/paged-execution:fused-compact:v0",
      Self::CslibFused => b"IxBy/Flock/paged-execution:cslib-fused:v0",
    }
  }
  pub fn fused(self) -> bool {
    matches!(self, Self::FusedCompact | Self::CslibFused)
  }
  pub fn fused_quotas(self) -> [usize; Chip::FUSED.len()] {
    match self {
      Self::FusedCompact => [2; Chip::FUSED.len()],
      Self::CslibFused => [544, 367, 144, 32, 40, 192, 113, 104],
      _ => [0; Chip::FUSED.len()],
    }
  }
  pub fn chip_quotas(self) -> impl Iterator<Item = (Chip, usize)> {
    Chip::ALL
      .into_iter()
      .zip(self.quotas())
      .chain(Chip::FUSED.into_iter().zip(self.fused_quotas()))
  }
  pub fn quotas(self) -> [usize; 31] {
    let old = match self {
      Self::Small => {
        [6, 8, 2, 3, 2, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
      },
      Self::Objects => [
        24, 40, 8, 16, 2, 32, 4, 8, 8, 4, 4, 12, 48, 32, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0,
      ],
      Self::Compact
      | Self::SharedCompact
      | Self::SharedCompactBoolean
      | Self::SharedCompactPacked
      | Self::SharedCompactLinked => {
        [2, 4, 1, 2, 1, 3, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
      },
      Self::Shared | Self::SharedBoolean => Self::SharedCompact.quotas()[..24]
        .try_into()
        .map(|x: [usize; 24]| x.map(|quota| quota * 16))
        .unwrap(),
      Self::Shared1024 | Self::SharedPacked1024 | Self::SharedLinked1024 => [
        1024, 2048, 384, 512, 256, 1024, 128, 64, 64, 256, 256, 256, 768, 512,
        32, 64, 64, 64, 32, 64, 64, 64, 64, 64,
      ],
      Self::Bytes => [
        20, 36, 4, 4, 2, 8, 0, 0, 0, 0, 0, 0, 0, 0, 16, 8, 8, 4, 16, 8, 20, 8,
        8, 8,
      ],
      _ => return tuning::shape(self).unwrap().quotas,
    };
    let extra = match self {
      Self::Small => [0; 7],
      Self::Objects => [8, 32, 32, 8, 0, 0, 0],
      Self::Bytes => [12, 24, 24, 12, 8, 12, 8],
      Self::Shared1024 | Self::SharedPacked1024 | Self::SharedLinked1024 => {
        [128, 512, 512, 128, 256, 512, 256]
      },
      Self::Shared | Self::SharedBoolean => [16, 32, 32, 16, 16, 32, 16],
      _ => [1, 2, 2, 1, 1, 2, 1],
    };
    old.into_iter().chain(extra).collect::<Vec<_>>().try_into().unwrap()
  }
  pub fn cells(self) -> usize {
    match self {
      Self::Small => 24,
      Self::Objects => 96,
      Self::Compact
      | Self::SharedCompact
      | Self::SharedCompactBoolean
      | Self::SharedCompactPacked
      | Self::SharedCompactLinked => 16,
      Self::Shared | Self::SharedBoolean => 256,
      Self::Shared1024 | Self::SharedPacked1024 | Self::SharedLinked1024 => {
        2048
      },
      Self::Bytes => 96,
      _ => tuning::shape(self).unwrap().cells,
    }
  }
  pub fn nu(self) -> usize {
    match self {
      Self::Small => 11,
      Self::Objects => 13,
      Self::Compact => 11,
      Self::Bytes => 13,
      Self::SharedCompact
      | Self::SharedCompactBoolean
      | Self::SharedCompactPacked
      | Self::SharedCompactLinked => 10,
      Self::Shared | Self::SharedBoolean => 13,
      Self::Shared1024 | Self::SharedPacked1024 | Self::SharedLinked1024 => 16,
      _ => tuning::shape(self).unwrap().nu,
    }
  }
  pub fn transitions(self) -> usize {
    self.chip_quotas().map(|(_, quota)| quota).sum()
  }
  pub fn shared_memory(self) -> Option<MultiCapacity> {
    match self {
      Self::SharedCompact
      | Self::SharedCompactBoolean
      | Self::SharedCompactPacked
      | Self::SharedCompactLinked => {
        Some(MultiCapacity::new(self.cells(), 192).unwrap())
      },
      Self::Shared | Self::SharedBoolean => {
        Some(MultiCapacity::new(self.cells(), 3_072).unwrap())
      },
      Self::Shared1024 | Self::SharedPacked1024 | Self::SharedLinked1024 => {
        Some(MultiCapacity::new(self.cells(), 8_191).unwrap())
      },
      _ => tuning::shape(self).and_then(BatchShape::shared_memory),
    }
  }
  pub fn accesses(self) -> usize {
    self.chip_quotas().map(|(chip, quota)| quota * chip.accesses()).sum()
  }
  pub fn routing(self) -> RoutingKind {
    match self {
      Self::SharedCompactBoolean | Self::SharedBoolean | Self::Shared1024 => {
        RoutingKind::Boolean
      },
      Self::SharedCompactPacked
      | Self::SharedPacked1024
      | Self::SharedCompactLinked
      | Self::SharedLinked1024 => RoutingKind::BooleanPacked,
      _ if tuning::shape(self).is_some() => RoutingKind::BooleanPacked,
      _ => RoutingKind::Element,
    }
  }
  pub fn linked_states(self) -> bool {
    matches!(self, Self::SharedCompactLinked | Self::SharedLinked1024)
      || tuning::shape(self).is_some()
  }
}
/// Canonical paged machine state: the layout preserves every active bit of
/// each register, including complete value/hash words. The packing gate
/// constrains every omitted bit, including the three reserved state words.
pub(super) fn state_record_layout() -> RecordLayout {
  let mut masks = [
    64, 3, // Clock and record kind.
    88, 64, 128, 128, 72, // Frame.
    128, 37, 37, 25,
    128, // Fuel budget and usage, heap/byte counts, control, instruction.
    128, 128, 128, 128,
    72, // Pending frame or byte results/ranges/position.
    72, 72, 128, 128, 27, 65, 0, 0, 0,
  ]
  .map(RecordLayout::low_bits)
  .to_vec();
  // Collection continuations contain complete values and a 256-bit copy
  // buffer. Preserve every bit through packed state linking.
  for mask in &mut masks[2 + 10..] {
    *mask = u128::MAX;
  }
  // The frame header reserves bits 40..48 between locals and depth.
  masks[2] &= !(RecordLayout::low_bits(8) << 40);

  RecordLayout::new(masks).unwrap()
}
pub struct BatchEmission {
  pub class: BatchClass,
  pub execution: ExecutionSlots,
  pub order: StateChainSlots,
  pub memory: TimedMemoryLogSlots,
  pub tree: Option<MultiMemorySlots>,
  pub inputs: InputLayout,
  pub public: PublicLayout,
}
/// Physical bounds used by the shared emitter. Only named `BatchClass`
/// values enter production; the opt-in census can sweep candidate bounds
/// through this same emitter before a class is approved.
#[derive(Clone, Copy, Debug)]
pub(super) struct BatchShape {
  pub quotas: [usize; 31],
  pub fused: [usize; Chip::FUSED.len()],
  pub cells: usize,
  pub parents: Option<usize>,
  pub nu: usize,
}
impl BatchShape {
  pub(super) fn from_class(class: BatchClass) -> Self {
    Self {
      quotas: class.quotas(),
      fused: class.fused_quotas(),
      cells: class.cells(),
      parents: class.shared_memory().map(|c| c.parents),
      nu: class.nu(),
    }
  }
  pub(super) fn transitions(self) -> usize {
    self.quotas.iter().chain(&self.fused).sum()
  }
  pub(super) fn accesses(self) -> usize {
    self.chip_quotas().map(|(chip, quota)| quota * chip.accesses()).sum()
  }
  pub(super) fn chip_quotas(self) -> impl Iterator<Item = (Chip, usize)> {
    Chip::ALL
      .into_iter()
      .zip(self.quotas)
      .chain(Chip::FUSED.into_iter().zip(self.fused))
  }
  pub(super) fn shared_memory(self) -> Option<MultiCapacity> {
    self.parents.map(|parents| MultiCapacity::new(self.cells, parents).unwrap())
  }
}
pub fn emit_batch(
  b: &mut impl CircuitEmitter,
  class: BatchClass,
) -> Result<BatchEmission> {
  emit_shape(b, class, BatchShape::from_class(class))
}
pub(super) fn emit_shape(
  b: &mut impl CircuitEmitter,
  class: BatchClass,
  shape: BatchShape,
) -> Result<BatchEmission> {
  let mut b = LayoutEmitter::new(b);
  let nu = shape.nu;
  let memory = TimedMemoryLogSlots::declare_with_routing(
    &mut b,
    nu,
    MemoryDepth::new(40)?,
    class.routing(),
  )?;
  let execution = if class.fused() {
    ExecutionSlots::declare_fused(
      &mut b,
      nu,
      memory.log().memory().compression(),
    )?
  } else {
    ExecutionSlots::declare(&mut b, nu, memory.log().memory().compression())?
  };
  let order = if class.fused() {
    StateChainSlots::declare_linked_spans(
      &mut b,
      nu,
      STATE_WORDS,
      state_record_layout(),
      &[2, 3, 4, 6, 8, 10],
    )?
  } else if class.linked_states() {
    StateChainSlots::declare_linked(
      &mut b,
      nu,
      STATE_WORDS,
      state_record_layout(),
    )?
  } else {
    StateChainSlots::declare_with_record_layout(
      &mut b,
      nu,
      STATE_WORDS,
      class.routing(),
      (class.routing() == RoutingKind::BooleanPacked).then(state_record_layout),
    )?
  };
  let tree = shape
    .shared_memory()
    .map(|_| {
      MultiMemorySlots::sharing_compression_with_routing(
        &mut b,
        nu,
        MemoryDepth::new(40)?,
        memory.log().memory().compression(),
        class.routing(),
      )
    })
    .transpose()?;
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
  for (chip, count) in shape.chip_quotas() {
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
        span: chip.span(),
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
  let switches = (0..order.routing_plan(shape.transitions())?.switches())
    .map(|_| b.input())
    .collect::<Vec<_>>();
  order.check(
    &mut b,
    StateBoundary { clock: initial_clock, state: initial_state },
    StateBoundary { clock: final_clock, state: final_state },
    &transitions,
    &switches,
  );
  if let Some(tree) = &tree {
    let final_root = std::array::from_fn(|_| {
      let w = b.input();
      b.publish(w);
      w
    });
    let proof = MultiProofWires::inputs(&mut b, shape.shared_memory().unwrap());
    if class.fused() {
      // Authenticate the reserved zero cell once per batch. Merely binding
      // an omitted dummy read's wires to zero would not check its memory cell
      // for a conditional segment with an arbitrary initial root.
      let nil = &proof.leaves[0];
      let matching = execution.forwarding_gate().unwrap().0;
      for value in [nil.old, nil.new] {
        // Consume the boundary inputs through an actual equality gate. The
        // pinned builder does not merge cells added to an aliased input
        // after connect(), so an early input-only connection is insufficient.
        let residuals = b.gate(
          matching,
          &[
            nil.address,
            value[0],
            value[1],
            execution.zero,
            execution.zero,
            execution.zero,
          ],
        );
        for residual in residuals {
          execution.constrain_zero(&mut b, residual);
        }
      }
    }
    let switches = (0..MemoryLogSlots::plan(shape.accesses(), shape.cells)?
      .switches())
      .map(|_| b.input())
      .collect::<Vec<_>>();
    memory.check_shared(
      &mut b,
      tree,
      [initial_root, final_root],
      &accesses,
      &proof,
      &switches,
    );
  } else {
    let cells = (0..shape.cells)
      .map(|_| BoundaryWires {
        address: b.input(),
        opening: MemoryOpeningWires {
          value: std::array::from_fn(|_| b.input()),
          siblings: (0..40)
            .map(|_| std::array::from_fn(|_| b.input()))
            .collect(),
        },
        final_value: std::array::from_fn(|_| b.input()),
      })
      .collect::<Vec<_>>();
    let switches = (0..MemoryLogSlots::plan(shape.accesses(), shape.cells)?
      .switches())
      .map(|_| b.input())
      .collect::<Vec<_>>();
    for w in memory.check(&mut b, initial_root, &accesses, &cells, &switches) {
      b.publish(w);
    }
  }
  let (inputs, public) = b.finish();
  Ok(BatchEmission { class, execution, order, memory, tree, inputs, public })
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
    Self::assemble(class, parameters, rows, memory, None)
  }
  pub fn new_shared(
    class: BatchClass,
    parameters: [F128; 3],
    rows: &[RowAdvice],
    memory: &MemoryBatchAdvice,
    tree: &MultiAdvice,
  ) -> Result<Self> {
    Self::assemble(class, parameters, rows, memory, Some(tree))
  }
  fn assemble(
    class: BatchClass,
    parameters: [F128; 3],
    rows: &[RowAdvice],
    memory: &MemoryBatchAdvice,
    tree: Option<&MultiAdvice>,
  ) -> Result<Self> {
    ensure!(
      class.shared_memory().is_some() == tree.is_some(),
      "execution memory profile"
    );
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
    private.push(F128::new(end.end_clock()?, 0));
    private.extend(end.after);
    let mut expected = private.clone();
    expected.extend(memory.final_root);
    let mut offsets = Vec::with_capacity(rows.len());
    let mut offset = 0;
    for (i, row) in rows.iter().enumerate() {
      if i > 0 {
        ensure!(
          rows[i - 1].end_clock()? == row.clock
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
    for (chip, quota) in class.chip_quotas() {
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
            record(row.end_clock()?, execution_order::AFTER, &row.after),
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
      record(end.end_clock()?, execution_order::SEAL, &end.after),
    ]);
    if class.linked_states() {
      private.extend(execution_order::linked_routing(&state_records)?);
    } else {
      state_records
        .resize(StateChainSlots::plan(class.transitions())?.lanes(), pad);
      private.extend(execution_order::routing(&state_records)?);
    }
    if let Some(tree) = tree {
      let roots = memory
        .initial_root
        .into_iter()
        .chain(memory.final_root)
        .collect::<Vec<_>>();
      let boundary = memory.boundary_words();
      ensure!(
        tree.private.get(..4) == Some(roots.as_slice())
          && tree.private.get(4..4 + boundary.len())
            == Some(boundary.as_slice()),
        "native execution shared-tree boundary"
      );
      private.extend(memory.final_root);
      private.extend_from_slice(&tree.private[4..]);
    } else {
      private.extend(memory.boundary_words());
    }
    private.extend(memory.timed_switches(&memory_order)?);
    Ok(Self { private, expected })
  }
}
