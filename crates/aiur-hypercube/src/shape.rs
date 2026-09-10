//! Shard shapes: the finite, machine-determined catalogue of proof shapes
//! every shard lands in, and the padding that puts it there.
//!
//! SP1's recursion programs are compiled per proof *shape* — the chip set,
//! the stacked area of each commitment round (in multiples of the stacking
//! height) and the number of padding columns — but not per row count: the
//! jagged PCS witnesses the per-chip heights. A fixed recursion pipeline
//! (one program per shape, one verifying key per program, and above the
//! leaves a single shape everything is padded to) therefore needs the
//! backend to emit shards from a finite catalogue, the way SP1's RISC-V
//! core emits shards from a fixed set of chip clusters and area multiples.
//! For an Aiur machine:
//!
//! - the chip set is always the whole machine (`MachineShape::all`; a chip
//!   without rows is committed at zero area, for free);
//! - the preprocessed round is a constant of the machine: the atomic
//!   circuits are replicated into every shard;
//! - the main round is padded to one of a few areas — the powers of two
//!   from the stacking height up, and a top class just under the jagged
//!   PCS's bound on the two rounds together (see [`main_areas`]) — by the
//!   *pad chip*, a lookup-free chip of [`PAD_WIDTH`] zero columns whose
//!   height fills the gap. Its rows are aligned like every other trace, so
//!   the leftover the stacked PCS pads itself is at most
//!   `PAD_WIDTH * ROW_ALIGNMENT` cells; the padding-column count that
//!   leftover induces is the only other varying quantity, and it is bounded
//!   by [`ShardShape::max_padding_cols`] (one, at production parameters).
//!
//! Padding at most doubles a shard's committed area; the partitioner fills
//! shards to the area bound, so typically only the last shard of a proof
//! grows. Chips absent from a shard still cost the recursion program their
//! constraint evaluation, so a smaller catalogue of chip clusters would
//! make light shards cheaper to normalize; that is a later refinement.

use serde::{Deserialize, Serialize};
use slop_air::BaseAir;
use slop_algebra::AbstractField;
use slop_matrix::dense::RowMajorMatrix;
use sp1_hypercube::{
  Machine, MachineVerifier, SP1PcsProofInner, ShardProof, air::MachineAir,
  prover::CoreProofShape,
};
use sp1_primitives::SP1GlobalContext;

use crate::{
  F,
  air::AiurAir,
  machine::{AiurMachine, BuildError, ROW_ALIGNMENT},
  prover::{ProverParams, shard_verifier},
  record::{AiurProgram, AiurRecord},
};

/// The jagged PCS (and the recursion circuit verifying it) reject a proof
/// whose commitment rounds together exceed `2^MAX_LOG_AREA` cells.
pub const MAX_LOG_AREA: u32 = 29;

/// Width of the pad chip. A `2^29` gap at `2^20` rows per chip needs 512
/// columns; narrower would exceed the row cap on a nearly empty shard
/// padded to the top class.
pub const PAD_WIDTH: usize = 512;

/// One entry of a machine's shape catalogue.
#[derive(
  Clone,
  Copy,
  Debug,
  PartialEq,
  Eq,
  PartialOrd,
  Ord,
  Hash,
  Serialize,
  Deserialize,
)]
pub struct ShardShape {
  /// The main round's stacked area.
  pub main_area: usize,
  /// Padding columns of the main round (see the module docs).
  pub main_padding_cols: usize,
}

impl ShardShape {
  /// The most padding columns a padded shard can have under `params`:
  /// the pad chip's row alignment leaves at most `PAD_WIDTH * ROW_ALIGNMENT`
  /// cells to the stacked PCS's own padding.
  pub fn max_padding_cols(params: ProverParams) -> usize {
    (PAD_WIDTH * ROW_ALIGNMENT).div_ceil(1 << params.max_log_row_count).max(1)
  }
}

/// The main areas of the catalogue, ascending: the powers of two from the
/// stacking height up to `2^(MAX_LOG_AREA - 1)`, then the largest stacking
/// multiple that keeps both rounds within `2^MAX_LOG_AREA` (when larger).
pub fn main_areas(
  machine: &Machine<F, AiurAir>,
  params: ProverParams,
) -> Vec<usize> {
  let (preprocessed_area, _) = preprocessed_round(machine, params);
  let stacking = 1usize << params.log_stacking_height;
  let mut areas: Vec<usize> =
    (params.log_stacking_height..MAX_LOG_AREA).map(|k| 1usize << k).collect();
  let top =
    ((1usize << MAX_LOG_AREA) - preprocessed_area) / stacking * stacking;
  if areas.last().is_none_or(|&last| top > last) {
    areas.push(top);
  }
  areas
}

/// Every shape a padded shard of `machine` can have under `params`.
pub fn catalogue(
  machine: &Machine<F, AiurAir>,
  params: ProverParams,
) -> Vec<ShardShape> {
  let mut out = Vec::new();
  for main_area in main_areas(machine, params) {
    for main_padding_cols in 1..=ShardShape::max_padding_cols(params) {
      out.push(ShardShape { main_area, main_padding_cols });
    }
  }
  out
}

/// The preprocessed round's `(stacked area, padding columns)`: a constant
/// of the machine, since every shard carries the full preprocessed traces.
pub fn preprocessed_round(
  machine: &Machine<F, AiurAir>,
  params: ProverParams,
) -> (usize, usize) {
  let real: usize = machine
    .chips()
    .iter()
    .map(|chip| {
      chip.preprocessed_width()
        * chip.preprocessed_num_rows(&AiurProgram).unwrap_or(0)
    })
    .sum();
  let area = real.next_multiple_of(1 << params.log_stacking_height);
  let padding_cols =
    (area - real).div_ceil(1 << params.max_log_row_count).max(1);
  (area, padding_cols)
}

/// The SP1 proof shape of a shard of `machine` in shape class `shape`.
pub fn core_shape(
  machine: &Machine<F, AiurAir>,
  params: ProverParams,
  shape: ShardShape,
) -> CoreProofShape<F, AiurAir> {
  let (preprocessed_area, preprocessed_padding_cols) =
    preprocessed_round(machine, params);
  CoreProofShape {
    shard_chips: machine.chips().iter().cloned().collect(),
    preprocessed_area,
    main_area: shape.main_area,
    preprocessed_padding_cols,
    main_padding_cols: shape.main_padding_cols,
  }
}

/// Errors of [`shape_of_proof`].
#[derive(Debug)]
pub enum ShapeError {
  /// The proof's main round is not in the catalogue.
  NotInCatalogue { main_area: usize, main_padding_cols: usize },
  /// The proof has fewer than two commitment rounds.
  Rounds(usize),
}

impl std::fmt::Display for ShapeError {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      Self::NotInCatalogue { main_area, main_padding_cols } => write!(
        f,
        "shard proof of main area {main_area} with {main_padding_cols} \
         padding column(s) is not in the shape catalogue (unpadded proof?)"
      ),
      Self::Rounds(n) => write!(f, "shard proof has {n} commitment rounds"),
    }
  }
}

impl std::error::Error for ShapeError {}

/// The shape class of a shard proof, read off its jagged commitment rounds
/// (round 0 is preprocessed, round 1 main; each round lists its tables'
/// `(rows, columns)` followed by the two padding tables).
pub fn shape_of_proof(
  machine: &Machine<F, AiurAir>,
  params: ProverParams,
  proof: &ShardProof<SP1GlobalContext, SP1PcsProofInner>,
) -> Result<ShardShape, ShapeError> {
  let rounds = &proof.evaluation_proof.row_counts_and_column_counts;
  let Some(main) = rounds.get(1) else {
    return Err(ShapeError::Rounds(rounds.len()));
  };
  let main_area: usize = main.iter().map(|(r, c)| r * c).sum();
  // The padding tables: `(2^max_rows, cols - 1)` then `(leftover, 1)`.
  let main_padding_cols =
    main.len().checked_sub(2).map_or(1, |i| main[i].1 + 1);
  let shape = ShardShape { main_area, main_padding_cols };
  if !catalogue(machine, params).contains(&shape) {
    return Err(ShapeError::NotInCatalogue { main_area, main_padding_cols });
  }
  Ok(shape)
}

/// Pads `record` into the smallest class its real main area fits under,
/// filling the pad chip, and returns the class. Idempotent.
pub fn pad_record(
  machine: &AiurMachine,
  params: ProverParams,
  record: &mut AiurRecord,
) -> Result<ShardShape, BuildError> {
  let pad_slot = machine.idx_pad();
  if record.traces.len() < machine.num_slots() {
    record.traces.resize(machine.num_slots(), None);
  }
  record.traces[pad_slot] = None;
  assert!(
    PAD_WIDTH * ROW_ALIGNMENT <= 1 << params.log_stacking_height,
    "log_stacking_height too small for the pad chip's granularity"
  );

  let real: usize = machine
    .machine()
    .chips()
    .iter()
    .filter(|chip| chip.included(record))
    .map(|chip| chip.width() * chip.num_rows(record).unwrap_or(0))
    .sum();
  // The smallest class strictly above the real area, so the stacked PCS
  // always has a (nonempty) leftover to pad.
  let Some(area) =
    main_areas(machine.machine(), params).into_iter().find(|&a| a > real)
  else {
    return Err(BuildError::ShardTooLarge { shard: usize::MAX, cells: real });
  };
  let gap = area - real - 1;
  let rows = (gap / PAD_WIDTH) / ROW_ALIGNMENT * ROW_ALIGNMENT;
  if rows > 1 << params.max_log_row_count {
    return Err(BuildError::ShardTooLarge { shard: usize::MAX, cells: real });
  }
  if rows > 0 {
    record.traces[pad_slot] =
      Some(RowMajorMatrix::new(vec![F::zero(); rows * PAD_WIDTH], PAD_WIDTH));
  }
  let leftover = area - real - rows * PAD_WIDTH;
  debug_assert!((1..=PAD_WIDTH * ROW_ALIGNMENT).contains(&leftover));
  let main_padding_cols =
    leftover.div_ceil(1 << params.max_log_row_count).max(1);
  let shape = ShardShape { main_area: area, main_padding_cols };

  // The prover derives the same shape from the record.
  debug_assert_eq!(
    sp1_hypercube::prover::shape_from_record(
      &MachineVerifier::new(shard_verifier(machine, params)),
      record
    )
    .as_ref(),
    Some(&core_shape(machine.machine(), params, shape)),
    "padded record does not have its catalogue shape"
  );
  Ok(shape)
}

/// Pads every record (see [`pad_record`]).
pub fn pad_records(
  machine: &AiurMachine,
  params: ProverParams,
  records: &mut [AiurRecord],
) -> Result<Vec<ShardShape>, BuildError> {
  records
    .iter_mut()
    .enumerate()
    .map(|(shard, record)| {
      pad_record(machine, params, record).map_err(|e| match e {
        BuildError::ShardTooLarge { cells, .. } => {
          BuildError::ShardTooLarge { shard, cells }
        },
        e => e,
      })
    })
    .collect()
}
