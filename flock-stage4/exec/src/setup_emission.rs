//! Setup-owned, assignment-free emission of the WHOLE root-closed relation.
//! Zero scratch values do not make private slots constants. All constraints
//! and structural validation run; native witness diagnostics do not.

use crate::{CompiledExecReplay, CompiledExecRootClosure};
use anyhow::{Result, ensure};
use ix_stage4_trace::{
  ExecCommitmentsV0, F128_MULTIPOINT_JAGGED_CLAIMS, F128_WIRING_PRIVATE_VALUES,
};
use ix_terminal_circuit::{
  CanonicalR1csV1, ExecReplayCircuitWitnessV0, R1csBuilder, R1csError,
  R1csShapeLimitsV0, Stage4PublicInputsV1, Stage4TraceWitnessV1,
  Stage4TranscriptWitnessV1, constrain_exec_root_closed,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ExecSetupR1csLimitsV0 {
  /// Logical payload of the heap-backed source-slot scratch, checked BEFORE
  /// allocating it. Excludes Vec headers, allocator overhead, inline B/I/O/Q,
  /// approved setup/tables, gadget intermediates and matrices. Not peak RAM.
  pub source_payload_bytes: u64,
  pub r1cs: R1csShapeLimitsV0,
}

/// Read-only diagnostic counts derived afresh from approved topology. This
/// returned value is never accepted back as an input to the setup emitter.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ExecSetupSourceSlotsV0 {
  pub f128_words: u64,
  pub digest32_words: u64,
  pub byte_payloads: u64,
  pub byte_payload_bytes: u64,
}

impl ExecSetupSourceSlotsV0 {
  pub fn payload_bytes(self) -> Result<u64, R1csError> {
    self
      .f128_words
      .checked_mul(16)
      .and_then(|bytes| {
        self
          .digest32_words
          .checked_mul(32)
          .and_then(|digests| bytes.checked_add(digests))
      })
      .and_then(|bytes| bytes.checked_add(self.byte_payload_bytes))
      .ok_or(R1csError::CountOverflow)
  }
}

impl CompiledExecRootClosure<'_, '_> {
  /// Slot geometry is reconstructed from setup, never a proof or exported
  /// replay. The payload figure is NOT whole-pipeline resource admission.
  pub fn setup_source_slots(&self) -> Result<ExecSetupSourceSlotsV0> {
    Ok(SourceLayout::new(self.replay_setup())?.counts)
  }

  /// Materialize actual canonical R1CS, using only this approved topology and
  /// fixed root programs. No guest, commitment, Q, proof, or assignment input
  /// exists. Errors return no matrices, including a size refusal on the last
  /// emitted constraint. This is not FFLONK preprocessing or proof generation.
  pub fn build_setup_r1cs(
    &self,
    limits: ExecSetupR1csLimitsV0,
  ) -> Result<CanonicalR1csV1> {
    let mut builder = R1csBuilder::new_shape(limits.r1cs)?;
    let emitted = self.emit_setup(&mut builder, limits.source_payload_bytes);
    let r1cs = builder.finish_shape()?;
    emitted?;
    ensure!(r1cs.public_variables() == 2, "setup requires exactly two Q limbs");
    Ok(r1cs)
  }

  /// Stream the same whole relation to a shape-only builder, e.g. a fallible
  /// PLONK observer. Builder/observer refusals are sticky. Source preflight
  /// failures occur before any allocation and must also be propagated.
  /// Scratch outputs are discarded: this API cannot return a replay witness,
  /// native acceptance result or fabricated satisfying assignment. The caller
  /// must propagate this result and finish the builder before using matrices.
  pub fn emit_setup(
    &self,
    builder: &mut R1csBuilder,
    source_payload_limit: u64,
  ) -> Result<()> {
    ensure!(
      builder.is_shape_only(),
      "setup emission needs a shape-only builder"
    );
    builder.check_status()?;
    let replay = self.replay_setup();
    let layout = SourceLayout::new(replay)?;
    let payload_bytes = layout.counts.payload_bytes()?;
    if payload_bytes > source_payload_limit {
      return Err(
        R1csError::ResourceLimit {
          resource: "Exec setup source-slot payload bytes",
          limit: source_payload_limit,
          actual: payload_bytes,
        }
        .into(),
      );
    }
    // All these zeroes are unknown private values, not circuit constants.
    // In particular this is NOT a native replay or a valid Flock proof.
    let main = TranscriptScratch::new(
      layout.main_observed,
      layout.main_challenges,
      &replay.main.payload_lengths,
    )?;
    let accumulator = TranscriptScratch::new(
      layout.fold_observed,
      layout.fold_challenges,
      &replay.folds.payload_lengths,
    )?;
    let boolean = zeroed::<16>(layout.boolean)?;
    let wiring = zeroed::<16>(F128_WIRING_PRIVATE_VALUES)?;
    let multipoint = zeroed::<16>(F128_MULTIPOINT_JAGGED_CLAIMS)?;
    let inner = zeroed::<16>(layout.inner_values)?;
    let digests = zeroed::<32>(layout.inner_digests)?;
    constrain_exec_root_closed(
      builder,
      Stage4PublicInputsV1::from_statement_digest([0; 32]),
      self.tables(),
      ExecReplayCircuitWitnessV0 {
        statement_binding: replay.binding(),
        commitments: ExecCommitmentsV0 {
          program: [0; 32],
          input: [0; 32],
          output: [0; 32],
        },
        transcript: main.inputs(replay.main.hash.setup_topology()),
        algebra: Stage4TraceWitnessV1 {
          trace: &replay.boolean.trace,
          private_values: &boolean,
        },
        wiring: Stage4TraceWitnessV1 {
          trace: &replay.wiring,
          private_values: &wiring,
        },
        merged_pcs: &replay.pcs.frontend,
        multipoint: Stage4TraceWitnessV1 {
          trace: &replay.pcs.multipoint,
          private_values: &multipoint,
        },
        inner_ligerito: Stage4TraceWitnessV1 {
          trace: &replay.main.inner,
          private_values: &inner,
        },
        inner_ligerito_private_digests: &digests,
        accumulator_transcript: accumulator
          .inputs(replay.folds.hash.setup_topology()),
        matrix_fold: &replay.folds.matrices,
        structure_fold: &replay.folds.structure,
        jagged_fold: &replay.folds.jagged,
      },
    )?;
    builder.check_status()?;
    Ok(())
  }
}

struct SourceLayout {
  main_observed: usize,
  main_challenges: usize,
  fold_observed: usize,
  fold_challenges: usize,
  boolean: usize,
  inner_values: usize,
  inner_digests: usize,
  counts: ExecSetupSourceSlotsV0,
}

impl SourceLayout {
  fn new(replay: &CompiledExecReplay<'_>) -> Result<Self> {
    let main_observed = usize::try_from(replay.main.observed_values)?;
    let main_challenges = usize::try_from(replay.main.challenges)?;
    let fold_observed = usize::try_from(replay.folds.observed_values)?;
    let fold_challenges = usize::try_from(replay.folds.challenges)?;
    // The approved Boolean compiler has one private evaluation per matrix;
    // each table contributes A at 2t and B at 2t+1. Validate its references.
    let boolean = replay.boolean.trace.deferred_matrix_claims.len();
    let inner_values = sum_counts(
      replay
        .main
        .inner
        .levels
        .iter()
        .flat_map(|level| &level.opened_rows)
        .map(Vec::len),
    )?;
    let inner_digests = sum_counts(
      replay
        .main
        .inner
        .levels
        .iter()
        .flat_map(|level| &level.merkle_paths)
        .map(Vec::len),
    )?;
    let public = replay.binding().public_template.len();
    replay.boolean.trace.validate(
      public,
      main_observed,
      main_challenges,
      boolean,
    )?;
    replay.wiring.validate(
      public,
      main_observed,
      main_challenges,
      F128_WIRING_PRIVATE_VALUES,
    )?;
    replay.pcs.multipoint.validate(
      main_observed,
      main_challenges,
      F128_MULTIPOINT_JAGGED_CLAIMS,
    )?;
    replay.main.inner.validate(
      main_observed,
      main_challenges,
      &replay.main.payload_lengths,
      inner_values,
      inner_digests,
    )?;
    replay
      .main
      .hash
      .setup_topology()
      .validate(main_observed, &replay.main.payload_lengths)?;
    replay
      .folds
      .hash
      .setup_topology()
      .validate(fold_observed, &replay.folds.payload_lengths)?;
    let f128_words = sum_counts([
      main_observed,
      main_challenges,
      fold_observed,
      fold_challenges,
      boolean,
      F128_WIRING_PRIVATE_VALUES,
      F128_MULTIPOINT_JAGGED_CLAIMS,
      inner_values,
    ])?;
    let byte_payload_bytes = sum_counts(
      replay
        .main
        .payload_lengths
        .iter()
        .chain(&replay.folds.payload_lengths)
        .copied(),
    )?;
    let byte_payloads = sum_counts([
      replay.main.payload_lengths.len(),
      replay.folds.payload_lengths.len(),
    ])?;
    let counts = ExecSetupSourceSlotsV0 {
      f128_words: u64::try_from(f128_words)?,
      digest32_words: u64::try_from(inner_digests)?,
      byte_payloads: u64::try_from(byte_payloads)?,
      byte_payload_bytes: u64::try_from(byte_payload_bytes)?,
    };
    counts.payload_bytes()?;
    Ok(Self {
      main_observed,
      main_challenges,
      fold_observed,
      fold_challenges,
      boolean,
      inner_values,
      inner_digests,
      counts,
    })
  }
}

fn sum_counts(
  counts: impl IntoIterator<Item = usize>,
) -> Result<usize, R1csError> {
  counts.into_iter().try_fold(0usize, |sum, count| {
    sum.checked_add(count).ok_or(R1csError::CountOverflow)
  })
}

fn zeroed<const N: usize>(count: usize) -> Result<Vec<[u8; N]>> {
  let mut values = Vec::new();
  values.try_reserve_exact(count)?;
  values.resize(count, [0; N]);
  Ok(values)
}

struct TranscriptScratch {
  observed: Vec<[u8; 16]>,
  challenges: Vec<[u8; 16]>,
  payloads: Vec<Vec<u8>>,
}

impl TranscriptScratch {
  fn new(
    observed: usize,
    challenges: usize,
    payload_lengths: &[usize],
  ) -> Result<Self> {
    let mut payloads = Vec::new();
    payloads.try_reserve_exact(payload_lengths.len())?;
    for &length in payload_lengths {
      let mut bytes = Vec::new();
      bytes.try_reserve_exact(length)?;
      bytes.resize(length, 0);
      payloads.push(bytes);
    }
    Ok(Self {
      observed: zeroed::<16>(observed)?,
      challenges: zeroed::<16>(challenges)?,
      payloads,
    })
  }

  fn inputs<'a>(
    &'a self,
    trace: &'a ix_stage4_trace::ChainedBlake3TranscriptV1,
  ) -> Stage4TranscriptWitnessV1<'a> {
    Stage4TranscriptWitnessV1 {
      trace,
      observed_values: &self.observed,
      byte_payloads: &self.payloads,
      challenges: &self.challenges,
    }
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn slot_payload_accounting_is_checked() {
    let counts = ExecSetupSourceSlotsV0 {
      f128_words: 3,
      digest32_words: 2,
      byte_payloads: 2,
      byte_payload_bytes: 9,
    };
    assert_eq!(counts.payload_bytes().unwrap(), 121);
    for bad in [
      ExecSetupSourceSlotsV0 { f128_words: u64::MAX, ..counts },
      ExecSetupSourceSlotsV0 { digest32_words: u64::MAX, ..counts },
      ExecSetupSourceSlotsV0 { byte_payload_bytes: u64::MAX, ..counts },
    ] {
      assert_eq!(bad.payload_bytes(), Err(R1csError::CountOverflow));
    }
    assert_eq!(sum_counts([usize::MAX, 1]), Err(R1csError::CountOverflow));
  }
}
