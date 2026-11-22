//! What each execution is charged when the record pool admits it, and the
//! run's account of how those charges compared with the records measured.

use ixon::shard::{RECORD_STORAGE_FACTOR, ShardInfo, predicted_record_bytes};

use crate::format_gib;

/// The charge of an aggregation execution (a join or the root) before this
/// run has measured an aggregation record or either of its inputs' records:
/// at least every one of the 54 aggregation records (53 joins and the root)
/// of the 2026-11-04 Mathlib run (1 GPU, 1.5e9 cells), whose largest was
/// 43.4 GiB and mean 27.5 GiB.
pub(crate) const AGGREGATION_RECORD_BYTES: usize = 44 << 30;

/// Where a predicted record size comes from.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Basis {
  /// The claim's record as a previous run measured it, from the manifest.
  Measured,
  /// The record model over the claim's owned and frontier bytes.
  Model,
  /// The larger of the aggregation's two inputs' measured records.
  Inputs,
  /// The largest aggregation record this run has measured, when an input's
  /// record was not measured in this run.
  Observed,
  /// [`AGGREGATION_RECORD_BYTES`].
  Constant,
}

impl Basis {
  fn name(self) -> String {
    match self {
      Self::Measured => "measured".into(),
      Self::Model => "model".into(),
      Self::Inputs => "larger input".into(),
      Self::Observed => "largest aggregation so far".into(),
      Self::Constant => "aggregation default".into(),
    }
  }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Prediction {
  pub bytes: usize,
  pub basis: Basis,
}

impl Prediction {
  pub(crate) fn describe(self) -> String {
    format!("{} GiB ({})", format_gib(self.bytes), self.basis.name())
  }
}

/// Growth of a claim's record from the row references a CUDA prover
/// records for per-shard device population (`aiur::refs`,
/// `AIUR_RECORD_REFS=1`), which [`predicted_record_bytes`], fitted before
/// they existed, leaves out. On Init claim 0 they took 2.05 GB beside
/// 25.8 GB of query and ROM storage (7.9%).
pub(crate) const RECORD_REFS_FACTOR: f64 = 1.08;


/// [`RECORD_REFS_FACTOR`] when executions record row references, else 1.
fn record_refs_factor() -> f64 {
  if std::env::var("AIUR_RECORD_REFS").as_deref() == Ok("1") {
    RECORD_REFS_FACTOR
  } else {
    1.0
  }
}

/// A claim's predicted record: its measured size when the manifest has
/// one, otherwise the record model ([`predicted_record_bytes`]) at the
/// current storage layout ([`RECORD_STORAGE_FACTOR`]) with any row
/// references ([`RECORD_REFS_FACTOR`]).
#[allow(clippy::cast_precision_loss, clippy::cast_possible_truncation)]
#[allow(clippy::cast_sign_loss)]
pub(crate) fn claim_prediction(info: &ShardInfo) -> Prediction {
  if info.measured_record_bytes != 0 {
    return Prediction {
      bytes: usize::try_from(info.measured_record_bytes).unwrap_or(usize::MAX),
      basis: Basis::Measured,
    };
  }
  let bytes = (predicted_record_bytes(info.own_size, info.cross_ingress) as f64
    * RECORD_STORAGE_FACTOR
    * record_refs_factor()) as u64;
  Prediction {
    bytes: usize::try_from(bytes).unwrap_or(usize::MAX),
    basis: Basis::Model,
  }
}

/// An aggregation's predicted record: the larger of its two inputs'
/// records when both were measured in this run, otherwise the largest
/// aggregation record measured so far, otherwise
/// [`AGGREGATION_RECORD_BYTES`]. Over the 54 aggregations of the 2026-11-04
/// Mathlib run the larger input fell short 3 times, by at most 9.2 GiB (the
/// root, 32.2 GiB, joined inputs of 23.0 and 22.6 GiB), within the
/// overshoot buffer; the largest aggregation so far overcharged the median
/// aggregation by 1.6x.
pub(crate) fn aggregation_prediction(
  largest: Option<usize>,
  inputs: [Option<usize>; 2],
) -> Prediction {
  match (inputs, largest) {
    ([Some(left), Some(right)], _) => {
      Prediction { bytes: left.max(right), basis: Basis::Inputs }
    },
    (_, Some(bytes)) => Prediction { bytes, basis: Basis::Observed },
    (_, None) => {
      Prediction { bytes: AGGREGATION_RECORD_BYTES, basis: Basis::Constant }
    },
  }
}

/// How the run's admissions went, accumulated across passes.
#[derive(Clone, Debug, Default)]
pub(crate) struct AdmissionStats {
  /// The record share `s`, also the overshoot buffer.
  pub share: usize,
  /// Per executed claim: the prediction it was admitted by and its
  /// measured record bytes.
  pub claims: Vec<(usize, usize)>,
  /// Per executed model-predicted claim: the uncorrected model prediction
  /// and the measured record bytes.
  pub model: Vec<(usize, usize)>,
  /// Per executed aggregation: predicted and measured record bytes.
  pub aggregations: Vec<(usize, usize)>,
  /// Executions cancelled for memory contention, and the executor-seconds
  /// they had run.
  pub cancellations: usize,
  pub discarded_secs: f64,
  pub peak_executing: usize,
}

#[allow(clippy::cast_precision_loss)]
fn ratio(predicted: usize, actual: usize) -> f64 {
  actual as f64 / predicted.max(1) as f64
}

#[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
#[allow(clippy::cast_precision_loss)]
fn quantile(sorted: &[f64], q: f64) -> f64 {
  sorted[((sorted.len() - 1) as f64 * q).round() as usize]
}

impl AdmissionStats {
  pub(crate) fn merge(&mut self, other: Self) {
    self.share = self.share.max(other.share);
    self.claims.extend(other.claims);
    self.model.extend(other.model);
    self.aggregations.extend(other.aggregations);
    self.cancellations += other.cancellations;
    self.discarded_secs += other.discarded_secs;
    self.peak_executing = self.peak_executing.max(other.peak_executing);
  }

  /// One line: the distribution of actual over predicted record size for
  /// claims and aggregations, how many claims outgrew their prediction and
  /// by more than the share, the most executions at once, and the cost of
  /// contention.
  pub(crate) fn summary(&self, freezes: usize, frozen_secs: f64) -> String {
    let share = self.share;
    let distribution = |records: &[(usize, usize)]| {
      if records.is_empty() {
        return "none executed".to_string();
      }
      let mut ratios: Vec<f64> =
        records.iter().map(|&(p, a)| ratio(p, a)).collect();
      ratios.sort_by(f64::total_cmp);
      format!(
        "{} executed, actual/predicted min {:.2} p50 {:.2} p90 {:.2} max {:.2}",
        records.len(),
        ratios[0],
        quantile(&ratios, 0.5),
        quantile(&ratios, 0.9),
        ratios[ratios.len() - 1],
      )
    };
    let over = self.claims.iter().filter(|&&(p, a)| a > p).count();
    let beyond =
      self.claims.iter().filter(|&&(p, a)| a > p.saturating_add(share)).count();
    format!(
      "admission: claims {} ({over} over prediction, {beyond} by more than the {} GiB share); record model alone {}; aggregations {}; at most {} executions at once; admission frozen {freezes} times for {frozen_secs:.0}s; {} executions cancelled for memory contention, discarding {:.0} executor-seconds",
      distribution(&self.claims),
      format_gib(share),
      distribution(&self.model),
      distribution(&self.aggregations),
      self.peak_executing,
      self.cancellations,
      self.discarded_secs,
    )
  }
}
