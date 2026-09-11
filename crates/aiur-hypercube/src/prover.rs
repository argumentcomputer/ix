//! Proving and verifying an [`AiurMachine`] execution — one or many shards —
//! with the Hypercube CPU prover.
//!
//! The crate's `MachineVerifier` checks each shard independently against the
//! shared verifying key; everything cross-shard is checked here (see
//! [`crate::global`]): exactly one shard carries the claim flag, and the
//! shards' septic digests, less the common starting point, sum to the
//! identity.

use std::sync::Arc;

use slop_algebra::AbstractField;
use slop_basefold::FriConfig;
use sp1_hypercube::{
  MachineProof, MachineVerifier, MachineVerifierConfigError,
  MachineVerifyingKey, SP1InnerPcs, SP1PcsProofInner, ShardVerifier,
  prover::simple_prover,
  septic_curve::{SepticCurve, SepticCurveComplete},
  septic_digest::SepticDigest,
};
use sp1_primitives::{
  SP1GlobalContext,
  fri_params::{SP1_PROOF_OF_WORK_BITS, unique_decoding_queries},
};

use crate::{
  F,
  air::AiurAir,
  machine::AiurMachine,
  record::{AiurProgram, AiurRecord, NUM_AIUR_PVS, PV_CLAIM_FLAG, PV_DIGEST},
};

/// Hypercube PCS parameters.
#[derive(Clone, Copy, Debug)]
pub struct ProverParams {
  pub log_blowup: usize,
  /// Traces are stacked into columns of `2^log_stacking_height` elements.
  pub log_stacking_height: u32,
  /// No chip may have more than `2^max_log_row_count` rows.
  pub max_log_row_count: usize,
}

impl Default for ProverParams {
  fn default() -> Self {
    Self { log_blowup: 1, log_stacking_height: 21, max_log_row_count: 20 }
  }
}

pub type AiurVerifyingKey = MachineVerifyingKey<SP1GlobalContext>;
pub type AiurProof = MachineProof<SP1GlobalContext, SP1PcsProofInner>;

/// Verification errors: the per-shard errors of the crate's verifier, plus
/// the cross-shard checks.
#[derive(Debug)]
pub enum AiurVerifyError {
  Shards(MachineVerifierConfigError<SP1GlobalContext, SP1InnerPcs>),
  /// The proof carries no shards.
  Empty,
  /// A shard's public values have the wrong shape.
  MalformedPublicValues,
  /// Not exactly one shard carries the claim flag.
  ClaimShards {
    count: usize,
  },
  /// The shards' septic digests do not cancel: the cross-shard boundary
  /// multisets do not match.
  GlobalDigest,
}

impl std::fmt::Display for AiurVerifyError {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      Self::Shards(e) => write!(f, "shard verification failed: {e:?}"),
      Self::Empty => write!(f, "proof has no shards"),
      Self::MalformedPublicValues => write!(f, "malformed public values"),
      Self::ClaimShards { count } => {
        write!(f, "expected exactly one claim shard, found {count}")
      },
      Self::GlobalDigest => {
        write!(f, "cross-shard digests do not cancel")
      },
    }
  }
}

impl std::error::Error for AiurVerifyError {}

/// The FRI parameters of the Hypercube PCS under `params`.
pub fn fri_config(params: ProverParams) -> FriConfig<F> {
  FriConfig::new(
    params.log_blowup,
    unique_decoding_queries(params.log_blowup),
    SP1_PROOF_OF_WORK_BITS,
  )
}

pub fn shard_verifier(
  machine: &AiurMachine,
  params: ProverParams,
) -> ShardVerifier<SP1GlobalContext, sp1_hypercube::InnerSC<AiurAir>> {
  ShardVerifier::from_basefold_parameters(
    fri_config(params),
    params.log_stacking_height,
    params.max_log_row_count,
    machine.machine().clone(),
  )
}

/// Where a prover's records come from: shard `k` is built on demand, by
/// whichever thread asks first (see [`prove_source`]).
pub trait RecordSource: Sync {
  /// Number of shards.
  fn len(&self) -> usize;
  fn is_empty(&self) -> bool {
    self.len() == 0
  }
  fn take(&self, machine: &AiurMachine, k: usize) -> AiurRecord;
}

/// Records built up front.
pub struct Records(Vec<std::sync::Mutex<Option<AiurRecord>>>);

impl RecordSource for Records {
  fn len(&self) -> usize {
    self.0.len()
  }

  fn take(&self, _machine: &AiurMachine, k: usize) -> AiurRecord {
    self.0[k].lock().expect("record lock").take().expect("taken once")
  }
}

/// Proves an execution's shards, returning the verifying key and the proof.
/// See [`prove_source`].
pub fn prove(
  machine: &AiurMachine,
  records: Vec<AiurRecord>,
  params: ProverParams,
) -> (AiurVerifyingKey, AiurProof) {
  let records = Records(
    records.into_iter().map(|r| std::sync::Mutex::new(Some(r))).collect(),
  );
  prove_source(machine, &records, params)
}

/// Proves an execution's shards, returning the verifying key and the proof.
///
/// Records are taken from `source` in shard order by a few producer threads
/// (`IX_HC_ASSEMBLERS`, default 2) — assembled, padded into the shape
/// catalogue, and handed to the prover through a bounded channel — so
/// assembly overlaps proving and a lazily assembled partition
/// ([`crate::shard::Partition`]) keeps a few shards' traces resident at a
/// time. With the `cuda` feature, `IX_HC_GPU=1` routes proving through
/// [`crate::cuda::prove`]; verification is identical either way.
pub fn prove_source(
  machine: &AiurMachine,
  source: &impl RecordSource,
  params: ProverParams,
) -> (AiurVerifyingKey, AiurProof) {
  let debug = std::env::var_os("IX_HC_DEBUG").is_some();
  let timing = crate::shard::timing_enabled();
  let mv = debug.then(|| MachineVerifier::new(shard_verifier(machine, params)));
  let num_shards = source.len();
  let producers = std::env::var("IX_HC_ASSEMBLERS")
    .ok()
    .and_then(|v| v.parse::<usize>().ok())
    .unwrap_or(2)
    .clamp(1, num_shards.max(1));
  // Every shard is padded into the machine's shape catalogue (see
  // [`crate::shape`]); the partitioner keeps shards under the area bound,
  // so the only way this fails is a row cap too low for the pad chip.
  let build = |k: usize| -> AiurRecord {
    let mut record = source.take(machine, k);
    let start = std::time::Instant::now();
    let class = crate::shape::pad_record(machine, params, &mut record)
      .unwrap_or_else(|e| panic!("shard {k} shape padding: {e}"));
    if timing {
      eprintln!("hypercube shard {k}: padded in {:.2?}", start.elapsed());
    }
    if let Some(mv) = &mv {
      match sp1_hypercube::prover::shape_from_record(mv, &record) {
        Some(shape) => eprintln!(
          "hypercube shard {k} shape: preprocessed_area {}, main_area {} \
           (class {} with {} padding column(s))",
          shape.preprocessed_area,
          shape.main_area,
          class.main_area,
          class.main_padding_cols
        ),
        None => eprintln!("hypercube shard {k} shape: no matching cluster"),
      }
    }
    record
  };
  if debug && std::env::var_os("IX_HC_PLAN_ONLY").is_some() {
    (0..num_shards).for_each(|k| drop(build(k)));
    panic!("IX_HC_PLAN_ONLY: stopping after shape report");
  }
  let next = std::sync::atomic::AtomicUsize::new(0);
  std::thread::scope(|scope| {
    let (tx, rx) =
      std::sync::mpsc::sync_channel::<(usize, AiurRecord)>(producers);
    let (next, build) = (&next, &build);
    for _ in 0..producers {
      let tx = tx.clone();
      scope.spawn(move || {
        loop {
          let k = next.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
          if k >= num_shards || tx.send((k, build(k))).is_err() {
            break;
          }
        }
      });
    }
    drop(tx);
    let records =
      InOrder { rx, pending: std::collections::BTreeMap::new(), next: 0 };
    #[cfg(feature = "cuda")]
    if std::env::var_os("IX_HC_GPU").is_some() {
      return crate::cuda::prove(machine, records, num_shards, params);
    }
    let verifier = shard_verifier(machine, params);
    let runtime = tokio::runtime::Runtime::new().expect("tokio runtime");
    runtime.block_on(async move {
      let prover = simple_prover(verifier);
      let (pk, vk) = prover.setup(Arc::new(AiurProgram)).await;
      // SAFETY: the preprocessed data was produced by this very prover.
      let pk = unsafe { pk.into_inner() };
      let mut shard_proofs = Vec::with_capacity(num_shards);
      let mut pulled = std::time::Instant::now();
      for record in records {
        let waited = pulled.elapsed();
        let start = std::time::Instant::now();
        shard_proofs.push(prover.prove_shard(pk.clone(), record).await);
        if timing {
          eprintln!(
            "hypercube shard {}: waited {waited:.2?} for the record, cpu \
             prove {:.2?}",
            shard_proofs.len() - 1,
            start.elapsed()
          );
        }
        pulled = std::time::Instant::now();
      }
      (vk, MachineProof { shard_proofs })
    })
  })
}

/// The producers' records, yielded in shard order.
struct InOrder {
  rx: std::sync::mpsc::Receiver<(usize, AiurRecord)>,
  pending: std::collections::BTreeMap<usize, AiurRecord>,
  next: usize,
}

impl Iterator for InOrder {
  type Item = AiurRecord;

  fn next(&mut self) -> Option<AiurRecord> {
    loop {
      if let Some(record) = self.pending.remove(&self.next) {
        self.next += 1;
        return Some(record);
      }
      let (k, record) = self.rx.recv().ok()?;
      self.pending.insert(k, record);
    }
  }
}

/// Verifies a proof against the machine and verifying key, returning the
/// verified claim (the claim shard's public-value prefix).
pub fn verify(
  machine: &AiurMachine,
  params: ProverParams,
  vk: &AiurVerifyingKey,
  proof: &AiurProof,
) -> Result<Vec<F>, AiurVerifyError> {
  if std::env::var_os("IX_HC_DEBUG").is_some() {
    for (i, shard) in proof.shard_proofs.iter().enumerate() {
      let areas: Vec<usize> = shard
        .evaluation_proof
        .row_counts_and_column_counts
        .iter()
        .map(|rc_cc| {
          let n = rc_cc.len().saturating_sub(2);
          rc_cc.iter().take(n).map(|(r, c)| r * c).sum()
        })
        .collect();
      eprintln!("hypercube shard {i} jagged round areas: {areas:?}");
    }
  }
  MachineVerifier::new(shard_verifier(machine, params))
    .verify(vk, proof)
    .map_err(AiurVerifyError::Shards)?;

  if proof.shard_proofs.is_empty() {
    return Err(AiurVerifyError::Empty);
  }
  let start = SepticDigest::<F>::zero().0;
  let neg_start =
    SepticCurveComplete::Affine(SepticCurve { x: start.x, y: -start.y });
  let mut sum = SepticCurveComplete::Infinity;
  let mut claim = None;
  let mut claim_shards = 0usize;
  for shard in &proof.shard_proofs {
    let pv = &shard.public_values;
    if pv.len() < NUM_AIUR_PVS {
      return Err(AiurVerifyError::MalformedPublicValues);
    }
    if pv[PV_CLAIM_FLAG] == F::one() {
      claim_shards += 1;
      // The claim message is the full zero-padded prefix; junk in the
      // padding would make it a different tuple than the one returned.
      if pv[machine.claim_len()..PV_CLAIM_FLAG].iter().any(|v| *v != F::zero())
      {
        return Err(AiurVerifyError::MalformedPublicValues);
      }
      claim = Some(pv[..machine.claim_len()].to_vec());
    }
    let septic = |at: usize| {
      sp1_hypercube::septic_extension::SepticExtension::<F>(
        core::array::from_fn(|k| pv[at + k]),
      )
    };
    let end = SepticCurve { x: septic(PV_DIGEST), y: septic(PV_DIGEST + 7) };
    // Each shard contributes its chain's net movement, `end ⊖ start`.
    sum = sum + SepticCurveComplete::Affine(end) + neg_start;
  }
  if claim_shards != 1 {
    return Err(AiurVerifyError::ClaimShards { count: claim_shards });
  }
  if !matches!(sum, SepticCurveComplete::Infinity) {
    return Err(AiurVerifyError::GlobalDigest);
  }
  Ok(claim.expect("claim shard found"))
}
