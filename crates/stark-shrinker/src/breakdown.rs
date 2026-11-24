//! Exact byte-by-byte size breakdown for Protocol `v6` (`Fp^3`) and `v6-zk`
//! (`Fp^3` hiding) `multi-stark` proofs.

use multi_stark::{
  prover::Proof,
  types::{GoldilocksBlake3V6Config, GoldilocksBlake3V6ZkConfig},
};

const VAL_BYTES: usize = 8;
const EXT3_BYTES: usize = 24;
const HASH_BYTES: usize = 32;
const SALT_BYTES: usize = 16;

/// Exact component-by-component breakdown of a `multi-stark` proof.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ProofBreakdown {
  /// Total `Proof::to_bytes()` (`bincode` Fixint) serialized size in bytes.
  pub total_bincode_bytes: usize,
  /// Compact canonical fixed-shape packed size (when measured).
  pub total_compact_bytes: usize,
  /// Active bitmap, `log_degrees`, and `intermediate_accumulators` raw payload.
  pub header_and_accumulators_bytes: usize,
  /// Stage-1, Stage-2, and Quotient Merkle cap roots (`32 B` per root).
  pub commitments_cap_bytes: usize,
  /// Out-of-domain (`zeta`, `zeta*g`) opened values across all 4 batches.
  pub ood_openings_bytes: usize,
  /// Query-phase opened Stage-1 (main) rows (`8 B` per `Val`).
  pub query_stage1_rows_bytes: usize,
  /// Query-phase opened Stage-2 (LogUp) rows (`8 B` per `Val`).
  pub query_stage2_rows_bytes: usize,
  /// Query-phase opened Quotient rows (`8 B` per `Val`, incl. ZK randomizer).
  pub query_quotient_rows_bytes: usize,
  /// Query-phase opened Preprocessed rows (`8 B` per `Val`).
  pub query_preprocessed_rows_bytes: usize,
  /// Pruned Merkle sibling hashes for the 4 input batches (`[s1, s2, q, prep]`).
  pub input_merkle_siblings_by_batch: [usize; 4],
  /// Leaf salts for the 4 input batches (`v6-zk` only; `0` for transparent `v6`).
  pub input_leaf_salts_bytes: usize,
  /// FRI commit-phase Merkle cap roots + commit/query PoW witnesses.
  pub fri_commits_and_pow_bytes: usize,
  /// FRI final polynomial coefficients (`24 B` per `ExtVal3`).
  pub fri_final_poly_bytes: usize,
  /// FRI query-phase folding sibling values (`24 B` per `ExtVal3`).
  pub fri_query_siblings_bytes: usize,
  /// Pruned Merkle sibling hashes across all FRI commit rounds (`32 B` each).
  pub fri_merkle_siblings_bytes: usize,
  /// Leaf salts across all FRI commit rounds (`v6-zk` only).
  pub fri_leaf_salts_bytes: usize,
  /// Number of FRI commit rounds.
  pub fri_rounds: usize,
  /// Number of active circuits in the outer proof.
  pub active_circuits: usize,
  /// Maximum trace log-degree in the outer proof.
  pub max_log_degree: u8,
  /// Total raw payload bytes (excluding bincode Vec-length framing).
  pub raw_payload_bytes: usize,
  /// Redundant bincode Fixint `Vec` length / Option framing overhead.
  pub bincode_framing_overhead_bytes: usize,
}

impl ProofBreakdown {
  pub const fn query_rows_total_bytes(&self) -> usize {
    self.query_stage1_rows_bytes
      + self.query_stage2_rows_bytes
      + self.query_quotient_rows_bytes
      + self.query_preprocessed_rows_bytes
  }

  pub const fn input_merkle_siblings_total_bytes(&self) -> usize {
    self.input_merkle_siblings_by_batch[0]
      + self.input_merkle_siblings_by_batch[1]
      + self.input_merkle_siblings_by_batch[2]
      + self.input_merkle_siblings_by_batch[3]
  }

  pub const fn total_leaf_salts_bytes(&self) -> usize {
    self.input_leaf_salts_bytes + self.fri_leaf_salts_bytes
  }

  pub const fn fri_total_bytes(&self) -> usize {
    self.fri_commits_and_pow_bytes
      + self.fri_final_poly_bytes
      + self.fri_query_siblings_bytes
      + self.fri_merkle_siblings_bytes
      + self.fri_leaf_salts_bytes
  }

  fn finalize(&mut self) {
    self.raw_payload_bytes = self.header_and_accumulators_bytes
      + self.commitments_cap_bytes
      + self.ood_openings_bytes
      + self.query_rows_total_bytes()
      + self.input_merkle_siblings_total_bytes()
      + self.input_leaf_salts_bytes
      + self.fri_total_bytes();
    self.bincode_framing_overhead_bytes =
      self.total_bincode_bytes.saturating_sub(self.raw_payload_bytes);
  }

  #[allow(clippy::cast_precision_loss)]
  pub fn summary_line(&self) -> String {
    format!(
      "bincode={} B ({:.1} KB) | compact={} B ({:.1} KB) | raw={} B + framing={} B | \
       rows={} B (s1={}, s2={}, q={}, prep={}) | in_merkle={} B | \
       fri={} B (caps+pow={}, fpoly={}, sibs={}, merkle={}, salts={}) | \
       in_salts={} B | ood={} B | caps={} B | circuits={} max_log={} rounds={}",
      self.total_bincode_bytes,
      self.total_bincode_bytes as f64 / 1024.0,
      self.total_compact_bytes,
      self.total_compact_bytes as f64 / 1024.0,
      self.raw_payload_bytes,
      self.bincode_framing_overhead_bytes,
      self.query_rows_total_bytes(),
      self.query_stage1_rows_bytes,
      self.query_stage2_rows_bytes,
      self.query_quotient_rows_bytes,
      self.query_preprocessed_rows_bytes,
      self.input_merkle_siblings_total_bytes(),
      self.fri_total_bytes(),
      self.fri_commits_and_pow_bytes,
      self.fri_final_poly_bytes,
      self.fri_query_siblings_bytes,
      self.fri_merkle_siblings_bytes,
      self.fri_leaf_salts_bytes,
      self.input_leaf_salts_bytes,
      self.ood_openings_bytes,
      self.commitments_cap_bytes,
      self.active_circuits,
      self.max_log_degree,
      self.fri_rounds,
    )
  }
}

fn ood_round_bytes<T>(round: &[Vec<Vec<T>>]) -> usize {
  let count: usize = round.iter().flat_map(|m| m.iter()).map(Vec::len).sum();
  count * EXT3_BYTES
}

/// Compute the exact byte-by-byte breakdown of a transparent Protocol `v6` proof.
pub fn analyze_v6(
  proof: &Proof<GoldilocksBlake3V6Config>,
  compact_bytes: usize,
) -> Result<ProofBreakdown, String> {
  let bincode_bytes = proof
    .to_bytes()
    .map_err(|e| format!("v6 proof serialize failed: {e}"))?
    .len();
  let mut out = ProofBreakdown {
    total_bincode_bytes: bincode_bytes,
    total_compact_bytes: compact_bytes,
    active_circuits: proof.active.iter().filter(|&&a| a).count(),
    max_log_degree: proof.log_degrees.iter().copied().max().unwrap_or(0),
    fri_rounds: proof.opening_proof.commit_phase_openings.len(),
    ..Default::default()
  };

  out.header_and_accumulators_bytes = proof.active.len()
    + proof.log_degrees.len()
    + proof.intermediate_accumulators.len() * EXT3_BYTES;
  out.commitments_cap_bytes = (proof.commitments.stage_1_trace.roots().len()
    + proof.commitments.stage_2_trace.roots().len()
    + proof.commitments.quotient_chunks.roots().len())
    * HASH_BYTES;
  out.ood_openings_bytes = ood_round_bytes(&proof.stage_1_opened_values)
    + ood_round_bytes(&proof.stage_2_opened_values)
    + ood_round_bytes(&proof.quotient_opened_values)
    + proof
      .preprocessed_opened_values
      .as_ref()
      .map_or(0, |r| ood_round_bytes(r));

  let fri = &proof.opening_proof;
  for (batch, opening) in fri.input_openings.iter().enumerate() {
    let vals: usize =
      opening.opened_values.iter().flat_map(|q| q.iter()).map(Vec::len).sum();
    let row_bytes = vals * VAL_BYTES;
    match batch {
      0 => out.query_stage1_rows_bytes = row_bytes,
      1 => out.query_stage2_rows_bytes = row_bytes,
      2 => out.query_quotient_rows_bytes = row_bytes,
      3 => out.query_preprocessed_rows_bytes = row_bytes,
      _ => {},
    }
    if batch < 4 {
      out.input_merkle_siblings_by_batch[batch] =
        opening.opening_proof.sibling_hashes.len() * HASH_BYTES;
    }
  }

  let fri_cap_roots: usize =
    fri.commit_phase_commits.iter().map(|c| c.roots().len()).sum();
  out.fri_commits_and_pow_bytes = fri_cap_roots * HASH_BYTES
    + fri.commit_pow_witnesses.len() * VAL_BYTES
    + VAL_BYTES; // query_pow_witness
  out.fri_final_poly_bytes = fri.final_poly.len() * EXT3_BYTES;
  for step in &fri.commit_phase_openings {
    let sib_vals: usize = step.sibling_values.iter().map(Vec::len).sum();
    out.fri_query_siblings_bytes += 1 + sib_vals * EXT3_BYTES; // 1B log_arity
    out.fri_merkle_siblings_bytes +=
      step.opening_proof.sibling_hashes.len() * HASH_BYTES;
  }

  out.finalize();
  Ok(out)
}

/// Compute the exact byte-by-byte breakdown of a hiding Protocol `v6-zk` proof.
pub fn analyze_v6_zk(
  proof: &Proof<GoldilocksBlake3V6ZkConfig>,
  compact_bytes: usize,
) -> Result<ProofBreakdown, String> {
  let bincode_bytes = proof
    .to_bytes()
    .map_err(|e| format!("v6-zk proof serialize failed: {e}"))?
    .len();
  let mut out = ProofBreakdown {
    total_bincode_bytes: bincode_bytes,
    total_compact_bytes: compact_bytes,
    active_circuits: proof.active.iter().filter(|&&a| a).count(),
    max_log_degree: proof.log_degrees.iter().copied().max().unwrap_or(0),
    fri_rounds: proof.opening_proof.commit_phase_openings.len(),
    ..Default::default()
  };

  out.header_and_accumulators_bytes = proof.active.len()
    + proof.log_degrees.len()
    + proof.intermediate_accumulators.len() * EXT3_BYTES;
  out.commitments_cap_bytes = (proof.commitments.stage_1_trace.roots().len()
    + proof.commitments.stage_2_trace.roots().len()
    + proof.commitments.quotient_chunks.roots().len())
    * HASH_BYTES;
  out.ood_openings_bytes = ood_round_bytes(&proof.stage_1_opened_values)
    + ood_round_bytes(&proof.stage_2_opened_values)
    + ood_round_bytes(&proof.quotient_opened_values)
    + proof
      .preprocessed_opened_values
      .as_ref()
      .map_or(0, |r| ood_round_bytes(r));

  let fri = &proof.opening_proof;
  for (batch, opening) in fri.input_openings.iter().enumerate() {
    let vals: usize =
      opening.opened_values.iter().flat_map(|q| q.iter()).map(Vec::len).sum();
    let row_bytes = vals * VAL_BYTES;
    match batch {
      0 => out.query_stage1_rows_bytes = row_bytes,
      1 => out.query_stage2_rows_bytes = row_bytes,
      2 => out.query_quotient_rows_bytes = row_bytes,
      3 => out.query_preprocessed_rows_bytes = row_bytes,
      _ => {},
    }
    if batch < 4 {
      out.input_merkle_siblings_by_batch[batch] =
        opening.opening_proof.pruned.sibling_hashes.len() * HASH_BYTES;
    }
    let salts: usize = opening.opening_proof.salts.iter().map(Vec::len).sum();
    out.input_leaf_salts_bytes += salts * SALT_BYTES;
  }

  let fri_cap_roots: usize =
    fri.commit_phase_commits.iter().map(|c| c.roots().len()).sum();
  out.fri_commits_and_pow_bytes = fri_cap_roots * HASH_BYTES
    + fri.commit_pow_witnesses.len() * VAL_BYTES
    + VAL_BYTES; // query_pow_witness
  out.fri_final_poly_bytes = fri.final_poly.len() * EXT3_BYTES;
  for step in &fri.commit_phase_openings {
    let sib_vals: usize = step.sibling_values.iter().map(Vec::len).sum();
    out.fri_query_siblings_bytes += 1 + sib_vals * EXT3_BYTES;
    out.fri_merkle_siblings_bytes +=
      step.opening_proof.pruned.sibling_hashes.len() * HASH_BYTES;
    let salts: usize = step.opening_proof.salts.iter().map(Vec::len).sum();
    out.fri_leaf_salts_bytes += salts * SALT_BYTES;
  }

  out.finalize();
  Ok(out)
}
