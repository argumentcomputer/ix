//! Versioned diagnostics. These encodings are not cryptographic statements.

use serde::{Serialize, Serializer};
use serde_json::{Value, json};

use crate::{FLOCK_UPSTREAM_REVISION, FlockConfigV1, Stage3PreflightReportV1};

pub(crate) fn hex(digest: [u8; 32]) -> String {
  blake3::Hash::from_bytes(digest).to_hex().to_string()
}

pub(crate) fn serialize_digest<S: Serializer>(
  digest: &[u8; 32],
  serializer: S,
) -> Result<S::Ok, S::Error> {
  serializer.serialize_str(&hex(*digest))
}

pub(crate) fn elapsed_us(start: std::time::Instant) -> u64 {
  u64::try_from(start.elapsed().as_micros()).unwrap_or(u64::MAX)
}

#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize)]
pub struct Stage3PreflightTimingsV1 {
  pub native_prepare_us: u64,
  pub lowering_us: u64,
  pub compile_us: u64,
  pub evaluate_us: u64,
  pub total_us: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct Stage3ResourceReportV1 {
  pub virtual_union_log: u64,
  pub committed_union_log: u64,
  pub dense_witness_bytes: u64,
  pub padded_union_witness_bytes: u64,
  pub pcs_message_bytes: u64,
  pub pcs_codeword_bytes: u64,
  pub pcs_log_batch_size: u64,
  pub pcs_lanes: u64,
  pub pcs_log_inverse_rate: u64,
  pub tables: Vec<Stage3TableReportV1>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct Stage3TableReportV1 {
  pub registry_slot: u64,
  pub rows: u64,
  pub boolean_columns: u64,
  pub useful_boolean_columns: u64,
  pub padded_witness_bytes: u64,
}

impl Stage3PreflightReportV1 {
  /// Stable JSON object, suitable for one JSONL record per aggregate root.
  /// Durations and process memory are diagnostic and excluded from digests.
  pub fn to_json_value(&self) -> Value {
    let advice = &self.advice;
    json!({
      "schema": "ix.flock-stage3.preflight", "version": 1,
      "stage2_root_digest": hex(self.stage2_root_digest),
      "relation_digest": hex(self.relation_digest),
      "stage3_statement_digest": hex(self.stage3_statement_digest),
      "config_digest": hex(FlockConfigV1.digest()),
      "flock_revision": FLOCK_UPSTREAM_REVISION,
      "profile": "fast128", "merkle_hash": "blake3",
      "transcript": "chained-blake3",
      "transcript_domain": String::from_utf8_lossy(crate::STAGE3_TRANSCRIPT_DOMAIN),
      "transport": {
        "verifying_key_digest": hex(self.verifying_key_digest),
        "compact_proof_digest": hex(self.compact_proof_digest),
        "verifying_key_bytes": self.verifying_key_bytes,
        "claim_bytes": self.claim_bytes,
        "compact_proof_bytes": self.compact_proof_bytes,
      },
      "specialization": {
        "typed_witness_layout_digest": hex(self.typed_witness_layout_digest),
        "activation": self.activation, "active_log_degrees": self.log_degrees,
        "fri_parameter_words": self.fri_parameter_words,
      },
      "advice": {
        "advice_bytes": advice.advice_bytes,
        "total_circuits": advice.total_circuits,
        "active_circuits": advice.active_circuits,
        "queries": advice.queries, "fri_rounds": advice.fri_rounds,
        "input_rounds_per_query": advice.input_rounds_per_query,
        "commitment_cap_digests": advice.commitment_cap_digests,
        "input_merkle_siblings": advice.input_merkle_siblings,
        "fri_merkle_siblings": advice.fri_merkle_siblings,
        "opened_base_values": advice.opened_base_values,
        "fri_sibling_extension_values": advice.fri_sibling_extension_values,
        "other_extension_values": advice.other_extension_values,
      },
      "relation": self.relation, "resources": self.resources,
      "limits": self.limits, "timings": self.timings,
      "relation_cache": "none",
      "process_peak_rss_bytes": self.process_peak_rss_bytes,
      "memory_note": "Padded witness covers z/a/b; compiler, lincheck, PCS and allocator scratch are additional. RSS is the process lifetime high-water mark, not a per-root peak.",
    })
  }
}

/// Linux's process high-water mark. A batch's later records include previous
/// roots; use separate processes when measuring individual peak memory.
pub fn process_peak_rss_bytes() -> Option<u64> {
  let status = std::fs::read_to_string("/proc/self/status").ok()?;
  let line = status.lines().find(|line| line.starts_with("VmHWM:"))?;
  line.split_whitespace().nth(1)?.parse::<u64>().ok()?.checked_mul(1024)
}
