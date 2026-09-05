use anyhow::{Result, bail};
use ix_terminal::{
  OUTER_CLAIM_BYTES, STAGE2_CLAIMS_BYTES, Stage2AdviceProfileV1,
  ValidatedStage2RootV1,
};
use multi_stark::types::FriParameters;
use serde::{Deserialize, Serialize};

const MIB: u64 = 1024 * 1024;

/// Host-side admission limits applied before a Stage 3 relation is built.
///
/// These limits are denial-of-service guards, not cryptographic parameters and
/// not a claim that every admitted proof will fit a particular machine. The
/// exact relation census printed by preflight remains the operator's sizing
/// input.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(default, deny_unknown_fields)]
pub struct Stage3ResourceLimitsV1 {
  pub max_verifying_key_bytes: u64,
  pub max_compact_proof_bytes: u64,
  pub max_advice_bytes: u64,
  pub max_total_circuits: u64,
  pub max_fri_queries: u64,
  pub max_fri_rounds: u64,
  pub max_profile_items: u64,
  /// Capacity guard checked before building the circuit's wiring.
  pub max_table_capacity: u64,
  /// Combined size of the three padded union buffers, excluding PCS and
  /// compiler scratch space. This is not a total process RSS limit.
  pub max_union_witness_bytes: u64,
}

impl Default for Stage3ResourceLimitsV1 {
  fn default() -> Self {
    Self {
      max_verifying_key_bytes: 16 * MIB,
      max_compact_proof_bytes: 64 * MIB,
      max_advice_bytes: 256 * MIB,
      max_total_circuits: 1 << 16,
      max_fri_queries: 1_024,
      max_fri_rounds: 32,
      max_profile_items: 1 << 24,
      max_table_capacity: 1 << 22,
      max_union_witness_bytes: 32 * 1024 * MIB,
    }
  }
}

impl Stage3ResourceLimitsV1 {
  pub(crate) fn ensure_table_capacity(self, nu: usize) -> Result<()> {
    let capacity = 1u64
      .checked_shl(u32::try_from(nu)?)
      .ok_or_else(|| anyhow::anyhow!("Stage 3 table capacity overflows u64"))?;
    if capacity > self.max_table_capacity {
      bail!(
        "Stage 3 table capacity {capacity} (nu={nu}) exceeds admission limit {}",
        self.max_table_capacity
      );
    }
    Ok(())
  }

  pub(crate) fn ensure_union_witness(self, bytes: u64) -> Result<()> {
    if bytes > self.max_union_witness_bytes {
      bail!(
        "Stage 3 padded union witness requires {bytes} bytes; admission limit is {} (PCS/compiler scratch is additional)",
        self.max_union_witness_bytes
      );
    }
    Ok(())
  }
  /// Reject impossible or oversized raw inputs before decoding/verifying them.
  pub fn ensure_transport(
    self,
    vk_bytes: &[u8],
    claim_bytes: &[u8],
    proof_bytes: &[u8],
    fri: &FriParameters,
  ) -> Result<()> {
    self.ensure_raw_transport(vk_bytes, claim_bytes, proof_bytes)?;
    self.ensure_fri(fri)
  }

  pub(crate) fn ensure_raw_transport(
    self,
    vk_bytes: &[u8],
    claim_bytes: &[u8],
    proof_bytes: &[u8],
  ) -> Result<()> {
    ensure_nonempty_bounded(
      vk_bytes.len(),
      self.max_verifying_key_bytes,
      "Stage 2 verifying key",
    )?;
    if claim_bytes.len() != OUTER_CLAIM_BYTES {
      bail!(
        "Stage 2 outer claim is {} bytes; expected {OUTER_CLAIM_BYTES}",
        claim_bytes.len()
      );
    }
    ensure_nonempty_bounded(
      proof_bytes.len(),
      self.max_compact_proof_bytes,
      "compact Stage 2 proof",
    )?;
    Ok(())
  }

  fn ensure_fri(self, fri: &FriParameters) -> Result<()> {
    if fri.log_final_poly_len != 0 {
      bail!("Stage 3 currently requires a constant final FRI polynomial");
    }
    if fri.max_log_arity != 1 {
      bail!("Stage 3 currently requires binary FRI (maximum log arity 1)");
    }
    let queries = as_u64(fri.num_queries, "FRI query count")?;
    if queries == 0 || queries > self.max_fri_queries {
      bail!(
        "Stage 3 FRI query count {queries} is outside 1..={}",
        self.max_fri_queries
      );
    }
    for (label, bits) in [
      ("commit", fri.commit_proof_of_work_bits),
      ("query", fri.query_proof_of_work_bits),
    ] {
      if bits >= 64 {
        bail!("Stage 3 FRI {label} PoW width {bits} is outside 0..64");
      }
    }
    Ok(())
  }

  /// Reject expanded proof geometry that is too large to hand to the relation
  /// compiler. This runs immediately after native proof expansion.
  pub fn ensure_prepared(self, prepared: &ValidatedStage2RootV1) -> Result<()> {
    ensure_nonempty_bounded(
      prepared.verifying_key_bytes().len(),
      self.max_verifying_key_bytes,
      "expanded Stage 2 verifying key",
    )?;
    if prepared.claims_bytes().len() != STAGE2_CLAIMS_BYTES {
      bail!(
        "expanded Stage 2 claims are {} bytes; expected {STAGE2_CLAIMS_BYTES}",
        prepared.claims_bytes().len()
      );
    }
    ensure_nonempty_bounded(
      prepared.advice_bytes().len(),
      self.max_advice_bytes,
      "expanded Stage 2 advice",
    )?;

    let profile = prepared.advice_profile();
    if profile.advice_bytes
      != as_u64(prepared.advice_bytes().len(), "expanded advice length")?
    {
      bail!("Stage 2 advice profile byte length disagrees with its transport");
    }
    ensure_range(
      profile.total_circuits,
      self.max_total_circuits,
      "total circuit count",
    )?;
    if profile.active_circuits == 0
      || profile.active_circuits > profile.total_circuits
    {
      bail!(
        "Stage 2 active circuit count {} is outside 1..={}",
        profile.active_circuits,
        profile.total_circuits
      );
    }
    ensure_range(profile.queries, self.max_fri_queries, "FRI query count")?;
    ensure_range(profile.fri_rounds, self.max_fri_rounds, "FRI round count")?;

    for (label, value) in profile_items(profile) {
      if value > self.max_profile_items {
        bail!(
          "Stage 2 {label} count {value} exceeds host admission limit {}",
          self.max_profile_items
        );
      }
    }
    Ok(())
  }
}

fn profile_items(profile: &Stage2AdviceProfileV1) -> [(&'static str, u64); 7] {
  [
    ("input rounds per query", profile.input_rounds_per_query),
    ("commitment cap digest", profile.commitment_cap_digests),
    ("input Merkle sibling", profile.input_merkle_siblings),
    ("FRI Merkle sibling", profile.fri_merkle_siblings),
    ("opened base value", profile.opened_base_values),
    ("FRI sibling extension value", profile.fri_sibling_extension_values),
    ("other extension value", profile.other_extension_values),
  ]
}

fn ensure_nonempty_bounded(
  observed: usize,
  maximum: u64,
  label: &str,
) -> Result<()> {
  let observed = as_u64(observed, label)?;
  if observed == 0 || observed > maximum {
    bail!("{label} length {observed} is outside 1..={maximum} bytes");
  }
  Ok(())
}

fn ensure_range(observed: u64, maximum: u64, label: &str) -> Result<()> {
  if observed == 0 || observed > maximum {
    bail!("Stage 2 {label} {observed} is outside 1..={maximum}");
  }
  Ok(())
}

fn as_u64(value: usize, label: &str) -> Result<u64> {
  u64::try_from(value)
    .map_err(|error| anyhow::anyhow!("{label} exceeds u64: {error}"))
}

#[cfg(test)]
mod tests {
  use super::*;

  fn production_fri() -> FriParameters {
    FriParameters {
      log_final_poly_len: 0,
      max_log_arity: 1,
      num_queries: 100,
      commit_proof_of_work_bits: 0,
      query_proof_of_work_bits: 20,
    }
  }

  #[test]
  fn production_parameters_pass_early_admission() {
    Stage3ResourceLimitsV1::default()
      .ensure_transport(
        b"canonical-looking vk transport",
        &[0; OUTER_CLAIM_BYTES],
        b"canonical-looking compact proof transport",
        &production_fri(),
      )
      .unwrap();
  }

  #[test]
  fn transport_admission_rejects_unsupported_or_oversized_work() {
    let limits = Stage3ResourceLimitsV1 {
      max_verifying_key_bytes: 2,
      max_compact_proof_bytes: 3,
      ..Stage3ResourceLimitsV1::default()
    };
    let claim = [0; OUTER_CLAIM_BYTES];
    assert!(
      limits
        .ensure_transport(b"too long", &claim, b"ok", &production_fri())
        .is_err()
    );
    assert!(
      limits
        .ensure_transport(b"ok", &claim, b"long", &production_fri())
        .is_err()
    );

    let mut non_binary = production_fri();
    non_binary.max_log_arity = 2;
    assert!(
      limits.ensure_transport(b"ok", &claim, b"ok", &non_binary).is_err()
    );

    let mut non_constant = production_fri();
    non_constant.log_final_poly_len = 1;
    assert!(
      limits.ensure_transport(b"ok", &claim, b"ok", &non_constant).is_err()
    );

    let mut too_many_queries = production_fri();
    too_many_queries.num_queries = 1_025;
    assert!(
      limits.ensure_transport(b"ok", &claim, b"ok", &too_many_queries).is_err()
    );

    let mut invalid_pow = production_fri();
    invalid_pow.query_proof_of_work_bits = 64;
    assert!(
      limits.ensure_transport(b"ok", &claim, b"ok", &invalid_pow).is_err()
    );
  }

  #[test]
  fn resource_limits_are_strict_configurable_and_checked_at_boundaries() {
    let defaults = Stage3ResourceLimitsV1::default();
    assert_eq!(
      serde_json::from_str::<Stage3ResourceLimitsV1>("{}").unwrap(),
      defaults
    );
    let limits: Stage3ResourceLimitsV1 = serde_json::from_str(
      r#"{"max_table_capacity":1024,"max_union_witness_bytes":2048}"#,
    )
    .unwrap();
    assert!(limits.ensure_table_capacity(10).is_ok());
    assert!(limits.ensure_table_capacity(11).is_err());
    assert!(limits.ensure_table_capacity(64).is_err());
    assert!(limits.ensure_union_witness(2048).is_ok());
    assert!(limits.ensure_union_witness(2049).is_err());
    for json in [r#"{"max_witness_bytes":1}"#, r#"{"max_advice_bytes":-1}"#] {
      assert!(serde_json::from_str::<Stage3ResourceLimitsV1>(json).is_err());
    }
  }
}
