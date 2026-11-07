//! The security floor every Aiur verifying key must meet.
//!
//! The metric is the conjectured soundness of FRI's query phase under the
//! ethSTARK conjecture, `log_blowup · num_queries + query_proof_of_work_bits`
//! (plonky3's `FriParameters::conjectured_soundness_bits`). It is not the
//! end-to-end soundness of a proof: the degree-2 Goldilocks extension, the
//! instance's size and the commit phase bound that from above, and
//! `lake exe fri-security` computes every term. The floor is the level of the
//! parameters main shipped before formal Aiur (`log_blowup` 2, 100 queries,
//! 20 query proof-of-work bits), so no key may be configured weaker than
//! those; see `docs/stark-parameters.md`.
//!
//! The Lean mirror is `Aiur.minConjecturedSecurityBits` and
//! `Aiur.maxProofOfWorkBits` in `Ix/Aiur/Parameters.lean`; a test in the `aiur`
//! crate checks that they agree.

use multi_stark::types::{CommitmentParameters, FriParameters};

/// The least `log_blowup · num_queries + query_proof_of_work_bits` a key may
/// carry.
pub const MIN_CONJECTURED_BITS: usize = 220;

/// The most proof-of-work bits either grinding phase may require. Beyond
/// this a grind is impractical, so it must not stand in for queries.
pub const MAX_PROOF_OF_WORK_BITS: usize = 32;

/// The rates the Aiur adapter supports: a blowup of 2 to 16.
pub const LOG_BLOWUP_RANGE: std::ops::RangeInclusive<usize> = 1..=4;

/// Conjectured query-phase soundness in bits (the ethSTARK conjecture).
pub const fn conjectured_bits(
  commitment: &CommitmentParameters,
  fri: &FriParameters,
) -> usize {
  commitment
    .log_blowup
    .saturating_mul(fri.num_queries)
    .saturating_add(fri.query_proof_of_work_bits)
}

/// Reject parameters below the floor. Builders call this before they create
/// a key, and the codec calls it before it accepts one.
pub fn check(
  commitment: &CommitmentParameters,
  fri: &FriParameters,
) -> Result<(), String> {
  if !LOG_BLOWUP_RANGE.contains(&commitment.log_blowup) {
    return Err(format!(
      "log_blowup {} is outside {LOG_BLOWUP_RANGE:?}",
      commitment.log_blowup
    ));
  }
  if fri.num_queries == 0 {
    return Err("FRI needs at least one query".into());
  }
  for (phase, bits) in [
    ("commit", fri.commit_proof_of_work_bits),
    ("query", fri.query_proof_of_work_bits),
  ] {
    if bits > MAX_PROOF_OF_WORK_BITS {
      return Err(format!(
        "{phase} proof of work of {bits} bits exceeds {MAX_PROOF_OF_WORK_BITS}"
      ));
    }
  }
  let bits = conjectured_bits(commitment, fri);
  if bits < MIN_CONJECTURED_BITS {
    return Err(format!(
      "FRI parameters below the security floor: log_blowup {} x {} queries + \
       {} query proof-of-work bits = {bits} conjectured bits, at least \
       {MIN_CONJECTURED_BITS} required",
      commitment.log_blowup, fri.num_queries, fri.query_proof_of_work_bits
    ));
  }
  Ok(())
}

#[cfg(test)]
mod tests {
  use super::*;

  fn parameters(
    log_blowup: usize,
    num_queries: usize,
    commit_pow: usize,
    query_pow: usize,
  ) -> (CommitmentParameters, FriParameters) {
    (
      CommitmentParameters { log_blowup, cap_height: 0 },
      FriParameters {
        log_final_poly_len: 0,
        max_log_arity: 1,
        num_queries,
        commit_proof_of_work_bits: commit_pow,
        query_proof_of_work_bits: query_pow,
      },
    )
  }

  #[test]
  fn floor_admits_main_and_equivalent_parameters() {
    for (b, q, c, p) in [(2, 100, 0, 20), (1, 220, 0, 0), (3, 67, 0, 20)] {
      let (cp, fp) = parameters(b, q, c, p);
      assert!(conjectured_bits(&cp, &fp) >= MIN_CONJECTURED_BITS);
      check(&cp, &fp).unwrap();
    }
  }

  #[test]
  fn floor_rejects_weaker_or_degenerate_parameters() {
    for (b, q, c, p) in [
      (1, 64, 0, 0),  // #678's original default
      (2, 99, 0, 20), // one query short of main
      (2, 100, 0, 19),
      (0, 300, 0, 0),
      (5, 50, 0, 0),
      (2, 0, 0, 0),
      (4, 47, 0, 33), // proof of work standing in for queries
      (2, 100, 33, 20),
    ] {
      let (cp, fp) = parameters(b, q, c, p);
      assert!(check(&cp, &fp).is_err(), "accepted {b} {q} {c} {p}");
    }
  }
}
