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

/// Minimum provable unique-decoding (`CertiFRI`) query-phase soundness in bits.
/// Blocks high-blowup / low-query configurations such as `(4, 55, 0)` (50.2
/// bits UD) that pass the conjectured floor while falling well below provable
/// unique-decoding soundness.
pub const MIN_PROVABLE_UD_BITS: usize = 80;

/// Minimum Johnson (list-decoding) query-phase soundness in bits, evaluated
/// with finite-`m` (`m = JOHNSON_M`) proximity slack.
pub const MIN_JOHNSON_BITS: usize = 100;

/// Finite Johnson list-decoding parameter `m` used to account for the
/// per-query proximity slack `-log2(1 + 1/(2m))` (`Ix/Aiur/FriSecurity.lean`).
pub const JOHNSON_M: usize = 16;

/// Conservative integer upper bound on `1000 · log2(1 + 1/(2 · JOHNSON_M))`
/// (milli-bits lost per FRI query relative to the asymptotic `m -> inf` rate).
pub const JOHNSON_SLACK_MILLIBITS_PER_QUERY: usize = 45; // 1000 * log2(33/32) ≈ 44.394

/// The most proof-of-work bits either grinding phase may require. Beyond
/// this a grind is impractical, so it must not stand in for queries.
pub const MAX_PROOF_OF_WORK_BITS: usize = 32;

/// The rates the Aiur adapter supports: a blowup of 2 to 16.
pub const LOG_BLOWUP_RANGE: std::ops::RangeInclusive<usize> = 1..=4;

/// Conservative integer lower bound on `-1000 · log2((1 + 2^{-log_blowup}) / 2)`
/// (milli-bits of unique-decoding query soundness per FRI query).
/// Note: this is the large-domain rate; per-instance finite-domain CertiFRI
/// `+1` degree-slack (`2δ + ρ + 1/|D| <= 1`) is tracked in `Ix/Aiur/FriSecurity.lean`.
pub const fn ud_millibits_per_query(log_blowup: usize) -> Option<usize> {
  match log_blowup {
    1 => Some(415), // -log2(3/4)   ≈ 0.415037
    2 => Some(678), // -log2(5/8)   ≈ 0.678072
    3 => Some(830), // -log2(9/16)  ≈ 0.830075
    4 => Some(912), // -log2(17/32) ≈ 0.912537
    _ => None,
  }
}

/// Conservative integer lower bound on
/// `-1000 · log2((1 + 1/(2 · JOHNSON_M)) · 2^{-log_blowup / 2})`
/// (milli-bits of finite-`m` Johnson query soundness per FRI query).
pub const fn johnson_millibits_per_query(log_blowup: usize) -> Option<usize> {
  match log_blowup {
    1 => Some(455), // 500 - 45  (-log2((33/32) * 2^{-1/2}) ≈ 0.455606)
    2 => Some(955), // 1000 - 45 (-log2((33/32) * 2^{-1})   ≈ 0.955606)
    3 => Some(1455), // 1500 - 45 (-log2((33/32) * 2^{-3/2}) ≈ 1.455606)
    4 => Some(1955), // 2000 - 45 (-log2((33/32) * 2^{-2})   ≈ 1.955606)
    _ => None,
  }
}

/// Explicit per-`log_blowup` minimum FRI query count guaranteeing that
/// `MIN_PROVABLE_UD_BITS` is attainable with at most `MAX_PROOF_OF_WORK_BITS`
/// query grinding bits (`ceil((80 - 32) / ud_rate(log_blowup))`).
pub const fn min_queries_for_log_blowup(log_blowup: usize) -> Option<usize> {
  match log_blowup {
    1 => Some(116),
    2 => Some(71),
    3 => Some(58),
    4 => Some(53),
    _ => None,
  }
}

/// Provable unique-decoding query-phase soundness in milli-bits:
/// `1000 · query_pow + ud_millibits_per_query(log_blowup) · num_queries`.
pub const fn provable_ud_millibits(
  commitment: &CommitmentParameters,
  fri: &FriParameters,
) -> Option<usize> {
  let Some(rate) = ud_millibits_per_query(commitment.log_blowup) else {
    return None;
  };
  Some(
    fri
      .num_queries
      .saturating_mul(rate)
      .saturating_add(fri.query_proof_of_work_bits.saturating_mul(1000)),
  )
}

/// Finite-`m` (`m = JOHNSON_M`) Johnson-bound query-phase soundness in milli-bits:
/// `1000 · query_pow + (500 · log_blowup - JOHNSON_SLACK_MILLIBITS_PER_QUERY) · num_queries`.
pub const fn johnson_millibits(
  commitment: &CommitmentParameters,
  fri: &FriParameters,
) -> usize {
  let rate = commitment
    .log_blowup
    .saturating_mul(500)
    .saturating_sub(JOHNSON_SLACK_MILLIBITS_PER_QUERY);
  fri
    .num_queries
    .saturating_mul(rate)
    .saturating_add(fri.query_proof_of_work_bits.saturating_mul(1000))
}

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
  if commitment.cap_height != 0 {
    return Err(format!(
      "unsupported cap_height {}: expected 0",
      commitment.cap_height
    ));
  }
  if fri.log_final_poly_len != 0 {
    return Err(format!(
      "unsupported log_final_poly_len {}: expected 0",
      fri.log_final_poly_len
    ));
  }
  if fri.max_log_arity != 1 {
    return Err(format!(
      "unsupported max_log_arity {}: expected 1",
      fri.max_log_arity
    ));
  }
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
  let min_q =
    min_queries_for_log_blowup(commitment.log_blowup).ok_or_else(|| {
      format!("unsupported log_blowup {}", commitment.log_blowup)
    })?;
  if fri.num_queries < min_q {
    return Err(format!(
      "FRI parameters below the query floor for log_blowup {}: {} queries < minimum {min_q}",
      commitment.log_blowup, fri.num_queries
    ));
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
  let ud_mb = provable_ud_millibits(commitment, fri).ok_or_else(|| {
    format!("unsupported log_blowup {}", commitment.log_blowup)
  })?;
  if ud_mb < MIN_PROVABLE_UD_BITS * 1000 {
    return Err(format!(
      "FRI parameters below the provable unique-decoding security floor: \
       log_blowup {}, {} queries, {} query PoW gives {}.{:03} UD bits, \
       at least {MIN_PROVABLE_UD_BITS}.000 required",
      commitment.log_blowup,
      fri.num_queries,
      fri.query_proof_of_work_bits,
      ud_mb / 1000,
      ud_mb % 1000
    ));
  }
  let johnson_mb = johnson_millibits(commitment, fri);
  if johnson_mb < MIN_JOHNSON_BITS * 1000 {
    return Err(format!(
      "FRI parameters below the Johnson security floor: \
       log_blowup {}, {} queries, {} query PoW gives {}.{:03} Johnson bits, \
       at least {MIN_JOHNSON_BITS}.000 required",
      commitment.log_blowup,
      fri.num_queries,
      fri.query_proof_of_work_bits,
      johnson_mb / 1000,
      johnson_mb % 1000
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
    for (b, q, c, p) in [
      (2, 100, 0, 20), // main default: 87.8 UD, 115.5 Johnson (m=16), 220 conj
      (1, 220, 0, 0),  // 91.3 UD, 100.1 Johnson (m=16), 220 conj
      (2, 118, 0, 0),  // 80.0 UD, 112.7 Johnson (m=16), 236 conj
      (3, 73, 0, 20),  // 80.6 UD, 126.2 Johnson (m=16), 239 conj
      (4, 66, 0, 20),  // 80.2 UD, 149.0 Johnson (m=16), 284 conj
      (4, 88, 0, 0),   // 80.3 UD, 172.0 Johnson (m=16), 352 conj
    ] {
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
      (2, 110, 0, 0), // 220 conjectured, but only 74.6 UD bits
      (3, 67, 0, 20), // 221 conjectured, but only 75.6 UD bits
      (4, 55, 0, 0),  // 220 conjectured, but only 50.2 UD bits (HIGH-8!)
      (4, 87, 0, 0),  // 79.3 UD bits (< 80)
      (4, 52, 0, 32), // below per-log_blowup query floor 53
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

  #[test]
  fn floor_rejects_unsupported_structural_parameters() {
    let (base_cp, base_fp) = parameters(2, 100, 0, 20);
    for cap_height in [1, 4, u16::MAX as usize] {
      let cp = CommitmentParameters { cap_height, ..base_cp };
      let err = check(&cp, &base_fp).expect_err("accepted nonzero cap_height");
      assert!(err.contains("cap_height"), "{err}");
    }
    for log_final_poly_len in [1, 4, u16::MAX as usize] {
      let fp = FriParameters { log_final_poly_len, ..base_fp };
      let err =
        check(&base_cp, &fp).expect_err("accepted nonzero log_final_poly_len");
      assert!(err.contains("log_final_poly_len"), "{err}");
    }
    for max_log_arity in [0, 2, 4, u16::MAX as usize] {
      let fp = FriParameters { max_log_arity, ..base_fp };
      let err =
        check(&base_cp, &fp).expect_err("accepted non-binary max_log_arity");
      assert!(err.contains("max_log_arity"), "{err}");
    }
  }

  #[test]
  fn finite_m_johnson_accounts_for_proximity_slack() {
    let johnson_m = f64::from(u32::try_from(JOHNSON_M).unwrap());
    let slack_const =
      f64::from(u32::try_from(JOHNSON_SLACK_MILLIBITS_PER_QUERY).unwrap());
    let slack = (1.0 + 0.5 / johnson_m).log2() * 1000.0;
    assert!(
      slack_const >= slack,
      "slack constant {JOHNSON_SLACK_MILLIBITS_PER_QUERY} must upper-bound {slack}"
    );
    for b in 1..=4usize {
      let b_i32 = i32::try_from(b).unwrap();
      let exact_ud = -((1.0 + 2f64.powi(-b_i32)) / 2.0).log2() * 1000.0;
      let ud_rate =
        f64::from(u32::try_from(ud_millibits_per_query(b).unwrap()).unwrap());
      assert!(ud_rate <= exact_ud && ud_rate + 1.0 >= exact_ud);

      let exact_j =
        -((1.0 + 0.5 / johnson_m) * 2f64.powf(-f64::from(b_i32) / 2.0)).log2()
          * 1000.0;
      let j_rate = f64::from(
        u32::try_from(johnson_millibits_per_query(b).unwrap()).unwrap(),
      );
      assert!(j_rate <= exact_j && j_rate + 1.0 >= exact_j);
    }
    assert_eq!(johnson_millibits_per_query(0), None);
    assert_eq!(johnson_millibits_per_query(5), None);

    // (1, 220, 0) clears 100b with finite-m slack (100.100b < asymptotic 110.0b);
    // (1, 219, 0) drops below 100b (99.645b).
    let (cp, fp) = parameters(1, 220, 0, 0);
    assert_eq!(johnson_millibits(&cp, &fp), 100_100);
    let (cp, fp) = parameters(1, 219, 0, 0);
    assert_eq!(johnson_millibits(&cp, &fp), 99_645);
    assert!(johnson_millibits(&cp, &fp) < MIN_JOHNSON_BITS * 1000);

    let (cp, fp) = parameters(2, 100, 0, 20);
    assert_eq!(johnson_millibits(&cp, &fp), 115_500);
  }
}
