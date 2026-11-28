//! The security floor every Aiur verifying key must meet (Protocol v6, Fp^3).
//!
//! Every production key must simultaneously satisfy:
//! - Conjectured ethSTARK query soundness >= `MIN_CONJECTURED_BITS` (220 bits),
//! - Provable unique-decoding (`CertiFRI`) query soundness >= `MIN_PROVABLE_UD_BITS` (80 bits),
//! - Finite-`m` (`m = JOHNSON_M = 16`) Johnson list-decoding query soundness >=
//!   `MIN_JOHNSON_BITS` (128 bits), enabled by the degree-3 cubic trinomial
//!   Goldilocks extension Fp^3 = Fp[X]/(X^3 - X - 1) (~192-bit field),
//! - Explicit per-`log_blowup` minimum query count and PoW cap <= 32 bits.
//!
//! The default Protocol v6 parameters (`log_blowup = 2, num_queries = 128,
//! query_proof_of_work_bits = 20`) give FRI query terms of 142.24 bits
//! finite-`m` Johnson, 106.78 bits UD, and 276 bits conjectured. These are
//! query terms only, not soundness levels (the weakest term decides; the
//! 32-byte digest alone caps the level at about 128 bits), and no
//! machine-checked theorem covers the tensor-batched v6 verifier.
//!
//! The Lean mirror lives in `Ix/Aiur/Parameters.lean`; a test in the `aiur`
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
/// with finite-`m` (`m = JOHNSON_M`) proximity slack (128-bit Protocol v6 Fp^3 floor).
pub const MIN_JOHNSON_BITS: usize = 128;

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

/// Extension field degree for the `v6` 128-bit security profile
/// (Goldilocks cubic extension `Fp^3`, `p^3 > 2^191`).
pub const EXTENSION_DEGREE_V6: usize = 3;

/// Protocol version tag for the `v6` `Fp^3` + BLAKE3 `derive_key` profile.
pub const PROTOCOL_VERSION_V6: usize = 6;

/// Target provable security floor (in bits) for the `v6` 128-bit profile
/// (both unique-decoding and finite-`m` Johnson list-decoding regimes).
pub const MIN_PROVABLE_SECURITY_BITS_128: usize = 128;

/// Digest width in bytes for the production 128-bit classical `BLAKE3-256`
/// profile (`32` bytes = 256 bits; `127.7` classical BCS collision bits,
/// `85.3` BHT quantum bits).
pub const DIGEST_BYTES_BLAKE3_256: usize = 32;

/// Digest width in bytes for the certified 128-bit post-quantum RFC 7693
/// `BLAKE2b-512` profile (`64` bytes = 512 bits, true 512-bit internal state,
/// 128-byte block = single-block 2-to-1 Merkle compression; `255.7` classical
/// BCS collision bits, `170.7` BHT quantum bits, `204.8` CNS bits, `256` Grover bits).
pub const DIGEST_BYTES_BLAKE2B512: usize = 64;

/// Legacy 48-byte (384-bit) BLAKE3 XOF digest width constant, retained solely
/// for `Ix/Aiur/Parameters.lean` mirror test compatibility.
///
/// **Retired for concrete 128-bit post-quantum security:** BLAKE3's 256-bit
/// internal chaining value (`cv`) caps concrete collision resistance at `128`
/// classical / `85.3` BHT quantum bits on every `> 64`-byte input regardless
/// of XOF output length. Use `DIGEST_BYTES_BLAKE2B512` (64 bytes, RFC 7693
/// `BLAKE2b-512`) for concrete 128-bit post-quantum security.
pub const DIGEST_BYTES_XOF48: usize = 48;

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

/// Explicit per-`log_blowup` minimum FRI query count guaranteeing that both
/// `MIN_JOHNSON_BITS` (128) and `MIN_PROVABLE_UD_BITS` (80) are attainable
/// with at most `MAX_PROOF_OF_WORK_BITS` (32) query grinding bits.
pub const fn min_queries_for_log_blowup(log_blowup: usize) -> Option<usize> {
  match log_blowup {
    1 => Some(211), // ceil((128 - 32) / 0.455) = 211
    2 => Some(101), // ceil((128 - 32) / 0.955) = 101
    3 => Some(66),  // ceil((128 - 32) / 1.455) = 66
    4 => Some(53),  // ceil((80 - 32) / 0.912) = 53 (Johnson needs 50)
    _ => None,
  }
}

/// Explicit per-`log_blowup` minimum FRI query count guaranteeing that
/// `MIN_PROVABLE_SECURITY_BITS_128` unique-decoding query soundness is
/// attainable with at most `MAX_PROOF_OF_WORK_BITS` query grinding bits
/// (`ceil((128 - 32) * 1000 / ud_millibits_per_query(log_blowup))`).
pub const fn min_queries_for_log_blowup_128_ud(
  log_blowup: usize,
) -> Option<usize> {
  match log_blowup {
    1 => Some(232),
    2 => Some(142),
    3 => Some(116),
    4 => Some(106),
    _ => None,
  }
}

/// Explicit per-`log_blowup` minimum FRI query count guaranteeing that both
/// `MIN_PROVABLE_SECURITY_BITS_128` finite-`m` (`m = 16`) Johnson soundness
/// and `MIN_PROVABLE_UD_BITS` unique-decoding soundness are attainable with at
/// most `MAX_PROOF_OF_WORK_BITS` query grinding bits.
pub const fn min_queries_for_log_blowup_128_johnson(
  log_blowup: usize,
) -> Option<usize> {
  match log_blowup {
    1 => Some(211),
    2 => Some(101),
    3 => Some(66),
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

/// The FRI shapes a floor check admits besides the query-phase numbers:
/// folding arity up to `2^max_log_arity` and a final polynomial of up to
/// `2^max_log_final_poly_len` coefficients. Every shape requires
/// `cap_height = 0` (single-root commitments), whatever the limits.
///
/// The numeric floors of [`check_with_shape`] count FRI query-phase bits
/// only; they read `log_blowup`, `num_queries` and `query_proof_of_work_bits`
/// and do not depend on the arity or the final-polynomial length. No term
/// for the commit-phase cost of folding by more than two is counted, and no
/// machine-checked theorem covers a shape other than [`ShapeLimits::BINARY`]
/// (`CertiFRI`'s verifier folds by two only).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ShapeLimits {
  pub max_log_arity: usize,
  pub max_log_final_poly_len: usize,
}

impl ShapeLimits {
  /// Binary folding, constant final polynomial: the only shape [`check`]
  /// admits, and the one `CertiFRI`'s verifier models.
  pub const BINARY: Self = Self { max_log_arity: 1, max_log_final_poly_len: 0 };
}

/// Reject parameters below the floor. Builders call this before they create
/// a key, and the codec calls it before it accepts one. Admits only
/// [`ShapeLimits::BINARY`] with `cap_height = 0`.
pub fn check(
  commitment: &CommitmentParameters,
  fri: &FriParameters,
) -> Result<(), String> {
  check_with_shape(commitment, fri, ShapeLimits::BINARY)
}

/// [`check`] for a caller that admits the FRI shapes of `shape`: the
/// structural limits and the numeric floors are evaluated on the real
/// parameter values, never on substitutes. `cap_height` must be 0.
pub fn check_with_shape(
  commitment: &CommitmentParameters,
  fri: &FriParameters,
  shape: ShapeLimits,
) -> Result<(), String> {
  if commitment.cap_height != 0 {
    return Err(format!(
      "unsupported cap_height {}: expected 0",
      commitment.cap_height
    ));
  }
  if fri.log_final_poly_len > shape.max_log_final_poly_len {
    return Err(if shape.max_log_final_poly_len == 0 {
      format!(
        "unsupported log_final_poly_len {}: expected 0",
        fri.log_final_poly_len
      )
    } else {
      format!(
        "unsupported log_final_poly_len {}: expected at most {}",
        fri.log_final_poly_len, shape.max_log_final_poly_len
      )
    });
  }
  if !(1..=shape.max_log_arity).contains(&fri.max_log_arity) {
    return Err(if shape.max_log_arity == 1 {
      format!("unsupported max_log_arity {}: expected 1", fri.max_log_arity)
    } else {
      format!(
        "unsupported max_log_arity {}: expected 1..={}",
        fri.max_log_arity, shape.max_log_arity
      )
    });
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

/// Reject parameters below the `v6` 128-bit provable unique-decoding security
/// profile (`Fp^3`, protocol version `>= 6`, `>= 128.000` UD query bits).
pub fn check_128_ud(
  extension_degree: usize,
  protocol_version: usize,
  commitment: &CommitmentParameters,
  fri: &FriParameters,
) -> Result<(), String> {
  if extension_degree < EXTENSION_DEGREE_V6 {
    return Err(format!(
      "extension_degree {extension_degree} below 128-bit v6 floor \
       {EXTENSION_DEGREE_V6} (Goldilocks Fp^2 has < 128 bits of field entropy)"
    ));
  }
  if protocol_version < PROTOCOL_VERSION_V6 {
    return Err(format!(
      "protocol_version {protocol_version} below 128-bit v6 floor \
       {PROTOCOL_VERSION_V6}"
    ));
  }
  check(commitment, fri)?;
  let min_q = min_queries_for_log_blowup_128_ud(commitment.log_blowup)
    .ok_or_else(|| {
      format!("unsupported log_blowup {}", commitment.log_blowup)
    })?;
  if fri.num_queries < min_q {
    return Err(format!(
      "FRI parameters below the 128-bit UD query floor for log_blowup {}: \
       {} queries < minimum {min_q}",
      commitment.log_blowup, fri.num_queries
    ));
  }
  let ud_mb = provable_ud_millibits(commitment, fri).ok_or_else(|| {
    format!("unsupported log_blowup {}", commitment.log_blowup)
  })?;
  if ud_mb < MIN_PROVABLE_SECURITY_BITS_128 * 1000 {
    return Err(format!(
      "FRI parameters below the 128-bit provable unique-decoding floor: \
       log_blowup {}, {} queries, {} query PoW gives {}.{:03} UD bits, \
       at least {MIN_PROVABLE_SECURITY_BITS_128}.000 required",
      commitment.log_blowup,
      fri.num_queries,
      fri.query_proof_of_work_bits,
      ud_mb / 1000,
      ud_mb % 1000
    ));
  }
  Ok(())
}

/// Reject parameters below the `v6` 128-bit finite-`m` Johnson list-decoding
/// security profile (`Fp^3`, protocol version `>= 6`, `>= 128.000` Johnson
/// query bits and `>= 80.000` UD query bits).
pub fn check_128_johnson(
  extension_degree: usize,
  protocol_version: usize,
  commitment: &CommitmentParameters,
  fri: &FriParameters,
) -> Result<(), String> {
  if extension_degree < EXTENSION_DEGREE_V6 {
    return Err(format!(
      "extension_degree {extension_degree} below 128-bit v6 floor \
       {EXTENSION_DEGREE_V6} (Goldilocks Fp^2 has < 128 bits of field entropy)"
    ));
  }
  if protocol_version < PROTOCOL_VERSION_V6 {
    return Err(format!(
      "protocol_version {protocol_version} below 128-bit v6 floor \
       {PROTOCOL_VERSION_V6}"
    ));
  }
  check(commitment, fri)?;
  let min_q = min_queries_for_log_blowup_128_johnson(commitment.log_blowup)
    .ok_or_else(|| {
      format!("unsupported log_blowup {}", commitment.log_blowup)
    })?;
  if fri.num_queries < min_q {
    return Err(format!(
      "FRI parameters below the 128-bit Johnson query floor for \
       log_blowup {}: {} queries < minimum {min_q}",
      commitment.log_blowup, fri.num_queries
    ));
  }
  let johnson_mb = johnson_millibits(commitment, fri);
  if johnson_mb < MIN_PROVABLE_SECURITY_BITS_128 * 1000 {
    return Err(format!(
      "FRI parameters below the 128-bit Johnson security floor: \
       log_blowup {}, {} queries, {} query PoW gives {}.{:03} Johnson bits, \
       at least {MIN_PROVABLE_SECURITY_BITS_128}.000 required",
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
      (2, 128, 0, 20), // Protocol v6 default: 106.8 UD, 142.2 Johnson (m=16), 276 conj
      (1, 282, 0, 0),  // 117.0 UD, 128.3 Johnson (m=16), 282 conj
      (1, 238, 0, 20), // 118.8 UD, 128.3 Johnson (m=16), 258 conj
      (2, 135, 0, 0),  // 91.5 UD, 128.9 Johnson (m=16), 270 conj
      (2, 114, 0, 20), // 97.3 UD, 128.9 Johnson (m=16), 248 conj
      (3, 78, 0, 20), // 84.7 UD, 133.5 Johnson (m=16), 254 conj (shrinker --stark-128)
      (4, 66, 0, 20), // 80.2 UD, 149.0 Johnson (m=16), 284 conj
      (4, 88, 0, 0),  // 80.3 UD, 172.0 Johnson (m=16), 352 conj
    ] {
      let (cp, fp) = parameters(b, q, c, p);
      assert!(conjectured_bits(&cp, &fp) >= MIN_CONJECTURED_BITS);
      check(&cp, &fp).unwrap();
    }
  }

  #[test]
  fn floor_rejects_weaker_or_degenerate_parameters() {
    for (b, q, c, p) in [
      (1, 64, 0, 0),   // #678's original default
      (2, 100, 0, 20), // retired v5 default: only 115.5 Johnson (< 128)
      (2, 113, 0, 20), // 127.9 Johnson (< 128)
      (2, 118, 0, 0),  // 112.7 Johnson (< 128)
      (3, 74, 0, 20),  // 127.7 Johnson (< 128)
      (4, 58, 0, 20),  // 133.4 Johnson, but only 72.9 UD (< 80)
      (4, 55, 0, 0),   // 220 conjectured, but only 50.2 UD bits
      (4, 87, 0, 0),   // 79.3 UD bits (< 80)
      (4, 52, 0, 32),  // below per-log_blowup query floor 53
      (0, 300, 0, 0),
      (5, 50, 0, 0),
      (2, 0, 0, 0),
      (4, 47, 0, 33), // proof of work standing in for queries
      (2, 128, 33, 20),
    ] {
      let (cp, fp) = parameters(b, q, c, p);
      assert!(check(&cp, &fp).is_err(), "accepted {b} {q} {c} {p}");
    }
  }

  #[test]
  fn floor_rejects_unsupported_structural_parameters() {
    let (base_cp, base_fp) = parameters(2, 128, 0, 20);
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

  /// `check_with_shape` evaluates the shape on the real values: it admits the
  /// declared arity and final-polynomial limits, still requires a single
  /// root, and applies the same numeric floors as `check`.
  #[test]
  fn shape_limits_are_checked_on_real_values() {
    let wide = ShapeLimits { max_log_arity: 3, max_log_final_poly_len: 8 };
    let (cp, fp) = parameters(4, 58, 0, 28);
    let shaped =
      FriParameters { max_log_arity: 3, log_final_poly_len: 8, ..fp };
    check_with_shape(&cp, &shaped, wide).unwrap();
    // `check` is `check_with_shape(.., BINARY)` and still refuses the shape.
    assert!(check(&cp, &shaped).is_err());
    check_with_shape(&cp, &fp, ShapeLimits::BINARY).unwrap();
    // A single root is required at every shape.
    for cap_height in [1, 4, 12] {
      let capped = CommitmentParameters { cap_height, ..cp };
      let err = check_with_shape(&capped, &shaped, wide).unwrap_err();
      assert!(err.contains("cap_height"), "{err}");
    }
    // Arity and final length beyond the limits, and arity 0, are refused.
    for (mla, lfp, needle) in [
      (4, 8, "max_log_arity"),
      (0, 8, "max_log_arity"),
      (3, 9, "log_final_poly_len"),
      (3, 12, "log_final_poly_len"),
    ] {
      let bad =
        FriParameters { max_log_arity: mla, log_final_poly_len: lfp, ..fp };
      let err = check_with_shape(&cp, &bad, wide).unwrap_err();
      assert!(err.contains(needle), "{err}");
    }
    // The numeric floors are unchanged by the shape.
    for (b, q, c, p) in [(4, 58, 0, 20), (4, 52, 0, 32), (3, 74, 0, 20)] {
      let (cp, fp) = parameters(b, q, c, p);
      let shaped =
        FriParameters { max_log_arity: 3, log_final_poly_len: 8, ..fp };
      assert!(
        check_with_shape(&cp, &shaped, wide).is_err(),
        "accepted {b} {q} {c} {p}"
      );
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

    // (2, 114, 0, 20) clears 128b (128.870b); (2, 113, 0, 20) drops below 128b (127.915b).
    let (cp, fp) = parameters(2, 114, 0, 20);
    assert_eq!(johnson_millibits(&cp, &fp), 128_870);
    let (cp, fp) = parameters(2, 113, 0, 20);
    assert_eq!(johnson_millibits(&cp, &fp), 127_915);
    assert!(johnson_millibits(&cp, &fp) < MIN_JOHNSON_BITS * 1000);

    // Protocol v6 default (2, 128, 0, 20): 142.240b finite-m Johnson (+14.24b headroom).
    let (cp, fp) = parameters(2, 128, 0, 20);
    assert_eq!(johnson_millibits(&cp, &fp), 142_240);
  }

  #[test]
  fn v6_128bit_profile_admits_valid_and_rejects_weak_params() {
    // Valid 128-bit UD profiles (also satisfy 128-bit Johnson).
    for (b, q, c, p) in [
      (2, 160, 0, 20), // 128.480 UD, 172.800 Johnson
      (1, 261, 0, 20), // 128.315 UD, 138.755 Johnson
      (3, 131, 0, 20), // 128.730 UD, 210.605 Johnson
      (4, 119, 0, 20), // 128.528 UD, 252.645 Johnson
    ] {
      let (cp, fp) = parameters(b, q, c, p);
      check_128_ud(EXTENSION_DEGREE_V6, PROTOCOL_VERSION_V6, &cp, &fp).unwrap();
      check_128_johnson(EXTENSION_DEGREE_V6, PROTOCOL_VERSION_V6, &cp, &fp)
        .unwrap();
    }

    // Valid 128-bit Johnson profiles below 128-bit UD.
    for (b, q, c, p) in [
      (2, 118, 0, 20), // 100.004 UD, 132.690 Johnson
      (2, 128, 0, 20), // 106.784 UD, 142.240 Johnson
      (3, 78, 0, 20),  // 84.740 UD, 133.490 Johnson
      (4, 66, 0, 20),  // 80.192 UD, 149.030 Johnson
    ] {
      let (cp, fp) = parameters(b, q, c, p);
      assert!(
        check_128_ud(EXTENSION_DEGREE_V6, PROTOCOL_VERSION_V6, &cp, &fp)
          .is_err(),
        "expected UD rejection for ({b}, {q}, {c}, {p})"
      );
      check_128_johnson(EXTENSION_DEGREE_V6, PROTOCOL_VERSION_V6, &cp, &fp)
        .unwrap();
    }

    // Rejects Fp2 and v5 protocol version even with strong FRI params.
    let (cp_strong, fp_strong) = parameters(2, 160, 0, 20);
    assert!(
      check_128_ud(2, PROTOCOL_VERSION_V6, &cp_strong, &fp_strong)
        .unwrap_err()
        .contains("extension_degree")
    );
    assert!(
      check_128_johnson(2, PROTOCOL_VERSION_V6, &cp_strong, &fp_strong)
        .unwrap_err()
        .contains("extension_degree")
    );
    assert!(
      check_128_ud(EXTENSION_DEGREE_V6, 5, &cp_strong, &fp_strong)
        .unwrap_err()
        .contains("protocol_version")
    );
    assert!(
      check_128_johnson(EXTENSION_DEGREE_V6, 5, &cp_strong, &fp_strong)
        .unwrap_err()
        .contains("protocol_version")
    );

    // Rejects v5 default (2, 100, 0, 20) and deceptive (4, 55, 0, 0).
    for (b, q, c, p) in [
      (2, 100, 0, 20),
      (2, 113, 0, 20), // 127.915 Johnson (< 128)
      (4, 55, 0, 0),   // 50.160 UD, 107.525 Johnson
      (4, 65, 0, 20),  // 79.280 UD (< 80)
      (2, 159, 0, 20), // 127.802 UD (rejected by UD, admitted by Johnson)
    ] {
      let (cp, fp) = parameters(b, q, c, p);
      assert!(
        check_128_ud(EXTENSION_DEGREE_V6, PROTOCOL_VERSION_V6, &cp, &fp)
          .is_err(),
        "UD accepted ({b}, {q}, {c}, {p})"
      );
      if (b, q, c, p) != (2, 159, 0, 20) {
        assert!(
          check_128_johnson(EXTENSION_DEGREE_V6, PROTOCOL_VERSION_V6, &cp, &fp)
            .is_err(),
          "Johnson accepted ({b}, {q}, {c}, {p})"
        );
      }
    }
  }

  #[test]
  fn digest_width_constants_match_classical_and_pq_profiles() {
    assert_eq!(DIGEST_BYTES_BLAKE3_256, 32);
    assert_eq!(DIGEST_BYTES_BLAKE2B512, 64);
    const {
      assert!(DIGEST_BYTES_BLAKE2B512 > DIGEST_BYTES_XOF48);
      assert!(DIGEST_BYTES_XOF48 > DIGEST_BYTES_BLAKE3_256);
    }
  }
}
