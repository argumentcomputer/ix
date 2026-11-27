//! Zero-panic Lean FFI bridge for Endpoint 1 native `Fp^3` STARK shrinking
//! (`--stark-128` transparent `v6` and `--stark-128-zk` hiding `v6-zk`).

use aiur::trace::stark::{
  BatchProof as AiurBatchProof, VerifyingKey as AiurVerifyingKey,
};
use ix_proof_compression::pipeline::FixedRoot;
use lean_ffi::object::{
  LeanBorrowed, LeanByteArray, LeanIOResult, LeanOwned, LeanString,
};
use stark_shrinker::{
  COMPACT_PARAMS, CompiledVerifier, DEFAULT_PARAMS, MAX_PLONKISH_HOPS,
  OuterFriParams, PlonkishCircuitVerifier, PlonkishOptions, StarkShrinker,
  decode_single_claim_bytes,
  envelope::ShrinkMode,
  hash_publics, peek_plonkish_header,
  plonkish::{ENDPOINT1_PROFILES, admitted_profile},
  shrink_fixed_root, verify_v1_pinned,
};
use std::path::Path;

fn parse_digest32(
  label: &str,
  bytes: &LeanByteArray<LeanBorrowed<'_>>,
) -> Result<[u8; 32], String> {
  let slice = bytes.as_bytes();
  slice.try_into().map_err(|err| {
    format!("{label} must be exactly 32 bytes (got {}): {err}", slice.len())
  })
}

fn load_pinned_verifier(
  verifier_artifact: &LeanString<LeanBorrowed<'_>>,
  expected_artifact_digest: &LeanByteArray<LeanBorrowed<'_>>,
) -> Result<CompiledVerifier, String> {
  let expected = parse_digest32(
    "expected verifier artifact digest",
    expected_artifact_digest,
  )?;
  let path = verifier_artifact.to_string();
  let compiled = CompiledVerifier::from_package_path(Path::new(&path))?;
  if compiled.artifact_digest() != &expected {
    return Err(format!(
      "verifier artifact digest mismatch: pinned {} != loaded {}",
      blake3::Hash::from_bytes(expected).to_hex(),
      blake3::Hash::from_bytes(*compiled.artifact_digest()).to_hex()
    ));
  }
  Ok(compiled)
}

/// Shrink an inner Protocol `v6` proof (e.g., an `IXAGGR2` aggregate root) into
/// a self-verified `IXSTARK6\0` envelope using `--stark-128` (`is_zk = false`)
/// or `--stark-128-zk` (`is_zk = true`).
///
/// Logs the honest trust/ZK metadata banner to stderr and returns the canonical
/// `IXSTARK6\0` envelope bytes.
#[unsafe(no_mangle)]
extern "C" fn rs_stark_shrinker_shrink(
  verifier_artifact: LeanString<LeanBorrowed<'_>>,
  expected_artifact_digest: LeanByteArray<LeanBorrowed<'_>>,
  inner_vk: LeanByteArray<LeanBorrowed<'_>>,
  inner_claims: LeanByteArray<LeanBorrowed<'_>>,
  inner_proof: LeanByteArray<LeanBorrowed<'_>>,
  is_zk: bool,
  compact: bool,
  has_device: bool,
  device: u32,
) -> LeanIOResult<LeanOwned> {
  let result = (|| -> Result<Vec<u8>, String> {
    let compiled =
      load_pinned_verifier(&verifier_artifact, &expected_artifact_digest)?;
    let device = if has_device {
      let d = i32::try_from(device).map_err(|err| {
        format!("GPU device index {device} exceeds i32::MAX: {err}")
      })?;
      Some(d)
    } else {
      None
    };
    let mode =
      if is_zk { ShrinkMode::Stark128Zk } else { ShrinkMode::Stark128 };
    let params = if compact { COMPACT_PARAMS } else { DEFAULT_PARAMS };
    let plan = compiled.trace_plan()?;
    let shrinker = StarkShrinker::new(&compiled, &plan, mode, params, device)?;
    let output = shrinker.shrink(
      inner_vk.as_bytes(),
      inner_claims.as_bytes(),
      inner_proof.as_bytes(),
    )?;
    eprintln!("{}", output.report.banner());
    Ok(output.envelope_bytes)
  })();
  match result {
    Ok(bytes) => LeanIOResult::ok(LeanByteArray::from_bytes(bytes.as_slice())),
    Err(err) => LeanIOResult::error_string(&err),
  }
}

/// Independently verify an `IXSTARK6\0` shrunk proof envelope against the
/// pinned `MultiStark::verify_multi_stark_proof` artifact, `expected_inner_vk_digest`,
/// and `expected_claim_digest`, returning the formatted honest trust & ZK banner.
#[unsafe(no_mangle)]
extern "C" fn rs_stark_shrinker_verify(
  verifier_artifact: LeanString<LeanBorrowed<'_>>,
  expected_artifact_digest: LeanByteArray<LeanBorrowed<'_>>,
  envelope: LeanByteArray<LeanBorrowed<'_>>,
  expected_inner_vk_digest: LeanByteArray<LeanBorrowed<'_>>,
  expected_claim_digest: LeanByteArray<LeanBorrowed<'_>>,
) -> LeanIOResult<LeanOwned> {
  let result = (|| -> Result<String, String> {
    let envelope_bytes = envelope.as_bytes();
    let expected_inner =
      parse_digest32("expected inner VK digest", &expected_inner_vk_digest)?;
    let expected_claim =
      parse_digest32("expected claim digest", &expected_claim_digest)?;
    let compiled =
      load_pinned_verifier(&verifier_artifact, &expected_artifact_digest)?;
    // Mode and parameters must be a shipped v1 profile; the backend is built
    // from that constant, not from the envelope.
    let report = verify_v1_pinned(
      &compiled,
      envelope_bytes,
      &expected_inner,
      &expected_claim,
    )?;
    Ok(report.banner())
  })();
  match result {
    Ok(banner) => LeanIOResult::ok(LeanString::new(&banner)),
    Err(err) => LeanIOResult::error_string(&err),
  }
}

const fn fixed_root_params(compact: bool) -> OuterFriParams {
  if compact {
    OuterFriParams::ULTRA_COMPACT_400KB_ZK
  } else {
    OuterFriParams::COMPACT_400KB_BALANCED
  }
}

fn shrink_fixed_root_with_params(
  inner_vk_bytes: &[u8],
  layout_bytes: &[u8],
  inner_proof_bytes: &[u8],
  expected_claim_bytes: &[u8],
  is_zk: bool,
  params: OuterFriParams,
  device: Option<i32>,
) -> Result<(Vec<u8>, String), String> {
  let inner_key = AiurVerifyingKey::from_bytes(inner_vk_bytes)
    .map_err(|e| format!("inner verifying key rejected: {e}"))?;
  let layout = FixedRoot::from_bytes(layout_bytes)
    .map_err(|e| format!("fixed root layout rejected: {e}"))?;
  let inner_proof = AiurBatchProof::from_bytes(inner_proof_bytes)
    .map_err(|e| format!("normalized root proof decode failed: {e}"))?;
  let canonical = inner_proof
    .to_bytes()
    .map_err(|e| format!("normalized root proof re-encode failed: {e}"))?;
  if canonical != inner_proof_bytes {
    return Err("noncanonical or trailing normalized root proof bytes".into());
  }
  let claim_vals = decode_single_claim_bytes(expected_claim_bytes)?;
  let mode = if is_zk { ShrinkMode::Stark128Zk } else { ShrinkMode::Stark128 };
  let (output, _verifier) = shrink_fixed_root(
    &inner_key,
    &layout,
    &inner_proof,
    &claim_vals,
    mode,
    params,
    PlonkishOptions::default(),
    device,
  )?;
  Ok((output.envelope_bytes, output.report.banner()))
}

/// Verify an Endpoint 1 v2 envelope as `ix verify` does: the outer FRI
/// parameters and mode come from [`ENDPOINT1_PROFILES`], the verifier's
/// constants, never from the envelope.
fn verify_fixed_root_bytes(
  inner_vk_bytes: &[u8],
  layout_bytes: &[u8],
  envelope_bytes: &[u8],
  expected_claim_bytes: &[u8],
) -> Result<String, String> {
  verify_fixed_root_bytes_admitting(
    inner_vk_bytes,
    layout_bytes,
    envelope_bytes,
    expected_claim_bytes,
    &ENDPOINT1_PROFILES,
  )
}

/// [`verify_fixed_root_bytes`] under an explicit list of admitted
/// `(mode, params)` profiles: the verifier is derived from the admitted
/// constant equal to the header; any other header is rejected first.
fn verify_fixed_root_bytes_admitting(
  inner_vk_bytes: &[u8],
  layout_bytes: &[u8],
  envelope_bytes: &[u8],
  expected_claim_bytes: &[u8],
  admitted: &[(ShrinkMode, OuterFriParams)],
) -> Result<String, String> {
  let header = peek_plonkish_header(envelope_bytes)?;
  let (mode, params) = admitted_profile(&header, admitted)?;
  if !(1..=MAX_PLONKISH_HOPS).contains(&header.hops) {
    return Err(format!(
      "FixedRoot Plonkish verifier expects 1..={MAX_PLONKISH_HOPS} hops (got {} hops)",
      header.hops
    ));
  }
  if !header.compact_encoding {
    return Err(
      "FixedRoot Plonkish verifier expects compact-v1 payload encoding".into(),
    );
  }
  let inner_key = AiurVerifyingKey::from_bytes(inner_vk_bytes)
    .map_err(|e| format!("inner verifying key rejected: {e}"))?;
  let layout = FixedRoot::from_bytes(layout_bytes)
    .map_err(|e| format!("fixed root layout rejected: {e}"))?;
  let claim_vals = decode_single_claim_bytes(expected_claim_bytes)?;
  let expected_inner_vk = layout.identity(&inner_key);
  let expected_claim = hash_publics(&claim_vals);
  let verifier = PlonkishCircuitVerifier::derive_fixed_root(
    &inner_key,
    &layout,
    mode,
    params,
    PlonkishOptions::default(),
  )?;
  if verifier.num_outer_circuits() != 1 {
    return Err(format!(
      "Endpoint 1 outer system must be one circuit (derived {})",
      verifier.num_outer_circuits()
    ));
  }
  let report = verifier.verify_report(
    envelope_bytes,
    &claim_vals,
    &expected_inner_vk,
    &expected_claim,
  )?;
  Ok(report.banner())
}

/// Shrink a normalized `FixedRoot` Protocol `v6` aggregate root into a compact
/// `~400 KiB` 1-circuit Plonkish `IXSTARK6\0` v2 envelope using `--stark-128`
/// (`is_zk = false`) or `--stark-128-zk` (`is_zk = true`).
///
/// Uses `OuterFriParams::COMPACT_400KB_BALANCED` by default and
/// `OuterFriParams::ULTRA_COMPACT_400KB_ZK` when `compact = true`.
/// Logs the honest trust/ZK metadata banner to stderr and returns the canonical
/// `IXSTARK6\0` v2 envelope bytes.
#[unsafe(no_mangle)]
extern "C" fn rs_stark_shrinker_shrink_fixed_root(
  inner_vk: LeanByteArray<LeanBorrowed<'_>>,
  layout_bytes: LeanByteArray<LeanBorrowed<'_>>,
  inner_proof: LeanByteArray<LeanBorrowed<'_>>,
  expected_claim: LeanByteArray<LeanBorrowed<'_>>,
  is_zk: bool,
  compact: bool,
  has_device: bool,
  device: u32,
) -> LeanIOResult<LeanOwned> {
  let result = (|| -> Result<Vec<u8>, String> {
    let device = if has_device {
      let d = i32::try_from(device).map_err(|err| {
        format!("GPU device index {device} exceeds i32::MAX: {err}")
      })?;
      Some(d)
    } else {
      None
    };
    let (envelope_bytes, banner) = shrink_fixed_root_with_params(
      inner_vk.as_bytes(),
      layout_bytes.as_bytes(),
      inner_proof.as_bytes(),
      expected_claim.as_bytes(),
      is_zk,
      fixed_root_params(compact),
      device,
    )?;
    eprintln!("{banner}");
    Ok(envelope_bytes)
  })();
  match result {
    Ok(bytes) => LeanIOResult::ok(LeanByteArray::from_bytes(bytes.as_slice())),
    Err(err) => LeanIOResult::error_string(&err),
  }
}

/// Independently verify a compact 1-circuit Plonkish `IXSTARK6\0` v2 envelope
/// against the trusted aggregate `inner_vk`, release `FixedRoot` layout bytes,
/// and serialized `expected_claim` statement (no `.ixa` recursive verifier
/// artifact required), returning the formatted honest trust & ZK banner.
#[unsafe(no_mangle)]
extern "C" fn rs_stark_shrinker_verify_fixed_root(
  inner_vk: LeanByteArray<LeanBorrowed<'_>>,
  layout_bytes: LeanByteArray<LeanBorrowed<'_>>,
  envelope: LeanByteArray<LeanBorrowed<'_>>,
  expected_claim: LeanByteArray<LeanBorrowed<'_>>,
) -> LeanIOResult<LeanOwned> {
  let result = verify_fixed_root_bytes(
    inner_vk.as_bytes(),
    layout_bytes.as_bytes(),
    envelope.as_bytes(),
    expected_claim.as_bytes(),
  );
  match result {
    Ok(banner) => LeanIOResult::ok(LeanString::new(&banner)),
    Err(err) => LeanIOResult::error_string(&err),
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use aiur::trace::stark::MEMSEG;
  use multi_stark::{
    batch::{BatchMessage, ShardInput},
    expr::Expr,
    lookup::Lookup,
    p3_field::PrimeCharacteristicRing,
    p3_matrix::dense::RowMajorMatrix,
    system::{CircuitInputs, System, SystemWitness},
    types::{
      CommitmentParameters, FriParameters, GoldilocksBlake3V6Config, Val,
    },
  };

  fn fixed_root_fixture_bytes() -> (Vec<u8>, Vec<u8>, Vec<u8>, Vec<u8>) {
    let cp = CommitmentParameters { log_blowup: 4, cap_height: 0 };
    let fp = FriParameters {
      log_final_poly_len: 0,
      max_log_arity: 1,
      num_queries: 66,
      commit_proof_of_work_bits: 0,
      query_proof_of_work_bits: 20,
    };
    let channel = Val::from_u64(MEMSEG);
    let (system, pk) = System::new(
      GoldilocksBlake3V6Config::new(cp, fp),
      [(2usize, 4usize), (1, 2)].into_iter().map(|(width, height)| {
        CircuitInputs {
          main_width: width + 3,
          preprocessed: Some(RowMajorMatrix::new_col(vec![Val::ZERO; height])),
          lookups: vec![
            Lookup::pull(
              if width == 2 { Expr::main(2) } else { Val::ZERO.into() },
              vec![Expr::main(0), Expr::main(1)],
            ),
            Lookup::push(
              Expr::main(2),
              vec![
                channel.into(),
                Val::from_usize(width).into(),
                Val::ZERO.into(),
              ],
            ),
            Lookup::pull(
              Expr::main(2),
              vec![
                channel.into(),
                Val::from_usize(width).into(),
                Expr::main(3),
              ],
            ),
          ],
          ..Default::default()
        }
      }),
    );
    let vk_bytes = stark_key::to_bytes(&system, cp, fp);
    let layout = FixedRoot::new(vec![2, 1], vec![(1, 1), (2, 0)], 2).unwrap();
    let expected = vec![Val::from_u32(19), Val::from_u32(39)];
    let messages = [(1u32, 2u32), (2, 4)]
      .into_iter()
      .flat_map(|(width, end)| {
        [
          BatchMessage::pull(vec![channel, Val::from_u32(width), Val::ZERO]),
          BatchMessage::push(vec![
            channel,
            Val::from_u32(width),
            Val::from_u32(end),
          ]),
        ]
      })
      .collect();
    let traces = [(2usize, 4u32, 4usize), (1, 2, 2)]
      .into_iter()
      .map(|(width, end, height)| {
        let row_width = width + 3;
        let mut values = vec![Val::ZERO; row_width * height];
        values[..4].copy_from_slice(&[
          expected[0],
          expected[1],
          Val::ONE,
          Val::from_u32(end),
        ]);
        RowMajorMatrix::new(values, row_width)
      })
      .collect();
    let proof = system.prove_batch(
      &pk,
      vec![ShardInput {
        claims: vec![expected.clone()],
        witness: SystemWitness::from_stage_1(traces, &system),
      }],
      messages,
    );
    let proof_bytes = proof.to_bytes().unwrap();
    let claim_bytes =
      stark_verifier::claims_bytes(std::slice::from_ref(&expected));
    (vk_bytes, layout.to_bytes(), proof_bytes, claim_bytes)
  }

  #[test]
  fn fixed_root_ffi_params_select_c2_profiles() {
    assert_eq!(
      fixed_root_params(false),
      OuterFriParams::COMPACT_400KB_BALANCED
    );
    assert_eq!(fixed_root_params(true), OuterFriParams::ULTRA_COMPACT_400KB_ZK);
  }

  #[test]
  fn fixed_root_ffi_v2_roundtrip_and_negative_controls() {
    let (vk_bytes, layout_bytes, proof_bytes, claim_bytes) =
      fixed_root_fixture_bytes();

    // Production 128-bit floor for both v6 and v6-zk (lb=3 >= 3, 129.13b Johnson,
    // 82.25b CertiFRI UD, 245b conjectured, 8-ary FRI, lfp=8): keeps the 2^20-row
    // FixedRoot FFI roundtrip well within 61.8 GiB CI runners (production preset
    // selection is checked separately in `fixed_root_ffi_params_select_c2_profiles`).
    let test_params = OuterFriParams {
      log_blowup: 3,
      num_queries: 75,
      commit_proof_of_work_bits: 0,
      query_proof_of_work_bits: 20,
      cap_height: 0,
      max_log_arity: 3,
      log_final_poly_len: 8,
    };

    // Noncanonical trailing byte on normalized inner proof is rejected fail-closed.
    let mut trailing_proof = proof_bytes.clone();
    trailing_proof.push(0);
    assert!(
      shrink_fixed_root_with_params(
        &vk_bytes,
        &layout_bytes,
        &trailing_proof,
        &claim_bytes,
        false,
        test_params,
        None,
      )
      .is_err()
    );

    // Capped / higher-arity shapes (cap 4 / 8-ary, cap 12 / 16-ary) can no
    // longer be produced: the floor runs on the real values.
    for (cap_height, max_log_arity) in [(4, 3), (12, 4)] {
      let err = shrink_fixed_root_with_params(
        &vk_bytes,
        &layout_bytes,
        &proof_bytes,
        &claim_bytes,
        false,
        OuterFriParams { cap_height, max_log_arity, ..test_params },
        None,
      )
      .expect_err("shrank under a capped outer shape");
      assert!(err.contains("cap_height"), "{err}");
    }

    let test_profiles = [
      (ShrinkMode::Stark128, test_params),
      (ShrinkMode::Stark128Zk, test_params),
    ];
    for (is_zk, expected_tag) in [(false, "NON-ZK"), (true, "BLINDED")] {
      let (env_bytes, shrink_banner) = shrink_fixed_root_with_params(
        &vk_bytes,
        &layout_bytes,
        &proof_bytes,
        &claim_bytes,
        is_zk,
        test_params,
        None,
      )
      .unwrap();
      assert!(shrink_banner.contains(expected_tag));
      assert_eq!(
        u16::from_le_bytes([env_bytes[9], env_bytes[10]]),
        stark_shrinker::PLONKISH_ENVELOPE_VERSION
      );

      let verify_banner = verify_fixed_root_bytes_admitting(
        &vk_bytes,
        &layout_bytes,
        &env_bytes,
        &claim_bytes,
        &test_profiles,
      )
      .unwrap();
      assert!(verify_banner.contains(expected_tag));
      assert!(verify_banner.contains("1 outer circuit(s)"));

      // `ix verify`'s entry admits only the shipped profiles, so this
      // honest envelope under a test profile is rejected there.
      let err = verify_fixed_root_bytes(
        &vk_bytes,
        &layout_bytes,
        &env_bytes,
        &claim_bytes,
      )
      .unwrap_err();
      assert!(err.contains("not an admitted Endpoint 1 profile"), "{err}");

      // A header rewritten to a shipped profile no longer matches its proof.
      let mut relabelled =
        stark_shrinker::PlonkishEnvelope::from_bytes(&env_bytes).unwrap();
      relabelled.header.params = fixed_root_params(false);
      relabelled.header.min_log_degree = u16::try_from(
        relabelled
          .header
          .mode
          .expected_min_log_degree(relabelled.header.params.num_queries),
      )
      .unwrap();
      assert!(
        verify_fixed_root_bytes(
          &vk_bytes,
          &layout_bytes,
          &relabelled.to_bytes().unwrap(),
          &claim_bytes,
        )
        .is_err()
      );

      // Wrong expected claim rejected fail-closed.
      let wrong_claim = stark_verifier::claims_bytes(&[vec![
        Val::from_u32(20),
        Val::from_u32(39),
      ]]);
      assert!(
        verify_fixed_root_bytes_admitting(
          &vk_bytes,
          &layout_bytes,
          &env_bytes,
          &wrong_claim,
          &test_profiles,
        )
        .is_err()
      );

      // Tampered layout rejected fail-closed.
      let mut bad_layout = layout_bytes.clone();
      bad_layout[0] ^= 1;
      assert!(
        verify_fixed_root_bytes_admitting(
          &vk_bytes,
          &bad_layout,
          &env_bytes,
          &claim_bytes,
          &test_profiles,
        )
        .is_err()
      );

      // v1 envelope version rejected by v2 verifier.
      let mut v1_like = env_bytes.clone();
      v1_like[9..11].copy_from_slice(&1u16.to_le_bytes());
      assert!(
        verify_fixed_root_bytes_admitting(
          &vk_bytes,
          &layout_bytes,
          &v1_like,
          &claim_bytes,
          &test_profiles,
        )
        .is_err()
      );
    }
  }

  /// Honest envelopes under the shipped presets (`--stark-128` default,
  /// `--stark-128-zk --compact`) verify through `ix verify`'s entry, which
  /// admits only the shipped profiles.
  #[test]
  #[ignore = "proves two lb=4 FixedRoot envelopes: 813 s and 62.0 GB peak RSS \
              at 16 threads, beyond the 61.8 GiB CI runner; run with \
              --ignored on a larger host"]
  fn fixed_root_ffi_release_profiles_verify() {
    let (vk_bytes, layout_bytes, proof_bytes, claim_bytes) =
      fixed_root_fixture_bytes();
    for (is_zk, compact) in [(false, false), (true, true)] {
      let (env_bytes, _) = shrink_fixed_root_with_params(
        &vk_bytes,
        &layout_bytes,
        &proof_bytes,
        &claim_bytes,
        is_zk,
        fixed_root_params(compact),
        None,
      )
      .unwrap();
      let banner = verify_fixed_root_bytes(
        &vk_bytes,
        &layout_bytes,
        &env_bytes,
        &claim_bytes,
      )
      .unwrap();
      assert!(banner.contains("1 outer circuit(s)"), "{banner}");
      assert!(banner.contains("cap=0"), "{banner}");
      eprintln!("{banner}");
    }
  }

  #[test]
  fn shipped_presets_are_the_admitted_endpoint1_profiles() {
    for mode in [ShrinkMode::Stark128, ShrinkMode::Stark128Zk] {
      for compact in [false, true] {
        assert!(
          ENDPOINT1_PROFILES.contains(&(mode, fixed_root_params(compact))),
          "{mode:?} compact={compact}"
        );
      }
    }
    assert_eq!(ENDPOINT1_PROFILES.len(), 4);
  }
}
