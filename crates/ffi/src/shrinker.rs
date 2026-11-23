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
  COMPACT_PARAMS, CompiledVerifier, DEFAULT_PARAMS, OuterFriParams,
  PlonkishCircuitVerifier, PlonkishOptions, StarkShrinker,
  StarkShrinkerVerifier, decode_single_claim_bytes,
  envelope::{ShrinkMode, peek_header},
  hash_publics, peek_plonkish_header, shrink_fixed_root_1hop,
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
    let header = peek_header(envelope_bytes)?;
    let expected_inner =
      parse_digest32("expected inner VK digest", &expected_inner_vk_digest)?;
    let expected_claim =
      parse_digest32("expected claim digest", &expected_claim_digest)?;
    let compiled =
      load_pinned_verifier(&verifier_artifact, &expected_artifact_digest)?;
    let plan = compiled.trace_plan()?;
    let verifier =
      StarkShrinkerVerifier::new(&plan, header.mode, header.params)?;
    let report = verifier.verify(
      envelope_bytes,
      Some(&expected_inner),
      Some(&expected_claim),
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
  let (output, _verifier) = shrink_fixed_root_1hop(
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

fn verify_fixed_root_bytes(
  inner_vk_bytes: &[u8],
  layout_bytes: &[u8],
  envelope_bytes: &[u8],
  expected_claim_bytes: &[u8],
) -> Result<String, String> {
  let header = peek_plonkish_header(envelope_bytes)?;
  if header.hops != 1 {
    return Err(format!(
      "FixedRoot Plonkish verifier expects 1-hop envelope (got {} hops)",
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
    header.mode,
    header.params,
    PlonkishOptions::default(),
  )?;
  let report = verifier.verify_report(
    envelope_bytes,
    &claim_vals,
    Some(&expected_inner_vk),
    Some(&expected_claim),
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
      [(8usize, 8usize), (1, 2)].into_iter().map(|(width, height)| {
        CircuitInputs {
          main_width: width + 3,
          preprocessed: Some(RowMajorMatrix::new_col(vec![Val::ZERO; height])),
          lookups: vec![
            Lookup::pull(
              if width == 8 { Expr::main(2) } else { Val::ZERO.into() },
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
    let layout = FixedRoot::new(vec![3, 1], vec![(1, 1), (8, 0)], 2).unwrap();
    let expected = vec![Val::from_u32(19), Val::from_u32(39)];
    let messages = [(1u32, 2u32), (8, 8)]
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
    let traces = [(8usize, 8u32, 8usize), (1, 2, 2)]
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
        OuterFriParams::COMPACT_400KB_FAST,
        None,
      )
      .is_err()
    );

    for (is_zk, expected_tag) in [(false, "NON-ZK"), (true, "ZERO-KNOWLEDGE")] {
      let (env_bytes, shrink_banner) = shrink_fixed_root_with_params(
        &vk_bytes,
        &layout_bytes,
        &proof_bytes,
        &claim_bytes,
        is_zk,
        OuterFriParams::COMPACT_400KB_FAST,
        None,
      )
      .unwrap();
      assert!(shrink_banner.contains(expected_tag));
      assert_eq!(
        u16::from_le_bytes([env_bytes[9], env_bytes[10]]),
        stark_shrinker::PLONKISH_ENVELOPE_VERSION
      );

      let verify_banner = verify_fixed_root_bytes(
        &vk_bytes,
        &layout_bytes,
        &env_bytes,
        &claim_bytes,
      )
      .unwrap();
      assert!(verify_banner.contains(expected_tag));
      assert!(verify_banner.contains("1 outer circuit(s)"));

      // Wrong expected claim rejected fail-closed.
      let wrong_claim = stark_verifier::claims_bytes(&[vec![
        Val::from_u32(20),
        Val::from_u32(39),
      ]]);
      assert!(
        verify_fixed_root_bytes(
          &vk_bytes,
          &layout_bytes,
          &env_bytes,
          &wrong_claim,
        )
        .is_err()
      );

      // Tampered layout rejected fail-closed.
      let mut bad_layout = layout_bytes.clone();
      bad_layout[0] ^= 1;
      assert!(
        verify_fixed_root_bytes(
          &vk_bytes,
          &bad_layout,
          &env_bytes,
          &claim_bytes,
        )
        .is_err()
      );

      // v1 envelope version rejected by v2 verifier.
      let mut v1_like = env_bytes.clone();
      v1_like[9..11].copy_from_slice(&1u16.to_le_bytes());
      assert!(
        verify_fixed_root_bytes(
          &vk_bytes,
          &layout_bytes,
          &v1_like,
          &claim_bytes,
        )
        .is_err()
      );
    }
  }
}
