//! Endpoint 1: Native `Fp^3` STARK Shrinker supporting both transparent
//! `--stark-128` (Protocol `v6`) and hiding `--stark-128-zk` (Protocol `v6-zk`).
//!
//! Wraps a valid Protocol `v6` (`Fp^3`) inner proof (such as an `IXAGGR2`
//! aggregate root) in one outer standalone `Fp^3` STARK proof of
//! `MultiStark::verify_multi_stark_proof` using high-blowup / lower-query
//! 128-bit parameters (`DEFAULT_PARAMS = (lb=3, q=78, qpow=20)`, 133.49b
//! finite-`m` Johnson soundness, or `COMPACT_PARAMS = (lb=4, q=66, qpow=20)`,
//! 149.03b finite-`m` Johnson soundness).
//!
//! - Zero trusted setup (transparent).
//! - Hash-based (BLAKE3 `derive_key`, 32-byte digests: ~128-bit classical,
//!   ~85-bit quantum collision resistance) + `Fp^3` FRI.
//! - Fail-closed Protocol `v6` / `Fp^3` / `FriBatching::Tensor` enforcement;
//!   `v5` and `Fp^2` are retired and rejected.
//! - Standalone (non-segmented) ROM eliminates cleartext `MEMSEG` count leakage
//!   in `--stark-128-zk` proofs.

pub mod breakdown;
pub mod circuit_merge;
pub mod compact_codec;
pub mod envelope;
pub mod plonkish;

use aiur::{
  artifact::Package,
  bytecode::CheckedProgram,
  field::NativeField,
  trace::{
    TraceArtifact, TracePlan,
    stark::{Backend, BatchProof, Parameters, Proof, ZkBackend, ZkProof},
  },
};
use envelope::{
  ENTRYPOINT, EnvelopeHeader, ShrinkEnvelope, ShrinkMode,
  compute_shrinker_vk_digest, peek_header,
};
use multi_stark::{
  p3_field::{PrimeCharacteristicRing, PrimeField64},
  types::Val,
};
use std::{path::Path, time::Instant};

pub use envelope::{
  COMPACT_PARAMS, DEFAULT_PARAMS, ENVELOPE_MAGIC, HEADER_LEN, is_shrunk,
};
pub use plonkish::{
  MAX_PLONKISH_HOPS, OuterFriParams, PLONKISH_ENVELOPE_VERSION,
  PLONKISH_HEADER_LEN, PlonkishCircuitVerifier, PlonkishEnvelope,
  PlonkishHeader, PlonkishOptions, PlonkishShrinkOutput, PlonkishVerifyReport,
  decode_single_claim_bytes, hash_publics, peek_plonkish_header,
  prove_plonkish_circuit, shrink_fixed_root, shrink_fixed_root_1hop,
  shrink_single_batch_1hop, shrink_single_batch_2hop,
};

/// Convert a 32-byte BLAKE3 digest into the 8 canonical Goldilocks `u32` limb
/// field elements expected by `MultiStark::verify_multi_stark_proof`.
pub fn digest_to_vals(digest: &[u8; 32]) -> [Val; 8] {
  let mut out = [Val::from_u64(0); 8];
  for (slot, chunk) in out.iter_mut().zip(digest.as_chunks::<4>().0) {
    *slot = Val::from_u64(u64::from(u32::from_le_bytes(*chunk)));
  }
  out
}

/// Build the 16 public Goldilocks arguments `[inner_vk_digest_words[0..8],
/// claim_digest_words[0..8]]` for `MultiStark::verify_multi_stark_proof`.
pub fn public_args(
  inner_vk_digest: &[u8; 32],
  claim_digest: &[u8; 32],
) -> Vec<Val> {
  let mut args = Vec::with_capacity(16);
  args.extend_from_slice(&digest_to_vals(inner_vk_digest));
  args.extend_from_slice(&digest_to_vals(claim_digest));
  args
}

fn hex_digest(digest: &[u8; 32]) -> String {
  blake3::Hash::from_bytes(*digest).to_hex().to_string()
}

/// Verified metadata and honest trust/ZK posture returned by verification.
#[derive(Clone, Debug)]
pub struct VerifyReport {
  pub mode: ShrinkMode,
  pub params: Parameters,
  pub shrinker_vk_digest: [u8; 32],
  pub inner_vk_digest: [u8; 32],
  pub claim_digest: [u8; 32],
  pub envelope_bytes: usize,
  pub proof_bytes: usize,
  pub verify_ms: f64,
  pub johnson_millibits: usize,
  pub provable_ud_millibits: usize,
  pub conjectured_bits: usize,
  pub zk_randomizer_width: usize,
  pub min_log_degree: usize,
}

impl VerifyReport {
  fn build(
    header: &EnvelopeHeader,
    envelope_bytes: usize,
    verify_ms: f64,
  ) -> Self {
    let cp = header.params.commitment();
    let fp = header.params.fri();
    let johnson_millibits = stark_key::security::johnson_millibits(&cp, &fp);
    let provable_ud_millibits =
      stark_key::security::provable_ud_millibits(&cp, &fp).unwrap_or(0);
    let conjectured_bits = stark_key::security::conjectured_bits(&cp, &fp);
    Self {
      mode: header.mode,
      params: header.params,
      shrinker_vk_digest: header.shrinker_vk_digest,
      inner_vk_digest: header.inner_vk_digest,
      claim_digest: header.claim_digest,
      envelope_bytes,
      proof_bytes: envelope_bytes.saturating_sub(HEADER_LEN),
      verify_ms,
      johnson_millibits,
      provable_ud_millibits,
      conjectured_bits,
      zk_randomizer_width: usize::from(header.zk_randomizer_width),
      min_log_degree: usize::from(header.min_log_degree),
    }
  }

  /// Format a concise, honest trust and zero-knowledge banner for CLI output.
  pub fn banner(&self) -> String {
    let johnson_whole = self.johnson_millibits / 1000;
    let johnson_frac = (self.johnson_millibits % 1000) / 10;
    let ud_whole = self.provable_ud_millibits / 1000;
    let ud_frac = (self.provable_ud_millibits % 1000) / 10;
    let zk_line = match self.mode {
      ShrinkMode::Stark128 => {
        "NON-ZK (transparent witness — no hiding PCS or leaf salting)"
          .to_owned()
      },
      ShrinkMode::Stark128Zk => format!(
        "BLINDED (v6-zk hiding-PCS construction: 2x odd-coset blinding, W_R={} randomizer, 16-byte BLAKE3-CTR leaf salts, telescoping quotient blinding, blinded accumulators, min_log_degree={}; no hiding property is stated or proved)",
        self.zk_randomizer_width, self.min_log_degree
      ),
    };
    format!(
      "Endpoint 1 Native Fp^3 STARK Shrinker ({flag} / {proto})\n\
       \x20 Field/PCS : Fp^3 = Fp[X]/(X^3 - X - 1) | BLAKE3 derive_key | FriBatching::Tensor\n\
       \x20 FRI query : {johnson_whole}.{johnson_frac:02}b finite-m Johnson (m=16) | {ud_whole}.{ud_frac:02}b unique-decoding | {conj}b conjectured; query-phase floor terms (lb={lb}, q={q}, cpow={cpow}, qpow={qpow})\n\
       \x20 Trust     : Transparent (zero trusted setup) | 32-byte BLAKE3: ~128-bit classical, ~85-bit quantum collision resistance\n\
       \x20 Privacy   : {zk_line}\n\
       \x20 Outer VK  : {svk} (derived by the verifier from the pinned package)\n\
       \x20 Inner VK  : {ivk}\n\
       \x20 Claim     : {claim}\n\
       \x20 Proof     : {env} bytes ({raw} B STARK payload) | verified in {ms:.2} ms",
      flag = self.mode.cli_flag(),
      proto = self.mode.protocol_name(),
      conj = self.conjectured_bits,
      lb = self.params.log_blowup,
      q = self.params.num_queries,
      cpow = self.params.commit_proof_of_work_bits,
      qpow = self.params.query_proof_of_work_bits,
      svk = hex_digest(&self.shrinker_vk_digest),
      ivk = hex_digest(&self.inner_vk_digest),
      claim = hex_digest(&self.claim_digest),
      env = self.envelope_bytes,
      raw = self.proof_bytes,
      ms = self.verify_ms,
    )
  }
}

/// Output of [`StarkShrinker::shrink`]: canonical `IXSTARK6\0` envelope bytes
/// plus self-verification report and wall-clock proving time.
#[derive(Clone, Debug)]
pub struct ShrinkOutput {
  pub envelope_bytes: Vec<u8>,
  pub report: VerifyReport,
  pub prove_ms: f64,
}

/// Loaded, field-checked, depth-tracked `MultiStark::verify_multi_stark_proof`
/// artifact ready to build a [`TracePlan`].
pub struct CompiledVerifier {
  program: CheckedProgram<NativeField<Val>>,
  trace: TraceArtifact,
  artifact_digest: [u8; 32],
}

impl CompiledVerifier {
  /// Load a compiled `.ixa` verifier package from disk and validate its field
  /// (`Goldilocks`) and depth instrumentation.
  pub fn from_package_path(path: &Path) -> Result<Self, String> {
    let (package, digest) = Package::load(path)?;
    Self::from_package(package, digest.0)
  }

  /// Decode a compiled `.ixa` verifier package from raw bytes.
  pub fn from_package_bytes(bytes: &[u8]) -> Result<Self, String> {
    let digest = *blake3::hash(bytes).as_bytes();
    let package = Package::decode(bytes)?;
    Self::from_package(package, digest)
  }

  fn from_package(
    package: Package,
    artifact_digest: [u8; 32],
  ) -> Result<Self, String> {
    let (program, trace) = package.traced()?;
    let mut program = program.check_field::<Val>()?;
    program.track_depth(&trace)?;
    // Fail fast if this package does not expose the recursive verifier entry.
    program.entry(ENTRYPOINT)?;
    Ok(Self { program, trace, artifact_digest })
  }

  pub const fn artifact_digest(&self) -> &[u8; 32] {
    &self.artifact_digest
  }

  pub const fn program(&self) -> &CheckedProgram<NativeField<Val>> {
    &self.program
  }

  pub fn trace_plan(&self) -> Result<TracePlan<'_, NativeField<Val>>, String> {
    TracePlan::new(&self.program, self.trace.clone())
  }
}

enum ShrinkerBackend<'p, 'a> {
  Transparent(Box<Backend<'p, 'a, NativeField<Val>>>),
  Zk(Box<ZkBackend<'p, 'a, NativeField<Val>>>),
}

impl<'p, 'a> ShrinkerBackend<'p, 'a> {
  fn build(
    plan: &'p TracePlan<'a, NativeField<Val>>,
    mode: ShrinkMode,
    params: Parameters,
    device: Option<i32>,
  ) -> Result<(Self, [u8; 32], u16, u16), String> {
    params.check()?;
    let zero_args = [Val::from_u64(0); 16];
    match mode {
      ShrinkMode::Stark128 => {
        let backend = Backend::new_on_device(plan, params, device)?;
        let claim = backend.claim(ENTRYPOINT, &zero_args, &[])?;
        let entry_call_channel = claim[0].as_canonical_u64();
        let entry_function_index = claim[1].as_canonical_u64();
        let vk_digest = compute_shrinker_vk_digest(
          mode,
          params,
          0,
          0,
          entry_call_channel,
          entry_function_index,
          &backend.system().vk_digest,
          backend.system().preprocessed_commit.as_ref().map(|c| c.roots()),
        )?;
        Ok((Self::Transparent(Box::new(backend)), vk_digest, 0, 0))
      },
      ShrinkMode::Stark128Zk => {
        if params.log_blowup < 3 {
          return Err(format!(
            "v6-zk shrinker requires log_blowup >= 3 to satisfy quotient_degree_for(true) <= blowup (got {})",
            params.log_blowup
          ));
        }
        let backend = ZkBackend::new_on_device(plan, params, device)?;
        let claim = backend.claim(ENTRYPOINT, &zero_args, &[])?;
        let entry_call_channel = claim[0].as_canonical_u64();
        let entry_function_index = claim[1].as_canonical_u64();
        let rw = backend.zk_randomizer_width();
        let mld = backend.min_log_degree();
        let vk_digest = compute_shrinker_vk_digest(
          mode,
          params,
          rw,
          mld,
          entry_call_channel,
          entry_function_index,
          &backend.system().vk_digest,
          backend.system().preprocessed_commit.as_ref().map(|c| c.roots()),
        )?;
        let rw_u16 = u16::try_from(rw)
          .map_err(|err| format!("zk_randomizer_width exceeds u16: {err}"))?;
        let mld_u16 = u16::try_from(mld)
          .map_err(|err| format!("min_log_degree exceeds u16: {err}"))?;
        Ok((Self::Zk(Box::new(backend)), vk_digest, rw_u16, mld_u16))
      },
    }
  }

  fn prove_record(
    &self,
    record: aiur::Execution<NativeField<Val>>,
    args: &[Val],
  ) -> Result<Vec<u8>, String> {
    match self {
      Self::Transparent(backend) => {
        // Generate only stage-1 main traces, immediately drop the execution
        // record, and prove via streaming lazy lookups to keep peak RAM low
        // even when shrinking multi-megabyte aggregate root proofs.
        let traces = backend.generate_stage_1(&record, ENTRYPOINT, args)?;
        drop(record);
        let proof = backend.prove_streaming(ENTRYPOINT, args, &[], traces)?;
        backend.verify(ENTRYPOINT, args, &[], &proof)?;
        proof.to_bytes().map_err(|e| format!("v6 proof encode failed: {e}"))
      },
      Self::Zk(backend) => {
        let traces = backend.generate_stage_1(&record, ENTRYPOINT, args)?;
        drop(record);
        let proof = backend.prove_streaming(ENTRYPOINT, args, &[], traces)?;
        backend.verify(ENTRYPOINT, args, &[], &proof)?;
        proof.to_bytes().map_err(|e| format!("v6-zk proof encode failed: {e}"))
      },
    }
  }

  fn verify_raw_proof(
    &self,
    args: &[Val],
    proof_bytes: &[u8],
  ) -> Result<(), String> {
    match self {
      Self::Transparent(backend) => {
        let proof = Proof::from_bytes(proof_bytes)
          .map_err(|e| format!("v6 proof decode failed: {e}"))?;
        let canonical = proof
          .to_bytes()
          .map_err(|e| format!("v6 proof re-encode failed: {e}"))?;
        if canonical != proof_bytes {
          return Err("noncanonical or trailing v6 proof bytes".into());
        }
        backend.verify(ENTRYPOINT, args, &[], &proof)
      },
      Self::Zk(backend) => {
        let proof = ZkProof::from_bytes(proof_bytes)
          .map_err(|e| format!("v6-zk proof decode failed: {e}"))?;
        let canonical = proof
          .to_bytes()
          .map_err(|e| format!("v6-zk proof re-encode failed: {e}"))?;
        if canonical != proof_bytes {
          return Err("noncanonical or trailing v6-zk proof bytes".into());
        }
        backend.verify(ENTRYPOINT, args, &[], &proof)
      },
    }
  }
}

/// Reusable prover + self-verifier for Endpoint 1 native `Fp^3` STARK shrinking.
pub struct StarkShrinker<'p, 'a> {
  program: &'a CheckedProgram<NativeField<Val>>,
  mode: ShrinkMode,
  params: Parameters,
  zk_randomizer_width: u16,
  min_log_degree: u16,
  vk_digest: [u8; 32],
  backend: ShrinkerBackend<'p, 'a>,
}

impl<'p, 'a> StarkShrinker<'p, 'a> {
  pub fn new(
    verifier: &'a CompiledVerifier,
    plan: &'p TracePlan<'a, NativeField<Val>>,
    mode: ShrinkMode,
    params: Parameters,
    device: Option<i32>,
  ) -> Result<Self, String> {
    let (backend, vk_digest, zk_randomizer_width, min_log_degree) =
      ShrinkerBackend::build(plan, mode, params, device)?;
    Ok(Self {
      program: verifier.program(),
      mode,
      params,
      zk_randomizer_width,
      min_log_degree,
      vk_digest,
      backend,
    })
  }

  pub const fn mode(&self) -> ShrinkMode {
    self.mode
  }

  pub const fn params(&self) -> Parameters {
    self.params
  }

  pub const fn vk_digest(&self) -> &[u8; 32] {
    &self.vk_digest
  }

  /// Shrink a valid Protocol `v6` (`Fp^3`) inner proof into a self-verified
  /// `IXSTARK6\0` envelope.
  ///
  /// Fails closed if the inner verifying key is `v5`, `Fp^2`, Horner, or below
  /// the 128-bit security floor, if the inner proof is malformed/invalid, or if
  /// `MultiStark::verify_multi_stark_proof` rejects the witness.
  pub fn shrink(
    &self,
    inner_key_bytes: &[u8],
    inner_claims_bytes: &[u8],
    inner_proof_bytes: &[u8],
  ) -> Result<ShrinkOutput, String> {
    // 1. Validate inner v6 key & 128-bit floor fail-closed (rejects v5 / Fp^2 / Horner).
    let _ = stark_key::from_bytes(inner_key_bytes)
      .map_err(|e| format!("inner verifying key rejected: {e}"))?;
    // 2. Validate inner v6 proof canonical wire encoding before executing recursion.
    let inner_proof = BatchProof::from_bytes(inner_proof_bytes)
      .map_err(|e| format!("inner proof decode failed: {e}"))?;
    let canonical_inner = inner_proof
      .to_bytes()
      .map_err(|e| format!("inner proof re-encode failed: {e}"))?;
    if canonical_inner != inner_proof_bytes {
      return Err("noncanonical or trailing inner proof bytes".into());
    }
    drop(inner_proof);
    drop(canonical_inner);

    let start = Instant::now();
    let inner_vk_digest = *blake3::hash(inner_key_bytes).as_bytes();
    let claim_digest = *blake3::hash(inner_claims_bytes).as_bytes();
    let args = public_args(&inner_vk_digest, &claim_digest);

    // 3. Execute MultiStark::verify_multi_stark_proof on the inner proof advice,
    //    then immediately drop advice and prepared hints before proving.
    let record = {
      let advice = stark_verifier::advice(
        self.program.field(),
        inner_key_bytes,
        inner_claims_bytes,
        inner_proof_bytes,
      )?;
      let hints = stark_verifier::prepare_advice(self.program, &advice)?;
      hints
        .execute(ENTRYPOINT, args.clone())
        .map_err(|e| format!("recursive verifier rejected inner proof: {e}"))?
    };
    if !record.output.is_empty() {
      return Err("recursive verifier returned a non-unit output".into());
    }

    // 4. Prove outer v6 or v6-zk STARK over the verifier trace (streaming
    //    lookups lazily and dropping `record` before PCS commitments).
    let proof_bytes = self.backend.prove_record(record, &args)?;
    let prove_ms = start.elapsed().as_secs_f64() * 1000.0;

    let proof_len = u64::try_from(proof_bytes.len())
      .map_err(|err| format!("outer proof length exceeds u64: {err}"))?;
    let envelope = ShrinkEnvelope {
      header: EnvelopeHeader {
        mode: self.mode,
        params: self.params,
        zk_randomizer_width: self.zk_randomizer_width,
        min_log_degree: self.min_log_degree,
        shrinker_vk_digest: self.vk_digest,
        inner_vk_digest,
        claim_digest,
        proof_len,
      },
      proof_bytes,
    };
    let envelope_bytes = envelope.to_bytes()?;

    // 5. Independently self-verify the complete serialized envelope before returning.
    let report =
      self.verify_envelope(&envelope_bytes, &inner_vk_digest, &claim_digest)?;
    Ok(ShrinkOutput { envelope_bytes, report, prove_ms })
  }

  /// Verify an `IXSTARK6\0` envelope against this shrinker's pinned verifying
  /// key, the caller's inner-key digest and the caller's claim digest.
  pub fn verify_envelope(
    &self,
    envelope_bytes: &[u8],
    expected_inner_vk_digest: &[u8; 32],
    expected_claim_digest: &[u8; 32],
  ) -> Result<VerifyReport, String> {
    verify_against_backend(
      &self.backend,
      self.mode,
      self.params,
      &self.vk_digest,
      envelope_bytes,
      expected_inner_vk_digest,
      expected_claim_digest,
    )
  }
}

/// CPU-only pinned verifier for `IXSTARK6\0` envelopes.
pub struct StarkShrinkerVerifier<'p, 'a> {
  mode: ShrinkMode,
  params: Parameters,
  vk_digest: [u8; 32],
  backend: ShrinkerBackend<'p, 'a>,
}

impl<'p, 'a> StarkShrinkerVerifier<'p, 'a> {
  pub fn new(
    plan: &'p TracePlan<'a, NativeField<Val>>,
    mode: ShrinkMode,
    params: Parameters,
  ) -> Result<Self, String> {
    let (backend, vk_digest, _, _) =
      ShrinkerBackend::build(plan, mode, params, None)?;
    Ok(Self { mode, params, vk_digest, backend })
  }

  pub const fn mode(&self) -> ShrinkMode {
    self.mode
  }

  pub const fn params(&self) -> Parameters {
    self.params
  }

  pub const fn vk_digest(&self) -> &[u8; 32] {
    &self.vk_digest
  }

  /// Verify an envelope against this verifier's key, the caller's inner-key
  /// digest and the caller's claim digest (both mandatory: the proof's public
  /// arguments are these two digests).
  pub fn verify(
    &self,
    envelope_bytes: &[u8],
    expected_inner_vk_digest: &[u8; 32],
    expected_claim_digest: &[u8; 32],
  ) -> Result<VerifyReport, String> {
    verify_against_backend(
      &self.backend,
      self.mode,
      self.params,
      &self.vk_digest,
      envelope_bytes,
      expected_inner_vk_digest,
      expected_claim_digest,
    )
  }
}

fn verify_against_backend(
  backend: &ShrinkerBackend<'_, '_>,
  expected_mode: ShrinkMode,
  expected_params: Parameters,
  pinned_vk_digest: &[u8; 32],
  envelope_bytes: &[u8],
  expected_inner_vk_digest: &[u8; 32],
  expected_claim_digest: &[u8; 32],
) -> Result<VerifyReport, String> {
  let start = Instant::now();
  let envelope = ShrinkEnvelope::from_bytes(envelope_bytes)?;
  let header = &envelope.header;

  if header.mode != expected_mode {
    return Err(format!(
      "shrink mode mismatch (cross-mode replay rejected): verifier expects {} but envelope is {}",
      expected_mode.cli_flag(),
      header.mode.cli_flag()
    ));
  }
  if header.params != expected_params {
    return Err(format!(
      "shrinker FRI parameters mismatch: verifier expects {:?} but envelope declares {:?}",
      expected_params, header.params
    ));
  }
  if &header.shrinker_vk_digest != pinned_vk_digest {
    return Err(format!(
      "shrinker VK digest mismatch: pinned {} != envelope {}",
      hex_digest(pinned_vk_digest),
      hex_digest(&header.shrinker_vk_digest)
    ));
  }
  if &header.inner_vk_digest != expected_inner_vk_digest {
    return Err(format!(
      "inner VK digest mismatch: expected {} != envelope {}",
      hex_digest(expected_inner_vk_digest),
      hex_digest(&header.inner_vk_digest)
    ));
  }
  if &header.claim_digest != expected_claim_digest {
    return Err(format!(
      "claim digest mismatch: expected {} != envelope {}",
      hex_digest(expected_claim_digest),
      hex_digest(&header.claim_digest)
    ));
  }

  // The proof's public arguments are the caller's digests (equal to the
  // header's, checked above).
  let args = public_args(expected_inner_vk_digest, expected_claim_digest);
  backend.verify_raw_proof(&args, &envelope.proof_bytes)?;
  let verify_ms = start.elapsed().as_secs_f64() * 1000.0;
  Ok(VerifyReport::build(header, envelope_bytes.len(), verify_ms))
}

/// One-shot convenience API (used by FFI / CLI): shrink a Protocol `v6` proof
/// using the compiled `MultiStark::verify_multi_stark_proof` `.ixa` package at
/// `package_path`.
pub fn shrink_with_package(
  package_path: &Path,
  inner_key_bytes: &[u8],
  inner_claims_bytes: &[u8],
  inner_proof_bytes: &[u8],
  mode: ShrinkMode,
  params: Parameters,
  device: Option<i32>,
) -> Result<ShrinkOutput, String> {
  let compiled = CompiledVerifier::from_package_path(package_path)?;
  let plan = compiled.trace_plan()?;
  let shrinker = StarkShrinker::new(&compiled, &plan, mode, params, device)?;
  shrinker.shrink(inner_key_bytes, inner_claims_bytes, inner_proof_bytes)
}

/// The (mode, parameters) pairs a v1 `IXSTARK6\0` verifier admits: the two
/// presets the v1 shrinker produces ([`DEFAULT_PARAMS`], `--compact`
/// [`COMPACT_PARAMS`]) in both modes. The verifier builds its backend from
/// these constants; an envelope declaring any other parameters is rejected.
pub const V1_PROFILES: [(ShrinkMode, Parameters); 4] = [
  (ShrinkMode::Stark128, DEFAULT_PARAMS),
  (ShrinkMode::Stark128, COMPACT_PARAMS),
  (ShrinkMode::Stark128Zk, DEFAULT_PARAMS),
  (ShrinkMode::Stark128Zk, COMPACT_PARAMS),
];

/// The admitted `(mode, parameters)` pair equal to a v1 envelope header's.
pub fn admitted_v1_profile(
  header: &EnvelopeHeader,
  admitted: &[(ShrinkMode, Parameters)],
) -> Result<(ShrinkMode, Parameters), String> {
  admitted
    .iter()
    .copied()
    .find(|&(mode, params)| mode == header.mode && params == header.params)
    .ok_or_else(|| {
      format!(
        "{} envelope under parameters {:?} is not an admitted v1 shrinker profile (admitted: {admitted:?})",
        header.mode.cli_flag(),
        header.params
      )
    })
}

/// Verify a v1 `IXSTARK6\0` envelope with an already pinned compiled verifier:
/// the mode and parameters must be an admitted profile ([`V1_PROFILES`]), the
/// backend is derived from that constant and `compiled`, and the inner-key and
/// claim digests must equal the caller's.
pub fn verify_v1_pinned(
  compiled: &CompiledVerifier,
  envelope_bytes: &[u8],
  expected_inner_vk_digest: &[u8; 32],
  expected_claim_digest: &[u8; 32],
) -> Result<VerifyReport, String> {
  let header = peek_header(envelope_bytes)?;
  let (mode, params) = admitted_v1_profile(&header, &V1_PROFILES)?;
  let plan = compiled.trace_plan()?;
  let verifier = StarkShrinkerVerifier::new(&plan, mode, params)?;
  verifier.verify(
    envelope_bytes,
    expected_inner_vk_digest,
    expected_claim_digest,
  )
}

/// One-shot convenience API: verify a v1 `IXSTARK6\0` envelope with the
/// compiled verifier package at `package_path`, which must hash to
/// `expected_package_digest` (as the FFI entry requires), against the caller's
/// inner-key and claim digests ([`verify_v1_pinned`]).
pub fn verify_with_package(
  package_path: &Path,
  expected_package_digest: &[u8; 32],
  envelope_bytes: &[u8],
  expected_inner_vk_digest: &[u8; 32],
  expected_claim_digest: &[u8; 32],
) -> Result<VerifyReport, String> {
  let compiled = CompiledVerifier::from_package_path(package_path)?;
  if compiled.artifact_digest() != expected_package_digest {
    return Err(format!(
      "verifier artifact digest mismatch: pinned {} != loaded {}",
      hex_digest(expected_package_digest),
      hex_digest(compiled.artifact_digest())
    ));
  }
  verify_v1_pinned(
    &compiled,
    envelope_bytes,
    expected_inner_vk_digest,
    expected_claim_digest,
  )
}

#[cfg(test)]
mod tests {
  use super::*;
  use multi_stark::{
    batch::ShardInput,
    expr::Expr,
    lookup::Lookup,
    p3_field::PrimeCharacteristicRing,
    p3_matrix::dense::RowMajorMatrix,
    system::{CircuitInputs, System, SystemWitness},
    types::{GoldilocksBlake3V6Config, Val},
  };
  use std::path::PathBuf;

  /// Build a real production-grade 128-bit Protocol v6 (`Fp^3`) inner proof
  /// (`Parameters::DEFAULT = (lb=2, q=128, qpow=20)`, 142.24b Johnson).
  fn build_production_inner_v6_proof() -> (Vec<u8>, Vec<u8>, Vec<u8>) {
    let params = Parameters::DEFAULT;
    let (cp, fp) = (params.commitment(), params.fri());
    let x = Expr::main(0);
    let y = Expr::main(1);
    let one = Expr::constant(Val::ONE);
    let inputs = vec![CircuitInputs {
      main_width: 2,
      constraints: vec![x.clone() * x.clone() - y.clone()],
      lookups: vec![Lookup::pull(
        one.clone(),
        vec![one, Expr::constant(Val::ZERO), x, y],
      )],
      ..Default::default()
    }];
    let (system, pk) =
      System::new(GoldilocksBlake3V6Config::new(cp, fp), inputs);
    let claims =
      vec![vec![Val::ONE, Val::ZERO, Val::from_u64(3), Val::from_u64(9)]];
    let witness = SystemWitness::from_stage_1(
      vec![RowMajorMatrix::new(vec![Val::from_u64(3), Val::from_u64(9)], 2)],
      &system,
    );
    let proof = system.prove_batch(
      &pk,
      vec![ShardInput { claims: claims.clone(), witness }],
      vec![],
    );
    system.verify_batch(&proof).expect("inner v6 proof verifies natively");
    let key_bytes = stark_key::to_bytes(&system, cp, fp);
    let claims_bytes = stark_verifier::claims_bytes(&claims);
    let proof_bytes = proof.to_bytes().expect("inner proof encodes");
    (key_bytes, claims_bytes, proof_bytes)
  }

  /// Locate the cached compiled `MultiStark::verify_multi_stark_proof` `.ixa`
  /// artifact from `IX_VERIFIER_ARTIFACT` or `<repo>/.lake/aiur/stark-export-*.ixa`.
  fn find_verifier_package() -> Option<PathBuf> {
    if let Ok(path) = std::env::var("IX_VERIFIER_ARTIFACT") {
      let pb = PathBuf::from(path);
      if pb.is_file() {
        return Some(pb);
      }
    }
    let repo_root = Path::new(env!("CARGO_MANIFEST_DIR")).parent()?.parent()?;
    let cache_dir = repo_root.join(".lake/aiur");
    let entries = std::fs::read_dir(&cache_dir).ok()?;
    for entry in entries.flatten() {
      let path = entry.path();
      if path.extension().and_then(|s| s.to_str()) != Some("ixa") {
        continue;
      }
      let name = path.file_name().and_then(|s| s.to_str()).unwrap_or("");
      if !name.starts_with("stark-export-") {
        continue;
      }
      if CompiledVerifier::from_package_path(&path).is_ok() {
        return Some(path);
      }
    }
    None
  }

  fn dummy_envelope(mode: ShrinkMode, params: Parameters) -> Vec<u8> {
    let rw = u16::try_from(mode.expected_randomizer_width()).unwrap();
    let mld =
      u16::try_from(mode.expected_min_log_degree(params.num_queries)).unwrap();
    ShrinkEnvelope {
      header: EnvelopeHeader {
        mode,
        params,
        zk_randomizer_width: rw,
        min_log_degree: mld,
        shrinker_vk_digest: [0x11; 32],
        inner_vk_digest: [0x22; 32],
        claim_digest: [0x33; 32],
        proof_len: 4,
      },
      proof_bytes: vec![1, 2, 3, 4],
    }
    .to_bytes()
    .unwrap()
  }

  #[test]
  fn envelope_header_fail_closed_security_controls() {
    for mode in [ShrinkMode::Stark128, ShrinkMode::Stark128Zk] {
      let good = dummy_envelope(mode, DEFAULT_PARAMS);
      let parsed = ShrinkEnvelope::from_bytes(&good).unwrap();
      assert_eq!(parsed.header.mode, mode);
      assert_eq!(parsed.header.params, DEFAULT_PARAMS);
      assert_eq!(parsed.to_bytes().unwrap(), good);

      // Bad magic
      let mut bad = good.clone();
      bad[7] = b'5';
      assert!(peek_header(&bad).is_err());

      // Bad envelope version
      let mut bad = good.clone();
      bad[9..11].copy_from_slice(&2u16.to_le_bytes());
      assert!(peek_header(&bad).is_err());

      // Protocol v5 downgrade rejected fail-closed
      let mut bad = good.clone();
      bad[11..13].copy_from_slice(&5u16.to_le_bytes());
      assert!(peek_header(&bad).unwrap_err().contains("retired"));

      // Fp^2 extension degree downgrade rejected fail-closed
      let mut bad = good.clone();
      bad[13..15].copy_from_slice(&2u16.to_le_bytes());
      assert!(peek_header(&bad).unwrap_err().contains("Fp^2"));

      // Unknown mode tag rejected
      let mut bad = good.clone();
      bad[15] = 9;
      assert!(peek_header(&bad).is_err());

      // FriBatching::Horner (0) downgrade rejected fail-closed
      let mut bad = good.clone();
      bad[16] = 0;
      assert!(peek_header(&bad).unwrap_err().contains("Tensor"));

      // Sub-128-bit FRI queries rejected fail-closed
      let mut bad = good.clone();
      bad[25..27].copy_from_slice(&40u16.to_le_bytes()); // num_queries = 40
      assert!(peek_header(&bad).unwrap_err().contains("security floor"));

      // Trailing byte rejected fail-closed
      let mut bad = good.clone();
      bad.push(0);
      assert!(peek_header(&bad).unwrap_err().contains("length mismatch"));

      // Truncated payload rejected
      let mut bad = good.clone();
      bad.pop();
      assert!(peek_header(&bad).is_err());
    }

    // Mode-specific ZK traps:
    // 1. Transparent mode rejects nonzero W_R / min_log_degree
    let mut bad = dummy_envelope(ShrinkMode::Stark128, DEFAULT_PARAMS);
    bad[31..33].copy_from_slice(&4u16.to_le_bytes());
    assert!(peek_header(&bad).is_err());

    // 2. ZK mode rejects W_R < 4
    let mut bad = dummy_envelope(ShrinkMode::Stark128Zk, DEFAULT_PARAMS);
    bad[31..33].copy_from_slice(&3u16.to_le_bytes());
    assert!(peek_header(&bad).unwrap_err().contains("randomizer width"));

    // 3. ZK mode rejects min_log_degree < 8
    let mut bad = dummy_envelope(ShrinkMode::Stark128Zk, DEFAULT_PARAMS);
    bad[33..35].copy_from_slice(&7u16.to_le_bytes());
    assert!(peek_header(&bad).unwrap_err().contains("min_log_degree"));

    // 4. ZK mode rejects log_blowup = 2 (below quotient_degree_for(true) = 8)
    let mut bad = dummy_envelope(ShrinkMode::Stark128Zk, DEFAULT_PARAMS);
    bad[17..19].copy_from_slice(&2u16.to_le_bytes()); // log_blowup = 2
    bad[25..27].copy_from_slice(&128u16.to_le_bytes()); // num_queries = 128
    bad[33..35].copy_from_slice(&9u16.to_le_bytes()); // min_log_degree(128, 3) = 9
    assert!(peek_header(&bad).unwrap_err().contains("log_blowup >= 3"));
  }

  #[test]
  fn default_and_compact_params_meet_128bit_security_floor() {
    for (name, params) in
      [("DEFAULT", DEFAULT_PARAMS), ("COMPACT", COMPACT_PARAMS)]
    {
      params.check().unwrap_or_else(|e| panic!("{name} failed floor: {e}"));
      let cp = params.commitment();
      let fp = params.fri();
      assert!(
        stark_key::security::johnson_millibits(&cp, &fp) >= 128_000,
        "{name} below 128b Johnson"
      );
      assert!(
        stark_key::security::provable_ud_millibits(&cp, &fp).unwrap() >= 80_000,
        "{name} below 80b UD"
      );
      assert!(
        stark_key::security::conjectured_bits(&cp, &fp) >= 220,
        "{name} below 220b conjectured"
      );
      assert_eq!(
        ShrinkMode::Stark128Zk.expected_min_log_degree(params.num_queries),
        8,
        "{name} min_zk_log_degree"
      );
    }
  }

  /// Endpoint 1 v1 path: the verifier admits only the two v1 presets, in both
  /// modes, and builds its backend from the constant, not the envelope.
  #[test]
  fn v1_verifier_admits_only_the_shipped_profiles() {
    let header = |mode, params| EnvelopeHeader {
      mode,
      params,
      zk_randomizer_width: 0,
      min_log_degree: 0,
      shrinker_vk_digest: [0; 32],
      inner_vk_digest: [0; 32],
      claim_digest: [0; 32],
      proof_len: 1,
    };
    for mode in [ShrinkMode::Stark128, ShrinkMode::Stark128Zk] {
      for params in [DEFAULT_PARAMS, COMPACT_PARAMS] {
        assert_eq!(
          admitted_v1_profile(&header(mode, params), &V1_PROFILES).unwrap(),
          (mode, params)
        );
      }
      // Floor-passing but not shipped: rejected.
      for params in [
        Parameters { num_queries: 79, ..DEFAULT_PARAMS },
        Parameters { query_proof_of_work_bits: 32, ..COMPACT_PARAMS },
        Parameters {
          log_blowup: 1,
          num_queries: 211,
          commit_proof_of_work_bits: 0,
          query_proof_of_work_bits: 32,
        },
      ] {
        params.check().unwrap();
        let err =
          admitted_v1_profile(&header(mode, params), &V1_PROFILES).unwrap_err();
        assert!(err.contains("not an admitted"), "{err}");
      }
    }
  }

  #[test]
  fn end_to_end_stark128_and_stark128_zk_roundtrip_and_negative_controls() {
    let Some(pkg_path) = find_verifier_package() else {
      eprintln!(
        "skipping full verifier .ixa integration test: no cached stark-export-*.ixa found (set IX_VERIFIER_ARTIFACT)"
      );
      return;
    };
    eprintln!("using compiled recursive verifier: {}", pkg_path.display());

    let (inner_key, inner_claims, inner_proof) =
      build_production_inner_v6_proof();
    let inner_vk_digest = *blake3::hash(&inner_key).as_bytes();
    let claim_digest = *blake3::hash(&inner_claims).as_bytes();
    eprintln!(
      "inner 128-bit v6 proof: {} bytes (key {} B, claims {} B)",
      inner_proof.len(),
      inner_key.len(),
      inner_claims.len()
    );

    let compiled = CompiledVerifier::from_package_path(&pkg_path).unwrap();
    let plan = compiled.trace_plan().unwrap();

    // Build BOTH shrinkers & verifiers for DEFAULT_PARAMS (lb=3, q=78, qpow=20).
    let shrinker_v6 = StarkShrinker::new(
      &compiled,
      &plan,
      ShrinkMode::Stark128,
      DEFAULT_PARAMS,
      None,
    )
    .unwrap();
    let shrinker_zk = StarkShrinker::new(
      &compiled,
      &plan,
      ShrinkMode::Stark128Zk,
      DEFAULT_PARAMS,
      None,
    )
    .unwrap();
    let verifier_v6 =
      StarkShrinkerVerifier::new(&plan, ShrinkMode::Stark128, DEFAULT_PARAMS)
        .unwrap();
    let verifier_zk =
      StarkShrinkerVerifier::new(&plan, ShrinkMode::Stark128Zk, DEFAULT_PARAMS)
        .unwrap();

    // Independently pinned VK digests MUST match between prover & verifier and
    // MUST differ across modes!
    assert_eq!(shrinker_v6.vk_digest(), verifier_v6.vk_digest());
    assert_eq!(shrinker_zk.vk_digest(), verifier_zk.vk_digest());
    assert_ne!(
      shrinker_v6.vk_digest(),
      shrinker_zk.vk_digest(),
      "v6 and v6-zk shrinker VK digests must be cryptographically distinct"
    );

    // 1. Roundtrip --stark-128 (transparent v6)
    let out_v6 = shrinker_v6
      .shrink(&inner_key, &inner_claims, &inner_proof)
      .expect("--stark-128 shrink failed");
    let rep_v6 = verifier_v6
      .verify(&out_v6.envelope_bytes, &inner_vk_digest, &claim_digest)
      .expect("--stark-128 verify failed");
    assert_eq!(rep_v6.mode, ShrinkMode::Stark128);
    assert!(rep_v6.banner().contains("NON-ZK"));
    assert!(rep_v6.banner().contains("~85-bit quantum"));
    assert!(!rep_v6.banner().contains("Post-quantum ready"));
    eprintln!(
      "\n[BENCH --stark-128 lb=3 q=78 qpow=20] prove={:.1}ms verify={:.2}ms envelope={}B raw={}B\n{}\n",
      out_v6.prove_ms,
      rep_v6.verify_ms,
      rep_v6.envelope_bytes,
      rep_v6.proof_bytes,
      rep_v6.banner()
    );

    // 2. Roundtrip --stark-128-zk (hiding v6-zk)
    let out_zk = shrinker_zk
      .shrink(&inner_key, &inner_claims, &inner_proof)
      .expect("--stark-128-zk shrink failed");
    let rep_zk = verifier_zk
      .verify(&out_zk.envelope_bytes, &inner_vk_digest, &claim_digest)
      .expect("--stark-128-zk verify failed");
    assert_eq!(rep_zk.mode, ShrinkMode::Stark128Zk);
    assert!(rep_zk.banner().contains("BLINDED"));
    assert!(rep_zk.banner().contains("no hiding property is stated"));
    assert!(rep_zk.banner().contains("W_R=4"));
    assert!(rep_zk.banner().contains("min_log_degree=8"));
    eprintln!(
      "\n[BENCH --stark-128-zk lb=3 q=78 qpow=20] prove={:.1}ms verify={:.2}ms envelope={}B raw={}B\n{}\n",
      out_zk.prove_ms,
      rep_zk.verify_ms,
      rep_zk.envelope_bytes,
      rep_zk.proof_bytes,
      rep_zk.banner()
    );

    // 3. v6-zk randomization check: a second proof of the exact same witness
    //    must produce different proof bytes while verifying identically.
    let out_zk_2 = shrinker_zk
      .shrink(&inner_key, &inner_claims, &inner_proof)
      .expect("--stark-128-zk second shrink failed");
    assert_ne!(
      out_zk.envelope_bytes, out_zk_2.envelope_bytes,
      "v6-zk proofs must be freshly randomized"
    );
    verifier_zk
      .verify(&out_zk_2.envelope_bytes, &inner_vk_digest, &claim_digest)
      .expect("--stark-128-zk second proof verify failed");

    // 4. Negative controls across BOTH modes
    for (label, env_bytes, verifier) in [
      ("--stark-128", &out_v6.envelope_bytes, &verifier_v6),
      ("--stark-128-zk", &out_zk.envelope_bytes, &verifier_zk),
    ] {
      // 4a. Wrong expected claim digest
      let mut wrong_claim = claim_digest;
      wrong_claim[0] ^= 0x01;
      assert!(
        verifier.verify(env_bytes, &inner_vk_digest, &wrong_claim).is_err(),
        "{label}: accepted wrong expected claim digest"
      );

      // 4b. Wrong expected inner VK digest
      let mut wrong_inner = inner_vk_digest;
      wrong_inner[0] ^= 0x01;
      assert!(
        verifier.verify(env_bytes, &wrong_inner, &claim_digest).is_err(),
        "{label}: accepted wrong expected inner VK digest"
      );

      // 4c. Tampered claim_digest inside envelope: rejected against the true
      // expected digest, and rejected by the proof check when the caller
      // expects the tampered digest itself.
      let mut tampered = ShrinkEnvelope::from_bytes(env_bytes).unwrap();
      tampered.header.claim_digest[0] ^= 0x80;
      let tampered_claim = tampered.header.claim_digest;
      let tampered_bytes = tampered.to_bytes().unwrap();
      assert!(
        verifier
          .verify(&tampered_bytes, &inner_vk_digest, &claim_digest)
          .is_err(),
        "{label}: accepted tampered claim digest in envelope"
      );
      assert!(
        verifier
          .verify(&tampered_bytes, &inner_vk_digest, &tampered_claim)
          .is_err(),
        "{label}: proof verified under a tampered claim digest"
      );

      // 4d. Tampered shrinker_vk_digest inside envelope
      let mut tampered = ShrinkEnvelope::from_bytes(env_bytes).unwrap();
      tampered.header.shrinker_vk_digest[31] ^= 0x01;
      let tampered_bytes = tampered.to_bytes().unwrap();
      assert!(
        verifier
          .verify(&tampered_bytes, &inner_vk_digest, &claim_digest)
          .is_err(),
        "{label}: accepted wrong shrinker VK digest"
      );

      // 4e. Bit-flipped proof bytes
      let mut tampered = ShrinkEnvelope::from_bytes(env_bytes).unwrap();
      let mid = tampered.proof_bytes.len() / 2;
      tampered.proof_bytes[mid] ^= 0x01;
      let tampered_bytes = tampered.to_bytes().unwrap();
      assert!(
        verifier
          .verify(&tampered_bytes, &inner_vk_digest, &claim_digest)
          .is_err(),
        "{label}: accepted corrupted proof bytes"
      );

      // 4f. Trailing byte appended
      let mut trailing = env_bytes.clone();
      trailing.push(0x42);
      assert!(
        verifier.verify(&trailing, &inner_vk_digest, &claim_digest).is_err(),
        "{label}: accepted trailing bytes"
      );
    }

    // 5. Cross-mode replay attacks (header level AND re-headered raw proof level!)
    assert!(
      verifier_zk
        .verify(&out_v6.envelope_bytes, &inner_vk_digest, &claim_digest)
        .unwrap_err()
        .contains("cross-mode"),
      "v6-zk verifier accepted v6 envelope"
    );
    assert!(
      verifier_v6
        .verify(&out_zk.envelope_bytes, &inner_vk_digest, &claim_digest)
        .unwrap_err()
        .contains("cross-mode"),
      "v6 verifier accepted v6-zk envelope"
    );
    // Re-header raw v6 proof bytes as v6-zk with the real pinned v6-zk VK digest!
    let raw_v6 =
      ShrinkEnvelope::from_bytes(&out_v6.envelope_bytes).unwrap().proof_bytes;
    let forged_as_zk = ShrinkEnvelope {
      header: EnvelopeHeader {
        mode: ShrinkMode::Stark128Zk,
        params: DEFAULT_PARAMS,
        zk_randomizer_width: 4,
        min_log_degree: 8,
        shrinker_vk_digest: *verifier_zk.vk_digest(),
        inner_vk_digest,
        claim_digest,
        proof_len: raw_v6.len() as u64,
      },
      proof_bytes: raw_v6,
    }
    .to_bytes()
    .unwrap();
    assert!(
      verifier_zk
        .verify(&forged_as_zk, &inner_vk_digest, &claim_digest)
        .is_err(),
      "v6-zk verifier accepted re-headered raw v6 proof"
    );
    // Re-header raw v6-zk proof bytes as v6 with the real pinned v6 VK digest!
    let raw_zk =
      ShrinkEnvelope::from_bytes(&out_zk.envelope_bytes).unwrap().proof_bytes;
    let forged_as_v6 = ShrinkEnvelope {
      header: EnvelopeHeader {
        mode: ShrinkMode::Stark128,
        params: DEFAULT_PARAMS,
        zk_randomizer_width: 0,
        min_log_degree: 0,
        shrinker_vk_digest: *verifier_v6.vk_digest(),
        inner_vk_digest,
        claim_digest,
        proof_len: raw_zk.len() as u64,
      },
      proof_bytes: raw_zk,
    }
    .to_bytes()
    .unwrap();
    assert!(
      verifier_v6
        .verify(&forged_as_v6, &inner_vk_digest, &claim_digest)
        .is_err(),
      "v6 verifier accepted re-headered raw v6-zk proof"
    );

    // 6. Prover fail-closed on v5 / tampered inner inputs
    let mut v5_key = inner_key.clone();
    v5_key[8..10].copy_from_slice(&5u16.to_le_bytes()); // protocol_version = 5
    assert!(
      shrinker_v6.shrink(&v5_key, &inner_claims, &inner_proof).is_err(),
      "shrinker accepted v5 inner key"
    );
    let mut bad_claims = inner_claims.clone();
    let last = bad_claims.len() - 1;
    bad_claims[last] ^= 0x01;
    assert!(
      shrinker_zk.shrink(&inner_key, &bad_claims, &inner_proof).is_err(),
      "shrinker accepted mismatched inner claims"
    );

    // 7. Also benchmark COMPACT_PARAMS (lb=4, q=66, qpow=20) on both modes!
    for mode in [ShrinkMode::Stark128, ShrinkMode::Stark128Zk] {
      let shrinker =
        StarkShrinker::new(&compiled, &plan, mode, COMPACT_PARAMS, None)
          .unwrap();
      let verifier =
        StarkShrinkerVerifier::new(&plan, mode, COMPACT_PARAMS).unwrap();
      let out =
        shrinker.shrink(&inner_key, &inner_claims, &inner_proof).unwrap();
      let rep = verifier
        .verify(&out.envelope_bytes, &inner_vk_digest, &claim_digest)
        .unwrap();
      eprintln!(
        "[BENCH {} lb=4 q=66 qpow=20] prove={:.1}ms verify={:.2}ms envelope={}B raw={}B",
        mode.cli_flag(),
        out.prove_ms,
        rep.verify_ms,
        rep.envelope_bytes,
        rep.proof_bytes,
      );
    }
  }
}
