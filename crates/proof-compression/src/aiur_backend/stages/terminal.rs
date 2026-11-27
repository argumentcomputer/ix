//! `plonk`: the terminal relation proved over Lean's formally checked
//! constraint system (`ix-aiur-scs-v1`).
//!
//! The stage runs the pure-Rust (+ optional Ix-CUDA) native PLONK + BSB22
//! backend (`ix-aiur-native-plonk-v1`) on both BN254 and BLS12-381 with zero
//! Go, CGo, or `bindgen` dependencies. Legacy gnark manifests
//! (`ix-aiur-scs-artifacts-v1`) are retired and rejected with a clear error
//! pointing to `ix-aiur-native-plonk-v1`.
//!
//! Manifest fields: `artifact`, `prepared_manifest` (the prepared directory's
//! `manifest.json`), `scs` (`path` and `sha256`), optional `policy` (product,
//! required for native BN254 circuits consuming narrow KZG proof advice),
//! optional `backend` (must be `"native"` when present), optional `cuda`
//! (boolean; defaults to `cfg!(feature = "cuda")` and supports Ix-CUDA on both
//! BN254 and BLS12-381), optional `entry` (overrides
//! `CompressFinalNarrow::verify_accumulator_v1`), optional `advice` (product
//! `.ixa` bound via `ixcc::register_advice_program`), optional `field`
//! (`"bn254"` default or `"bls12-381"`).
//!
//! The prepared directory is reused, never rebuilt: its manifest must pin this
//! SCS file's digest.

use super::{
  Error, Handoff, Product, Stage,
  exports::{Field, parse_optional_entry, parse_stage_field},
};
use crate::{
  aiur_backend::{
    Bls12381, Bn254, bls12_381,
    compress_bn::{PackedCapacity, PackedPolicy},
    fq, g1,
    kzg::Compiler,
    kzg_advice as wire,
    pairing::final_program::{
      ACCUMULATOR_WORDS, NARROW_ACCUMULATOR_ENTRY, statement_arguments,
    },
    plonk::{native, scs},
  },
  kzg::{
    Scalar,
    curve::{Bls12381 as Bls12381Curve, Bn254 as Bn254Curve, KzgCurve},
    field::{Bls12381Scalar, CurveScalar},
  },
  pipeline::SetupConfig,
};
use aiur::{
  Execution, FieldWord, artifact::WidePackage, field::FieldBackend,
  hints::HintChannels, maps::MapOverrides, trace::TracePlan,
};
use ark_ec::pairing::Pairing;
use serde_json::{Value, json};
use sha2::{Digest, Sha256};
use std::{
  fs,
  path::{Path, PathBuf},
  sync::Arc,
  time::Instant,
};

const LEGACY_GNARK_MANIFEST_FORMAT: &str = "ix-aiur-scs-artifacts-v1";

fn retired_gnark_error() -> Error {
  format!(
    "legacy gnark PLONK backend ({LEGACY_GNARK_MANIFEST_FORMAT}) has been \
     retired and removed; prepare native PLONK artifacts with format {:?}",
    native::NATIVE_MANIFEST_FORMAT,
  )
}

fn validate_optional_backend(spec: &Value) -> Result<(), Error> {
  match &spec["backend"] {
    Value::Null => Ok(()),
    Value::String(name) => match name.as_str() {
      "native" => Ok(()),
      "gnark" => Err(retired_gnark_error()),
      other => Err(format!(
        "unknown plonk stage backend {other:?}; expected \"native\""
      )),
    },
    _ => Err("manifest plonk backend must be a string (\"native\")".into()),
  }
}

fn validate_manifest_format(manifest_bytes: &[u8]) -> Result<(), Error> {
  let value: Value = serde_json::from_slice(manifest_bytes)
    .map_err(|e| format!("prepared_manifest JSON: {e}"))?;
  let fmt = value
    .get("format")
    .and_then(Value::as_str)
    .or_else(|| value.get("Format").and_then(Value::as_str))
    .ok_or("prepared_manifest missing string \"format\" / \"Format\" field")?;
  match fmt {
    native::NATIVE_MANIFEST_FORMAT => Ok(()),
    LEGACY_GNARK_MANIFEST_FORMAT => Err(retired_gnark_error()),
    other => Err(format!(
      "unsupported prepared_manifest format {other:?}; expected {:?}",
      native::NATIVE_MANIFEST_FORMAT,
    )),
  }
}

fn validate_backend(spec: &Value, manifest_bytes: &[u8]) -> Result<(), Error> {
  validate_optional_backend(spec)?;
  validate_manifest_format(manifest_bytes)
}

fn parse_native_cuda(spec: &Value) -> Result<bool, Error> {
  match &spec["cuda"] {
    Value::Null => Ok(cfg!(feature = "cuda")),
    Value::Bool(flag) => Ok(*flag),
    _ => Err("manifest cuda must be a boolean".into()),
  }
}

/// Resolve the prepared artifacts directory for a native PLONK manifest.
///
/// `native::prepare_to_dir` writes `manifest.json` alongside `verifying-key.bin`
/// and `proving-key.bin`; also accepts a nested `prepared/` layout beside
/// `manifest.json`.
fn resolve_native_prepared_dir(manifest_path: &Path) -> Result<PathBuf, Error> {
  let parent = manifest_path.parent().ok_or("prepared manifest path")?;
  if parent.join("verifying-key.bin").is_file() {
    Ok(parent.to_path_buf())
  } else {
    let nested = parent.join("prepared");
    if nested.join("verifying-key.bin").is_file() {
      Ok(nested)
    } else {
      Ok(parent.to_path_buf())
    }
  }
}

struct Phases(serde_json::Map<String, Value>);

impl Phases {
  fn record(&mut self, name: &str, started: Instant) {
    self.0.insert(
      name.into(),
      json!({"seconds": started.elapsed().as_secs_f64(),
        "peak_rss_gb_after": super::peak_rss_gb()}),
    );
  }
}

fn check_bn254_native_outputs(
  scs_outputs: usize,
  record_output: &[Scalar],
  anchors: &[ark_bn254::G2Affine; 2],
) -> Result<(), Error> {
  match scs_outputs {
    // Self-contained circuit (e.g. in-circuit pairing): no external pairing
    // output words required; `record.output` may be empty or a scalar status.
    0 => Ok(()),
    ACCUMULATOR_WORDS => {
      if record_output.len() != ACCUMULATOR_WORDS {
        return Err(format!(
          "BN254 terminal accumulator needs {ACCUMULATOR_WORDS} words, got {}",
          record_output.len(),
        ));
      }
      let pair =
        [g1::decode(&record_output[..9])?, g1::decode(&record_output[9..])?];
      if ark_bn254::Bn254::multi_pairing(pair, *anchors).0
        != <ark_bn254::Bn254 as Pairing>::TargetField::from(1u8)
      {
        return Err(
          "terminal accumulator fails the Ignition pairing check".into(),
        );
      }
      Ok(())
    },
    other => Err(format!(
      "unsupported BN254 native PLONK output count {other}; expected 0 \
       (self-contained) or {ACCUMULATOR_WORDS} (external pairing accumulator)"
    )),
  }
}

fn check_bls12_381_native_outputs(
  scs_outputs: usize,
  record_output: &[Bls12381Scalar],
  anchors: &[ark_bls12_381::G2Affine; 2],
) -> Result<(), Error> {
  match scs_outputs {
    // Self-contained circuit (e.g. in-circuit pairing): no external pairing
    // output words required; `record.output` may be empty or a scalar status.
    0 => Ok(()),
    bls12_381::ACCUMULATOR_WORDS => {
      bls12_381::check_pairing(record_output, *anchors)
    },
    other => Err(format!(
      "unsupported BLS12-381 native PLONK output count {other}; expected 0 \
       (self-contained) or {} (external pairing accumulator)",
      bls12_381::ACCUMULATOR_WORDS,
    )),
  }
}

fn read_verified_native_inputs<C: KzgCurve>(
  prepared_dir: &Path,
  manifest: &native::PreparedManifest,
  scs: &native::ScsFile<C>,
) -> Result<scs::Inputs, Error> {
  let layout_bytes = fs::read(prepared_dir.join("inputs.json"))
    .map_err(|e| format!("inputs.json: {e}"))?;
  if super::sha256_hex(&layout_bytes) != manifest.inputs_sha256 {
    return Err("prepared inputs.json differs from manifest SHA-256".into());
  }
  let inputs: scs::Inputs = serde_json::from_slice(&layout_bytes)
    .map_err(|e| format!("inputs.json: {e}"))?;
  if inputs != scs.to_inputs() {
    return Err("prepared inputs.json differs from SCS input layout".into());
  }
  Ok(inputs)
}

fn native_expected_publics<B, C>(
  plan: &TracePlan<'_, B>,
  entry: &str,
  record: &Execution<B>,
  arguments: &[CurveScalar<C>],
  scs_publics: usize,
  scs_outputs: usize,
) -> Result<Vec<C::Fr>, Error>
where
  B: FieldBackend<Element = CurveScalar<C>, Word = FieldWord>,
  C: KzgCurve,
{
  let public_args = plan.public_args(record, entry, arguments)?;
  let claim = plan.public_claim(entry, &public_args, &record.output)?;
  if claim.len() != 2 + scs_publics + scs_outputs {
    return Err(format!(
      "public claim width {} differs from SCS root table \
       ({scs_publics} publics + {scs_outputs} outputs)",
      claim.len().saturating_sub(2),
    ));
  }
  if scs_publics < arguments.len()
    || &claim[2..2 + arguments.len()] != arguments
  {
    return Err(
      "SCS public inputs do not start with the stage statement".into(),
    );
  }
  Ok(claim[2..2 + scs_publics].iter().map(|v| v.0).collect())
}

struct NativeProofChecks {
  proof: native::ProofBundle,
  key: Vec<u8>,
  key_sha256: String,
  wrong_statement_refused_by_prover: bool,
  wrong_statement_rejected_by_verifier: bool,
  solidity_wrong_statement_rejected: bool,
  verifying_key_is_prepared: bool,
}

fn prove_verify_native_with<C: KzgCurve>(
  prover: &native::NativeProver<C>,
  prepared_dir: &Path,
  manifest: &native::PreparedManifest,
  witness: &[u8],
  expected_publics: &[C::Fr],
  phases: &mut Phases,
  run_prove: impl Fn(&[u8], &[C::Fr]) -> Result<native::ProofBundle, String>,
) -> Result<NativeProofChecks, Error> {
  if expected_publics.is_empty() {
    return Err("native PLONK circuit has no public inputs".into());
  }
  let started = Instant::now();
  let proof = run_prove(witness, expected_publics)?;
  phases.record("prove", started);

  let mut wrong = expected_publics.to_vec();
  wrong[0] += C::FR_ONE;
  let refused = run_prove(witness, &wrong).is_err();

  let started = Instant::now();
  let key = fs::read(prepared_dir.join("verifying-key.bin"))
    .map_err(|e| format!("verifying-key.bin: {e}"))?;
  let key_sha256 = super::sha256_hex(&key);
  let key_pin: [u8; 32] = Sha256::digest(&key).into();
  let vk = prover.vk();
  native::verify_native_bytes(vk, &key_pin, &proof.native, expected_publics)?;
  native::verify_solidity_bytes(
    vk,
    &key_pin,
    &proof.solidity,
    expected_publics,
  )?;
  phases.record("verify", started);

  let native_rejected =
    native::verify_native_bytes(vk, &key_pin, &proof.native, &wrong).is_err();
  let sol_rejected =
    native::verify_solidity_bytes(vk, &key_pin, &proof.solidity, &wrong)
      .is_err();
  let prepared_key = key_sha256 == manifest.vk_sha256
    && key_pin == prover.vk_sha256()
    && key_pin == vk.sha256();

  Ok(NativeProofChecks {
    proof,
    key,
    key_sha256,
    wrong_statement_refused_by_prover: refused,
    wrong_statement_rejected_by_verifier: native_rejected && sol_rejected,
    solidity_wrong_statement_rejected: sol_rejected,
    verifying_key_is_prepared: prepared_key,
  })
}

struct NativeFinalizeContext<'a, C: KzgCurve> {
  stage: &'a Stage<'a>,
  prover: &'a native::NativeProver<C>,
  prepared_dir: &'a Path,
  manifest: &'a native::PreparedManifest,
  scs_path: &'a Path,
  scs_sha256: &'a str,
  entry: &'a str,
  artifact_path: &'a Path,
  artifact_blake3: &'a str,
  statement_bytes: [u8; 32],
  narrow_stage: u32,
  use_cuda: bool,
  witness: &'a [u8],
  expected_publics: &'a [C::Fr],
  outputs_decimal: Vec<String>,
  phases: Phases,
}

fn finalize_native_stage<C: KzgCurve>(
  mut ctx: NativeFinalizeContext<'_, C>,
) -> Result<Handoff, Error> {
  let checks = prove_verify_native_with(
    ctx.prover,
    ctx.prepared_dir,
    ctx.manifest,
    ctx.witness,
    ctx.expected_publics,
    &mut ctx.phases,
    |w, pubs| ctx.stage.gpu(|| ctx.prover.prove_binary(w, pubs)),
  )?;

  ctx.stage.stages.checks.set(
    "plonk_wrong_statement_refused_by_prover",
    checks.wrong_statement_refused_by_prover,
  );
  ctx.stage.stages.checks.set(
    "plonk_wrong_statement_rejected_by_verifier",
    checks.wrong_statement_rejected_by_verifier,
  );
  ctx
    .stage
    .stages
    .checks
    .set("plonk_verifying_key_is_prepared", checks.verifying_key_is_prepared);

  if !checks.wrong_statement_refused_by_prover {
    return Err(format!(
      "native {} PLONK prover accepted a changed statement",
      C::NAME
    ));
  }
  if !checks.wrong_statement_rejected_by_verifier {
    return Err(format!(
      "native {} PLONK verifier accepted a changed statement",
      C::NAME
    ));
  }
  if !checks.verifying_key_is_prepared {
    return Err(
      "the verifying key differs from the prepared manifest's".into(),
    );
  }

  ctx.stage.write("proof.bin", &checks.proof.native)?;
  ctx.stage.write("proof.solidity.bin", &checks.proof.solidity)?;
  let summary = json!({
    "format": "ix-aiur-narrow-terminal-plonk-v1",
    "prover": "native",
    "curve": C::NAME,
    "circuit": "ix-aiur-scs-v1",
    "scs": ctx.scs_path,
    "scs_sha256": ctx.scs_sha256,
    "entry": ctx.entry,
    "artifact": ctx.artifact_path,
    "artifact_blake3": ctx.artifact_blake3,
    "statement": super::hex(&ctx.statement_bytes),
    "backend": if ctx.use_cuda { "cuda" } else { "cpu" },
    "constraints": ctx.manifest.gates,
    "gates": ctx.manifest.gates,
    "domain": ctx.manifest.domain,
    "public_inputs": ctx.manifest.public_inputs,
    "outputs": ctx.manifest.outputs,
    "commitments": ctx.manifest.commits,
    "witness_bytes": ctx.witness.len(),
    "witness_sha256": super::sha256_hex(ctx.witness),
    "srs_blake3": ctx.manifest.srs_blake3,
    "verifying_key_sha256": checks.key_sha256,
    "proof_bytes": checks.proof.native.len(),
    "solidity_proof_bytes": checks.proof.solidity.len(),
    "public_inputs_decimal": ctx
      .expected_publics
      .iter()
      .map(ToString::to_string)
      .collect::<Vec<_>>(),
    "outputs_decimal": ctx.outputs_decimal,
    "wrong_statement_refused_by_prover": checks.wrong_statement_refused_by_prover,
    "wrong_statement_rejected_by_verifier": checks.wrong_statement_rejected_by_verifier,
    "solidity_proof_verified": true,
    "solidity_wrong_statement_rejected": checks.solidity_wrong_statement_rejected,
    "prover_timings": checks.proof.timings,
    "phases": ctx.phases.0,
    "peak_rss_gb": super::peak_rss_gb(),
  });
  ctx.stage.write_json("summary.json", &summary)?;
  Ok(Handoff {
    key: checks.key,
    claims: Vec::new(),
    proof: checks.proof.native,
    stage: ctx.narrow_stage + 1,
    statement: Some(ctx.statement_bytes),
    solidity: checks.proof.solidity,
  })
}

#[allow(clippy::too_many_lines)]
fn run_native_bn254(
  stage: &Stage<'_>,
  entry: &str,
  advice_bytes: Option<&[u8]>,
  manifest_file: &Product,
) -> Result<Handoff, Error> {
  let spec = &stage.spec.spec;
  let use_cuda = parse_native_cuda(spec)?;
  let scs_path = stage.stages.manifest.path(&spec["scs"]["path"])?;
  let scs_pin = spec["scs"]["sha256"].as_str().ok_or("scs.sha256")?.to_owned();
  let manifest: native::PreparedManifest =
    serde_json::from_slice(&manifest_file.bytes)
      .map_err(|e| format!("native prepared_manifest: {e}"))?;
  if manifest.scs_sha256 != scs_pin {
    return Err(format!(
      "prepared manifest SCS SHA-256 {} differs from pinned {scs_pin}",
      manifest.scs_sha256,
    ));
  }
  let prepared_dir = resolve_native_prepared_dir(&manifest_file.path)?;
  let mut phases = Phases(serde_json::Map::new());

  let started = Instant::now();
  let artifact = stage.product("artifact")?;
  let pin = blake3::hash(&artifact.bytes);
  let package = WidePackage::decode(&artifact.bytes)?;
  let trace = package.trace.ok_or("missing trace")?;
  let mut program = package.program.check_with(Bn254)?;
  program.track_depth(&trace)?;
  program.entry(entry)?;
  let plan = TracePlan::new(Arc::new(program), trace)?;
  let advice_program = match advice_bytes {
    Some(bytes) => {
      let pkg = WidePackage::decode(bytes)?;
      let mut prog = pkg.program.check_with(Bn254)?;
      if let Some(t) = &pkg.trace {
        prog.track_depth(t)?;
      }
      Some(prog)
    },
    None => None,
  };
  let policy_context = if spec["policy"].is_null() {
    None
  } else {
    let setup = SetupConfig::from_env(false).map_err(|e| e.to_string())?;
    let capacity = PackedCapacity {
      log_cap: 1,
      quotient_degree: 1,
      lookup_quotient_budget: None,
    };
    let config = capacity.config(&setup)?;
    let parameters =
      multi_stark::config::ProofConfig::pcs(&config).parameters();
    let policy_file = stage.product("policy")?;
    let _policy =
      PackedPolicy::from_chain_bytes(parameters, &policy_file.bytes)?;
    Some((config, policy_file.bytes))
  };
  phases.record("setup", started);

  let started = Instant::now();
  let accel = if use_cuda {
    stage.gpu(|| native::PlonkAccelerator::<Bn254Curve>::new(true))?
  } else {
    native::PlonkAccelerator::<Bn254Curve>::cpu()
  };
  let prover = native::NativeProver::<Bn254Curve>::open(
    &prepared_dir,
    &scs_path,
    &manifest,
    accel,
  )?;
  let scs_sha256 = prover.scs().sha256_hex();
  if scs_sha256 != scs_pin {
    return Err(format!(
      "SCS SHA-256 {scs_sha256} differs from the pinned {scs_pin}"
    ));
  }
  if let Some((ref config, _)) = policy_context {
    let parameters = multi_stark::config::ProofConfig::pcs(config).parameters();
    prover.vk().check_anchors(parameters)?;
  }
  let inputs =
    read_verified_native_inputs(&prepared_dir, &manifest, prover.scs())?;
  let scs_outputs = prover.scs().outputs.len();
  if scs_outputs != 0 && scs_outputs != ACCUMULATOR_WORDS {
    return Err(format!(
      "unsupported BN254 native PLONK output count {scs_outputs}; expected 0 \
       (self-contained) or {ACCUMULATOR_WORDS} (external pairing accumulator)"
    ));
  }
  phases.record("load", started);
  stage.reserve(1);

  let started = Instant::now();
  let (narrow, _) = stage.input()?;
  phases.record("wait", started);
  stage.cancelled()?;
  stage.reserve(2);

  let started = Instant::now();
  let statement_bytes =
    narrow.statement.ok_or("the narrow stage passed no statement")?;
  let mut hints = HintChannels::new();
  aiur::library::u32::register(&mut hints, Bn254)?;
  aiur::library::u64::register(&mut hints, Bn254)?;
  fq::register(&mut hints)?;
  g1::register(&mut hints)?;
  wire::register(&mut hints)?;
  aiur::library::ixcc::register(&mut hints, Bn254)?;
  if let Some((_, policy_bytes)) = policy_context {
    wire::Inputs::new(
      narrow.key.clone(),
      narrow.claims.clone(),
      narrow.proof.clone(),
      policy_bytes,
    )?
    .register(&mut hints)?;
  }
  if let Some(advice_program) = advice_program {
    aiur::library::ixcc::register_advice_program(
      &mut hints,
      plan.program(),
      advice_program,
    )?;
  }
  let mut maps = MapOverrides::new();
  aiur::library::u8::register_maps(plan.program(), &mut maps)?;
  let arguments = statement_arguments(&statement_bytes).to_vec();
  let record = plan
    .program()
    .prepare_hint_channels(&[], &hints)?
    .with_map_overrides(&maps)?
    .execute(entry, arguments.clone())
    .map_err(|e| e.to_string())?;
  let anchors = [prover.vk().g2, prover.vk().tau_g2];
  check_bn254_native_outputs(scs_outputs, &record.output, &anchors)?;
  phases.record("execute", started);

  let started = Instant::now();
  let expected_publics = native_expected_publics::<Bn254, Bn254Curve>(
    &plan,
    entry,
    &record,
    &arguments,
    prover.scs().publics,
    scs_outputs,
  )?;
  let compiler = Compiler::new(&plan)?;
  let capacities: Vec<usize> =
    compiler.row_counts(&record)?.into_iter().map(|rows| rows.max(1)).collect();
  let witness =
    scs::Witness::new_fitting(&plan, compiler, &capacities, entry, inputs)?
      .binary(&record, &arguments)?;
  phases.record("witness", started);

  finalize_native_stage(NativeFinalizeContext {
    stage,
    prover: &prover,
    prepared_dir: &prepared_dir,
    manifest: &manifest,
    scs_path: &scs_path,
    scs_sha256: &scs_sha256,
    entry,
    artifact_path: &artifact.path,
    artifact_blake3: pin.to_hex().as_str(),
    statement_bytes,
    narrow_stage: narrow.stage,
    use_cuda,
    witness: &witness,
    expected_publics: &expected_publics,
    outputs_decimal: record.output.iter().map(|v| v.0.to_string()).collect(),
    phases,
  })
}

#[allow(clippy::too_many_lines)]
fn run_native_bls12_381(
  stage: &Stage<'_>,
  entry: &str,
  advice_bytes: Option<&[u8]>,
  manifest_file: &Product,
) -> Result<Handoff, Error> {
  let spec = &stage.spec.spec;
  let use_cuda = parse_native_cuda(spec)?;
  let scs_path = stage.stages.manifest.path(&spec["scs"]["path"])?;
  let scs_pin = spec["scs"]["sha256"].as_str().ok_or("scs.sha256")?.to_owned();
  let manifest: native::PreparedManifest =
    serde_json::from_slice(&manifest_file.bytes)
      .map_err(|e| format!("native prepared_manifest: {e}"))?;
  if manifest.scs_sha256 != scs_pin {
    return Err(format!(
      "prepared manifest SCS SHA-256 {} differs from pinned {scs_pin}",
      manifest.scs_sha256,
    ));
  }
  let prepared_dir = resolve_native_prepared_dir(&manifest_file.path)?;
  let mut phases = Phases(serde_json::Map::new());

  let started = Instant::now();
  let artifact = stage.product("artifact")?;
  let pin = blake3::hash(&artifact.bytes);
  let plan = bls12_381::load_trace_plan(&artifact.bytes)?;
  plan.program().entry(entry)?;
  let advice_program = match advice_bytes {
    Some(bytes) => Some(bls12_381::load_program(bytes)?),
    None => None,
  };
  phases.record("setup", started);

  let started = Instant::now();
  let accel = if use_cuda {
    stage.gpu(|| native::PlonkAccelerator::<Bls12381Curve>::new(true))?
  } else {
    native::PlonkAccelerator::<Bls12381Curve>::cpu()
  };
  let prover = native::NativeProver::<Bls12381Curve>::open(
    &prepared_dir,
    &scs_path,
    &manifest,
    accel,
  )?;
  let scs_sha256 = prover.scs().sha256_hex();
  if scs_sha256 != scs_pin {
    return Err(format!(
      "SCS SHA-256 {scs_sha256} differs from the pinned {scs_pin}"
    ));
  }
  let inputs =
    read_verified_native_inputs(&prepared_dir, &manifest, prover.scs())?;
  let scs_outputs = prover.scs().outputs.len();
  if scs_outputs != 0 && scs_outputs != bls12_381::ACCUMULATOR_WORDS {
    return Err(format!(
      "unsupported BLS12-381 native PLONK output count {scs_outputs}; \
       expected 0 (self-contained) or {} (external pairing accumulator)",
      bls12_381::ACCUMULATOR_WORDS,
    ));
  }
  phases.record("load", started);
  stage.reserve(1);

  let started = Instant::now();
  let (narrow, _) = stage.input()?;
  phases.record("wait", started);
  stage.cancelled()?;
  stage.reserve(2);

  let started = Instant::now();
  let statement_bytes =
    narrow.statement.ok_or("the narrow stage passed no statement")?;
  let mut hints = HintChannels::new();
  bls12_381::register_standard_hints(&mut hints)?;
  if let Some(advice_program) = advice_program {
    aiur::library::ixcc::register_advice_program(
      &mut hints,
      plan.program(),
      advice_program,
    )?;
  }
  let mut maps = MapOverrides::new();
  aiur::library::u8::register_maps(plan.program(), &mut maps)?;
  let arguments = bls12_381::statement_arguments(&statement_bytes).to_vec();
  let record = plan
    .program()
    .prepare_hint_channels(&[], &hints)?
    .with_map_overrides(&maps)?
    .execute(entry, arguments.clone())
    .map_err(|e| e.to_string())?;
  let anchors = [prover.vk().g2, prover.vk().tau_g2];
  check_bls12_381_native_outputs(scs_outputs, &record.output, &anchors)?;
  phases.record("execute", started);

  let started = Instant::now();
  let expected_publics = native_expected_publics::<Bls12381, Bls12381Curve>(
    &plan,
    entry,
    &record,
    &arguments,
    prover.scs().publics,
    scs_outputs,
  )?;
  let witness = scs::Bls12381Witness::new(&plan, entry, inputs)?
    .binary(&record, &arguments)?;
  phases.record("witness", started);

  finalize_native_stage(NativeFinalizeContext {
    stage,
    prover: &prover,
    prepared_dir: &prepared_dir,
    manifest: &manifest,
    scs_path: &scs_path,
    scs_sha256: &scs_sha256,
    entry,
    artifact_path: &artifact.path,
    artifact_blake3: pin.to_hex().as_str(),
    statement_bytes,
    narrow_stage: narrow.stage,
    use_cuda,
    witness: &witness,
    expected_publics: &expected_publics,
    outputs_decimal: record.output.iter().map(|v| v.0.to_string()).collect(),
    phases,
  })
}

pub(super) fn run(stage: &Stage<'_>) -> Result<Handoff, Error> {
  let spec = &stage.spec.spec;
  let field = parse_stage_field(spec)?;
  let entry_override = parse_optional_entry(spec)?;
  validate_optional_backend(spec)?;
  let advice_file = if spec["advice"].is_null() {
    None
  } else {
    Some(stage.product("advice")?)
  };
  let advice_bytes = advice_file.as_ref().map(|p| p.bytes.as_slice());
  let entry = entry_override.unwrap_or(NARROW_ACCUMULATOR_ENTRY);
  let manifest_file = stage.product("prepared_manifest")?;
  validate_backend(spec, &manifest_file.bytes)?;

  match field {
    Field::Bn254 => {
      run_native_bn254(stage, entry, advice_bytes, &manifest_file)
    },
    Field::Bls12381 => {
      run_native_bls12_381(stage, entry, advice_bytes, &manifest_file)
    },
    Field::Goldilocks => {
      Err("plonk stage field must be \"bn254\" or \"bls12-381\"".into())
    },
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::{
    aiur_backend::plonk::{
      native::{
        NativeProver, PackedGate, PlonkAccelerator, ScsBuilder, ScsFile,
        WireHint, domain_size_for_scs, prepare_to_dir,
        scs_file::{SEL_L, SEL_M, SEL_O, SEL_R},
      },
      scs::{Table, serialize_binary_witness},
    },
    kzg::{
      Srs, VerifierParams,
      srs::filecoin::{
        FILECOIN_PREFIX_2P8_FIXTURE, FILECOIN_PREFIX_2P8_MANIFEST_BLAKE3,
        filecoin_anchors, load_filecoin_cache,
      },
    },
  };
  use aiur::{
    Program,
    bytecode::{Binary, Entry, Function, Instruction as I, Type},
    trace::{
      Chip, ChipDepth, ColumnWrite, FunctionPlan, Polynomial, TraceArtifact,
    },
    value::IoType,
  };
  use std::sync::atomic::{AtomicU64, Ordering};

  static TEST_SEQ: AtomicU64 = AtomicU64::new(0);

  fn temp_dir(label: &str) -> PathBuf {
    let seq = TEST_SEQ.fetch_add(1, Ordering::Relaxed);
    let dir = std::env::temp_dir().join(format!(
      "ix-terminal-plonk-test-{label}-{}-{seq}",
      std::process::id(),
    ));
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).unwrap();
    dir
  }

  /// Build a synthetic `ix-aiur-scs-v1` circuit with 2 public inputs
  /// (`pub0 + pub1 == x * y + 5`), `num_outputs` output wires (`0`, `18`, or
  /// `22`), BSB22 commitment, gamma challenge, bit decomposition, and quotient
  /// gates.
  fn build_synthetic_scs<C: KzgCurve>(
    num_outputs: usize,
    output_values: &[C::Fr],
  ) -> (Vec<u8>, Vec<C::Fr>, Vec<C::Fr>) {
    assert_eq!(output_values.len(), num_outputs);
    let coeffs = vec![
      C::FR_ONE,
      C::FR_NEG_ONE,
      C::Fr::from(2u64),
      C::Fr::from(4u64),
      C::Fr::from(8u64),
    ];
    let publics = 2usize;
    let outputs: Vec<u32> = (0..num_outputs)
      .map(|k| u32::try_from(publics + k).expect("fits u32"))
      .collect();
    let w_x = u32::try_from(publics + num_outputs).expect("fits u32");
    let w_y = w_x + 1;
    let w_m = w_x + 2;
    let cells = (w_m as usize) + 1;

    let mut hints = vec![WireHint::Input; cells];
    let mut gates = Vec::new();
    let mut add_wire = |hint: WireHint| -> u32 {
      let id = u32::try_from(hints.len()).expect("fits u32");
      hints.push(hint);
      id
    };

    let g_prod = u32::try_from(gates.len()).expect("fits u32");
    let w_prod = add_wire(WireHint::Solve { gate: g_prod });
    gates.push(PackedGate {
      a: w_x,
      b: w_y,
      c: w_prod,
      sel: SEL_M | SEL_O,
      alpha_id: 0,
      beta_id: 0,
      omega_id: 1,
      qc: 0,
    });

    let g_diff = u32::try_from(gates.len()).expect("fits u32");
    let w_diff = add_wire(WireHint::Solve { gate: g_diff });
    gates.push(PackedGate {
      a: w_prod,
      b: 0,
      c: w_diff,
      sel: SEL_L | SEL_R | SEL_O,
      alpha_id: 0,
      beta_id: 1,
      omega_id: 1,
      qc: 5,
    });
    gates.push(PackedGate {
      a: w_diff,
      b: 1,
      c: 0,
      sel: SEL_L | SEL_R,
      alpha_id: 0,
      beta_id: 1,
      omega_id: 0,
      qc: 0,
    });
    let pre = gates.len();

    let w_gamma = add_wire(WireHint::Challenge);
    let mut bits = [0u32; 4];
    for (bit, slot) in bits.iter_mut().enumerate() {
      let wb = add_wire(WireHint::Bit {
        wire: w_gamma,
        bit: u32::try_from(bit).expect("fits u32"),
      });
      *slot = wb;
      gates.push(PackedGate {
        a: wb,
        b: wb,
        c: wb,
        sel: SEL_M | SEL_O,
        alpha_id: 0,
        beta_id: 0,
        omega_id: 1,
        qc: 0,
      });
    }
    let g_b01 = u32::try_from(gates.len()).expect("fits u32");
    let w_b01 = add_wire(WireHint::Solve { gate: g_b01 });
    gates.push(PackedGate {
      a: bits[0],
      b: bits[1],
      c: w_b01,
      sel: SEL_L | SEL_R | SEL_O,
      alpha_id: 0,
      beta_id: 2,
      omega_id: 1,
      qc: 0,
    });
    let g_b012 = u32::try_from(gates.len()).expect("fits u32");
    let w_b012 = add_wire(WireHint::Solve { gate: g_b012 });
    gates.push(PackedGate {
      a: w_b01,
      b: bits[2],
      c: w_b012,
      sel: SEL_L | SEL_R | SEL_O,
      alpha_id: 0,
      beta_id: 3,
      omega_id: 1,
      qc: 0,
    });
    let g_beta = u32::try_from(gates.len()).expect("fits u32");
    let w_beta = add_wire(WireHint::Solve { gate: g_beta });
    gates.push(PackedGate {
      a: w_b012,
      b: bits[3],
      c: w_beta,
      sel: SEL_L | SEL_R | SEL_O,
      alpha_id: 0,
      beta_id: 4,
      omega_id: 1,
      qc: 0,
    });

    let g_d0 = u32::try_from(gates.len()).expect("fits u32");
    let w_d0 = add_wire(WireHint::Solve { gate: g_d0 });
    gates.push(PackedGate {
      a: w_gamma,
      b: w_x,
      c: w_d0,
      sel: SEL_L | SEL_R | SEL_O,
      alpha_id: 0,
      beta_id: 0,
      omega_id: 1,
      qc: 1,
    });

    let mut qs = [0u32; 2];
    for slot in &mut qs {
      let g_idx = u32::try_from(gates.len()).expect("fits u32");
      let w_q = add_wire(WireHint::Solve { gate: g_idx });
      *slot = w_q;
      gates.push(PackedGate {
        a: w_q,
        b: w_d0,
        c: w_m,
        sel: SEL_M | SEL_O,
        alpha_id: 0,
        beta_id: 0,
        omega_id: 1,
        qc: 0,
      });
    }
    let g_zero = u32::try_from(gates.len()).expect("fits u32");
    let w_zero = add_wire(WireHint::Solve { gate: g_zero });
    gates.push(PackedGate {
      a: qs[0],
      b: qs[1],
      c: w_zero,
      sel: SEL_L | SEL_R | SEL_O,
      alpha_id: 0,
      beta_id: 1,
      omega_id: 1,
      qc: 0,
    });
    let w_free = add_wire(WireHint::Free);
    gates.push(PackedGate {
      a: w_free,
      b: w_gamma,
      c: w_zero,
      sel: SEL_M | SEL_O,
      alpha_id: 0,
      beta_id: 0,
      omega_id: 0,
      qc: 0,
    });

    let builder = ScsBuilder::<C> {
      publics,
      wires: hints.len(),
      pre,
      gamma: w_gamma,
      beta: w_beta,
      outputs,
      coeffs,
      gates,
      commits: vec![0, 1, w_x, w_y, w_m],
      hints,
      tables: vec![
        Table {
          name: "root".into(),
          cell_base: 0,
          rows: 1,
          width: u32::try_from(publics + num_outputs).expect("fits u32"),
        },
        Table {
          name: "witness".into(),
          cell_base: u64::try_from(publics + num_outputs).expect("fits u64"),
          rows: 1,
          width: 3,
        },
      ],
    };

    let pub0 = C::Fr::from(100u64);
    let pub1 = C::Fr::from(296u64);
    let mut input_wires = Vec::with_capacity(cells);
    input_wires.push(pub0);
    input_wires.push(pub1);
    input_wires.extend_from_slice(output_values);
    input_wires.push(C::Fr::from(17u64));
    input_wires.push(C::Fr::from(23u64));
    input_wires.push(C::Fr::from(9u64));
    (builder.encode(), input_wires, vec![pub0, pub1])
  }

  /// Minimal real `WidePackage` with a self-contained unit-returning (`()`)
  /// entry verifying `a + b == 396`, for testing `scs::Witness::new_fitting`
  /// and `scs::Bls12381Witness::new` with `outputs == 0`.
  fn build_unit_wide_package<B: FieldBackend<Word = FieldWord>>(
    field: B,
  ) -> WidePackage {
    let entry_name = "Prog::check_unit".to_owned();
    let program = Program {
      version: aiur::bytecode::VERSION,
      modulus: field.modulus(),
      functions: vec![Function {
        name: entry_name.clone(),
        params: vec![Type::Field, Type::Field],
        result: Type::Tuple { items: vec![] },
        registers: 4,
        code: vec![
          I::Literal { dest: 3, value: FieldWord::from(396u64) },
          I::Binary { dest: 2, operator: Binary::Add, left: 0, right: 1 },
          I::AssertEq {
            left: vec![2],
            right: vec![3],
            message: Some("sum check failed".into()),
            runtime_check: true,
          },
          I::Ret { value: vec![] },
        ],
      }],
      enums: vec![],
      tables: vec![],
      maps: vec![],
      entries: vec![Entry {
        name: entry_name.clone(),
        function: 0,
        inputs: vec![IoType::Field, IoType::Field],
        output: Some(IoType::Tuple { items: vec![] }),
      }],
    };
    let trace = TraceArtifact {
      version: 3,
      modulus: field.modulus(),
      limbs: vec![],
      functions: vec![FunctionPlan {
        name: entry_name.clone(),
        chip: entry_name.clone(),
        witnesses: 2,
        inputs: vec![0, 1],
        output: vec![],
        steps: vec![],
        writes: vec![
          ColumnWrite {
            column: 0,
            source: 0,
            guard: Polynomial::Const(FieldWord::from(1u64)),
          },
          ColumnWrite {
            column: 1,
            source: 1,
            guard: Polynomial::Const(FieldWord::from(1u64)),
          },
        ],
      }],
      chips: vec![Chip {
        name: entry_name,
        width: 3,
        activation: 2,
        inputs: vec![0, 1],
        output: vec![],
        constraints: vec![],
        sends: vec![],
        memory: vec![],
        depth: ChipDepth::default(),
      }],
      groups: vec![],
    };
    WidePackage { program, trace: Some(trace) }
  }

  /// Build a matching `ix-aiur-scs-v1` circuit whose `root` + `Prog::check_unit`
  /// tables match `build_unit_wide_package` (`outputs == 0`, `table_rows`
  /// power-of-two capacity, e.g. `1` or `4`).
  fn build_unit_matching_scs<C: KzgCurve>(table_rows: u32) -> Vec<u8> {
    let publics = 2usize;
    let table_width = 4u32; // [a, b, activation, multiplicity]
    let cells = publics + (table_rows as usize) * (table_width as usize);
    let coeffs = vec![C::FR_ONE, C::FR_NEG_ONE, C::Fr::from(396u64)];
    let mut hints = vec![WireHint::Input; cells];
    let mut gates = Vec::new();
    let mut add_wire = |hint: WireHint| -> u32 {
      let id = u32::try_from(hints.len()).expect("fits u32");
      hints.push(hint);
      id
    };

    // Pre-commitment: pub0 == cell[2] (row 0 col 0), pub1 == cell[3] (row 0 col 1),
    // and (pub0 + pub1) - 396 * act == 0 (where cell[4] == act == 1).
    gates.push(PackedGate {
      a: 0,
      b: 2,
      c: 0,
      sel: SEL_L | SEL_R,
      alpha_id: 0,
      beta_id: 1,
      omega_id: 0,
      qc: 0,
    });
    gates.push(PackedGate {
      a: 1,
      b: 3,
      c: 0,
      sel: SEL_L | SEL_R,
      alpha_id: 0,
      beta_id: 1,
      omega_id: 0,
      qc: 0,
    });
    let g_sum = u32::try_from(gates.len()).expect("fits u32");
    let w_sum = add_wire(WireHint::Solve { gate: g_sum });
    gates.push(PackedGate {
      a: 2,
      b: 3,
      c: w_sum,
      sel: SEL_L | SEL_R | SEL_O,
      alpha_id: 0,
      beta_id: 0,
      omega_id: 1,
      qc: 0,
    });
    gates.push(PackedGate {
      a: w_sum,
      b: 4,
      c: 0,
      sel: SEL_L | SEL_R,
      alpha_id: 1,
      beta_id: 2,
      omega_id: 0,
      qc: 0,
    });
    let pre = gates.len();

    let w_gamma = add_wire(WireHint::Challenge);
    let w_bit = add_wire(WireHint::Bit { wire: w_gamma, bit: 0 });
    gates.push(PackedGate {
      a: w_bit,
      b: w_bit,
      c: w_bit,
      sel: SEL_M | SEL_O,
      alpha_id: 0,
      beta_id: 0,
      omega_id: 1,
      qc: 0,
    });

    ScsBuilder::<C> {
      publics,
      wires: hints.len(),
      pre,
      gamma: w_gamma,
      beta: w_bit,
      outputs: vec![],
      coeffs,
      gates,
      commits: vec![0, 1, 2, 3, 4],
      hints,
      tables: vec![
        Table { name: "root".into(), cell_base: 0, rows: 1, width: 2 },
        Table {
          name: "Prog::check_unit".into(),
          cell_base: 2,
          rows: table_rows,
          width: table_width,
        },
      ],
    }
    .encode()
  }

  #[test]
  fn backend_and_cuda_manifest_dispatch() {
    let native_manifest = br#"{"format":"ix-aiur-native-plonk-v1"}"#;
    let gnark_manifest_pascal = br#"{"Format":"ix-aiur-scs-artifacts-v1"}"#;
    let gnark_manifest_lower = br#"{"format":"ix-aiur-scs-artifacts-v1"}"#;

    validate_optional_backend(&json!({})).unwrap();
    validate_optional_backend(&json!({"backend": "native"})).unwrap();
    let err_gnark_opt =
      validate_optional_backend(&json!({"backend": "gnark"})).unwrap_err();
    assert!(
      err_gnark_opt.contains("retired")
        && err_gnark_opt.contains(native::NATIVE_MANIFEST_FORMAT),
      "unexpected error: {err_gnark_opt}"
    );
    assert!(validate_optional_backend(&json!({"backend": "halo2"})).is_err());
    assert!(validate_optional_backend(&json!({"backend": 1})).is_err());

    validate_manifest_format(native_manifest).unwrap();
    for legacy in
      [gnark_manifest_pascal.as_slice(), gnark_manifest_lower.as_slice()]
    {
      let err = validate_manifest_format(legacy).unwrap_err();
      assert!(
        err.contains("retired")
          && err.contains(LEGACY_GNARK_MANIFEST_FORMAT)
          && err.contains(native::NATIVE_MANIFEST_FORMAT),
        "unexpected error: {err}"
      );
    }
    assert!(validate_manifest_format(br#"{"format":"unknown-v1"}"#).is_err());
    assert!(validate_manifest_format(br#"{}"#).is_err());
    assert!(validate_manifest_format(b"not-json").is_err());

    // Native auto-detect and explicit selection work under all feature sets.
    validate_backend(&json!({}), native_manifest).unwrap();
    validate_backend(&json!({"backend": "native"}), native_manifest).unwrap();

    // Legacy gnark manifests and explicit `"gnark"` backend always fail closed
    // with a clear error pointing to `ix-aiur-native-plonk-v1`.
    for spec in
      [json!({}), json!({"backend": "native"}), json!({"backend": "gnark"})]
    {
      let err = validate_backend(&spec, gnark_manifest_pascal).unwrap_err();
      assert!(
        err.contains("retired") && err.contains(native::NATIVE_MANIFEST_FORMAT),
        "unexpected error for spec {spec}: {err}"
      );
    }
    let err = validate_backend(&json!({"backend": "gnark"}), native_manifest)
      .unwrap_err();
    assert!(
      err.contains("retired") && err.contains(native::NATIVE_MANIFEST_FORMAT),
      "unexpected error: {err}"
    );

    // Native CUDA flag parsing.
    assert_eq!(parse_native_cuda(&json!({})).unwrap(), cfg!(feature = "cuda"));
    assert!(!parse_native_cuda(&json!({"cuda": false})).unwrap());
    assert!(parse_native_cuda(&json!({"cuda": true})).unwrap());
    assert!(parse_native_cuda(&json!({"cuda": "yes"})).is_err());

    // Prepared directory resolution supports both flat and nested layouts.
    let dir = temp_dir("layout");
    let flat_manifest = dir.join("manifest.json");
    fs::write(&flat_manifest, native_manifest).unwrap();
    let nested = dir.join("prepared");
    fs::create_dir_all(&nested).unwrap();
    fs::write(nested.join("verifying-key.bin"), b"vk").unwrap();
    assert_eq!(resolve_native_prepared_dir(&flat_manifest).unwrap(), nested);
    fs::write(dir.join("verifying-key.bin"), b"vk").unwrap();
    assert_eq!(resolve_native_prepared_dir(&flat_manifest).unwrap(), dir);
    let _ = fs::remove_dir_all(&dir);
  }

  #[test]
  fn native_output_checks_bn254_and_bls12_381() {
    // BN254 anchors and valid pairing accumulator: e(tau*G1, G2) * e(-G1, tau*G2) == 1.
    let bn_srs =
      Srs::<Bn254Curve>::unsafe_dev_setup(16, b"ix-terminal-bn254-outputs");
    let bn_anchors = [bn_srs.g2, bn_srs.tau_g2];
    check_bn254_native_outputs(0, &[], &bn_anchors).unwrap();
    check_bn254_native_outputs(0, &[Bn254.one()], &bn_anchors).unwrap();

    let mut bn_acc = Vec::with_capacity(ACCUMULATOR_WORDS);
    bn_acc.extend(g1::encode(bn_srs.g1[1]));
    bn_acc.extend(g1::encode(-bn_srs.g1[0]));
    check_bn254_native_outputs(ACCUMULATOR_WORDS, &bn_acc, &bn_anchors)
      .unwrap();

    let mut bn_inf = Vec::with_capacity(ACCUMULATOR_WORDS);
    bn_inf.extend(g1::encode(ark_bn254::G1Affine::identity()));
    bn_inf.extend(g1::encode(ark_bn254::G1Affine::identity()));
    check_bn254_native_outputs(ACCUMULATOR_WORDS, &bn_inf, &bn_anchors)
      .unwrap();

    let mut bn_bad = Vec::with_capacity(ACCUMULATOR_WORDS);
    bn_bad.extend(g1::encode(bn_srs.g1[2]));
    bn_bad.extend(g1::encode(-bn_srs.g1[0]));
    assert!(
      check_bn254_native_outputs(ACCUMULATOR_WORDS, &bn_bad, &bn_anchors)
        .is_err()
    );
    assert!(
      check_bn254_native_outputs(ACCUMULATOR_WORDS, &[], &bn_anchors).is_err()
    );
    assert!(
      check_bn254_native_outputs(1, &[Bn254.one()], &bn_anchors).is_err()
    );

    // BLS12-381 anchors (real Filecoin 256-power fixture) and valid accumulator.
    let bls_srs = load_filecoin_cache(
      Path::new(FILECOIN_PREFIX_2P8_FIXTURE),
      FILECOIN_PREFIX_2P8_MANIFEST_BLAKE3,
      64,
    )
    .unwrap();
    let bls_anchors = [bls_srs.g2, bls_srs.tau_g2];
    check_bls12_381_native_outputs(0, &[], &bls_anchors).unwrap();
    check_bls12_381_native_outputs(0, &[Bls12381.one()], &bls_anchors).unwrap();

    let mut bls_acc = Vec::with_capacity(bls12_381::ACCUMULATOR_WORDS);
    bls_acc.extend(bls12_381::encode_g1(bls_srs.g1[1]));
    bls_acc.extend(bls12_381::encode_g1(-bls_srs.g1[0]));
    check_bls12_381_native_outputs(
      bls12_381::ACCUMULATOR_WORDS,
      &bls_acc,
      &bls_anchors,
    )
    .unwrap();

    let mut bls_bad = Vec::with_capacity(bls12_381::ACCUMULATOR_WORDS);
    bls_bad.extend(bls12_381::encode_g1(bls_srs.g1[2]));
    bls_bad.extend(bls12_381::encode_g1(-bls_srs.g1[0]));
    assert!(
      check_bls12_381_native_outputs(
        bls12_381::ACCUMULATOR_WORDS,
        &bls_bad,
        &bls_anchors,
      )
      .is_err()
    );
    assert!(
      check_bls12_381_native_outputs(
        bls12_381::ACCUMULATOR_WORDS,
        &[],
        &bls_anchors,
      )
      .is_err()
    );
    assert!(
      check_bls12_381_native_outputs(1, &[Bls12381.one()], &bls_anchors)
        .is_err()
    );
  }

  fn run_native_e2e_roundtrip<C: KzgCurve>(
    label: &str,
    srs: &Srs<C>,
    srs_blake3: &str,
    output_values: &[C::Fr],
    nested_prepared: bool,
  ) {
    let num_outputs = output_values.len();
    let (scs_bytes, input_wires, expected_publics) =
      build_synthetic_scs::<C>(num_outputs, output_values);
    let scs = ScsFile::<C>::parse(&scs_bytes).unwrap();
    let dir = temp_dir(label);
    let scs_path = dir.join("circuit.ixscs");
    fs::write(&scs_path, &scs_bytes).unwrap();

    let prep_dir =
      if nested_prepared { dir.join("prepared") } else { dir.clone() };
    let accel = PlonkAccelerator::<C>::cpu();
    let manifest =
      prepare_to_dir(&scs_path, srs, srs_blake3, &prep_dir, &accel).unwrap();
    let manifest_path = if nested_prepared {
      let top = dir.join("manifest.json");
      fs::copy(prep_dir.join("manifest.json"), &top).unwrap();
      top
    } else {
      prep_dir.join("manifest.json")
    };
    let manifest_bytes = fs::read(&manifest_path).unwrap();
    validate_backend(&json!({}), &manifest_bytes).unwrap();
    validate_backend(&json!({"backend": "native"}), &manifest_bytes).unwrap();
    let resolved = resolve_native_prepared_dir(&manifest_path).unwrap();
    assert_eq!(resolved, prep_dir);

    let prover =
      NativeProver::<C>::open(&resolved, &scs_path, &manifest, accel).unwrap();
    let inputs =
      read_verified_native_inputs(&resolved, &manifest, prover.scs()).unwrap();
    assert_eq!(inputs, scs.to_inputs());

    let wrapped: Vec<CurveScalar<C>> =
      input_wires.iter().copied().map(CurveScalar::new).collect();
    let witness = serialize_binary_witness::<C>(scs.publics, &wrapped).unwrap();

    let mut phases = Phases(serde_json::Map::new());
    let checks = prove_verify_native_with(
      &prover,
      &resolved,
      &manifest,
      &witness,
      &expected_publics,
      &mut phases,
      |w, pubs| prover.prove_binary(w, pubs),
    )
    .unwrap();
    assert!(checks.wrong_statement_refused_by_prover);
    assert!(checks.wrong_statement_rejected_by_verifier);
    assert!(checks.solidity_wrong_statement_rejected);
    assert!(checks.verifying_key_is_prepared);
    assert_eq!(checks.key_sha256, manifest.vk_sha256);
    assert!(phases.0.contains_key("prove"));
    assert!(phases.0.contains_key("verify"));

    // Explicit negative control: tampered inputs.json is rejected.
    fs::write(resolved.join("inputs.json"), b"{}").unwrap();
    assert!(
      read_verified_native_inputs(&resolved, &manifest, prover.scs()).is_err()
    );

    let _ = fs::remove_dir_all(&dir);
  }

  #[test]
  fn native_terminal_e2e_bn254_outputs_0_and_18() {
    let srs =
      Srs::<Bn254Curve>::unsafe_dev_setup(64, b"ix-terminal-native-bn254");
    // Self-contained circuit (`outputs == 0`).
    run_native_e2e_roundtrip::<Bn254Curve>(
      "bn254-out0",
      &srs,
      "dev-bn254-srs",
      &[],
      false,
    );

    // External-output circuit (`outputs == 18`) with valid BN254 pairing accumulator.
    let mut acc = Vec::with_capacity(ACCUMULATOR_WORDS);
    acc.extend(g1::encode(srs.g1[1]));
    acc.extend(g1::encode(-srs.g1[0]));
    check_bn254_native_outputs(ACCUMULATOR_WORDS, &acc, &[srs.g2, srs.tau_g2])
      .unwrap();
    let acc_fr: Vec<ark_bn254::Fr> = acc.iter().map(|s| s.0).collect();
    run_native_e2e_roundtrip::<Bn254Curve>(
      "bn254-out18",
      &srs,
      "dev-bn254-srs",
      &acc_fr,
      true,
    );
  }

  #[test]
  fn native_terminal_e2e_bls12_381_outputs_0_and_22() {
    // Use the real checked-in Filecoin 256-power ceremony SRS fixture!
    let srs = load_filecoin_cache(
      Path::new(FILECOIN_PREFIX_2P8_FIXTURE),
      FILECOIN_PREFIX_2P8_MANIFEST_BLAKE3,
      64,
    )
    .unwrap();
    let filecoin_params =
      VerifierParams::<Bls12381Curve>::from_srs(&filecoin_anchors());
    let srs_blake3 =
      blake3::Hash::from(FILECOIN_PREFIX_2P8_MANIFEST_BLAKE3).to_hex();

    // Self-contained circuit (`outputs == 0`).
    run_native_e2e_roundtrip::<Bls12381Curve>(
      "bls12-381-out0",
      &srs,
      srs_blake3.as_str(),
      &[],
      false,
    );

    // External-output circuit (`outputs == 22`) with real Filecoin pairing accumulator.
    let mut acc = Vec::with_capacity(bls12_381::ACCUMULATOR_WORDS);
    acc.extend(bls12_381::encode_g1(srs.g1[1]));
    acc.extend(bls12_381::encode_g1(-srs.g1[0]));
    check_bls12_381_native_outputs(
      bls12_381::ACCUMULATOR_WORDS,
      &acc,
      &[filecoin_params.g2, filecoin_params.tau_g2],
    )
    .unwrap();
    let acc_fr: Vec<ark_bls12_381::Fr> = acc.iter().map(|s| s.0).collect();
    run_native_e2e_roundtrip::<Bls12381Curve>(
      "bls12-381-out22",
      &srs,
      srs_blake3.as_str(),
      &acc_fr,
      true,
    );

    // Without `--features cuda`, requesting CUDA on BLS12-381 fails cleanly
    // with the native CUDA feature message (rather than gnark's rejection).
    #[cfg(not(feature = "cuda"))]
    {
      let err = PlonkAccelerator::<Bls12381Curve>::new(true).unwrap_err();
      assert!(err.contains("--features cuda"), "unexpected error: {err}");
    }
  }

  #[test]
  fn native_wide_package_witness_e2e_outputs_0_both_curves() {
    let entry = "Prog::check_unit";

    // --- BN254 self-contained WidePackage + scs::Witness::new_fitting + NativeProver ---
    {
      let pkg = build_unit_wide_package(Bn254);
      let pkg_bytes = pkg.encode().unwrap();
      let decoded = WidePackage::decode(&pkg_bytes).unwrap();
      let trace = decoded.trace.unwrap();
      let mut program = decoded.program.check_with(Bn254).unwrap();
      program.track_depth(&trace).unwrap();
      let plan = TracePlan::new(Arc::new(program), trace).unwrap();

      let args = vec![Bn254.from_u64(100), Bn254.from_u64(296)];
      let record = plan
        .program()
        .prepare_hint_channels(&[], &HintChannels::new())
        .unwrap()
        .execute(entry, args.clone())
        .unwrap();
      assert!(record.output.is_empty());

      // Test prepared table capacity > execution row count (4 >= 1) via `new_fitting`.
      let scs_bytes = build_unit_matching_scs::<Bn254Curve>(4);
      let scs = ScsFile::<Bn254Curve>::parse(&scs_bytes).unwrap();
      assert!(scs.outputs.is_empty());
      let domain = domain_size_for_scs(&scs).unwrap();
      let srs = Srs::<Bn254Curve>::unsafe_dev_setup(
        (domain + 3).next_power_of_two(),
        b"ix-terminal-wide-bn254",
      );
      let dir = temp_dir("wide-bn254");
      let scs_path = dir.join("unit.ixscs");
      fs::write(&scs_path, &scs_bytes).unwrap();
      let accel = PlonkAccelerator::<Bn254Curve>::cpu();
      let manifest =
        prepare_to_dir(&scs_path, &srs, "dev-bn254", &dir, &accel).unwrap();
      let prover =
        NativeProver::<Bn254Curve>::open(&dir, &scs_path, &manifest, accel)
          .unwrap();
      let inputs =
        read_verified_native_inputs(&dir, &manifest, prover.scs()).unwrap();

      let expected_publics = native_expected_publics::<Bn254, Bn254Curve>(
        &plan,
        entry,
        &record,
        &args,
        prover.scs().publics,
        prover.scs().outputs.len(),
      )
      .unwrap();
      let compiler = Compiler::new(&plan).unwrap();
      let capacities: Vec<usize> = compiler
        .row_counts(&record)
        .unwrap()
        .into_iter()
        .map(|r| r.max(1))
        .collect();
      let witness =
        scs::Witness::new_fitting(&plan, compiler, &capacities, entry, inputs)
          .unwrap()
          .binary(&record, &args)
          .unwrap();
      let mut phases = Phases(serde_json::Map::new());
      let checks = prove_verify_native_with(
        &prover,
        &dir,
        &manifest,
        &witness,
        &expected_publics,
        &mut phases,
        |w, pubs| prover.prove_binary(w, pubs),
      )
      .unwrap();
      assert!(checks.wrong_statement_refused_by_prover);
      assert!(checks.wrong_statement_rejected_by_verifier);
      assert!(checks.verifying_key_is_prepared);
      let _ = fs::remove_dir_all(&dir);
    }

    // --- BLS12-381 self-contained WidePackage + scs::Bls12381Witness + NativeProver ---
    {
      let pkg = build_unit_wide_package(Bls12381);
      let pkg_bytes = pkg.encode().unwrap();
      let plan = bls12_381::load_trace_plan(&pkg_bytes).unwrap();
      let args = vec![Bls12381.from_u64(100), Bls12381.from_u64(296)];
      let record =
        bls12_381::execute_plan(&plan, entry, args.clone(), None).unwrap();
      assert!(record.output.is_empty());

      let scs_bytes = build_unit_matching_scs::<Bls12381Curve>(4);
      let scs = ScsFile::<Bls12381Curve>::parse(&scs_bytes).unwrap();
      assert!(scs.outputs.is_empty());
      let srs = load_filecoin_cache(
        Path::new(FILECOIN_PREFIX_2P8_FIXTURE),
        FILECOIN_PREFIX_2P8_MANIFEST_BLAKE3,
        64,
      )
      .unwrap();
      let dir = temp_dir("wide-bls12-381");
      let scs_path = dir.join("unit.ixscs");
      fs::write(&scs_path, &scs_bytes).unwrap();
      let accel = PlonkAccelerator::<Bls12381Curve>::cpu();
      let manifest =
        prepare_to_dir(&scs_path, &srs, "filecoin-2p8", &dir, &accel).unwrap();
      let prover =
        NativeProver::<Bls12381Curve>::open(&dir, &scs_path, &manifest, accel)
          .unwrap();
      let inputs =
        read_verified_native_inputs(&dir, &manifest, prover.scs()).unwrap();

      let expected_publics =
        native_expected_publics::<Bls12381, Bls12381Curve>(
          &plan,
          entry,
          &record,
          &args,
          prover.scs().publics,
          prover.scs().outputs.len(),
        )
        .unwrap();
      let witness = scs::Bls12381Witness::new(&plan, entry, inputs)
        .unwrap()
        .binary(&record, &args)
        .unwrap();
      let mut phases = Phases(serde_json::Map::new());
      let checks = prove_verify_native_with(
        &prover,
        &dir,
        &manifest,
        &witness,
        &expected_publics,
        &mut phases,
        |w, pubs| prover.prove_binary(w, pubs),
      )
      .unwrap();
      assert!(checks.wrong_statement_refused_by_prover);
      assert!(checks.wrong_statement_rejected_by_verifier);
      assert!(checks.verifying_key_is_prepared);
      let _ = fs::remove_dir_all(&dir);
    }

    // Verify `native_expected_publics` fails closed when statement limbs mismatch.
    let pkg = build_unit_wide_package(Bn254);
    let plan = {
      let decoded = WidePackage::decode(&pkg.encode().unwrap()).unwrap();
      let trace = decoded.trace.unwrap();
      let mut program = decoded.program.check_with(Bn254).unwrap();
      program.track_depth(&trace).unwrap();
      TracePlan::new(Arc::new(program), trace).unwrap()
    };
    let args = vec![Bn254.from_u64(100), Bn254.from_u64(296)];
    let record = plan
      .program()
      .prepare_hint_channels(&[], &HintChannels::new())
      .unwrap()
      .execute(entry, args.clone())
      .unwrap();
    assert!(
      native_expected_publics::<Bn254, Bn254Curve>(
        &plan, entry, &record, &args, 3, 0,
      )
      .is_err()
    );
  }
}
