//! A final PLONK proof of the narrow-stage terminal relation
//! (`CompressFinalNarrow::verify_accumulator_v1`) on the Ignition setup,
//! proved by the pure-Rust (+ optional Ix-CUDA) native PLONK + BSB22 backend.
//!
//! `aiur_narrow_terminal_prove ARTIFACT NARROW_DIR POLICY OUT_DIR --scs FILE [--cuda] [--reuse] [--wait-for F]`
//!
//! The circuit is `FILE`, the `ix-aiur-scs-v1` constraint system that
//! `plonk_export` wrote for this terminal's stage (`plonk::scs`). The native
//! backend preprocesses it directly (`ix-aiur-native-plonk-v1`), pinning the
//! SCS file, proving/verifying keys, input layout, and Solidity verifier in
//! `OUT_DIR/manifest.json`. The witness holds the file's input wires (the 2
//! public statement limbs, the outputs and every table's cells); the native
//! solver computes the remaining wires.
//!
//! `--stage-only` writes `OUT_DIR/stage.json` (the function and ROM circuits
//! at this execution's power-of-two capacities, which `plonk_export` reads)
//! and `OUT_DIR/pairing.json`, and stops.
//!
//! `--reuse` keeps `OUT_DIR/prepared` (keys, input layout, Solidity verifier)
//! when its `ix-aiur-native-plonk-v1` manifest pins this SCS file's digest,
//! skipping setup; otherwise it prepares afresh.
//!
//! `--wait-for FILE` (with `--reuse` and `--scs`) opens the native prover on
//! the prepared keys named by `OUT_DIR/manifest.json` before `NARROW_DIR` is
//! read, then waits until `FILE` exists, so the key load overlaps the narrow
//! stage.
//!
//! `--cuda` proves with the Ix-CUDA native PLONK backend (a `cuda` build).
//!
//! - `ARTIFACT` is the exported terminal (`compress_final_narrow_export`),
//!   whose fixed tables hold the narrow stage's key and configuration.
//! - `NARROW_DIR` holds the narrow stage's `claims.bin`, `proof.bin`, `key.bin`
//!   and `narrow.json` (`aiur_template_v2_init --save`); `POLICY` is the chain
//!   policy (`IXAUKG01`).
//!
//! The terminal executes on the narrow proof and its folded pair is checked
//! against the Ignition anchors. The tool proves, verifies both the native and
//! Solidity proof encodings against the verifying key's digest and the
//! Ignition anchors, and checks that a changed statement is refused and
//! rejected. It writes `proof.bin`, `proof.solidity.bin`, and `summary.json`
//! with each phase's time and the process's peak RSS after it.

use aiur::{
  artifact::WidePackage, hints::HintChannels, maps::MapOverrides,
  trace::TracePlan,
};
use ark_ec::pairing::Pairing;
use ix_proof_compression::{
  aiur_backend::{
    Bn254,
    compress_bn::{PackedCapacity, PackedPolicy},
    fq, g1,
    kzg::Compiler,
    kzg_advice as wire,
    pairing::final_program::{
      Configuration, NARROW_ACCUMULATOR_ENTRY, statement_arguments,
    },
    plonk::{
      native::{
        NATIVE_MANIFEST_FORMAT, NativeProver, PlonkAccelerator,
        PreparedManifest, ScsFile, domain_size_for_scs, prepare_to_dir,
        verify_native_bytes, verify_solidity_bytes,
      },
      scs,
    },
  },
  kzg::{
    Scalar, Srs, VerifierParams,
    curve::{Bn254 as Bn254Curve, KzgCurve},
    srs::gnark as ignition_srs,
  },
  pipeline::SetupConfig,
};
use serde_json::{Value, json};
use sha2::{Digest, Sha256};
use std::{
  fs,
  path::{Path, PathBuf},
  sync::Arc,
  time::{Duration, Instant},
};

type Error = Box<dyn std::error::Error>;

fn peak_rss_gb() -> f64 {
  let status = fs::read_to_string("/proc/self/status").unwrap_or_default();
  status
    .lines()
    .find(|l| l.starts_with("VmHWM"))
    .and_then(|l| l.split_whitespace().nth(1))
    .and_then(|v| v.parse::<f64>().ok())
    .unwrap_or(0.0)
    / 1e6
}

fn statement(dir: &Path) -> Result<[u8; 32], Error> {
  let narrow: Value =
    serde_json::from_slice(&fs::read(dir.join("narrow.json"))?)?;
  let hex = narrow["statement"].as_str().ok_or("narrow statement")?;
  let mut statement = [0u8; 32];
  for (i, byte) in statement.iter_mut().enumerate() {
    *byte = u8::from_str_radix(
      hex.get(2 * i..2 * i + 2).ok_or("narrow statement")?,
      16,
    )?;
  }
  Ok(statement)
}

struct Phases(serde_json::Map<String, Value>);

impl Phases {
  fn record(&mut self, name: &str, started: Instant) {
    let seconds = started.elapsed().as_secs_f64();
    let rss = peak_rss_gb();
    eprintln!("{name}: {seconds:.1} s, peak RSS {rss:.1} GB");
    self.0.insert(
      name.into(),
      json!({"seconds": seconds, "peak_rss_gb_after": rss}),
    );
  }
}

fn sha256_file(path: &Path) -> Result<String, String> {
  let mut hash = Sha256::new();
  std::io::copy(
    &mut fs::File::open(path).map_err(|e| e.to_string())?,
    &mut hash,
  )
  .map_err(|e| e.to_string())?;
  Ok(format!("{:x}", hash.finalize()))
}

fn load_ignition_srs(
  setup: &SetupConfig,
  parameters: &VerifierParams,
  domain: usize,
) -> Result<(Srs<Bn254Curve>, String, usize), Error> {
  let srs_path = match setup {
    SetupConfig::Ignition { srs, .. } => srs,
    _ => {
      return Err(
        "aiur_narrow_terminal_prove requires the Ignition BN254 SRS".into(),
      );
    },
  };
  let opening_powers =
    domain.checked_add(3).ok_or("PLONK domain size overflow")?;
  let prefix_len = opening_powers.next_power_of_two();
  let public_setup = parameters.public_setup();
  let srs = ignition_srs::load(srs_path, prefix_len, public_setup)?;
  let (g1_anchors, g2_anchors) =
    ix_proof_compression::aiur_backend::pairing::verifier_anchors(parameters);
  if srs.g1[..2] != g1_anchors
    || srs.g2 != g2_anchors[0]
    || srs.tau_g2 != g2_anchors[1]
  {
    return Err(
      "loaded Ignition SRS anchors differ from the released parameters".into(),
    );
  }
  let srs_blake3 =
    blake3::Hash::from_bytes(public_setup.id).to_hex().to_string();
  Ok((srs, srs_blake3, opening_powers))
}

struct Scs<'p, 'a> {
  path: &'p Path,
  sha256: std::thread::JoinHandle<Result<String, String>>,
  plan: &'p TracePlan<'a, Bn254>,
  compiler: Compiler<'p, 'a>,
  capacities: &'p [usize],
  record: &'p aiur::Execution<Bn254>,
  arguments: &'p [Scalar],
  out: &'p Path,
  use_cuda: bool,
  reuse: bool,
  early: Option<(NativeProver<Bn254Curve>, PreparedManifest)>,
  setup: &'p SetupConfig,
  parameters: &'p VerifierParams,
  phases: Phases,
  artifact: &'p str,
  artifact_blake3: String,
  statement: Value,
}

/// `OUT_DIR/manifest.json` when it names a native PLONK circuit prepared from
/// this SCS file.
fn reusable_manifest(out: &Path, scs_sha256: &str) -> Option<PreparedManifest> {
  let manifest: PreparedManifest =
    serde_json::from_slice(&fs::read(out.join("manifest.json")).ok()?).ok()?;
  (manifest.format == NATIVE_MANIFEST_FORMAT
    && manifest.curve == Bn254Curve::NAME
    && manifest.scs_sha256 == scs_sha256)
    .then_some(manifest)
}

/// The terminal proof on the native PLONK circuit loaded from the
/// Lean-exported constraint system (`--scs`): preprocess it unless `--reuse`
/// finds it prepared, build the witness of its input wires, prove, and verify.
#[allow(clippy::too_many_lines)]
fn prove_scs(run: Scs<'_, '_>) -> Result<(), Error> {
  let Scs {
    path,
    sha256,
    plan,
    compiler,
    capacities,
    record,
    arguments,
    out,
    use_cuda,
    reuse,
    early,
    setup,
    parameters,
    mut phases,
    artifact,
    artifact_blake3,
    statement,
  } = run;
  let started = Instant::now();
  let scs_sha256 = sha256.join().map_err(|_err| "SCS digest thread")??;
  let prepared = out.join("prepared");
  let reused = if reuse { reusable_manifest(out, &scs_sha256) } else { None };
  if early.is_some() && reused.is_none() {
    return Err(
      "--wait-for: the prepared circuit is not this SCS file's".into(),
    );
  }
  phases.record("scs_digest", started);

  let (srs_powers, manifest) = if let Some(manifest) = reused {
    eprintln!("reusing {} (SCS {scs_sha256})", prepared.display());
    (manifest.domain.saturating_add(3), manifest)
  } else {
    let started = Instant::now();
    let scs_bytes = fs::read(path)?;
    let parsed = ScsFile::<Bn254Curve>::parse(&scs_bytes)?;
    let domain = domain_size_for_scs(&parsed)?;
    eprintln!("{} gates, domain {domain}", parsed.gates_count);
    let (srs, srs_blake3, opening_powers) =
      load_ignition_srs(setup, parameters, domain)?;
    phases.record("load_srs", started);

    let started = Instant::now();
    if prepared.exists() {
      fs::remove_dir_all(&prepared)?;
    }
    let accel = PlonkAccelerator::<Bn254Curve>::new(use_cuda)?;
    let manifest = prepare_to_dir(path, &srs, &srs_blake3, &prepared, &accel)?;
    fs::write(
      out.join("manifest.json"),
      serde_json::to_vec_pretty(&manifest)?,
    )?;
    phases.record("setup", started);
    (opening_powers, manifest)
  };

  let prover = match early {
    Some((prover, preloaded)) => {
      if preloaded != manifest {
        return Err(
          "the preloaded prover's manifest differs from the prepared circuit"
            .into(),
        );
      }
      prover
    },
    None => {
      let started = Instant::now();
      let accel = PlonkAccelerator::<Bn254Curve>::new(use_cuda)?;
      let prover =
        NativeProver::<Bn254Curve>::open(&prepared, path, &manifest, accel)?;
      phases.record("load", started);
      prover
    },
  };
  prover.vk().check_anchors(parameters)?;

  let started = Instant::now();
  let layout_bytes = fs::read(prepared.join("inputs.json"))?;
  if format!("{:x}", Sha256::digest(&layout_bytes)) != manifest.inputs_sha256 {
    return Err("prepared inputs.json differs from its manifest".into());
  }
  let inputs: scs::Inputs = serde_json::from_slice(&layout_bytes)?;
  if inputs != prover.scs().to_inputs() {
    return Err("prepared inputs.json differs from SCS input layout".into());
  }
  let witness = scs::Witness::new_fitting(
    plan,
    compiler,
    capacities,
    NARROW_ACCUMULATOR_ENTRY,
    inputs,
  )?
  .binary(record, arguments)?;
  phases.record("witness", started);

  let expected_publics: Vec<ark_bn254::Fr> =
    arguments.iter().map(|value| value.0).collect();
  let started = Instant::now();
  let proof = prover.prove_binary(&witness, &expected_publics)?;
  phases.record("prove", started);
  let mut wrong = expected_publics.clone();
  wrong[0] += Bn254Curve::FR_ONE;
  let wrong_statement_refused = prover.prove_binary(&witness, &wrong).is_err();

  let started = Instant::now();
  let key = fs::read(prepared.join("verifying-key.bin"))?;
  let key_pin: [u8; 32] = Sha256::digest(&key).into();
  let vk = prover.vk();
  verify_native_bytes(vk, &key_pin, &proof.native, &expected_publics)?;
  verify_solidity_bytes(vk, &key_pin, &proof.solidity, &expected_publics)?;
  phases.record("verify", started);
  let native_rejected =
    verify_native_bytes(vk, &key_pin, &proof.native, &wrong).is_err();
  let solidity_rejected =
    verify_solidity_bytes(vk, &key_pin, &proof.solidity, &wrong).is_err();
  let wrong_statement_rejected = native_rejected && solidity_rejected;
  if !wrong_statement_rejected {
    return Err("PLONK verifier accepted a changed statement".into());
  }
  fs::write(out.join("proof.bin"), &proof.native)?;
  fs::write(out.join("proof.solidity.bin"), &proof.solidity)?;
  let public_decimal: Vec<String> =
    expected_publics.iter().map(ToString::to_string).collect();
  let summary = json!({
    "format": "ix-aiur-narrow-terminal-plonk-v1",
    "prover": "native",
    "curve": Bn254Curve::NAME,
    "circuit": "ix-aiur-scs-v1",
    "scs": path,
    "scs_sha256": scs_sha256,
    "entry": NARROW_ACCUMULATOR_ENTRY,
    "artifact": artifact,
    "artifact_blake3": artifact_blake3,
    "statement": statement,
    "backend": if use_cuda { "cuda" } else { "cpu" },
    "capacities": "power of two: this execution's padded rows",
    "constraints": manifest.gates,
    "gates": manifest.gates,
    "domain": manifest.domain,
    "public_inputs": manifest.public_inputs,
    "outputs": manifest.outputs,
    "commitments": manifest.commits,
    "input_wires": witness.len().saturating_sub(12) / 32,
    "witness_bytes": witness.len(),
    "witness_sha256": format!("{:x}", Sha256::digest(&witness)),
    "srs_blake3": manifest.srs_blake3,
    "srs_powers": srs_powers,
    "verifying_key_sha256": format!("{:x}", Sha256::digest(&key)),
    "proof_bytes": proof.native.len(),
    "solidity_proof_bytes": proof.solidity.len(),
    "public_inputs_decimal": public_decimal,
    "wrong_statement_refused_by_prover": wrong_statement_refused,
    "wrong_statement_rejected_by_verifier": wrong_statement_rejected,
    "solidity_proof_verified": true,
    "solidity_wrong_statement_rejected": solidity_rejected,
    "prover_timings": proof.timings,
    "phases": phases.0,
    "peak_rss_gb": peak_rss_gb(),
  });
  fs::write(out.join("summary.json"), serde_json::to_vec_pretty(&summary)?)?;
  println!("{}", serde_json::to_string_pretty(&summary)?);
  Ok(())
}

#[allow(clippy::too_many_lines)]
fn main() -> Result<(), Error> {
  let args: Vec<_> = std::env::args().skip(1).collect();
  let [artifact, narrow, policy, out, flags @ ..] = args.as_slice() else {
    return Err(
      "usage: aiur_narrow_terminal_prove ARTIFACT NARROW_DIR POLICY OUT_DIR --scs FILE [--cuda] [--reuse] [--wait-for FILE] | --stage-only".into(),
    );
  };
  let reuse = flags.iter().any(|f| f == "--reuse");
  let use_cuda = flags.iter().any(|f| f == "--cuda");
  let narrow = Path::new(narrow);
  let out = Path::new(out);
  let scs_path =
    flags.iter().position(|f| f == "--scs").and_then(|i| flags.get(i + 1));
  // The SCS file's digest is computed while the terminal executes.
  let scs_hash = scs_path.map(|p| {
    let p = PathBuf::from(p);
    std::thread::spawn(move || sha256_file(&p))
  });
  fs::create_dir_all(out)?;
  let mut phases = Phases(serde_json::Map::new());

  let started = Instant::now();
  let bytes = fs::read(artifact)?;
  let pin = blake3::hash(&bytes);
  let package = WidePackage::decode(&bytes)?;
  let trace = package.trace.ok_or("missing trace")?;
  let mut program = package.program.check_with(Bn254)?;
  program.track_depth(&trace)?;
  let plan = TracePlan::new(Arc::new(program), trace)?;
  let setup = SetupConfig::from_env(false)?;
  let capacity = PackedCapacity {
    log_cap: 1,
    quotient_degree: 1,
    lookup_quotient_budget: None,
  };
  let config = capacity.config(&setup)?;
  let parameters = multi_stark::config::ProofConfig::pcs(&config).parameters();
  let policy_bytes = fs::read(policy)?;
  let policy = PackedPolicy::from_chain_bytes(parameters, &policy_bytes)?;
  let wait_for =
    flags.iter().position(|f| f == "--wait-for").and_then(|i| flags.get(i + 1));
  let mut early = None;
  let started = match wait_for {
    Some(file) => {
      if !reuse {
        return Err("--wait-for needs --reuse".into());
      }
      let scs_file = scs_path.ok_or("--wait-for needs --scs FILE")?;
      phases.record("setup", started);
      let manifest: PreparedManifest =
        serde_json::from_slice(&fs::read(out.join("manifest.json"))?)?;
      let started = Instant::now();
      let accel = PlonkAccelerator::<Bn254Curve>::new(use_cuda)?;
      let prover = NativeProver::<Bn254Curve>::open(
        &out.join("prepared"),
        Path::new(scs_file),
        &manifest,
        accel,
      )?;
      early = Some((prover, manifest));
      phases.record("load", started);
      let started = Instant::now();
      while !Path::new(file).exists() {
        std::thread::sleep(Duration::from_millis(20));
      }
      phases.record("wait", started);
      Instant::now()
    },
    None => started,
  };
  let record_json: Value =
    serde_json::from_slice(&fs::read(narrow.join("narrow.json"))?)?;
  let narrow_stage =
    u32::try_from(record_json["stage"].as_u64().ok_or("narrow stage")?)?;
  let configuration =
    Configuration::narrow(&policy, parameters, narrow_stage + 1)?;
  let mut hints = HintChannels::new();
  aiur::library::u32::register(&mut hints, Bn254)?;
  aiur::library::u64::register(&mut hints, Bn254)?;
  fq::register(&mut hints)?;
  g1::register(&mut hints)?;
  wire::register(&mut hints)?;
  wire::Inputs::new(
    fs::read(narrow.join("key.bin"))?,
    fs::read(narrow.join("claims.bin"))?,
    fs::read(narrow.join("proof.bin"))?,
    policy_bytes,
  )?
  .register(&mut hints)?;
  let mut maps = MapOverrides::new();
  aiur::library::u8::register_maps(plan.program(), &mut maps)?;
  let statement = statement(narrow)?;
  let arguments = statement_arguments(&statement).to_vec();
  let record = plan
    .program()
    .prepare_hint_channels(&[], &hints)?
    .with_map_overrides(&maps)?
    .execute(NARROW_ACCUMULATOR_ENTRY, arguments.clone())?;
  let pair =
    [g1::decode(&record.output[..9])?, g1::decode(&record.output[9..])?];
  let (_, anchors) =
    ix_proof_compression::aiur_backend::pairing::verifier_anchors(parameters);
  if ark_bn254::Bn254::multi_pairing(pair, [anchors[0], anchors[1]]).0
    != <ark_bn254::Bn254 as Pairing>::TargetField::from(1u8)
  {
    return Err("terminal accumulator fails the Ignition pairing check".into());
  }
  phases.record("execute", started);

  let started = Instant::now();
  let compiler = Compiler::new(&plan)?;
  let capacities: Vec<usize> =
    compiler.row_counts(&record)?.into_iter().map(|rows| rows.max(1)).collect();
  let public =
    plan.public_args(&record, NARROW_ACCUMULATOR_ENTRY, &arguments)?;
  if flags.iter().any(|f| f == "--stage-only") {
    let stage = scs::stage(
      &plan,
      &compiler,
      &capacities,
      NARROW_ACCUMULATOR_ENTRY,
      &public,
      &record.output,
    )?;
    fs::write(out.join("stage.json"), serde_json::to_vec(&stage)?)?;
    let pairing =
      scs::pairing(&plan, NARROW_ACCUMULATOR_ENTRY, &configuration)?;
    fs::write(out.join("pairing.json"), serde_json::to_vec(&pairing)?)?;
    phases.record("stage", started);
    println!(
      "{}",
      serde_json::to_string_pretty(
        &json!({"stage": out.join("stage.json"), "phases": phases.0})
      )?
    );
    return Ok(());
  }
  let scs_path = scs_path.ok_or("--scs FILE is required (or --stage-only)")?;
  prove_scs(Scs {
    path: Path::new(scs_path),
    sha256: scs_hash.ok_or("SCS digest")?,
    plan: &plan,
    compiler,
    capacities: &capacities,
    record: &record,
    arguments: &arguments,
    out,
    use_cuda,
    reuse,
    early,
    setup: &setup,
    parameters,
    phases,
    artifact,
    artifact_blake3: pin.to_hex().to_string(),
    statement: record_json["statement"].clone(),
  })
}
