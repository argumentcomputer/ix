//! A final PLONK proof of the narrow-stage terminal relation
//! (`CompressFinalNarrow::verify_accumulator_v1`) on the Ignition setup.
//!
//! `aiur_narrow_terminal_prove ARTIFACT NARROW_DIR POLICY OUT_DIR --scs FILE [--cuda] [--reuse] [--wait-for F]`
//!
//! The circuit is `FILE`, the `ix-aiur-scs-v1` constraint system that
//! `plonk_export` wrote for this terminal's stage (`plonk::scs`): gnark
//! compiles it with the terminal's pairing configuration (`pairing.json`),
//! one constraint per file gate plus `PairingCheck` on the 18 private output
//! words and the commitment. `OUT_DIR/manifest.json` pins both by SHA-256.
//! The witness holds the file's input wires (the 2 public statement limbs,
//! the outputs and every table's cells); gnark computes the other wires.
//!
//! `--stage-only` writes `OUT_DIR/stage.json` (the function and ROM circuits
//! at this execution's power-of-two capacities, which `plonk_export` reads)
//! and `OUT_DIR/pairing.json`, and stops.
//!
//! `--reuse` keeps `OUT_DIR/prepared` (circuit, keys, input layout) when its
//! manifest names this file's and this configuration's digests, skipping
//! compilation, SRS export and setup; otherwise it prepares afresh.
//!
//! `--wait-for FILE` (with `--reuse`) opens the prover on the prepared keys
//! named by `OUT_DIR/manifest.json` before `NARROW_DIR` is read, then waits
//! until `FILE` exists, so the key load overlaps the narrow stage.
//!
//! `--cuda` proves with the CUDA PLONK backend (a `cuda,plonk` build) with a
//! device memory budget of `IX_PLONK_CUDA_MEMORY_GIB` (64 by default).
//!
//! - `ARTIFACT` is the exported terminal (`compress_final_narrow_export`),
//!   whose fixed tables hold the narrow stage's key and configuration.
//! - `NARROW_DIR` holds the narrow stage's `claims.bin`, `proof.bin`, `key.bin`
//!   and `narrow.json` (`aiur_template_v2_init --save`); `POLICY` is the chain
//!   policy (`IXAUKG01`).
//!
//! The terminal executes on the narrow proof and its folded pair is checked
//! against the Ignition anchors. The tool proves, verifies the proof against
//! the verifying key's digest and the Ignition anchors, and checks that a
//! changed statement is refused and rejected. It writes the proof, its
//! Solidity encoding and `summary.json` with each phase's time and the
//! process's peak RSS after it.

#[cfg(not(feature = "plonk"))]
fn main() -> Result<(), Box<dyn std::error::Error>> {
  Err("aiur_narrow_terminal_prove requires --features plonk".into())
}

#[cfg(feature = "plonk")]
fn main() -> Result<(), Box<dyn std::error::Error>> {
  prove::main()
}

#[cfg(feature = "plonk")]
mod prove {
  use aiur::{
    artifact::WidePackage, field::FieldBackend, hints::HintChannels,
    maps::MapOverrides, trace::TracePlan,
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
      plonk::{gnark, scs},
    },
    pipeline::SetupConfig,
  };
  use serde_json::{Value, json};
  use sha2::{Digest, Sha256};
  use std::{
    fs,
    path::Path,
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

  struct Scs<'p, 'a> {
    path: &'p Path,
    sha256: std::thread::JoinHandle<Result<String, String>>,
    pairing: Vec<u8>,
    plan: &'p TracePlan<'a, Bn254>,
    compiler: Compiler<'p, 'a>,
    capacities: &'p [usize],
    record: &'p aiur::Execution<Bn254>,
    arguments: &'p [ix_proof_compression::kzg::Scalar],
    out: &'p Path,
    backend: gnark::Backend,
    reuse: bool,
    early: Option<(gnark::Prover, gnark::Manifest)>,
    setup: &'p SetupConfig,
    parameters: &'p ix_proof_compression::kzg::VerifierParams,
    phases: Phases,
    artifact: &'p str,
    artifact_blake3: String,
    statement: Value,
  }

  /// `OUT_DIR/manifest.json` when it names a circuit prepared from this SCS
  /// file and pairing configuration.
  fn reusable_scs(
    out: &Path,
    scs_sha256: &str,
    pairing_sha256: &str,
  ) -> Option<gnark::Manifest> {
    let manifest: gnark::Manifest =
      serde_json::from_slice(&fs::read(out.join("manifest.json")).ok()?)
        .ok()?;
    (manifest.scs_sha256 == scs_sha256
      && manifest.pairing_sha256 == pairing_sha256)
      .then_some(manifest)
  }

  /// The terminal proof on the circuit compiled from the Lean-exported
  /// constraint system (`--scs`): compile and prepare it unless `--reuse`
  /// finds it prepared, build the witness of its input wires, prove and
  /// verify.
  fn prove_scs(run: Scs<'_, '_>) -> Result<(), Error> {
    let Scs {
      path,
      sha256,
      pairing,
      plan,
      compiler,
      capacities,
      record,
      arguments,
      out,
      backend,
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
    let scs_sha256 = sha256.join().map_err(|_| "SCS digest thread")??;
    let pairing_sha256 = format!("{:x}", Sha256::digest(&pairing));
    let prepared = out.join("prepared");
    let reused = if reuse {
      reusable_scs(out, &scs_sha256, &pairing_sha256)
    } else {
      None
    };
    if early.is_some() && reused.is_none() {
      return Err(
        "--wait-for: the prepared circuit is not this SCS file's".into(),
      );
    }
    phases.record("scs_digest", started);
    let (srs_blake3, srs_powers, manifest) = if let Some(manifest) = reused {
      eprintln!("reusing {} (SCS {scs_sha256})", prepared.display());
      let powers = fs::read(out.join("plonk-srs.json"))
        .ok()
        .and_then(|bytes| serde_json::from_slice::<Value>(&bytes).ok())
        .map_or(Value::Null, |receipt| receipt["powers"].clone());
      (manifest.srs_blake3.clone(), powers, manifest)
    } else {
      let pairing_path = out.join("pairing.json");
      fs::write(&pairing_path, &pairing)?;
      let source = gnark::ScsSource {
        scs: path,
        scs_sha256: &scs_sha256,
        pairing: &pairing_path,
        pairing_sha256: &pairing_sha256,
      };
      let started = Instant::now();
      let circuit = out.join("circuit.bin");
      let info = gnark::compile_scs(&source, &circuit)?;
      phases.record("compile", started);
      eprintln!("{} constraints, domain {}", info.constraints, info.domain);
      let started = Instant::now();
      let srs = out.join("plonk-srs.bin");
      ix_proof_compression::pipeline::plonk::export_parameters(
        info.domain as usize,
        &srs,
        setup,
      )?;
      let receipt: Value =
        serde_json::from_slice(&fs::read(srs.with_extension("json"))?)?;
      let srs_blake3 =
        receipt["blake3"].as_str().ok_or("SRS receipt")?.to_owned();
      phases.record("export_srs", started);
      let started = Instant::now();
      let circuit_hash = gnark::Artifact {
        sha256: sha256_file(&circuit)?,
        bytes: fs::metadata(&circuit)?.len(),
      };
      if prepared.exists() {
        fs::remove_dir_all(&prepared)?;
      }
      // A Lagrange basis left by an earlier setup of this domain is reused;
      // gnark checks it against the recorded digest.
      let lagrange = out.join("lagrange.bin");
      let lagrange_sha256 =
        if lagrange.exists() { sha256_file(&lagrange)? } else { String::new() };
      let manifest = gnark::prepare_scs(&gnark::ScsPreparation {
        source: &source,
        circuit: &circuit,
        circuit_hash: &circuit_hash,
        info: &info,
        srs: &srs,
        srs_blake3: &srs_blake3,
        lagrange: &lagrange,
        lagrange_sha256: &lagrange_sha256,
        output: &prepared,
      })?;
      fs::write(
        out.join("manifest.json"),
        serde_json::to_vec_pretty(&manifest)?,
      )?;
      phases.record(
        if lagrange_sha256.is_empty() {
          "setup"
        } else {
          "setup_cached_lagrange"
        },
        started,
      );
      (srs_blake3, receipt["powers"].clone(), manifest)
    };

    let started = Instant::now();
    let layout = fs::read(prepared.join("inputs.json"))?;
    let pinned = manifest
      .files
      .get("inputs.json")
      .ok_or("manifest without inputs.json")?;
    if format!("{:x}", Sha256::digest(&layout)) != pinned.sha256 {
      return Err("prepared inputs.json differs from its manifest".into());
    }
    let witness = scs::Witness::new(
      plan,
      compiler,
      capacities,
      NARROW_ACCUMULATOR_ENTRY,
      serde_json::from_slice(&layout)?,
    )?
    .binary(record, arguments)?;
    phases.record("witness", started);
    let info = &manifest.info;

    let mut prover = match early {
      Some((prover, preloaded)) => {
        if serde_json::to_vec(&preloaded)? != serde_json::to_vec(&manifest)? {
          return Err(
            "the preloaded prover's manifest differs from the prepared circuit"
              .into(),
          );
        }
        prover
      },
      None => {
        let started = Instant::now();
        let prover = gnark::Prover::open(&prepared, &manifest, backend)?;
        phases.record("load", started);
        prover
      },
    };
    let started = Instant::now();
    let proof = prover.prove(&witness, arguments)?;
    phases.record("prove", started);
    let mut wrong = arguments.to_vec();
    wrong[0] += Bn254.one();
    let wrong_statement_refused = prover.prove(&witness, &wrong).is_err();
    prover.close()?;

    let started = Instant::now();
    let key = fs::read(prepared.join("verifying-key.bin"))?;
    let key_pin: [u8; 32] = Sha256::digest(&key).into();
    let anchor_bytes = gnark::anchors(parameters);
    gnark::verify(&key, &key_pin, &proof.native, arguments, &anchor_bytes)?;
    phases.record("verify", started);
    let wrong_statement_rejected =
      gnark::verify(&key, &key_pin, &proof.native, &wrong, &anchor_bytes)
        .is_err();
    if !wrong_statement_rejected {
      return Err("PLONK verifier accepted a changed statement".into());
    }
    fs::write(out.join("proof.bin"), &proof.native)?;
    fs::write(out.join("proof.solidity.bin"), &proof.solidity)?;
    let public_decimal: Vec<String> =
      arguments.iter().map(|value| value.0.to_string()).collect();
    let summary = json!({
      "format": "ix-aiur-narrow-terminal-plonk-v1",
      "circuit": "ix-aiur-scs-v1", "scs": path, "scs_sha256": scs_sha256, "pairing_sha256": pairing_sha256,
      "entry": NARROW_ACCUMULATOR_ENTRY,
      "artifact": artifact, "artifact_blake3": artifact_blake3,
      "statement": statement,
      "backend": if matches!(backend, gnark::Backend::Cpu) { "cpu" } else { "cuda" },
      "capacities": "power of two: this execution's padded rows",
      "constraints": info.constraints, "domain": info.domain, "public_inputs": info.public_inputs,
      "commitments": info.commitments,
      "input_wires": (witness.len() - 12) / 32,
      "witness_bytes": witness.len(), "witness_sha256": format!("{:x}", Sha256::digest(&witness)),
      "srs_blake3": srs_blake3, "srs_powers": srs_powers,
      "verifying_key_sha256": format!("{:x}", Sha256::digest(&key)),
      "proof_bytes": proof.native.len(), "solidity_proof_bytes": proof.solidity.len(),
      "public_inputs_decimal": public_decimal,
      "wrong_statement_refused_by_prover": wrong_statement_refused,
      "wrong_statement_rejected_by_verifier": wrong_statement_rejected,
      "phases": phases.0,
      "peak_rss_gb": peak_rss_gb(),
    });
    fs::write(out.join("summary.json"), serde_json::to_vec_pretty(&summary)?)?;
    println!("{}", serde_json::to_string_pretty(&summary)?);
    Ok(())
  }

  pub(super) fn main() -> Result<(), Error> {
    let args: Vec<_> = std::env::args().skip(1).collect();
    let [artifact, narrow, policy, out, flags @ ..] = args.as_slice() else {
      return Err(
        "usage: aiur_narrow_terminal_prove ARTIFACT NARROW_DIR POLICY OUT_DIR --scs FILE [--cuda] [--reuse] [--wait-for FILE] | --stage-only".into(),
      );
    };
    let reuse = flags.iter().any(|f| f == "--reuse");
    let backend = if flags.iter().any(|f| f == "--cuda") {
      let gib: u64 = std::env::var("IX_PLONK_CUDA_MEMORY_GIB")
        .unwrap_or_else(|_| "64".into())
        .parse()?;
      gnark::Backend::Cuda {
        device: 0,
        memory_bytes: gib << 30,
        mask_msm: false,
      }
    } else {
      gnark::Backend::Cpu
    };
    let narrow = Path::new(narrow);
    let out = Path::new(out);
    let scs_path =
      flags.iter().position(|f| f == "--scs").and_then(|i| flags.get(i + 1));
    // The 0.8 GB file's digest is computed while the terminal executes.
    let scs_hash = scs_path.map(|p| {
      let p = std::path::PathBuf::from(p);
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
    let parameters =
      multi_stark::config::ProofConfig::pcs(&config).parameters();
    let policy_bytes = fs::read(policy)?;
    let policy = PackedPolicy::from_chain_bytes(parameters, &policy_bytes)?;
    let wait_for = flags
      .iter()
      .position(|f| f == "--wait-for")
      .and_then(|i| flags.get(i + 1));
    let mut early = None;
    let started = match wait_for {
      Some(file) => {
        if !reuse {
          return Err("--wait-for needs --reuse".into());
        }
        phases.record("setup", started);
        let manifest: gnark::Manifest =
          serde_json::from_slice(&fs::read(out.join("manifest.json"))?)?;
        let started = Instant::now();
        early = Some((
          gnark::Prover::open(&out.join("prepared"), &manifest, backend)?,
          manifest,
        ));
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
      record_json["stage"].as_u64().ok_or("narrow stage")? as u32;
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
      return Err(
        "terminal accumulator fails the Ignition pairing check".into(),
      );
    }
    phases.record("execute", started);

    let started = Instant::now();
    let compiler = Compiler::new(&plan)?;
    let capacities: Vec<usize> = compiler
      .row_counts(&record)?
      .into_iter()
      .map(|rows| rows.max(1))
      .collect();
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
    let scs_path =
      scs_path.ok_or("--scs FILE is required (or --stage-only)")?;
    let pairing = serde_json::to_vec(&scs::pairing(
      &plan,
      NARROW_ACCUMULATOR_ENTRY,
      &configuration,
    )?)?;
    prove_scs(Scs {
      path: Path::new(scs_path),
      sha256: scs_hash.ok_or("SCS digest")?,
      pairing,
      plan: &plan,
      compiler,
      capacities: &capacities,
      record: &record,
      arguments: &arguments,
      out,
      backend,
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
}
