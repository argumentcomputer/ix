//! A packed CompressGL stage followed by packed CompressBN chain stages.
//!
//! `compress_gl_packed_chain GL_ARTIFACT ROOT_DIR ROOT_KEY_BLAKE3 BN_ARTIFACT
//! LOG_CAP STAGES OUT_DIR [--dev] [--lookup-budget B] [--quotient-degree Q]
//! [--streaming] [--gl-shards K] [--shards K --shard-profile REPORT]
//! [--gl-only]`
//!
//! `ROOT_DIR` holds `root-vk.bin`, `root-claims.bin` and `root-proof.bin`;
//! the root key must hash to `ROOT_KEY_BLAKE3`. With `--wrap-package PKG
//! --wrap-layout CONFIG --wrap-dir DIR`, CompressGL verifies the normalized
//! `CompressWrap` proof in `DIR` (`key.bin`, `claims.bin`, `proof.bin`)
//! instead of the root, admitted by a [`compress_gl::WrapPolicy`] that pins
//! the wrapper artifact, key and layout; the chain's statement is then the
//! policy's image of the root statement. CompressGL is proven with
//! packed SHPLONK under `LOG_CAP` and the lookup budget. With `--gl-shards K`
//! its key fixes up to `K` copies of each function circuit, chosen by
//! [`plan_copies`] from this execution's raw rows.
//!
//! CompressGL's circuits are the Lean exporter's (`wide_export` at
//! `IX_WIDE_EXPORT`, cached under `IX_WIDE_EXPORT_CACHE`; `--wide-export EXE`
//! and `--wide-cache DIR` override them): the layout's single chips as
//! units, its trace groups as groups, the fixed maps in the compiler's shared
//! layout and one `romCircuit` table per memory width, read literally
//! ([`wide::Stage`]), in the export's order (units, groups, maps, ROMs). The
//! compiler only generates the witness, which is permuted into that order.
//! ROM tables have a fixed address column, so their heights are part of the
//! key: `--gl-rom FILE` pins them (`ix-compress-gl-rom-1`, `rom: [[words,
//! rows]…]`); without it each is the next power of two of this execution's
//! ROM count scaled by `1 + --gl-rom-headroom` (default 0). The capacities
//! used are written to `OUT_DIR/gl-rom.json`, and an execution exceeding a
//! pinned capacity fails before proving. `--rust-cross-check` compares every
//! exported circuit with the compiler lowering's and builds that lowering's
//! key for reference; `--rust-circuits` proves the compiler lowering's
//! circuits instead (the previous key). With `--wait-for FILE`
//! the setup, the CompressGL artifact and the wrapper package are loaded
//! first and the wrapper proof is read only once `FILE` exists, so the
//! process can start while the wrap is still being proved.
//!
//! Then `STAGES` consecutive stages of `CompressBNPacked::chain_v1` run under
//! a two-key chain policy: the packed CompressGL key at stage one, the chain
//! program's own key afterwards. Every proof is verified natively, a changed
//! output is rejected, each deferred accumulator is checked against the
//! setup's pairing anchors, and each stage's accumulator must equal the
//! native transcript fold ([`fold_packed`]) of its predecessor proof.
use aiur::field::FieldBackend;
use ix_proof_compression::{
  aiur_backend::{
    Bn254,
    compress_bn::{
      Accumulator, Input, PACKED_CHAIN_ENTRY, PackedCapacity, PackedGlProver,
      PackedProver, PolicyDigest, PublicInputs, Stage, StatementDigest,
      TraceLimits, Wrapper, fold_packed, plan_copies, plan_copies_of,
    },
    compress_gl,
    kzg::{Compiler, MAX_TOTAL_ROWS},
    wide,
  },
  kzg::{curve::G1Affine, packed_shplonk::Commitment},
  pipeline::{SetupClass, SetupConfig},
};
use multi_stark::config::ProofConfig;
use serde_json::{Value, json};
use std::{fs, path::PathBuf, time::Instant};

type Error = Box<dyn std::error::Error>;

fn peak_rss_bytes() -> Option<u64> {
  let status = fs::read_to_string("/proc/self/status").ok()?;
  let line = status.lines().find(|l| l.starts_with("VmHWM:"))?;
  let kib: u64 = line.split_whitespace().nth(1)?.parse().ok()?;
  Some(kib * 1024)
}

/// Resets the peak-RSS watermark so each phase reports its own peak.
fn reset_peak_rss() {
  let _ = fs::write("/proc/self/clear_refs", "5");
}

fn flag<T: std::str::FromStr>(
  args: &[String],
  name: &str,
) -> Result<Option<T>, Error> {
  match args.iter().position(|a| a == name) {
    None => Ok(None),
    Some(i) => Ok(Some(
      args
        .get(i + 1)
        .ok_or("missing flag value")?
        .parse()
        .map_err(|_e| format!("invalid {name}"))?,
    )),
  }
}

/// Packs, committed columns and requested/extra opened values of one proof.
fn proof_counts(
  p: &ix_proof_compression::aiur_backend::compress_bn::PackedProof,
) -> Value {
  let rounds: [&Commitment; 3] = [
    &p.commitments.stage_1_trace,
    &p.commitments.stage_2_trace,
    &p.commitments.quotient_chunks,
  ];
  let packs = rounds.map(|c| c.packs.len());
  let columns =
    rounds.map(|c| c.matrices.iter().map(|m| m.width as usize).sum::<usize>());
  let opened = |round: &Vec<Vec<Vec<_>>>| {
    round.iter().flatten().map(Vec::len).sum::<usize>()
  };
  let requested = opened(&p.stage_1_opened_values)
    + opened(&p.stage_2_opened_values)
    + opened(&p.quotient_opened_values)
    + p.preprocessed_opened_values.as_ref().map_or(0, opened);
  json!({
    "commitment_points": {"main": packs[0], "lookup": packs[1], "quotient": packs[2]},
    "committed_columns": {"main": columns[0], "lookup": columns[1], "quotient": columns[2]},
    "variable_g1_points": packs.iter().sum::<usize>() + 2,
    "requested_values": requested,
    "extra_values": p.opening_proof.extra_values.len(),
  })
}

fn main() -> Result<(), Error> {
  tracing_subscriber::fmt()
    .with_env_filter(tracing_subscriber::EnvFilter::from_default_env())
    .with_writer(std::io::stderr)
    .init();
  let args: Vec<String> = std::env::args().skip(1).collect();
  let [gl_path, root_dir, root_pin, artifact_path, log_cap, stages, out, ..] =
    args.as_slice()
  else {
    return Err("usage: compress_gl_packed_chain GL_ARTIFACT ROOT_DIR ROOT_KEY_BLAKE3 BN_ARTIFACT LOG_CAP STAGES OUT_DIR [options]".into());
  };
  let development = args.iter().any(|a| a == "--dev");
  let streaming = args.iter().any(|a| a == "--streaming");
  let gl_only = args.iter().any(|a| a == "--gl-only");
  let stages: u32 = stages.parse()?;
  let capacity = PackedCapacity {
    log_cap: log_cap.parse()?,
    quotient_degree: flag(&args, "--quotient-degree")?.unwrap_or(4),
    lookup_quotient_budget: flag(&args, "--lookup-budget")?,
  };
  let out = PathBuf::from(out);
  fs::create_dir_all(&out)?;
  #[cfg(feature = "cuda")]
  {
    use ix_proof_compression::kzg::cuda;
    let srs_cache =
      std::env::var("IX_KZG_CUDA_SRS_CACHE").as_deref() == Ok("1");
    cuda::configure(cuda::Settings { srs_cache, ..cuda::Settings::default() });
  }

  let process_started = Instant::now();
  let started = Instant::now();
  let setup = SetupConfig::from_env(development)?;
  let mut config = capacity.config(&setup)?;
  if streaming {
    config = config.with_streaming_lookups().with_streaming_quotient();
  }
  let setup_class = SetupClass::of(config.pcs().parameters());
  let srs_seconds = started.elapsed().as_secs_f64();

  let gl_artifact = fs::read(gl_path)?;
  let gl_wrapper = compress_gl::Wrapper::from_bytes(
    &gl_artifact,
    blake3::hash(&gl_artifact).as_bytes(),
  )?;
  let rust_circuits = args.iter().any(|a| a == "--rust-circuits");
  let cross_check = args.iter().any(|a| a == "--rust-cross-check");
  let pinned_rom = match flag::<String>(&args, "--gl-rom")? {
    None => None,
    Some(path) => Some(read_rom(&path)?),
  };
  let wide_export = |rom: &[(usize, usize)]| -> Result<wide::Exported, Error> {
    let (env_exporter, env_cache) =
      match flag::<String>(&args, "--wide-export")? {
        Some(_) => (PathBuf::new(), None),
        None => wide::exporter_from_env()?,
      };
    let exporter = flag::<String>(&args, "--wide-export")?
      .map_or(env_exporter, PathBuf::from);
    let cache =
      flag::<String>(&args, "--wide-cache")?.map(PathBuf::from).or(env_cache);
    let input = wide::grouped_input(
      gl_wrapper.plan(),
      capacity.cap()?,
      rom,
      gl_path.as_ref(),
      blake3::hash(&gl_artifact).to_hex().as_str(),
      compress_gl::ENTRY,
    )?;
    Ok(wide::export_cached(
      &input,
      &exporter,
      cache.as_deref(),
      &out.join("gl-wide"),
    )?)
  };
  // With pinned ROM capacities the export does not depend on the execution
  // and runs before the predecessor proof is awaited.
  let mut early_export = match (&pinned_rom, rust_circuits) {
    (Some(rom), false) => Some(wide_export(rom)?),
    _ => None,
  };
  let root_dir = PathBuf::from(root_dir);
  let root_key = fs::read(root_dir.join("root-vk.bin"))?;
  let root_claims = fs::read(root_dir.join("root-claims.bin"))?;
  let root_proof = fs::read(root_dir.join("root-proof.bin"))?;
  let root = stark_verifier::compress_wrap::Input::from_bytes(
    &root_key,
    *blake3::Hash::from_hex(root_pin)?.as_bytes(),
    &root_claims,
    &root_proof,
  )?;

  let wrap_report;
  let (mut ready_seconds, mut wait_seconds) = (0.0, 0.0);
  let wrapped = match flag::<String>(&args, "--wrap-package")? {
    None => {
      wrap_report = Value::Null;
      None
    },
    Some(package) => {
      let config_path: String =
        flag(&args, "--wrap-layout")?.ok_or("missing --wrap-layout")?;
      let wrap_dir = PathBuf::from(
        flag::<String>(&args, "--wrap-dir")?.ok_or("missing --wrap-dir")?,
      );
      let (package, _) = aiur::artifact::Package::load(package.as_ref())?;
      let config: stark_verifier::compress_wrap::LayoutConfig =
        serde_json::from_slice(&fs::read(&config_path)?)?;
      let wrapper = stark_verifier::compress_wrap::Wrapper::for_layout(
        package,
        aiur::trace::stark::Parameters::default(),
        None,
        &config.layout,
      )?;
      config.check(&wrapper)?;
      let policy = compress_gl::WrapPolicy::new(&wrapper, &config.layout)?;
      ready_seconds = process_started.elapsed().as_secs_f64();
      if let Some(file) = flag::<String>(&args, "--wait-for")? {
        let waiting = Instant::now();
        while !std::path::Path::new(&file).exists() {
          std::thread::sleep(std::time::Duration::from_millis(20));
        }
        wait_seconds = waiting.elapsed().as_secs_f64();
      }
      let started = Instant::now();
      let key = fs::read(wrap_dir.join("key.bin"))?;
      let claims = fs::read(wrap_dir.join("claims.bin"))?;
      let proof = fs::read(wrap_dir.join("proof.bin"))?;
      let input = policy.admit(
        &wrapper,
        &config.layout,
        root.statement(),
        &key,
        &claims,
        &proof,
      )?;
      let mut changed = claims.clone();
      *changed.last_mut().ok_or("empty wrapper claims")? ^= 1;
      if policy
        .admit(
          &wrapper,
          &config.layout,
          root.statement(),
          &key,
          &changed,
          &proof,
        )
        .is_ok()
      {
        return Err("wrap admission accepted a changed claim".into());
      }
      let mut other = config.layout.clone();
      other.log_heights[1] += 1;
      if policy
        .admit(&wrapper, &other, root.statement(), &key, &claims, &proof)
        .is_ok()
      {
        return Err("wrap admission accepted another layout".into());
      }
      wrap_report = json!({
        "config": config_path,
        "grouping": config.grouping,
        "version": config.version,
        "policy": policy,
        "policy_blake3": blake3::Hash::from_bytes(policy.digest()?).to_hex().as_str(),
        "proof_wire_bytes": proof.len(),
        "proof_blake3": blake3::hash(&proof).to_hex().as_str(),
        "admission_seconds": started.elapsed().as_secs_f64(),
        "admission_rejects_changed_claim_and_layout": true,
      });
      Some(input)
    },
  };
  let gl_input = wrapped.as_ref().unwrap_or(&root);

  reset_peak_rss();
  let started = Instant::now();
  let gl_execution = gl_wrapper.execute(gl_input)?;
  let gl_execution_seconds = started.elapsed().as_secs_f64();
  let gl_compiler = Compiler::with_lookup_budget(
    gl_wrapper.plan(),
    capacity.lookup_quotient_budget,
  )?;
  let gl_raw = gl_compiler.raw_row_counts(gl_execution.record())?;
  let shards = flag::<usize>(&args, "--gl-shards")?;
  let shard_costs = (
    flag(&args, "--shard-min-saving")?.unwrap_or(1 << 20),
    flag(&args, "--shard-column-cost")?.unwrap_or(3600),
    flag(&args, "--shard-node-cost")?.unwrap_or(600),
  );
  let rust_copies = || {
    shards.map(|max| {
      plan_copies(
        &gl_compiler,
        &gl_raw,
        max,
        shard_costs.0,
        shard_costs.1,
        shard_costs.2,
      )
    })
  };
  let started = Instant::now();
  let mut wide_report = Value::Null;
  let mut cross_report = Value::Null;
  let gl_prover = if rust_circuits {
    PackedGlProver::with_copies(
      &gl_wrapper,
      capacity,
      config.clone(),
      rust_copies(),
    )?
  } else {
    let rom = match &pinned_rom {
      Some(rom) => rom.clone(),
      None => wide::rom_capacities(
        &gl_compiler,
        &gl_raw,
        flag(&args, "--gl-rom-headroom")?.unwrap_or(0.0),
      )?,
    };
    fs::write(
      out.join("gl-rom.json"),
      serde_json::to_vec_pretty(
        &json!({"format": "ix-compress-gl-rom-1", "rom": rom}),
      )?,
    )?;
    let exported = match early_export.take() {
      Some(exported) => exported,
      None => wide_export(&rom)?,
    };
    let claim = gl_wrapper.plan().public_claim(
      compress_gl::ENTRY,
      &[Bn254.zero(); 16],
      &[],
    )?;
    let stage = wide::Stage::new(
      exported.layout,
      &gl_compiler,
      gl_wrapper.plan(),
      &claim,
      capacity.lookup_quotient_budget,
    )?;
    if stage.rom != rom {
      return Err(
        "the exported ROM tables differ from the requested capacities".into(),
      );
    }
    stage.check_rom(&gl_raw)?;
    wide_report = json!({
      "exporter": flag::<String>(&args, "--wide-export")?
        .or_else(|| std::env::var("IX_WIDE_EXPORT").ok()),
      "exporter_blake3": exported.exporter_blake3,
      "export_dir": exported.dir,
      "cached": exported.cached,
      "seconds": exported.seconds,
      "rom": rom,
      "units_and_groups": stage.function_circuits,
      "exported_graph_nodes": stage.graph_nodes,
    });
    if cross_check {
      let mut check = stage.rust_cross_check(&gl_compiler)?;
      let rust = PackedGlProver::with_copies(
        &gl_wrapper,
        capacity,
        config.clone(),
        rust_copies(),
      )?;
      check["rust_key"] =
        key_stats(rust.system(), rust.copies(), rust.key_bytes());
      eprintln!("Rust cross-check: {check}");
      if check["equal"] != json!(true) {
        return Err(
          format!(
            "exported circuits differ from the compiler lowering: {check}"
          )
          .into(),
        );
      }
      cross_report = check;
    }
    let copies = shards.map(|max| {
      plan_copies_of(
        &stage.inputs,
        stage.function_circuits,
        &stage.rows(&gl_raw),
        max,
        shard_costs.0,
        shard_costs.1,
        shard_costs.2,
      )
    });
    PackedGlProver::from_wide(
      &gl_wrapper,
      capacity,
      config.clone(),
      stage,
      copies,
    )?
  };
  let gl_key_seconds = started.elapsed().as_secs_f64();
  fs::write(out.join("gl-key.bin"), gl_prover.key_bytes())?;
  let (names, gl_inputs, gl_heights, gl_raw) = match gl_prover.stage() {
    Some(stage) => (
      stage.names.clone(),
      stage.inputs.as_slice(),
      stage.rows(&gl_compiler.row_counts(gl_execution.record())?),
      stage.rows(&gl_raw),
    ),
    None => (
      gl_compiler.names().to_vec(),
      gl_compiler.inputs(),
      gl_compiler.row_counts(gl_execution.record())?,
      gl_raw,
    ),
  };
  let gl_cells = |rows: &[usize]| -> usize {
    gl_inputs.iter().zip(rows).map(|(i, &r)| i.main_width * r).sum()
  };
  let gl_padded = gl_cells(&gl_heights);
  let gl_unpadded = gl_cells(&gl_raw);
  let gl_quotient = gl_prover
    .system()
    .circuits
    .iter()
    .map(|c| c.quotient_degree())
    .max()
    .unwrap_or(1);
  let timings = gl_prover.system().config.pcs().timings();
  let (commit0, open0) = (timings.commit_seconds(), timings.open_seconds());
  let gl_proven = gl_prover.prove(&gl_execution)?;
  let (gl_commit, gl_open) =
    (timings.commit_seconds() - commit0, timings.open_seconds() - open0);
  let mut changed = gl_proven.claim.clone();
  *changed.last_mut().ok_or("empty claim")? += Bn254.one();
  if gl_prover.verify(&changed, &gl_proven.proof).is_ok() {
    return Err("packed CompressGL accepted a changed output".into());
  }
  let gl_peak = peak_rss_bytes();
  let gl_report = json!({
    "program": compress_gl::ENTRY,
    "artifact": gl_path,
    "artifact_blake3": blake3::hash(&gl_artifact).to_hex().as_str(),
    "root_key_blake3": root_pin,
    "root_claims_blake3": blake3::hash(&root_claims).to_hex().as_str(),
    "root_proof_blake3": blake3::hash(&root_proof).to_hex().as_str(),
    "predecessor": if wrapped.is_some() { "normalized CompressWrap proof" } else { "raw root proof" },
    "wrap": wrap_report,
    "key_wire_bytes": gl_prover.key_bytes().len(),
    "key_blake3": blake3::hash(gl_prover.key_bytes()).to_hex().as_str(),
    "circuits": gl_prover.system().circuits.len(),
    "circuit_source": if rust_circuits { "compiler lowering" } else { "wide_export" },
    "key": key_stats(gl_prover.system(), gl_prover.copies(), gl_prover.key_bytes()),
    "wide_export": wide_report,
    "rust_cross_check": cross_report,
    "copies": gl_prover.copies().iter().enumerate().filter(|&(_, &k)| k > 1)
      .map(|(i, &k)| json!([names[i], k])).collect::<Vec<_>>(),
    "shards": gl_proven.shards.iter().map(|(c, h)| json!([names[*c], h])).collect::<Vec<_>>(),
    "counts": proof_counts(&gl_proven.proof),
    "proof_wire_bytes": gl_proven.source_proof.len(),
    "proof_blake3": blake3::hash(&gl_proven.source_proof).to_hex().as_str(),
    "native_accepts": true,
    "native_rejects_changed_output": true,
    "cells": {
      "main_cells_padded": gl_padded,
      "main_cells_unpadded": gl_unpadded,
      "main_cells_padded_sharded": gl_proven.main_cells,
      "max_height": gl_heights.iter().max(),
      "active_circuits": gl_heights.iter().filter(|&&h| h != 0).count(),
      "quotient_degree": gl_quotient,
      "instructions": gl_execution.record().instructions,
    },
    "seconds": {
      "execution": gl_execution_seconds,
      "key": gl_key_seconds,
      "trace": gl_proven.trace_seconds,
      "prove": gl_proven.proving_seconds,
      "pcs_commit": gl_commit,
      "pcs_open": gl_open,
      "verify": gl_proven.verification_seconds,
    },
    "peak_rss_bytes": gl_peak,
    "shape": names.iter().zip(&gl_heights).filter(|&(_, &h)| h != 0)
      .map(|(n, h)| json!([n, h])).collect::<Vec<_>>(),
  });
  fs::create_dir_all(out.join("gl"))?;
  fs::write(out.join("gl/proof.bin"), &gl_proven.source_proof)?;
  fs::write(out.join("gl/claims.bin"), &gl_proven.source_claims)?;
  fs::write(
    out.join("gl/report.json"),
    serde_json::to_vec_pretty(&gl_report)?,
  )?;
  eprintln!(
    "packed CompressGL: {} points, {} bytes, prove {:.1}s, peak RSS {:?}",
    gl_report["counts"]["variable_g1_points"],
    gl_proven.source_proof.len(),
    gl_proven.proving_seconds,
    gl_peak
  );
  let statement = StatementDigest::from_root(gl_input.statement());
  let gl_claims = gl_proven.source_claims.clone();
  let gl_proof = gl_proven.source_proof.clone();
  let mut native_predecessor =
    (gl_proven.claim.clone(), gl_proven.proof.clone(), None);
  drop(gl_proven);
  drop(gl_execution);
  let mut summary = json!({
    "format": "ix-aiur-compress-gl-packed-chain-v1",
    "setup": setup_class.label(),
    "capacity": capacity,
    "streaming": streaming,
    "backend": if cfg!(feature = "cuda") { "cuda" } else { "cpu" },
    "seconds": {"srs": srs_seconds, "ready": ready_seconds, "wait": wait_seconds},
    "gl": gl_report,
  });
  if gl_only {
    fs::write(out.join("summary.json"), serde_json::to_vec_pretty(&summary)?)?;
    return Ok(());
  }

  let artifact = fs::read(artifact_path)?;
  let wrapper = Wrapper::from_bytes_with_entry(
    &artifact,
    blake3::hash(&artifact).as_bytes(),
    PACKED_CHAIN_ENTRY,
  )?;
  let copies = match flag::<usize>(&args, "--shards")? {
    None => None,
    Some(max) => {
      let path: String =
        flag(&args, "--shard-profile")?.ok_or("missing shard profile")?;
      Some(copies_from_report(
        &wrapper,
        capacity,
        &path,
        max,
        flag(&args, "--shard-min-saving")?.unwrap_or(1 << 20),
        flag(&args, "--shard-column-cost")?.unwrap_or(3600),
        flag(&args, "--shard-node-cost")?.unwrap_or(600),
      )?)
    },
  };
  let started = Instant::now();
  let prover = PackedProver::with_copies(&wrapper, capacity, config, copies)?;
  let key_seconds = started.elapsed().as_secs_f64();
  fs::write(out.join("key.bin"), prover.key_bytes())?;
  let policy = prover.chain_policy(&gl_prover)?.to_bytes();
  fs::write(out.join("policy.bin"), &policy)?;

  let mut public = PublicInputs {
    policy: PolicyDigest::from_trusted(*blake3::hash(&policy).as_bytes()),
    stage: Stage::FIRST,
    statement,
  };
  let (mut key, mut claims, mut proof) =
    (gl_prover.key_bytes().to_vec(), gl_claims, gl_proof);
  let limits = TraceLimits {
    max_height: capacity.cap()?,
    max_total_rows: MAX_TOTAL_ROWS,
    max_trace_bytes: 160 << 30,
  };
  let bn_names = Compiler::with_lookup_budget(
    wrapper.plan(),
    capacity.lookup_quotient_budget,
  )?
  .names()
  .to_vec();
  let mut reports = vec![];
  for _ in 0..stages {
    reset_peak_rss();
    let stage = public.stage.get();
    let dir = out.join(format!("stage-{stage}"));
    fs::create_dir_all(&dir)?;
    let input = Input::from_packed_source(
      public,
      key.clone(),
      claims.clone(),
      proof.clone(),
      policy.clone(),
    )?;
    let started = Instant::now();
    let execution = wrapper.execute(&input, 64 << 30)?;
    let execution_seconds = started.elapsed().as_secs_f64();
    let timings = prover.system().config.pcs().timings();
    let (commit0, open0) = (timings.commit_seconds(), timings.open_seconds());
    let proven = prover.prove(&execution, limits)?;
    let (commit, open) =
      (timings.commit_seconds() - commit0, timings.open_seconds() - open0);
    drop(execution);
    let mut changed = proven.claim.clone();
    *changed.last_mut().ok_or("empty claim")? += Bn254.one();
    if prover.verify(&changed, &proven.proof).is_ok() {
      return Err("accepted a changed output".into());
    }
    proven.accumulator.check_pairing(prover.parameters())?;
    let (native_claim, native_proof, native_previous) = &native_predecessor;
    let (system, previous) = match native_previous {
      None => (
        gl_prover.system(),
        Accumulator::from_points(&[G1Affine::identity(); 2])?,
      ),
      Some(previous) => (prover.system(), Clone::clone(previous)),
    };
    let key_digest = *blake3::hash(&key).as_bytes();
    let (_, folded) = fold_packed(
      system,
      native_claim,
      native_proof,
      public,
      &key_digest,
      &previous,
    )?;
    if folded != proven.accumulator {
      return Err(
        "native transcript fold differs from the Aiur accumulator".into(),
      );
    }
    let profile = &proven.profile;
    let shape: Vec<_> = profile
      .circuits
      .iter()
      .filter(|c| c.height != 0)
      .map(|c| json!([c.name, c.height]))
      .collect();
    let accumulator_hex: String = proven
      .accumulator
      .words()
      .iter()
      .flat_map(|x| {
        x.canonical_limbs_le().into_iter().flat_map(u64::to_le_bytes)
      })
      .map(|b| format!("{b:02x}"))
      .collect();
    let report = json!({
      "stage": stage,
      "program": PACKED_CHAIN_ENTRY,
      "predecessor": if stage == 1 { "packed CompressGL proof" } else { "packed chain proof" },
      "predecessor_key_bytes": key.len(),
      "predecessor_proof_bytes": proof.len(),
      "accumulator_hex": accumulator_hex,
      "native_accepts": true,
      "native_rejects_changed_output": true,
      "native_fold_matches": true,
      "deferred_pairing_holds": true,
      "counts": proof_counts(&proven.proof),
      "shards": proven.shards.iter().map(|(c, h)| json!([bn_names[*c], h])).collect::<Vec<_>>(),
      "proof_wire_bytes": proven.source_proof.len(),
      "proof_blake3": blake3::hash(&proven.source_proof).to_hex().as_str(),
      "verify_cells": {
        "main_cells_padded": profile.main_cells,
        "main_cells_padded_sharded": proven.main_cells,
        "max_height": profile.max_height,
        "total_rows": profile.total_rows,
        "stage2_cells": profile.stage2_accumulator_cells,
        "quotient_degree": profile.quotient_degree,
        "instructions": profile.instructions,
        "active_circuits": shape.len(),
      },
      "seconds": {
        "execution": execution_seconds,
        "trace": proven.trace_seconds,
        "prove": proven.proving_seconds,
        "pcs_commit": commit,
        "pcs_open": open,
        "verify": proven.verification_seconds,
      },
      "peak_rss_bytes": peak_rss_bytes(),
      "shape": shape,
      "function_rows": profile.function_rows.iter().filter(|f| f.rows != 0)
        .map(|f| json!([f.name, f.rows])).collect::<Vec<_>>(),
    });
    fs::write(dir.join("proof.bin"), &proven.source_proof)?;
    fs::write(dir.join("claims.bin"), &proven.source_claims)?;
    fs::write(dir.join("report.json"), serde_json::to_vec_pretty(&report)?)?;
    eprintln!(
      "stage {stage}: {} points, {} bytes, prove {:.1}s, predecessor verify {} padded main cells ({} sharded), max height {}",
      report["counts"]["variable_g1_points"],
      proven.source_proof.len(),
      proven.proving_seconds,
      profile.main_cells,
      proven.main_cells,
      profile.max_height
    );
    reports.push(report);
    key = prover.key_bytes().to_vec();
    native_predecessor = (proven.claim, proven.proof, Some(proven.accumulator));
    claims = proven.source_claims;
    proof = proven.source_proof;
    public.stage = public.stage.next()?;
  }
  summary["artifact"] = json!(artifact_path);
  summary["artifact_blake3"] = json!(blake3::hash(&artifact).to_hex().as_str());
  summary["entry"] = json!(PACKED_CHAIN_ENTRY);
  summary["key_wire_bytes"] = json!(prover.key_bytes().len());
  summary["key_blake3"] =
    json!(blake3::hash(prover.key_bytes()).to_hex().as_str());
  summary["circuits"] = json!(prover.system().circuits.len());
  summary["copies"] = prover
    .copies()
    .iter()
    .enumerate()
    .filter(|&(_, &k)| k > 1)
    .map(|(i, &k)| json!([bn_names[i], k]))
    .collect();
  summary["policy_blake3"] = json!(blake3::hash(&policy).to_hex().as_str());
  summary["seconds"]["key"] = json!(key_seconds);
  summary["stages"] = json!(reports);
  fs::write(out.join("summary.json"), serde_json::to_vec_pretty(&summary)?)?;
  Ok(())
}

/// `ix-compress-gl-rom-1`: `(words, rows)` per ROM table.
fn read_rom(path: &str) -> Result<Vec<(usize, usize)>, Error> {
  let v: Value = serde_json::from_slice(&fs::read(path)?)?;
  if v["format"] != "ix-compress-gl-rom-1" {
    return Err(format!("{path}: not an ix-compress-gl-rom-1 file").into());
  }
  Ok(serde_json::from_value(v["rom"].clone())?)
}

/// Size of a packed key: distinct circuits, those with fixed columns, and
/// their constraint-graph nodes (one copy each, as the key bytes hold them).
fn key_stats(
  system: &multi_stark::system::System<
    ix_proof_compression::kzg::packed_shplonk::PackedShplonkConfig,
  >,
  copies: &[usize],
  key_bytes: &[u8],
) -> Value {
  let mut first = 0;
  let (mut nodes, mut fixed, mut fixed_rows) = (0, 0, 0);
  for &k in copies {
    let c = &system.circuits[first];
    first += k;
    nodes += c.graph.nodes.len();
    if c.preprocessed_height != 0 {
      fixed += 1;
      fixed_rows += c.preprocessed_height;
    }
  }
  json!({
    "bytes": key_bytes.len(),
    "blake3": blake3::hash(key_bytes).to_hex().as_str(),
    "circuits": copies.len(),
    "system_circuits": system.circuits.len(),
    "fixed_circuits": fixed,
    "fixed_rows": fixed_rows,
    "graph_nodes": nodes,
  })
}

/// Copy counts from the per-function rows of a stage report, summed per
/// compiler circuit through the plan's layout.
fn copies_from_report(
  wrapper: &Wrapper,
  capacity: PackedCapacity,
  path: &str,
  max_copies: usize,
  min_saving: usize,
  column_cost: usize,
  node_cost: usize,
) -> Result<Vec<usize>, Error> {
  let report: Value = serde_json::from_slice(&fs::read(path)?)?;
  let rows: std::collections::HashMap<String, usize> = report["function_rows"]
    .as_array()
    .ok_or("report without function rows")?
    .iter()
    .map(|entry| {
      Ok((
        entry[0].as_str().ok_or("function name")?.to_owned(),
        usize::try_from(entry[1].as_u64().ok_or("function rows")?)?,
      ))
    })
    .collect::<Result<_, Error>>()?;
  let plan = wrapper.plan();
  let compiler =
    Compiler::with_lookup_budget(plan, capacity.lookup_quotient_budget)?;
  let layout = plan.layout()?;
  let mut raw = vec![0usize; compiler.inputs().len()];
  for (function, &chip) in plan.function_chips().iter().enumerate() {
    let name = &plan.program().program().functions[function].name;
    raw[layout.placements[chip].circuit] +=
      rows.get(name).copied().unwrap_or(0);
  }
  Ok(plan_copies(
    &compiler,
    &raw,
    max_copies,
    min_saving,
    column_cost,
    node_cost,
  ))
}
