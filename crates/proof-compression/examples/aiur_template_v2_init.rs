//! The fixed-key narrow compression stage (`CompressNarrowFixed::step_v1`,
//! stage one) through the narrow template backend: counts and, with
//! `--prove`, a packed-SHPLONK proof.
//!
//! usage: aiur_template_v2_init NARROW.ixa GL_DIR OUT_DIR
//!   [--headroom H] [--prove] [--width W] [--log-shard L]
//!
//! - `NARROW.ixa` is the stage's export (`compress_narrow_fixed_export`, the
//!   CompressGL key in its tables); `GL_DIR` holds the CompressGL proof
//!   (`gl-key.bin`, `gl/{claims,proof}.bin`) and `policy.bin`, or
//!   `--policy FILE`.
//! - Capacities are this execution's instances times `1 + H` (`H` = 0 by
//!   default); an unrolled `Blake3::compress` instance is one compression.
//! - `--config FILE` fixes the stage's capacities, ROM capacities, width,
//!   shard height and shard count from FILE (as written by
//!   `--write-config FILE`) instead of deriving them from this execution;
//!   witness generation admits the execution against them. `--shards N`
//!   fixes the shard count of a derived configuration.
//! - `--prove` (requires `--config`) loads the Ignition SRS named by
//!   `IX_KZG_SRS`, commits the fixed matrix once, proves with streaming
//!   lookups and quotients, verifies natively and checks that a changed
//!   output is rejected.
//! - **Circuits and layout.** With `--config` every circuit proved comes
//!   from the verified Lean pass: the exporter (`--lean-exporter PATH`,
//!   default `IX_TILING_EXPORT2` or `MultiStark/.lake/build/bin/tiling_export2`)
//!   runs on this configuration's format-2 input (`OUT_DIR/lean-input.json`:
//!   the artifact and the configuration, `template::v2::lean::input2`) beside
//!   the execution and wide trace generation, writes
//!   `OUT_DIR/lean-layout.json`, `OUT_DIR/lean-export.log` and the compact map
//!   and ROM tables of `narrow_heap_sound_compact` (`OUT_DIR/lean-tables.bin`),
//!   and streams the fixed matrix through a pipe (it is never stored). The
//!   templates are lowered from the exported `Bridge.lower` graphs, the layout
//!   is validated against them, and the exported fixed matrix, shard circuit
//!   and table circuits are the ones committed and proved
//!   (`Backend::from_lean`). `--lean-input FILE` also copies the input there;
//!   `--rust-cross-check` compares this crate's own lowering and circuit
//!   construction with the export and records the result (diagnostic only).
//!   Without `--config` (sizing a configuration) the backend lowers the
//!   compiler circuits itself and proves nothing.
//! - `--save` (with `--prove`) writes the packed key, claims and proof in the
//!   Aiur wire format (`key.bin`, `claims.bin`, `proof.bin`) and
//!   `narrow.json`: the claim chunk headers `[tag, instance key]` the terminal
//!   fixes, the entry, stage and digests.
//! - `--wait-for FILE` (with `--prove` and `--config`) first does everything
//!   the configuration alone determines: it loads the artifact and the SRS
//!   prefix of the configured shard height, waits for the Lean export,
//!   builds the narrow circuits and commits the fixed slots (or interpolates
//!   the cached commitment). It reads `GL_DIR` only once `FILE` exists, so
//!   this preparation overlaps the CompressGL stage.
//! - `--fixed-commit-cache DIR` keeps the fixed-slot commitment in
//!   `DIR/<layout digest>.commitment`, the digest covering the artifact, the
//!   stage configuration, the exported layout and the SRS prefix. A cached
//!   commitment replaces the fixed round's multi-scalar multiplications; a
//!   wrong one changes the key, which native verification here and the
//!   terminal's embedded key reject.
//! - `--fixed-key` and `--packed` are accepted for compatibility; they name
//!   the only stage and PCS.
use ix_proof_compression::{
  aiur_backend::{
    compress_bn::{
      Input, PACKED_NARROW_FIXED_ENTRY, PolicyDigest, PublicInputs, Stage,
      StatementDigest, Wrapper,
    },
    kzg::Compiler,
    kzg_advice as wire, kzg_packed_advice as packed_wire,
    template::{
      fixed_slots, system_with_slots,
      v2::{Backend, Config, lean},
    },
    wide::with_headroom,
  },
  kzg::{
    Scalar,
    packed_shplonk::{self, PackedShplonkConfig},
    srs::gnark,
  },
};
use multi_stark::{
  config::ProofConfig,
  lookup::LookupValues,
  system::{System, SystemWitness},
  traits::Algebra,
};
use p3_matrix::Matrix;
use serde_json::{Value, json};
use std::{collections::BTreeMap, fs, path::PathBuf, sync::Arc, time::Instant};

type Error = Box<dyn std::error::Error>;

/// The message a panicking thread left, if it panicked with a string.
fn panic_message(payload: &(dyn std::any::Any + Send)) -> &str {
  payload
    .downcast_ref::<&str>()
    .copied()
    .or_else(|| payload.downcast_ref::<String>().map(String::as_str))
    .unwrap_or("non-string panic payload")
}

/// `used / capacity` as a fill fraction; both are row counts far below 2^52.
#[allow(clippy::cast_precision_loss)]
fn ratio(used: usize, capacity: usize) -> f64 {
  used as f64 / capacity as f64
}

fn statement_of(claims: &[u8], first_word: usize) -> [u8; 32] {
  let mut s = [0u8; 32];
  for i in 0..8 {
    let off = 16 + 32 * (first_word + i);
    s[4 * i..4 * i + 4].copy_from_slice(&claims[off..off + 4]);
  }
  s
}

fn flag<T: std::str::FromStr>(args: &[String], name: &str) -> Option<T> {
  args
    .iter()
    .position(|a| a == name)
    .and_then(|i| args.get(i + 1))
    .and_then(|v| v.parse().ok())
}

fn rss_gb() -> f64 {
  let s = fs::read_to_string("/proc/self/status").unwrap_or_default();
  s.lines()
    .find(|l| l.starts_with("VmHWM"))
    .and_then(|l| l.split_whitespace().nth(1))
    .and_then(|v| v.parse::<f64>().ok())
    .unwrap_or(0.0)
    / 1e6
}

fn main() -> Result<(), Error> {
  let args: Vec<String> = std::env::args().skip(1).collect();
  let (artifact, pred, out) =
    (&args[0], PathBuf::from(&args[1]), PathBuf::from(&args[2]));
  fs::create_dir_all(&out)?;
  let headroom: f64 = flag(&args, "--headroom").unwrap_or(0.0);
  let width: usize = flag(&args, "--width").unwrap_or(8);
  let log_shard: usize = flag(&args, "--log-shard").unwrap_or(25);
  let prove = args.iter().any(|a| a == "--prove");
  let save = args.iter().any(|a| a == "--save");
  let entry: &'static str = PACKED_NARROW_FIXED_ENTRY;
  let stage_number: u32 = 1;
  let commit_cache: Option<PathBuf> =
    flag::<String>(&args, "--fixed-commit-cache").map(PathBuf::from);
  let fixed_config: Option<Value> = match flag::<String>(&args, "--config") {
    Some(path) => Some(serde_json::from_slice(&fs::read(path)?)?),
    None => None,
  };
  #[cfg(feature = "cuda")]
  {
    use ix_proof_compression::kzg::cuda;
    let srs_cache =
      std::env::var("IX_KZG_CUDA_SRS_CACHE").as_deref() == Ok("1");
    cuda::configure(cuda::Settings { srs_cache, ..cuda::Settings::default() });
  }
  let wait_for = flag::<String>(&args, "--wait-for");
  // The SRS prefix a one-shard configuration needs: twice its shard height.
  let early_srs = match (&wait_for, &fixed_config) {
    (Some(_), Some(c)) if prove => {
      let len = 2usize
        << c["log_shard_rows"].as_u64().ok_or("config log_shard_rows")?;
      let path =
        PathBuf::from(std::env::var_os("IX_KZG_SRS").ok_or("IX_KZG_SRS")?);
      let setup =
        ix_proof_compression::pipeline::ignition_parameters()?.public_setup();
      Some((
        len,
        std::thread::spawn(move || {
          let started = Instant::now();
          gnark::load(&path, len, setup)
            .map(|srs| (srs, started.elapsed().as_secs_f64()))
            .map_err(|e| e.to_string())
        }),
      ))
    },
    (Some(_), _) => return Err("--wait-for needs --prove and --config".into()),
    _ => None,
  };

  let bytes = fs::read(artifact)?;
  let hash = blake3::hash(&bytes);
  let wrapper = Wrapper::from_bytes_with_entry(&bytes, hash.as_bytes(), entry)?;
  let policy_path = flag::<String>(&args, "--policy")
    .map_or_else(|| pred.join("policy.bin"), PathBuf::from);
  let policy = fs::read(&policy_path)?;
  let plan = wrapper.plan();
  let compiler = Compiler::with_lookup_budget(plan, Some(4))?;
  let nf = compiler.function_circuits();
  let compress = compiler.names().iter().position(|n| n == "Blake3::compress");
  let roms = compiler.names().iter().filter(|n| n.starts_with("<ROM:")).count();
  let numbers = |v: &Value, k: &str| -> Result<Vec<usize>, Error> {
    v[k]
      .as_array()
      .ok_or(format!("config {k}"))?
      .iter()
      .map(|x| {
        x.as_u64()
          .and_then(|x| usize::try_from(x).ok())
          .ok_or_else(|| format!("config {k}").into())
      })
      .collect()
  };
  let stage_config = |c: &Value| -> Result<Config, Error> {
    if c["format"] != "ix-template-v2-stage-config-v1"
      || c["functions"].as_array().map(Vec::len) != Some(nf)
    {
      return Err("stage configuration does not match this artifact".into());
    }
    Ok(Config {
      width: usize::try_from(c["width"].as_u64().ok_or("config width")?)?,
      capacities: numbers(c, "capacities")?,
      rom_capacities: numbers(c, "rom_capacities")?,
      log_shard_rows: usize::try_from(
        c["log_shard_rows"].as_u64().ok_or("config log_shard_rows")?,
      )?,
      shards: Some(usize::try_from(
        c["shards"].as_u64().ok_or("config shards")?,
      )?),
      lookup_budget: 2,
      unroll_compress: true,
      shard_offsets: true,
      entry: Some(entry.into()),
    })
  };
  let fixed = fixed_config.as_ref().map(stage_config).transpose()?;
  if prove && fixed.is_none() {
    return Err("--prove needs the stage configuration (--config)".into());
  }
  // With a fixed configuration the exporter's input is known before the
  // execution: it runs beside execution and wide trace generation.
  let export = match &fixed {
    Some(config) => {
      let exporter = PathBuf::from(
        flag::<String>(&args, "--lean-exporter").unwrap_or_else(|| {
          std::env::var("IX_TILING_EXPORT2").unwrap_or_else(|_| {
            "MultiStark/.lake/build/bin/tiling_export2".into()
          })
        }),
      );
      let input = out.join("lean-input.json");
      let input2 = lean::input2(
        &compiler,
        plan,
        config,
        std::path::Path::new(artifact),
        hash.to_hex().as_str(),
      )?;
      fs::write(&input, serde_json::to_vec(&input2)?)?;
      if let Some(path) = flag::<String>(&args, "--lean-input") {
        fs::copy(&input, path)?;
      }
      let (layout, log) =
        (out.join("lean-layout.json"), out.join("lean-export.log"));
      let tables = Some(out.join("lean-tables.bin"));
      let height = 1usize << config.log_shard_rows;
      let started = Instant::now();
      Some((
        std::thread::spawn(move || {
          lean::Layout::export(
            &exporter,
            &input,
            &layout,
            &log,
            height,
            tables.as_deref(),
          )
        }),
        started,
      ))
    },
    None => None,
  };
  let (mut fixed, mut export) = (fixed, export);
  let mut early_srs = early_srs;
  // With --wait-for the narrow circuits, the SRS and the fixed-slot setup
  // depend only on the configuration, so they are prepared before the
  // CompressGL proof exists.
  let mut early = None;
  if wait_for.is_some() {
    let (Some(config), Some(export)) = (fixed.take(), export.take()) else {
      return Err("--wait-for needs --prove and --config".into());
    };
    let started = Instant::now();
    let (mut backend, layout_source) =
      adopt(&args, &compiler, plan, config, export)?;
    let lower_s = started.elapsed().as_secs_f64();
    let setup = setup_system(
      &mut backend,
      early_srs.take(),
      commit_cache.as_deref(),
      &hash,
      &fixed_config,
      entry,
      &out,
    )?;
    early = Some((backend, layout_source, lower_s, setup));
  }
  let mut gl_wait_s = 0.0;
  if let Some(file) = &wait_for {
    let started = Instant::now();
    while !std::path::Path::new(file).exists() {
      std::thread::sleep(std::time::Duration::from_millis(20));
    }
    gl_wait_s = started.elapsed().as_secs_f64();
  }
  // A CompressGL claim is `[tag, entry, reserved(8), statement(8)]`.
  let (key_path, claims_path, proof_path, statement_word) = (
    pred.join("gl-key.bin"),
    pred.join("gl/claims.bin"),
    pred.join("gl/proof.bin"),
    10,
  );
  let claims_bytes = fs::read(&claims_path)?;
  let public = PublicInputs {
    policy: PolicyDigest::from_trusted(*blake3::hash(&policy).as_bytes()),
    stage: Stage::new(stage_number)?,
    statement: StatementDigest::new(statement_of(
      &claims_bytes,
      statement_word,
    )),
  };
  let input = Input::from_packed_source(
    public,
    fs::read(&key_path)?,
    claims_bytes,
    fs::read(&proof_path)?,
    policy,
  )?;
  let started = Instant::now();
  let execution = wrapper.execute(&input, 64 << 30)?;
  let exec_s = started.elapsed().as_secs_f64();
  let record = execution.record();
  let raw = compiler.raw_row_counts(record)?;
  let mut capacities = raw[..nf]
    .iter()
    .map(|&n| with_headroom(n, headroom))
    .collect::<Result<Vec<_>, _>>()?;
  if let Some(c) = compress {
    capacities[c] = with_headroom(raw[c] / 8, headroom)?;
  }
  let call_args = public.arguments();
  let started = Instant::now();
  let wide = if prove {
    Some(compiler.generate(record, entry, &call_args)?)
  } else {
    None
  };
  let wide_s = started.elapsed().as_secs_f64();
  let started = Instant::now();
  let mut layout_source = json!(null);
  let mut early_setup = None;
  let (mut backend, lower_s) = match (early, fixed, export) {
    (Some((backend, source, lower_s, setup)), _, _) => {
      layout_source = source;
      early_setup = Some(setup);
      (backend, lower_s)
    },
    (None, Some(config), Some(export)) => {
      let (backend, source) = adopt(&args, &compiler, plan, config, export)?;
      layout_source = source;
      (backend, started.elapsed().as_secs_f64())
    },
    _ => {
      // Sizing only (no proof): this crate's lowering of the compiler circuits.
      let config = Config {
        width,
        capacities,
        rom_capacities: raw[raw.len() - roms..]
          .iter()
          .map(|&n| with_headroom(n, headroom))
          .collect::<Result<_, _>>()?,
        log_shard_rows: log_shard,
        shards: flag(&args, "--shards"),
        lookup_budget: 2,
        unroll_compress: true,
        shard_offsets: true,
        entry: Some(entry.into()),
      };
      (Backend::new(&compiler, plan, config)?, started.elapsed().as_secs_f64())
    },
  };
  if fixed_config.is_none()
    && let Some(path) = flag::<String>(&args, "--write-config")
  {
    let c = &backend.config;
    fs::write(
      path,
      serde_json::to_vec_pretty(&json!({
        "format": "ix-template-v2-stage-config-v1",
        "artifact_blake3": hash.to_hex().as_str(), "entry": entry, "stage": stage_number,
        "headroom": headroom, "width": c.width, "log_shard_rows": c.log_shard_rows, "shards": backend.shards,
        "functions": compiler.names()[..nf].to_vec(), "capacities": c.capacities, "rom_capacities": c.rom_capacities,
        "rows_per_shard": backend.rows_per_shard,
      }))?,
    )?;
  }
  // Instances and ROM objects of this execution against the capacities.
  let mut fills = vec![];
  for (f, (&count, &capacity)) in
    raw[..nf].iter().zip(&backend.config.capacities).enumerate()
  {
    let used = if Some(f) == compress { count / 8 } else { count };
    if used > capacity {
      return Err(
        format!(
          "{}: {used} instances exceed capacity {capacity}",
          compiler.names()[f]
        )
        .into(),
      );
    }
    if capacity != 0 {
      fills.push((
        ratio(used, capacity),
        compiler.names()[f].clone(),
        used,
        capacity,
      ));
    }
  }
  fills.sort_by(|a, b| b.0.total_cmp(&a.0));
  let counts = backend.counts();
  let mut totals = json!({});
  for k in ["evaluations", "main_cells", "committed_cells", "fixed_cells"] {
    totals[k] = json!(
      counts
        .iter()
        .map(|c| serde_json::to_value(c).unwrap()[k].as_u64().unwrap())
        .sum::<u64>()
    );
  }
  let mut stats = BTreeMap::<String, u64>::new();
  let mut per = vec![];
  for (f, t) in backend.templates.iter().enumerate() {
    let n = backend.config.capacities[f] as u64;
    *stats.entry("template_rows".into()).or_default() +=
      t.rows.len() as u64 * n;
    for (k, v) in &t.stats {
      *stats.entry((*k).into()).or_default() += v * n;
    }
    per.push(json!({"name": compiler.names()[f], "instances": n, "template_rows": t.rows.len(),
      "weighted_rows": t.rows.len() as u64 * n, "stats": t.stats}));
  }
  per.sort_by_key(|p| std::cmp::Reverse(p["weighted_rows"].as_u64().unwrap()));
  per.truncate(12);
  let mut report = json!({
    "format": "ix-template-backend-v2-init",
    "artifact": artifact, "artifact_blake3": hash.to_hex().as_str(),
    "predecessor": pred, "entry": entry, "stage": stage_number, "width": backend.config.width, "headroom": headroom,
    "execution_seconds": exec_s, "lowering_seconds": lower_s, "wide_trace_seconds": wide_s,
    "shards": backend.shards, "shard_height": backend.height, "rows_per_shard": backend.rows_per_shard,
    "fixed_config": fixed_config.is_some(),
    "tightest_capacities": fills.iter().take(12).map(|(fill, name, used, cap)| json!({"function": name, "used": used, "capacity": cap, "fill": fill})).collect::<Vec<_>>(),
    "totals": totals, "template_counts": stats, "circuits": counts, "top_functions": per,
  });
  println!(
    "{}",
    serde_json::to_string_pretty(
      &json!({"totals": report["totals"], "shards": report["shards"],
    "rows_per_shard": report["rows_per_shard"], "template_rows": report["template_counts"]["template_rows"]})
    )?
  );
  if let Some(wide) = wide {
    let started = Instant::now();
    let (traces, key) =
      backend.witness_from_wide(&wide, entry, &call_args, record)?;
    drop(wide);
    let claim = wrapper.claim(public, execution.accumulator())?;
    let claims = backend.claims(&claim, key);
    let witness_s = started.elapsed().as_secs_f64();
    eprintln!("witness {witness_s:.1}s, RSS {:.1} GB", rss_gb());
    backend.check_lean_request(&claims)?;
    let mut traces = traces;
    backend.compact_traces(&mut traces)?;
    let setup = match early_setup {
      Some(setup) => setup,
      None => setup_system(
        &mut backend,
        early_srs.take(),
        commit_cache.as_deref(),
        &hash,
        &fixed_config,
        entry,
        &out,
      )?,
    };
    let Setup {
      system,
      key: prover_key,
      srs_path,
      srs_s,
      fixed_s,
      commit_s,
      cache_file,
      cache_hit,
    } = setup;
    let mut proof = {
      prove_with(
        &system,
        &prover_key,
        commit_s,
        traces,
        &claims,
        |system, proof| {
          if let Some(file) = &cache_file
            && !cache_hit
            && let Some(commitment) = &system.preprocessed_commit
          {
            fs::write(file, commitment.to_bytes()?)
              .map_err(|e| e.to_string())?;
          }
          if save {
            let key = packed_wire::key_bytes(system)?;
            let claims_bytes = wire::claims_bytes(&claims)?;
            fs::write(out.join("key.bin"), &key).map_err(|e| e.to_string())?;
            fs::write(out.join("claims.bin"), &claims_bytes)
              .map_err(|e| e.to_string())?;
            fs::write(out.join("proof.bin"), packed_wire::proof_bytes(proof)?)
              .map_err(|e| e.to_string())?;
            let text = |v: &Scalar| v.0.to_string();
            let narrow = json!({
              "format": "ix-template-v2-narrow-stage-v1",
              "entry": entry, "stage": stage_number, "width": width,
              "chunk_values": backend.config.width - 2,
              "claim_headers": claims.iter().map(|c| c[..2].iter().map(text).collect::<Vec<_>>()).collect::<Vec<_>>(),
              "claim_values": claims.iter().map(|c| c.len() - 2).sum::<usize>(),
              "key_blake3": blake3::hash(&key).to_hex().as_str(),
              "claims_blake3": blake3::hash(&claims_bytes).to_hex().as_str(),
              "policy_blake3": blake3::hash(&fs::read(&policy_path).map_err(|e| e.to_string())?).to_hex().as_str(),
              "statement": public.statement.as_bytes().iter().map(|b| format!("{b:02x}")).collect::<String>(),
              "fixed_slots": fixed_slots(system),
            });
            fs::write(
              out.join("narrow.json"),
              serde_json::to_vec_pretty(&narrow).map_err(|e| e.to_string())?,
            )
            .map_err(|e| e.to_string())?;
          }
          let bytes = packed_wire::proof_bytes(proof)?.len();
          let packs = [
            &proof.commitments.stage_1_trace,
            &proof.commitments.stage_2_trace,
            &proof.commitments.quotient_chunks,
          ]
          .iter()
          .map(|c| c.packs.len())
          .sum::<usize>()
            + system.preprocessed_commit.as_ref().map_or(0, |c| c.packs.len());
          Ok(
            json!({"pcs": "packed SHPLONK", "proof_wire_bytes": bytes, "packed_commitments": packs,
          "extra_pack_evaluations": proof.opening_proof.extra_values.len(),
          "fixed_commitment_cache": cache_file.as_ref().map(|f| json!({"file": f, "hit": cache_hit}))}),
          )
        },
      )?
    };
    proof["srs"] = json!(srs_path);
    proof["srs_load_seconds"] = json!(srs_s);
    proof["gl_wait_seconds"] = json!(gl_wait_s);
    proof["witness_seconds"] = json!(witness_s);
    proof["fixed_build_seconds"] = json!(fixed_s);
    proof["claims"] = json!(claims.len());
    proof["circuits"] = json!(backend.circuit_names());
    proof["peak_rss_gb"] = json!(rss_gb());
    eprintln!("{}", serde_json::to_string_pretty(&proof)?);
    report["proof"] = proof;
  }
  report["layout_source"] = layout_source;
  fs::write(
    out.join(if prove { "prove-packed.json" } else { "count.json" }),
    serde_json::to_vec_pretty(&report)?,
  )?;
  Ok(())
}

type Export =
  (std::thread::JoinHandle<Result<(lean::Layout, f64), String>>, Instant);
type EarlySrs = (
  usize,
  std::thread::JoinHandle<
    Result<(ix_proof_compression::kzg::srs::Srs, f64), String>,
  >,
);

/// Waits for the Lean export and builds the narrow circuits from it.
fn adopt<'c, 'p, 'a>(
  args: &[String],
  compiler: &'c Compiler<'p, 'a>,
  plan: &'p aiur::trace::TracePlan<
    'a,
    ix_proof_compression::aiur_backend::Bn254,
  >,
  config: Config,
  (handle, export_started): Export,
) -> Result<(Backend<'c, 'p, 'a>, Value), Error> {
  let started = Instant::now();
  let (layout, exporter_s) = handle.join().map_err(|e| {
    format!("Lean exporter thread panicked: {}", panic_message(&*e))
  })??;
  let waited_s = started.elapsed().as_secs_f64();
  let ms = layout.out["ms"].clone();
  let adopt = Instant::now();
  let backend = Backend::from_lean(compiler, plan, config, layout)?;
  let adopt_s = adopt.elapsed().as_secs_f64();
  eprintln!(
    "narrow circuits from the Lean export: exporter {exporter_s:.1}s, lowered and validated in {adopt_s:.1}s"
  );
  let mut layout_source = json!({"lean_exporter": true, "input_format": "ix-tiling-v2-input-2",
    "exporter_seconds": exporter_s, "ready_after_seconds": export_started.elapsed().as_secs_f64(),
    "exporter_wait_seconds": waited_s, "lower_and_validate_seconds": adopt_s, "exporter_ms": ms});
  if args.iter().any(|a| a == "--rust-cross-check") {
    let check = backend.rust_cross_check()?;
    eprintln!("Rust cross-check: {check}");
    layout_source["rust_cross_check"] = check;
  }
  Ok((backend, layout_source))
}

/// The fixed-slot setup of a proof: it depends on the circuits, the SRS and
/// the stage configuration, not on the execution.
struct Setup {
  system: System<PackedShplonkConfig>,
  key: multi_stark::system::ProverKey<PackedShplonkConfig>,
  srs_path: PathBuf,
  srs_s: f64,
  fixed_s: f64,
  commit_s: f64,
  cache_file: Option<PathBuf>,
  cache_hit: bool,
}

/// Loads the SRS (or joins its early load), takes the circuit inputs and
/// commits the fixed slots, from the commitment cache when it has them.
fn setup_system(
  backend: &mut Backend<'_, '_, '_>,
  early_srs: Option<EarlySrs>,
  commit_cache: Option<&std::path::Path>,
  hash: &blake3::Hash,
  fixed_config: &Option<Value>,
  entry: &str,
  out: &std::path::Path,
) -> Result<Setup, Error> {
  let srs_path =
    PathBuf::from(std::env::var_os("IX_KZG_SRS").ok_or("IX_KZG_SRS")?);
  let parameters = ix_proof_compression::pipeline::ignition_parameters()?;
  let started = Instant::now();
  let counts = backend.counts();
  let trace_cap = backend.height.max(
    counts.iter().flat_map(|c| c.heights.iter().copied()).max().unwrap_or(2),
  );
  let (srs, srs_s) = match early_srs {
    Some((len, handle)) if len == 2 * trace_cap => {
      let (srs, loaded_s) = handle.join().map_err(|e| {
        format!("SRS loader panicked: {}", panic_message(&*e))
      })??;
      eprintln!(
        "SRS loaded early in {loaded_s:.1}s, joined after {:.1}s",
        started.elapsed().as_secs_f64()
      );
      (Arc::new(srs), started.elapsed().as_secs_f64())
    },
    _ => {
      let srs = Arc::new(gnark::load(
        &srs_path,
        2 * trace_cap,
        parameters.public_setup(),
      )?);
      (srs, started.elapsed().as_secs_f64())
    },
  };
  let started = Instant::now();
  let (inputs, shared) = backend.take_circuit_inputs();
  let fixed_s = started.elapsed().as_secs_f64();
  // Packing capacity is the whole loaded prefix: two narrow columns per
  // pack. No narrow, table or ROM circuit reads the next main row.
  let config = PackedShplonkConfig::with_max_trace_len(srs, 2 * trace_cap, 2)
    .with_streaming_lookups()
    .with_streaming_quotient();
  config.set_main_next_rows(vec![false; backend.circuit_names().len()]);
  let cache_file = match commit_cache {
    Some(dir) => {
      let mut h = blake3::Hasher::new();
      h.update(b"ix-narrow-fixed-commitment-v1\0");
      h.update(hash.as_bytes());
      h.update(&serde_json::to_vec(&json!({"config": fixed_config, "entry": entry, "trace_cap": trace_cap,
        "srs": srs_path, "srs_bytes": fs::metadata(&srs_path)?.len(), "circuits": backend.circuit_names()}))?);
      // The exporter's input and outputs, without its timings.
      match fs::read(out.join("lean-layout.json")) {
        Ok(layout) => {
          let mut layout: Value = serde_json::from_slice(&layout)?;
          if let Some(o) = layout.as_object_mut() {
            o.remove("ms");
          }
          h.update(&serde_json::to_vec(&layout)?);
          for file in ["lean-input.json", "lean-tables.bin"] {
            if let Ok(bytes) = fs::read(out.join(file)) {
              h.update(blake3::hash(&bytes).as_bytes());
            }
          }
        },
        Err(_) => return Err("the narrow proof needs the Lean layout".into()),
      }
      fs::create_dir_all(dir)?;
      Some(dir.join(format!("{}.commitment", h.finalize().to_hex())))
    },
    None => None,
  };
  let mut cache_hit = false;
  if let Some(file) = &cache_file
    && let Ok(bytes) = fs::read(file)
  {
    ProofConfig::pcs(&config)
      .preload_commitment(packed_shplonk::Commitment::from_bytes(&bytes)?);
    cache_hit = true;
    eprintln!("fixed commitment from {}", file.display());
  }
  let started = Instant::now();
  let (system, key) = system_with_slots(config, inputs, &shared, false)?;
  let commit_s = started.elapsed().as_secs_f64();
  eprintln!("fixed commit {commit_s:.1}s, RSS {:.1} GB", rss_gb());
  Ok(Setup {
    system,
    key,
    srs_path,
    srs_s,
    fixed_s,
    commit_s,
    cache_file,
    cache_hit,
  })
}

/// Prove with streaming lookups and quotients, verify, and check that a
/// changed output is rejected.
fn prove_with<SC>(
  system: &System<SC>,
  pk: &multi_stark::system::ProverKey<SC>,
  commit_s: f64,
  traces: Vec<p3_matrix::dense::RowMajorMatrix<Scalar>>,
  claims: &[Vec<Scalar>],
  describe: impl Fn(
    &System<SC>,
    &multi_stark::prover::Proof<SC>,
  ) -> Result<Value, String>,
) -> Result<Value, Error>
where
  SC: ProofConfig,
  SC::Pcs: multi_stark::traits::Pcs<F = Scalar>,
{
  let lookups = traces
    .iter()
    .zip(&system.circuits)
    .map(|(t, c)| {
      let widths: Vec<usize> =
        c.graph.lookups.iter().map(|l| l.args.len()).collect();
      LookupValues::shape_only(t.height(), &widths)
    })
    .collect();
  let witness = SystemWitness { traces, lookups };
  let refs: Vec<&[Scalar]> = claims.iter().map(Vec::as_slice).collect();
  let started = Instant::now();
  let proof = system.prove_multiple_claims(pk, &refs, witness);
  let prove_s = started.elapsed().as_secs_f64();
  eprintln!("prove {prove_s:.1}s, RSS {:.1} GB", rss_gb());
  let started = Instant::now();
  system
    .verify_multiple_claims(&refs, &proof)
    .map_err(|e| format!("native verification: {e:?}"))?;
  let verify_s = started.elapsed().as_secs_f64();
  let mut wrong = claims.to_vec();
  *wrong.last_mut().unwrap().last_mut().unwrap() += Scalar::ONE;
  let wrong_refs: Vec<&[Scalar]> = wrong.iter().map(Vec::as_slice).collect();
  if system.verify_multiple_claims(&wrong_refs, &proof).is_ok() {
    return Err("changed output accepted".into());
  }
  let count = |v: &[Vec<Vec<SC::Challenge>>]| -> (usize, usize) {
    (
      v.iter().map(|m| m.len()).sum(),
      v.iter().map(|m| m.iter().map(Vec::len).sum::<usize>()).sum(),
    )
  };
  let rounds = [
    ("main", count(&proof.stage_1_opened_values)),
    ("lookup", count(&proof.stage_2_opened_values)),
    ("quotient", count(&proof.quotient_opened_values)),
    (
      "fixed",
      proof.preprocessed_opened_values.as_deref().map_or((0, 0), count),
    ),
  ];
  let evaluations: usize = rounds.iter().map(|(_, (_, e))| e).sum();
  let mut report = describe(system, &proof)?;
  report["fixed_commit_seconds"] = json!(commit_s);
  report["prove_seconds"] = json!(prove_s);
  report["verify_seconds"] = json!(verify_s);
  report["changed_output_rejected"] = json!(true);
  report["log_degrees"] = json!(proof.log_degrees);
  report["fixed_slots"] = json!(fixed_slots(system));
  report["evaluations"] = json!(evaluations);
  report["accumulators"] = json!(proof.intermediate_accumulators.len());
  report["opened"] = json!(
    rounds
      .iter()
      .map(|(n, (points, evals))| (
        n.to_string(),
        json!({"matrix_points": points, "evaluations": evals})
      ))
      .collect::<BTreeMap<_, _>>()
  );
  Ok(report)
}
