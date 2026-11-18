//! `narrow-fixed`: the fixed-key narrow stage (`CompressNarrowFixed::step_v1`)
//! on the CompressGL proof (`aiur_template_v2_init --fixed-key --config ...
//! --prove --packed --save --fixed-commit-cache ...`).
//!
//! Manifest fields: `artifact`, `config`, `policy`, `key` (the pinned key
//! file; the key produced must equal it byte for byte), all products;
//! `commit_cache` (directory of fixed-slot commitments, keyed by layout
//! digest), `stage` (default 1).
//!
//! Everything the configuration determines is prepared before the
//! CompressGL proof arrives: the SRS prefix, the Lean export
//! (`tiling_export2`), the circuits and the fixed-slot commitment.
use super::{Error, Handoff, Stage, exports::Kind};
use crate::{
  aiur_backend::{
    compress_bn::{
      Input, PACKED_NARROW_FIXED_ENTRY, PolicyDigest, PublicInputs,
      Stage as ChainStage, StatementDigest, Wrapper,
    },
    kzg::Compiler,
    kzg_advice as wire, kzg_packed_advice as packed_wire,
    template::{
      fixed_slots, system_with_slots,
      v2::{Backend, Config, lean},
    },
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
use std::{
  collections::BTreeMap,
  fs,
  path::PathBuf,
  sync::{Arc, Mutex},
  time::Instant,
};

fn statement_of(claims: &[u8], first_word: usize) -> Result<[u8; 32], Error> {
  let mut s = [0u8; 32];
  for i in 0..8 {
    let off = 16 + 32 * (first_word + i);
    s[4 * i..4 * i + 4].copy_from_slice(
      claims.get(off..off + 4).ok_or("short CompressGL claims")?,
    );
  }
  Ok(s)
}

fn numbers(v: &Value, k: &str) -> Result<Vec<usize>, Error> {
  v[k]
    .as_array()
    .ok_or(format!("config {k}"))?
    .iter()
    .map(|x| {
      x.as_u64()
        .and_then(|x| usize::try_from(x).ok())
        .ok_or_else(|| format!("config {k}"))
    })
    .collect()
}

fn number(v: &Value, k: &str) -> Result<usize, Error> {
  v[k]
    .as_u64()
    .and_then(|x| usize::try_from(x).ok())
    .ok_or_else(|| format!("config {k}"))
}

pub(super) fn run(stage: &Stage<'_>) -> Result<Handoff, Error> {
  let entry: &'static str = PACKED_NARROW_FIXED_ENTRY;
  let stage_number =
    u32::try_from(stage.spec.spec["stage"].as_u64().unwrap_or(1))
      .map_err(|e| e.to_string())?;
  let config_file = stage.product("config")?;
  let fixed_config: Value =
    serde_json::from_slice(&config_file.bytes).map_err(|e| e.to_string())?;
  let srs_path =
    PathBuf::from(std::env::var_os("IX_KZG_SRS").ok_or("IX_KZG_SRS")?);
  let parameters =
    crate::pipeline::ignition_parameters().map_err(|e| e.to_string())?;
  let early_len = 2usize << number(&fixed_config, "log_shard_rows")?;
  let early_srs = {
    let path = srs_path.clone();
    let setup = parameters.public_setup();
    std::thread::spawn(move || {
      let started = Instant::now();
      gnark::load(&path, early_len, setup)
        .map(|srs| (srs, started.elapsed().as_secs_f64()))
        .map_err(|e| e.to_string())
    })
  };

  let artifact = stage.product("artifact")?;
  let hash = blake3::hash(&artifact.bytes);
  let wrapper =
    Wrapper::from_bytes_with_entry(&artifact.bytes, hash.as_bytes(), entry)?;
  let policy = stage.product("policy")?;
  let plan = wrapper.plan();
  let compiler = Compiler::with_lookup_budget(plan, Some(4))?;
  let nf = compiler.function_circuits();
  let compress = compiler.names().iter().position(|n| n == "Blake3::compress");
  if fixed_config["format"] != "ix-template-v2-stage-config-v1"
    || fixed_config["functions"].as_array().map(Vec::len) != Some(nf)
  {
    return Err("stage configuration does not match this artifact".into());
  }
  let config = Config {
    width: number(&fixed_config, "width")?,
    capacities: numbers(&fixed_config, "capacities")?,
    rom_capacities: numbers(&fixed_config, "rom_capacities")?,
    log_shard_rows: number(&fixed_config, "log_shard_rows")?,
    shards: Some(number(&fixed_config, "shards")?),
    lookup_budget: 2,
    unroll_compress: true,
    shard_offsets: true,
    entry: Some(entry.into()),
  };

  // The Lean layout: the exporter's input is known before the execution.
  let started = Instant::now();
  let input2 = lean::input2(
    &compiler,
    plan,
    &config,
    &artifact.path,
    hash.to_hex().as_str(),
  )?;
  let input_bytes = serde_json::to_vec(&input2).map_err(|e| e.to_string())?;
  let exported = stage.ladder.exports.export(Kind::Tiling2, &input_bytes)?;
  stage.write("lean-input.json", &input_bytes)?;
  for (from, to) in [
    (exported.layout(), "lean-layout.json"),
    (exported.tables(), "lean-tables.bin"),
  ] {
    let target = stage.dir.join(to);
    let _ = fs::remove_file(&target);
    fs::hard_link(&from, &target)
      .or_else(|_| fs::copy(&from, &target).map(|_| ()))
      .map_err(|e| format!("{}: {e}", target.display()))?;
  }
  let height = 1usize << config.log_shard_rows;
  let layout = lean::Layout::load_export(
    &stage.dir.join("lean-layout.json"),
    &exported.fixed(),
    Some(&stage.dir.join("lean-tables.bin")),
    height,
  )?;
  let exporter_s = started.elapsed().as_secs_f64();
  let ms = layout.out["ms"].clone();
  let adopt = Instant::now();
  let mut backend = Backend::from_lean(&compiler, plan, config, layout)?;
  let adopt_s = adopt.elapsed().as_secs_f64();
  let layout_source = json!({"lean_exporter": true, "input_format": "ix-tiling-v2-input-2",
    "exporter_seconds": exporter_s, "ready_after_seconds": exporter_s,
    "exporter_wait_seconds": exporter_s, "lower_and_validate_seconds": adopt_s, "exporter_ms": ms,
    "export_cache": {"dir": exported.dir, "hit": exported.cached,
      "exporter_id": stage.ladder.exports.exporter_id(Kind::Tiling2)}});
  let lower_s = started.elapsed().as_secs_f64();

  // The fixed-slot setup.
  let started = Instant::now();
  let counts = backend.counts();
  let trace_cap = backend.height.max(
    counts.iter().flat_map(|c| c.heights.iter().copied()).max().unwrap_or(2),
  );
  let srs = if early_len == 2 * trace_cap {
    let (srs, _) = early_srs
      .join()
      .map_err(|_error| "the SRS loader panicked".to_string())??;
    Arc::new(srs)
  } else {
    drop(early_srs);
    Arc::new(
      gnark::load(&srs_path, 2 * trace_cap, parameters.public_setup())
        .map_err(|e| e.to_string())?,
    )
  };
  let srs_s = started.elapsed().as_secs_f64();
  let started = Instant::now();
  let (inputs, shared) = backend.take_circuit_inputs();
  let fixed_s = started.elapsed().as_secs_f64();
  let pcs = PackedShplonkConfig::with_max_trace_len(srs, 2 * trace_cap, 2)
    .with_streaming_lookups()
    .with_streaming_quotient();
  pcs.set_main_next_rows(vec![false; backend.circuit_names().len()]);
  let cache_file = match stage.spec.spec["commit_cache"].as_str() {
    Some(dir) => {
      let dir = stage.ladder.manifest.base.join(dir);
      let mut h = blake3::Hasher::new();
      h.update(b"ix-narrow-fixed-commitment-v1\0");
      h.update(hash.as_bytes());
      let srs_bytes = fs::metadata(&srs_path)
        .map_err(|e| format!("{}: {e}", srs_path.display()))?
        .len();
      h.update(
        &serde_json::to_vec(&json!({"config": fixed_config, "entry": entry, "trace_cap": trace_cap,
          "srs": srs_path, "srs_bytes": srs_bytes, "circuits": backend.circuit_names()}))
        .map_err(|e| e.to_string())?,
      );
      let mut layout: Value = serde_json::from_slice(
        &fs::read(stage.dir.join("lean-layout.json"))
          .map_err(|e| e.to_string())?,
      )
      .map_err(|e| e.to_string())?;
      if let Some(o) = layout.as_object_mut() {
        o.remove("ms");
      }
      h.update(&serde_json::to_vec(&layout).map_err(|e| e.to_string())?);
      for file in ["lean-input.json", "lean-tables.bin"] {
        if let Ok(bytes) = fs::read(stage.dir.join(file)) {
          h.update(blake3::hash(&bytes).as_bytes());
        }
      }
      fs::create_dir_all(&dir)
        .map_err(|e| format!("{}: {e}", dir.display()))?;
      Some(dir.join(format!("{}.commitment", h.finalize().to_hex())))
    },
    None => None,
  };
  let mut cache_hit = false;
  if let Some(file) = &cache_file
    && let Ok(bytes) = fs::read(file)
  {
    ProofConfig::pcs(&pcs)
      .preload_commitment(packed_shplonk::Commitment::from_bytes(&bytes)?);
    cache_hit = true;
  }
  let started = Instant::now();
  let (system, prover_key) =
    stage.gpu(|| system_with_slots(pcs, inputs, &shared, false))?;
  let commit_s = started.elapsed().as_secs_f64();
  stage.reserve(1);

  let (gl, gl_wait_s) = stage.input()?;
  stage.cancelled()?;
  // A CompressGL claim is `[tag, entry, reserved(8), statement(8)]`.
  let public = PublicInputs {
    policy: PolicyDigest::from_trusted(*blake3::hash(&policy.bytes).as_bytes()),
    stage: ChainStage::new(stage_number)?,
    statement: StatementDigest::new(statement_of(&gl.claims, 10)?),
  };
  let input = Input::from_packed_source(
    public,
    gl.key.clone(),
    gl.claims.clone(),
    gl.proof.clone(),
    policy.bytes.clone(),
  )?;
  let started = Instant::now();
  let execution = wrapper.execute(&input, 64 << 30)?;
  let exec_s = started.elapsed().as_secs_f64();
  let record = execution.record();
  let raw = compiler.raw_row_counts(record)?;
  for (f, (&count, &capacity)) in
    raw[..nf].iter().zip(&backend.config.capacities).enumerate()
  {
    let used = if Some(f) == compress { count / 8 } else { count };
    if used > capacity {
      return Err(format!(
        "{}: {used} instances exceed capacity {capacity}",
        compiler.names()[f]
      ));
    }
  }
  stage.reserve(2);
  let call_args = public.arguments();
  let started = Instant::now();
  let wide = compiler.generate(record, entry, &call_args)?;
  let wide_s = started.elapsed().as_secs_f64();
  let started = Instant::now();
  let (traces, key) =
    backend.witness_from_wide(&wide, entry, &call_args, record)?;
  drop(wide);
  let claim = wrapper.claim(public, execution.accumulator())?;
  let claims = backend.claims(&claim, key);
  let witness_s = started.elapsed().as_secs_f64();
  backend.check_lean_request(&claims)?;
  let mut traces = traces;
  backend.compact_traces(&mut traces)?;
  drop(execution);

  let saved: Mutex<Option<(Vec<u8>, Vec<u8>, Vec<u8>)>> = Mutex::new(None);
  let mut proof = prove_with(
    stage,
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
        fs::write(file, commitment.to_bytes()?).map_err(|e| e.to_string())?;
      }
      let key = packed_wire::key_bytes(system)?;
      let claims_bytes = wire::claims_bytes(&claims)?;
      let proof_bytes = packed_wire::proof_bytes(proof)?;
      let packs = [
        &proof.commitments.stage_1_trace,
        &proof.commitments.stage_2_trace,
        &proof.commitments.quotient_chunks,
      ]
      .iter()
      .map(|c| c.packs.len())
      .sum::<usize>()
        + system.preprocessed_commit.as_ref().map_or(0, |c| c.packs.len());
      let report = json!({"pcs": "packed SHPLONK", "proof_wire_bytes": proof_bytes.len(),
      "packed_commitments": packs,
      "extra_pack_evaluations": proof.opening_proof.extra_values.len(),
      "fixed_commitment_cache": cache_file.as_ref().map(|f| json!({"file": f, "hit": cache_hit}))});
      *saved.lock().unwrap_or_else(std::sync::PoisonError::into_inner) =
        Some((key, claims_bytes, proof_bytes));
      Ok(report)
    },
  )?;
  let (key, claims_bytes, proof_bytes) = saved
    .into_inner()
    .unwrap_or_else(std::sync::PoisonError::into_inner)
    .ok_or("the narrow proof was not serialized")?;
  stage.ladder.checks.set("narrow_verified_and_rejects_changed_output", true);
  let text = |v: &Scalar| v.0.to_string();
  let statement = *public.statement.as_bytes();
  let narrow_json = json!({
    "format": "ix-template-v2-narrow-stage-v1",
    "entry": entry, "stage": stage_number, "width": 8,
    "chunk_values": backend.config.width - 2,
    "claim_headers": claims.iter().map(|c| c[..2].iter().map(text).collect::<Vec<_>>()).collect::<Vec<_>>(),
    "claim_values": claims.iter().map(|c| c.len() - 2).sum::<usize>(),
    "key_blake3": blake3::hash(&key).to_hex().as_str(),
    "claims_blake3": blake3::hash(&claims_bytes).to_hex().as_str(),
    "policy_blake3": blake3::hash(&policy.bytes).to_hex().as_str(),
    "statement": super::hex(&statement),
    "fixed_slots": fixed_slots(&system),
  });
  stage.write("key.bin", &key)?;
  stage.write("claims.bin", &claims_bytes)?;
  stage.write("proof.bin", &proof_bytes)?;
  stage.write_json("narrow.json", &narrow_json)?;
  proof["srs"] = json!(srs_path);
  proof["srs_load_seconds"] = json!(srs_s);
  proof["gl_wait_seconds"] = json!(gl_wait_s);
  proof["witness_seconds"] = json!(witness_s);
  proof["fixed_build_seconds"] = json!(fixed_s);
  proof["claims"] = json!(claims.len());
  proof["circuits"] = json!(backend.circuit_names());
  proof["peak_rss_gb"] = json!(super::peak_rss_gb());
  proof["proof_blake3"] = json!(blake3::hash(&proof_bytes).to_hex().as_str());
  let report = json!({
    "format": "ix-template-backend-v2-init",
    "artifact": artifact.path, "artifact_blake3": hash.to_hex().as_str(),
    "entry": entry, "stage": stage_number, "width": backend.config.width,
    "execution_seconds": exec_s, "lowering_seconds": lower_s, "wide_trace_seconds": wide_s,
    "shards": backend.shards, "shard_height": backend.height, "rows_per_shard": backend.rows_per_shard,
    "fixed_config": true,
    "proof": proof,
    "layout_source": layout_source,
  });
  stage.write_json("prove-packed.json", &report)?;
  stage.check_key("key", &key)?;
  Ok(Handoff {
    key,
    claims: claims_bytes,
    proof: proof_bytes,
    stage: stage_number,
    statement: Some(statement),
    ..Handoff::default()
  })
}

/// Proves with streaming lookups and quotients, verifies, and checks that a
/// changed output is rejected.
fn prove_with<SC>(
  stage: &Stage<'_>,
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
  let proof = stage.gpu(|| system.prove_multiple_claims(pk, &refs, witness));
  let prove_s = started.elapsed().as_secs_f64();
  let started = Instant::now();
  system
    .verify_multiple_claims(&refs, &proof)
    .map_err(|e| format!("native verification: {e:?}"))?;
  let verify_s = started.elapsed().as_secs_f64();
  let mut wrong = claims.to_vec();
  *wrong
    .last_mut()
    .and_then(|c| c.last_mut())
    .ok_or("empty narrow claims")? += Scalar::ONE;
  let wrong_refs: Vec<&[Scalar]> = wrong.iter().map(Vec::as_slice).collect();
  if system.verify_multiple_claims(&wrong_refs, &proof).is_ok() {
    stage
      .ladder
      .checks
      .set("narrow_verified_and_rejects_changed_output", false);
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
