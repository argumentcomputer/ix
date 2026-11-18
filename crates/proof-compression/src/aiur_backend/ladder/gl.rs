//! `compress-gl`: packed CompressGL over the normalized wrap proof
//! (`compress_gl_packed_chain --gl-only --streaming --wrap-package ...
//! --gl-rom ...`).
//!
//! Manifest fields: `artifact`, `gl_rom`, `wrap_package`, `wrap_layout`,
//! `key` (the pinned key file; the key produced must equal it byte for
//! byte), all products; `log_cap`, `quotient_degree`, `lookup_budget`,
//! `gl_shards`, `streaming`.
use super::{
  Error, Handoff, Stage,
  exports::{Kind, WideSource},
};
use crate::{
  aiur_backend::{
    Bn254,
    compress_bn::{PackedCapacity, PackedGlProver, plan_copies_of},
    compress_gl,
    kzg::Compiler,
    wide,
  },
  pipeline::{SetupClass, SetupConfig},
};
use aiur::field::FieldBackend;
use multi_stark::config::ProofConfig;
use serde_json::{Value, json};
use std::time::Instant;

fn number(spec: &Value, key: &str) -> Result<usize, Error> {
  spec[key]
    .as_u64()
    .and_then(|v| usize::try_from(v).ok())
    .ok_or_else(|| format!("compress-gl {key}"))
}

pub(super) fn run(stage: &Stage<'_>) -> Result<Handoff, Error> {
  let spec = &stage.spec.spec;
  let started = Instant::now();
  let capacity = PackedCapacity {
    log_cap: u8::try_from(number(spec, "log_cap")?)
      .map_err(|e| e.to_string())?,
    quotient_degree: number(spec, "quotient_degree")?,
    lookup_quotient_budget: Some(number(spec, "lookup_budget")?),
  };
  let shards = number(spec, "gl_shards")?;
  let (min_saving, column_cost, node_cost) = (1usize << 20, 3600, 600);
  let setup = SetupConfig::from_env(false).map_err(|e| e.to_string())?;
  let mut config = capacity.config(&setup)?;
  if spec["streaming"].as_bool() == Some(true) {
    config = config.with_streaming_lookups().with_streaming_quotient();
  }
  let setup_class = SetupClass::of(config.pcs().parameters());
  let srs_seconds = started.elapsed().as_secs_f64();

  let gl_file = stage.product("artifact")?;
  let gl_hash = blake3::hash(&gl_file.bytes);
  let gl_wrapper =
    compress_gl::Wrapper::from_bytes(&gl_file.bytes, gl_hash.as_bytes())?;
  let rom_file = stage.product("gl_rom")?;
  let rom_json: Value =
    serde_json::from_slice(&rom_file.bytes).map_err(|e| e.to_string())?;
  if rom_json["format"] != "ix-compress-gl-rom-1" {
    return Err("gl_rom is not an ix-compress-gl-rom-1 file".into());
  }
  let rom: Vec<(usize, usize)> =
    serde_json::from_value(rom_json["rom"].clone())
      .map_err(|e| e.to_string())?;
  // The pinned ROM capacities make the export execution-independent.
  let input = wide::grouped_input(
    gl_wrapper.plan(),
    capacity.cap()?,
    &rom,
    &gl_file.path,
    gl_hash.to_hex().as_str(),
    compress_gl::ENTRY,
  )?;
  let input_bytes =
    serde_json::to_vec_pretty(&input).map_err(|e| e.to_string())?;
  let exported = stage.ladder.exports.export(Kind::Wide, &input_bytes)?;
  let layout = wide::Layout::load(&exported.layout(), &exported.fixed())?;

  let package_file = stage.product("wrap_package")?;
  let layout_file = stage.product("wrap_layout")?;
  let package = aiur::artifact::Package::decode(&package_file.bytes)?;
  let wrap_config: stark_verifier::compress_wrap::LayoutConfig =
    serde_json::from_slice(&layout_file.bytes).map_err(|e| e.to_string())?;
  let wrapper = stark_verifier::compress_wrap::Wrapper::for_layout_with(
    package,
    aiur::trace::stark::Parameters::default(),
    None,
    &wrap_config.layout,
    &WideSource(&stage.ladder.exports),
  )?;
  wrap_config.check(&wrapper)?;
  let policy = compress_gl::WrapPolicy::new(&wrapper, &wrap_config.layout)?;
  let ready_seconds = (super::unix_now() - stage.started).max(0.0);
  stage.reserve(1);

  let (wrapped, wait_seconds) = stage.input()?;
  stage.cancelled()?;
  let started = Instant::now();
  let root = &stage.ladder.root;
  let (key, claims, proof) = (&wrapped.key, &wrapped.claims, &wrapped.proof);
  let gl_input = policy.admit(
    &wrapper,
    &wrap_config.layout,
    root.statement(),
    key,
    claims,
    proof,
  )?;
  let mut changed = claims.clone();
  *changed.last_mut().ok_or("empty wrapper claims")? ^= 1;
  let mut other = wrap_config.layout.clone();
  other.log_heights[1] += 1;
  let rejects = policy
    .admit(
      &wrapper,
      &wrap_config.layout,
      root.statement(),
      key,
      &changed,
      proof,
    )
    .is_err()
    && policy
      .admit(&wrapper, &other, root.statement(), key, claims, proof)
      .is_err();
  stage
    .ladder
    .checks
    .set("gl_admission_rejects_changed_claim_and_layout", rejects);
  if !rejects {
    return Err("wrap admission accepted a changed claim or layout".into());
  }
  let wrap_report = json!({
    "config": layout_file.path,
    "grouping": wrap_config.grouping,
    "version": wrap_config.version,
    "policy": policy,
    "policy_blake3": blake3::Hash::from_bytes(policy.digest()?).to_hex().as_str(),
    "proof_wire_bytes": proof.len(),
    "proof_blake3": blake3::hash(proof).to_hex().as_str(),
    "admission_seconds": started.elapsed().as_secs_f64(),
    "admission_rejects_changed_claim_and_layout": true,
  });
  drop(wrapper);

  let started = Instant::now();
  let gl_execution = gl_wrapper.execute(&gl_input)?;
  let gl_execution_seconds = started.elapsed().as_secs_f64();
  stage.reserve(2);
  let gl_compiler = Compiler::with_lookup_budget(
    gl_wrapper.plan(),
    capacity.lookup_quotient_budget,
  )?;
  let gl_raw = gl_compiler.raw_row_counts(gl_execution.record())?;
  let started = Instant::now();
  let claim = gl_wrapper.plan().public_claim(
    compress_gl::ENTRY,
    &[Bn254.zero(); 16],
    &[],
  )?;
  let wide_stage = wide::Stage::new(
    layout,
    &gl_compiler,
    gl_wrapper.plan(),
    &claim,
    capacity.lookup_quotient_budget,
  )?;
  if wide_stage.rom != rom {
    return Err(
      "the exported ROM tables differ from the requested capacities".into(),
    );
  }
  wide_stage.check_rom(&gl_raw)?;
  let wide_report = json!({
    "exporter": "ladder",
    "exporter_blake3": stage.ladder.exports.exporter_id(Kind::Wide),
    "export_dir": exported.dir,
    "cached": exported.cached,
    "seconds": exported.seconds,
    "rom": rom,
    "units_and_groups": wide_stage.function_circuits,
    "exported_graph_nodes": wide_stage.graph_nodes,
  });
  let copies = Some(plan_copies_of(
    &wide_stage.inputs,
    wide_stage.function_circuits,
    &wide_stage.rows(&gl_raw),
    shards,
    min_saving,
    column_cost,
    node_cost,
  ));
  let gl_prover = stage.gpu(|| {
    PackedGlProver::from_wide(
      &gl_wrapper,
      capacity,
      config.clone(),
      wide_stage,
      copies,
    )
  })?;
  let gl_key_seconds = started.elapsed().as_secs_f64();
  stage.write("gl-key.bin", gl_prover.key_bytes())?;
  let (names, gl_inputs, gl_heights, gl_raw) = match gl_prover.stage() {
    Some(s) => (
      s.names.clone(),
      s.inputs.as_slice(),
      s.rows(&gl_compiler.row_counts(gl_execution.record())?),
      s.rows(&gl_raw),
    ),
    None => return Err("the CompressGL prover lost its exported stage".into()),
  };
  let gl_cells = |rows: &[usize]| -> usize {
    gl_inputs.iter().zip(rows).map(|(i, &r)| i.main_width * r).sum()
  };
  let timings = gl_prover.system().config.pcs().timings();
  let (commit0, open0) = (timings.commit_seconds(), timings.open_seconds());
  let gl_proven = stage.gpu(|| gl_prover.prove(&gl_execution))?;
  let (gl_commit, gl_open) =
    (timings.commit_seconds() - commit0, timings.open_seconds() - open0);
  let mut changed = gl_proven.claim.clone();
  *changed.last_mut().ok_or("empty claim")? += Bn254.one();
  let rejected = gl_prover.verify(&changed, &gl_proven.proof).is_err();
  stage.ladder.checks.set("gl_native_rejects_changed_output", rejected);
  if !rejected {
    return Err("packed CompressGL accepted a changed output".into());
  }
  let (gl_peak, _) = super::rss();
  let gl_report = json!({
    "program": compress_gl::ENTRY,
    "artifact": gl_file.path,
    "artifact_blake3": gl_hash.to_hex().as_str(),
    "root_key_blake3": blake3::hash(&stage.ladder.root_bytes[0]).to_hex().as_str(),
    "root_claims_blake3": blake3::hash(&stage.ladder.root_bytes[1]).to_hex().as_str(),
    "root_proof_blake3": blake3::hash(&stage.ladder.root_bytes[2]).to_hex().as_str(),
    "predecessor": "normalized CompressWrap proof",
    "wrap": wrap_report,
    "key_wire_bytes": gl_prover.key_bytes().len(),
    "key_blake3": blake3::hash(gl_prover.key_bytes()).to_hex().as_str(),
    "circuits": gl_prover.system().circuits.len(),
    "circuit_source": "wide_export",
    "wide_export": wide_report,
    "copies": gl_prover.copies().iter().enumerate().filter(|&(_, &k)| k > 1)
      .map(|(i, &k)| json!([names[i], k])).collect::<Vec<_>>(),
    "shards": gl_proven.shards.iter().map(|(c, h)| json!([names[*c], h])).collect::<Vec<_>>(),
    "proof_wire_bytes": gl_proven.source_proof.len(),
    "proof_blake3": blake3::hash(&gl_proven.source_proof).to_hex().as_str(),
    "native_accepts": true,
    "native_rejects_changed_output": true,
    "cells": {
      "main_cells_padded": gl_cells(&gl_heights),
      "main_cells_unpadded": gl_cells(&gl_raw),
      "main_cells_padded_sharded": gl_proven.main_cells,
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
  });
  stage.write("gl/proof.bin", &gl_proven.source_proof)?;
  stage.write("gl/claims.bin", &gl_proven.source_claims)?;
  stage.write_json("gl/report.json", &gl_report)?;
  stage.write_json(
    "summary.json",
    &json!({
      "format": "ix-aiur-compress-gl-packed-chain-v1",
      "setup": setup_class.label(),
      "capacity": capacity,
      "streaming": spec["streaming"],
      "backend": if cfg!(feature = "cuda") { "cuda" } else { "cpu" },
      "seconds": {"srs": srs_seconds, "ready": ready_seconds, "wait": wait_seconds},
      "gl": gl_report,
    }),
  )?;
  stage.check_key("key", gl_prover.key_bytes())?;
  let handoff = Handoff {
    key: gl_prover.key_bytes().to_vec(),
    claims: gl_proven.source_claims,
    proof: gl_proven.source_proof,
    ..Handoff::default()
  };
  drop(gl_prover);
  drop(gl_execution);
  Ok(handoff)
}
