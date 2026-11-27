//! `fri-verifier`: packed CompressGL over the normalized wrap proof
//! (`compress_gl_packed_chain --gl-only --streaming --wrap-package ...
//! --gl-rom ...`).
//!
//! Manifest fields: `artifact`, `gl_rom`, `wrap_package`, `wrap_layout`,
//! `key` (the pinned key file; the key produced must equal it byte for
//! byte), all products; `log_cap`, `quotient_degree`, `lookup_budget`,
//! `gl_shards`, `streaming`; optional `entry` (overrides `CompressGL::verify_root`),
//! optional `advice` (product `.ixa` bound via `ixcc::register_advice_program`),
//! optional `field` (`"bn254"` default or `"bls12-381"`).
use super::{
  Error, Handoff, Stage,
  exports::{Field, Kind, WideSource, parse_optional_entry, parse_stage_field},
};
use crate::{
  aiur_backend::{
    Bls12381, Bn254, bls12_381,
    compress_bn::{PackedCapacity, PackedGlProver, decompose, plan_copies_of},
    compress_gl,
    kzg::{Compiler, check_shape},
    kzg_advice as wire, kzg_packed_advice as packed_wire, wide,
  },
  kzg::{Scalar, packed_shplonk::PackedShplonkConfig},
  pipeline::{SetupClass, SetupConfig},
};
use aiur::{
  Execution,
  artifact::WidePackage,
  bytecode::{CheckedProgram, Type},
  field::FieldBackend,
  hints::{HintChannels, PreparedHints},
  library::{advice::Advice, io::StreamAdvice},
  maps::MapOverrides,
  trace::{FunctionCircuit, TracePlan},
};
use multi_stark::{
  config::ProofConfig,
  lookup::{LookupValues, logup_max_degree},
  system::{System, SystemWitness, extension_params},
};
use p3_matrix::{Matrix, dense::RowMajorMatrix};
use serde_json::{Value, json};
use std::{sync::Arc, time::Instant};

fn number(spec: &Value, key: &str) -> Result<usize, Error> {
  spec[key]
    .as_u64()
    .and_then(|v| usize::try_from(v).ok())
    .ok_or_else(|| format!("compress-gl {key}"))
}

fn prepare_custom_gl_hints<'a>(
  program: &'a CheckedProgram<Bn254>,
  advice: &Advice<Bn254>,
  advice_program: Option<CheckedProgram<Bn254>>,
) -> Result<PreparedHints<'a, Bn254>, String> {
  let mut channels = HintChannels::new();
  aiur::library::u32::register(&mut channels, Bn254)?;
  aiur::library::u64::register(&mut channels, Bn254)?;
  aiur::library::goldilocks::register(&mut channels, Bn254)?;
  aiur::library::ixcc::register(&mut channels, Bn254)?;
  if let Some(advice_program) = advice_program {
    aiur::library::ixcc::register_advice_program(
      &mut channels,
      program,
      advice_program,
    )?;
  }
  advice.register_read::<1>("stark.io.read1", false, &mut channels)?;
  advice.register_read::<8>("stark.io.read8", false, &mut channels)?;
  advice.register_read::<64>("stark.io.read64", false, &mut channels)?;
  let mut data = advice.metadata(
    "stark.io.info",
    &Type::Tuple { items: vec![Type::Field; 2] },
    None,
    |_, key| key.len() == 1,
    false,
  )?;
  data.extend(advice.metadata(
    "stark.io.address",
    &Type::Tuple {
      items: vec![Type::Field, Type::Tuple { items: vec![Type::Field; 32] }],
    },
    None,
    |_, key| key.len() == 32,
    false,
  )?);
  data.extend(advice.metadata(
    "stark.io.digest",
    &Type::Tuple { items: vec![Type::Field; 8] },
    Some(4),
    |channel, key| channel == 4 && key.len() == 8,
    false,
  )?);
  let prepared = program.prepare_hint_channels(&data, &channels)?;
  let mut maps = MapOverrides::new();
  aiur::library::u8::register_maps(program, &mut maps)?;
  prepared.with_map_overrides(&maps)
}

fn shard_traces(
  traces: Vec<RowMajorMatrix<Scalar>>,
  copies: &[usize],
  raw_rows: &[usize],
) -> Result<(Vec<RowMajorMatrix<Scalar>>, Vec<(usize, Vec<usize>)>), String> {
  let mut out = Vec::with_capacity(copies.iter().sum());
  let mut shards = vec![];
  for (index, ((trace, &k), &rows)) in
    traces.into_iter().zip(copies).zip(raw_rows).enumerate()
  {
    if k == 1 {
      out.push(trace);
      continue;
    }
    let width = trace.width;
    if rows > trace.height() {
      return Err("sharded circuit has fewer trace rows than executed".into());
    }
    let heights = decompose(rows, k);
    let Some(&first) = heights.first() else {
      out.extend((0..k).map(|_| RowMajorMatrix::new(vec![], width)));
      shards.push((index, heights));
      continue;
    };
    let mut values = trace.values;
    let mut start = first.min(rows);
    let mut rest = Vec::with_capacity(heights.len() - 1);
    for &height in &heights[1..] {
      let end = (start + height).min(rows);
      let mut piece: Vec<Scalar> = values[start * width..end * width].to_vec();
      piece.resize(height * width, Bn254.zero());
      rest.push(RowMajorMatrix::new(piece, width));
      start = end;
    }
    if values.len() > first * width {
      values.truncate(first * width);
    }
    if rows < first {
      values[rows * width..].fill(Bn254.zero());
    }
    out.push(RowMajorMatrix::new(values, width));
    out.extend(rest);
    for _ in heights.len()..k {
      out.push(RowMajorMatrix::new(vec![], width));
    }
    shards.push((index, heights));
  }
  Ok((out, shards))
}

fn build_packed_system(
  inputs: Vec<multi_stark::system::CircuitInputs<Scalar>>,
  functions: usize,
  capacity: PackedCapacity,
  config: PackedShplonkConfig,
  copies: Option<Vec<usize>>,
) -> Result<
  (
    System<PackedShplonkConfig>,
    multi_stark::system::ProverKey<PackedShplonkConfig>,
    Vec<u8>,
    Vec<usize>,
  ),
  String,
> {
  if config.pcs().parameters().max_trace_len() != capacity.cap()?
    || config.max_quotient_degree() != capacity.quotient_degree
  {
    return Err("packed configuration differs from its capacity".into());
  }
  let params = extension_params::<PackedShplonkConfig>();
  for input in &inputs {
    let graph = input
      .compile_graph(&params)
      .map_err(|error| format!("invalid compiler circuit: {error:?}"))?;
    let degree = graph
      .max_constraint_degree
      .max(logup_max_degree(&graph, input.lookup_group_size))
      as usize;
    let quotient = (degree.max(2) - 1)
      .checked_next_power_of_two()
      .ok_or("quotient degree overflow")?;
    if quotient > capacity.quotient_degree {
      return Err(format!(
        "circuit quotient degree {quotient} exceeds the packed capacity {}",
        capacity.quotient_degree
      ));
    }
    if let Some(fixed) = &input.preprocessed {
      let height = fixed.values.len() / fixed.width;
      if height > capacity.cap()? {
        return Err("fixed table exceeds the packed capacity".into());
      }
    }
  }
  let copies = copies.unwrap_or_else(|| vec![1; inputs.len()]);
  if copies.len() != inputs.len()
    || copies.contains(&0)
    || copies.iter().enumerate().any(|(i, &k)| k > 1 && i >= functions)
  {
    return Err("packed copies must cover every circuit, and only function circuits may have several".into());
  }
  let expanded: Vec<_> = inputs
    .into_iter()
    .zip(&copies)
    .flat_map(|(input, &k)| std::iter::repeat_n(input, k))
    .collect();
  let (mut system, key) = System::new(config, expanded);
  let unbound = packed_wire::key_bytes_with_copies(&system, &copies)?;
  system.config =
    system.config.clone().with_key_digest(*blake3::hash(&unbound).as_bytes());
  let key_bytes = packed_wire::key_bytes_with_copies(&system, &copies)?;
  Ok((system, key, key_bytes, copies))
}

#[allow(clippy::too_many_lines)]
fn run_custom_bn254(
  stage: &Stage<'_>,
  entry: &str,
  advice_bytes: Option<&[u8]>,
) -> Result<Handoff, Error> {
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
  let package = WidePackage::decode(&gl_file.bytes)?;
  let trace =
    package.trace.ok_or("CompressGL needs a compiler trace artifact")?;
  let mut program = package.program.check_with(Bn254)?;
  program.track_depth(&trace)?;
  program.entry(entry)?;
  let program = Arc::new(program);
  let plan = TracePlan::new(Arc::clone(&program), trace)?;
  let rom_file = stage.product("gl_rom")?;
  let rom_json: Value =
    serde_json::from_slice(&rom_file.bytes).map_err(|e| e.to_string())?;
  if rom_json["format"] != "ix-compress-gl-rom-1" {
    return Err("gl_rom is not an ix-compress-gl-rom-1 file".into());
  }
  let rom: Vec<(usize, usize)> =
    serde_json::from_value(rom_json["rom"].clone())
      .map_err(|e| e.to_string())?;
  let input = wide::grouped_input(
    &plan,
    capacity.cap()?,
    &rom,
    &gl_file.path,
    gl_hash.to_hex().as_str(),
    entry,
  )?;
  let input_bytes =
    serde_json::to_vec_pretty(&input).map_err(|e| e.to_string())?;
  let exported = stage.stages.exports.export_with_field(
    Kind::Wide,
    Some(Field::Bn254),
    &input_bytes,
  )?;
  let layout = wide::Layout::load(&exported.layout(), &exported.fixed())?;

  let package_file = stage.product("wrap_package")?;
  let layout_file = stage.product("wrap_layout")?;
  let wrap_pkg = aiur::artifact::Package::decode(&package_file.bytes)?;
  let wrap_config: stark_verifier::compress_wrap::LayoutConfig =
    serde_json::from_slice(&layout_file.bytes).map_err(|e| e.to_string())?;
  let wrapper = stark_verifier::compress_wrap::Wrapper::for_layout_with(
    wrap_pkg,
    aiur::trace::stark::Parameters::default(),
    None,
    &wrap_config.layout,
    &WideSource(&stage.stages.exports),
  )?;
  wrap_config.check(&wrapper)?;
  let policy = compress_gl::WrapPolicy::new(&wrapper, &wrap_config.layout)?;
  let ready_seconds = (super::unix_now() - stage.started).max(0.0);
  stage.reserve(1);

  let (wrapped, wait_seconds) = stage.input()?;
  stage.cancelled()?;
  let started = Instant::now();
  let root = &stage.stages.root;
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
    .stages
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
  let advice = stark_verifier::advice(
    Bn254,
    gl_input.key_bytes(),
    gl_input.claims_bytes(),
    gl_input.proof_bytes(),
  )?;
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
  let prepared = prepare_custom_gl_hints(&program, &advice, advice_program)?;
  let args: Vec<Scalar> = gl_input
    .statement()
    .arguments()
    .into_iter()
    .map(|word| Bn254.from_u64(word))
    .collect();
  let record: Execution<Bn254> =
    prepared.execute(entry, args.clone()).map_err(|e| e.to_string())?;
  let gl_execution_seconds = started.elapsed().as_secs_f64();

  stage.reserve(2);
  let gl_compiler =
    Compiler::with_lookup_budget(&plan, capacity.lookup_quotient_budget)?;
  let gl_raw = gl_compiler.raw_row_counts(&record)?;
  let started = Instant::now();
  let dummy_claim = plan.public_claim(
    entry,
    &vec![Bn254.zero(); args.len()],
    &vec![Bn254.zero(); record.output.len()],
  )?;
  let wide_stage = wide::Stage::new(
    layout,
    &gl_compiler,
    &plan,
    &dummy_claim,
    capacity.lookup_quotient_budget,
  )?;
  if wide_stage.rom != rom {
    return Err(
      "the exported ROM tables differ from the requested capacities".into(),
    );
  }
  wide_stage.check_rom(&gl_raw)?;
  let wide_report = json!({
    "exporter": "stages",
    "exporter_blake3": stage.stages.exports.exporter_id(Kind::Wide),
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
  let (system, pk, key_bytes, copies) = stage.gpu(|| {
    build_packed_system(
      wide_stage.inputs.clone(),
      wide_stage.function_circuits,
      capacity,
      config.clone(),
      copies,
    )
  })?;
  let gl_key_seconds = started.elapsed().as_secs_f64();
  stage.write("gl-key.bin", &key_bytes)?;
  let names = wide_stage.names.clone();
  let gl_heights = wide_stage.rows(&gl_compiler.row_counts(&record)?);
  let gl_stage_raw = wide_stage.rows(&gl_raw);
  let gl_cells = |rows: &[usize]| -> usize {
    wide_stage.inputs.iter().zip(rows).map(|(i, &r)| i.main_width * r).sum()
  };

  let claim = plan.public_claim(entry, &args, &record.output)?;
  let timings = system.config.pcs().timings();
  let (commit0, open0) = (timings.commit_seconds(), timings.open_seconds());
  let trace_started = Instant::now();
  let traces =
    wide_stage.traces(gl_compiler.generate(&record, entry, &args)?)?;
  let (traces, shard_info) = if copies.iter().all(|&k| k == 1) {
    (traces, vec![])
  } else {
    shard_traces(traces, &copies, &gl_stage_raw)?
  };
  let main_cells: usize = traces.iter().map(|t| t.height() * t.width()).sum();
  let lookups = if system.config.uses_streaming_lookups() {
    traces
      .iter()
      .zip(&system.circuits)
      .map(|(trace, circuit)| {
        let widths: Vec<usize> =
          circuit.graph.lookups.iter().map(|l| l.args.len()).collect();
        LookupValues::shape_only(trace.height(), &widths)
      })
      .collect()
  } else {
    SystemWitness::from_stage_1(traces.clone(), &system).lookups
  };
  let trace_seconds = trace_started.elapsed().as_secs_f64();
  let prove_started = Instant::now();
  let gl_proof =
    stage.gpu(|| system.prove(&pk, &claim, SystemWitness { traces, lookups }));
  let proving_seconds = prove_started.elapsed().as_secs_f64();
  let (gl_commit, gl_open) =
    (timings.commit_seconds() - commit0, timings.open_seconds() - open0);
  let verify_started = Instant::now();
  check_shape(&system, &gl_proof.active, &gl_proof.log_degrees)?;
  system
    .verify(&claim, &gl_proof)
    .map_err(|e| format!("packed CompressGL verification failed: {e:?}"))?;
  let verification_seconds = verify_started.elapsed().as_secs_f64();

  let mut changed = claim.clone();
  *changed.last_mut().ok_or("empty claim")? += Bn254.one();
  let rejected = system.verify(&changed, &gl_proof).is_err();
  stage.stages.checks.set("gl_native_rejects_changed_output", rejected);
  if !rejected {
    return Err("packed CompressGL accepted a changed output".into());
  }
  let source_proof = packed_wire::proof_bytes(&gl_proof)?;
  let source_claims = wire::claims_bytes(std::slice::from_ref(&claim))?;
  let (gl_peak, _) = super::rss();
  let gl_report = json!({
    "program": entry,
    "artifact": gl_file.path,
    "artifact_blake3": gl_hash.to_hex().as_str(),
    "root_key_blake3": blake3::hash(&stage.stages.root_bytes[0]).to_hex().as_str(),
    "root_claims_blake3": blake3::hash(&stage.stages.root_bytes[1]).to_hex().as_str(),
    "root_proof_blake3": blake3::hash(&stage.stages.root_bytes[2]).to_hex().as_str(),
    "predecessor": "normalized CompressWrap proof",
    "wrap": wrap_report,
    "key_wire_bytes": key_bytes.len(),
    "key_blake3": blake3::hash(&key_bytes).to_hex().as_str(),
    "circuits": system.circuits.len(),
    "circuit_source": "wide_export",
    "wide_export": wide_report,
    "copies": copies.iter().enumerate().filter(|&(_, &k)| k > 1)
      .map(|(i, &k)| json!([names[i], k])).collect::<Vec<_>>(),
    "shards": shard_info.iter().map(|(c, h)| json!([names[*c], h])).collect::<Vec<_>>(),
    "proof_wire_bytes": source_proof.len(),
    "proof_blake3": blake3::hash(&source_proof).to_hex().as_str(),
    "native_accepts": true,
    "native_rejects_changed_output": true,
    "cells": {
      "main_cells_padded": gl_cells(&gl_heights),
      "main_cells_unpadded": gl_cells(&gl_stage_raw),
      "main_cells_padded_sharded": main_cells,
      "instructions": record.instructions,
    },
    "seconds": {
      "execution": gl_execution_seconds,
      "key": gl_key_seconds,
      "trace": trace_seconds,
      "prove": proving_seconds,
      "pcs_commit": gl_commit,
      "pcs_open": gl_open,
      "verify": verification_seconds,
    },
    "peak_rss_bytes": gl_peak,
  });
  stage.write("gl/proof.bin", &source_proof)?;
  stage.write("gl/claims.bin", &source_claims)?;
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
  stage.check_key("key", &key_bytes)?;
  Ok(Handoff {
    key: key_bytes,
    claims: source_claims,
    proof: source_proof,
    ..Handoff::default()
  })
}

fn run_bls12_381(
  stage: &Stage<'_>,
  entry: &str,
  advice_bytes: Option<&[u8]>,
) -> Result<Handoff, Error> {
  let spec = &stage.spec.spec;
  let gl_file = stage.product("artifact")?;
  let gl_hash = blake3::hash(&gl_file.bytes);
  let plan = bls12_381::load_trace_plan(&gl_file.bytes)?;
  let function = plan.program().entry(entry)?.function;
  if let Some(bytes) = advice_bytes {
    let advice_program = bls12_381::load_program(bytes)?;
    let mut hints = HintChannels::new();
    bls12_381::register_standard_hints(&mut hints)?;
    aiur::library::ixcc::register_advice_program(
      &mut hints,
      plan.program(),
      advice_program,
    )?;
  }
  let rom_file = stage.product("gl_rom")?;
  let rom_json: Value =
    serde_json::from_slice(&rom_file.bytes).map_err(|e| e.to_string())?;
  let rom: Vec<(usize, usize)> =
    serde_json::from_value(rom_json["rom"].clone())
      .map_err(|e| e.to_string())?;
  let log_cap =
    u32::try_from(number(spec, "log_cap")?).map_err(|e| e.to_string())?;
  let function_rows = 1usize.checked_shl(log_cap).ok_or("log_cap overflow")?;
  let layout = plan.layout()?;
  let chips = &plan.artifact().chips;
  let groups = &plan.artifact().groups;
  let mut circuits = vec![];
  let mut grouped = vec![];
  for circuit in &layout.circuits {
    match *circuit {
      FunctionCircuit::Chip(i) => {
        circuits.push(json!({"chip": chips[i].name, "cap": function_rows}))
      },
      FunctionCircuit::Group(i) => {
        grouped.push(json!({"group": groups[i].name, "cap": function_rows}))
      },
    }
  }
  let entry_chip = &chips
    [*plan.function_chips().get(function).ok_or("entry without a chip")?]
  .name;
  let artifact_path =
    std::path::absolute(&gl_file.path).map_err(|e| e.to_string())?;
  let input = json!({
    "format": "ix-wide-input-1",
    "field": Field::Bls12381.name(),
    "artifact": artifact_path,
    "artifact_blake3": gl_hash.to_hex().as_str(),
    "circuits": circuits,
    "groups": grouped,
    "rom": rom.iter().map(|&(w, c)| json!([w, c])).collect::<Vec<_>>(),
    "entry": entry_chip,
    "all_maps": true,
    "pow2": true,
    "map_layout": "shared",
  });
  let input_bytes =
    serde_json::to_vec_pretty(&input).map_err(|e| e.to_string())?;
  let _exported = stage.stages.exports.export_with_field(
    Kind::Wide,
    Some(Field::Bls12381),
    &input_bytes,
  )?;
  Err(format!(
    "BLS12-381 fri-verifier artifact ({}, entry {entry}) validated and exported via wide_export --field bls12-381; packed-SHPLONK BLS12-381 prover is not yet wired",
    Bls12381.modulus()
  ))
}

pub(super) fn run(stage: &Stage<'_>) -> Result<Handoff, Error> {
  let spec = &stage.spec.spec;
  let field = parse_stage_field(spec)?;
  let entry_override = parse_optional_entry(spec)?;
  let advice_file = if spec["advice"].is_null() {
    None
  } else {
    Some(stage.product("advice")?)
  };
  let entry = entry_override.unwrap_or(compress_gl::ENTRY);
  if field == Field::Bls12381 {
    return run_bls12_381(
      stage,
      entry,
      advice_file.as_ref().map(|p| p.bytes.as_slice()),
    );
  }
  if entry_override.is_some() || advice_file.is_some() {
    return run_custom_bn254(
      stage,
      entry,
      advice_file.as_ref().map(|p| p.bytes.as_slice()),
    );
  }
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
  let exported = stage.stages.exports.export(Kind::Wide, &input_bytes)?;
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
    &WideSource(&stage.stages.exports),
  )?;
  wrap_config.check(&wrapper)?;
  let policy = compress_gl::WrapPolicy::new(&wrapper, &wrap_config.layout)?;
  let ready_seconds = (super::unix_now() - stage.started).max(0.0);
  stage.reserve(1);

  let (wrapped, wait_seconds) = stage.input()?;
  stage.cancelled()?;
  let started = Instant::now();
  let root = &stage.stages.root;
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
    .stages
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
    "exporter": "stages",
    "exporter_blake3": stage.stages.exports.exporter_id(Kind::Wide),
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
  stage.stages.checks.set("gl_native_rejects_changed_output", rejected);
  if !rejected {
    return Err("packed CompressGL accepted a changed output".into());
  }
  let (gl_peak, _) = super::rss();
  let gl_report = json!({
    "program": compress_gl::ENTRY,
    "artifact": gl_file.path,
    "artifact_blake3": gl_hash.to_hex().as_str(),
    "root_key_blake3": blake3::hash(&stage.stages.root_bytes[0]).to_hex().as_str(),
    "root_claims_blake3": blake3::hash(&stage.stages.root_bytes[1]).to_hex().as_str(),
    "root_proof_blake3": blake3::hash(&stage.stages.root_bytes[2]).to_hex().as_str(),
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
