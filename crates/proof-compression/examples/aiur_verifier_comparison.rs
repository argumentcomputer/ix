//! Compare both verifier implementations on one natively checked KZG proof.
//! The report separates execution cells, padding, fixed tables and commitments.
use aiur::{
  artifact::WidePackage, field::FieldBackend, hints::HintChannels,
  maps::MapOverrides, trace::TracePlan,
};
use ix_proof_compression::{
  aiur_backend::{
    Bn254, fq, g1,
    kzg::{Compiler, VerifyingKey},
    kzg_advice as wire,
  },
  foreign::KzgCircuitExt,
  kzg::{KzgConfig, Scalar, Srs},
  recursive::native_verifier,
};
use multi_stark::{
  config::ProofConfig,
  plonkish::CircuitBuilder,
  system::{System, SystemWitness},
};
use std::{fs, path::PathBuf, sync::Arc};

fn main() -> Result<(), Box<dyn std::error::Error>> {
  let args: Vec<_> = std::env::args().skip(1).collect();
  if args.first().is_some_and(|arg| arg == "--inspect") {
    if args.len() != 5 {
      return Err("usage: --inspect KEY KEY_BLAKE3 PROOF OUTPUT_JSON".into());
    }
    let key_bytes = fs::read(&args[1])?;
    let pin = blake3::Hash::from_hex(&args[2])?;
    let key = VerifyingKey::from_bytes(&key_bytes, pin.as_bytes())?;
    let proof_bytes = fs::read(&args[3])?;
    let proof = key.decode_proof(&proof_bytes)?;
    let count = |commitment: &ix_proof_compression::kzg::KzgCommitment| {
      commitment.0.iter().map(Vec::len).sum::<usize>()
    };
    let report = serde_json::json!({
      "scope":"Canonical key-bound proof transport inventory; does not establish a statement's validity",
      "proof_bytes":proof_bytes.len(),"key_blake3":pin.to_hex().as_str(),
      "active_circuits":proof.active.iter().filter(|&&active|active).count(),
      "total_circuits":proof.active.len(),"log_degrees":proof.log_degrees,
      "main_commitments":count(&proof.commitments.stage_1_trace),
      "lookup_commitments":count(&proof.commitments.stage_2_trace),
      "quotient_commitments":count(&proof.commitments.quotient_chunks),
      "opening_witnesses":proof.opening_proof.0.len(),
      "fixed_key_commitments":key.system().preprocessed_commit.as_ref().map(count),
    });
    fs::write(&args[4], serde_json::to_vec_pretty(&report)?)?;
    println!("{}", serde_json::to_string_pretty(&report)?);
    return Ok(());
  }
  if args.len() != 2 && !(args.len() == 4 && args[2] == "--prove-kzg") {
    return Err(
      "usage: aiur_verifier_comparison AIUR_VERIFIER_ARTIFACT NEW_OUTPUT [--prove-kzg MAX_LOG_HEIGHT]"
        .into(),
    );
  }
  let out = PathBuf::from(&args[1]);
  fs::create_dir(&out)?;
  let mut b = CircuitBuilder::<Scalar>::new();
  let table =
    b.fixed_table("small", vec![vec![Bn254.one()], vec![Bn254.from_u64(2)]]);
  let x = b.input("x");
  for _ in 0..30 {
    b.lookup(table, &[x]);
  }
  let square = b.mul(x, x);
  b.expose_public(square);
  let circuit = b.finish();
  let mut witness = circuit.witness();
  witness.set(x, Bn254.from_u64(2))?;
  let assignment = witness.generate()?;
  let lowered = circuit.lower_to_multi_stark_sharded(Bn254.from_u64(93), 32)?;
  let claims = lowered.claims(assignment.public_values())?;
  let refs: Vec<_> = claims.iter().map(Vec::as_slice).collect();
  let srs =
    Arc::new(Srs::unsafe_dev_setup(32, b"matched-aiur-native-verifier"));
  let (system, key) = System::new(
    KzgConfig::new(srs.clone(), 2),
    lowered.kzg_circuit_inputs(32, 2)?,
  );
  let proof = system.prove_multiple_claims(
    &key,
    &refs,
    SystemWitness::from_stage_1(lowered.traces(&assignment)?, &system),
  );
  system
    .verify_multiple_claims(&refs, &proof)
    .map_err(|e| format!("input proof: {e:?}"))?;
  let identity = native_verifier::InnerVerifyingKey {
    circuits: &system.circuits,
    fixed: system.preprocessed_commit.as_ref().unwrap(),
    transcript_seed: system.config.transcript_seed(),
    transcript_kind: system.config.transcript_kind(),
    generator: srs.g1[0],
    g2: srs.g2,
    tau_g2: srs.tau_g2,
    max_log_degree: system.config.max_log_degree(),
  };
  let public_locations: Vec<_> = claims
    .iter()
    .enumerate()
    .map(|(row, values)| (row, values.len() - 1))
    .collect();
  let native_counts =
    native_verifier::count(&identity, &proof, &claims, &public_locations)?;
  let built =
    native_verifier::build(&system, &srs, &proof, &claims, &public_locations)?;
  let native_assignment = built.assign()?;
  let native_stats = built.circuit.stats();
  assert_eq!(native_counts.stats, native_stats);
  let native_layout = built.circuit.multi_stark_layout()?;
  let native = built
    .circuit
    .lower_to_multi_stark_sharded(Bn254.from_u64(94), 1 << 24)?
    .merge_table_traces(1 << 24)?;
  let native_inputs = native.kzg_circuit_inputs(1 << 24, 2)?;
  let native_circuits: Vec<_> = native_inputs
    .iter()
    .enumerate()
    .map(|(index, input)| {
      let (height, _) = native.trace_dimensions(index).unwrap();
      dimensions(&format!("native:{index}"), input, height)
    })
    .collect();
  let key = VerifyingKey::from_system(&system)?;
  let key_bytes = wire::key_bytes(&key)?;
  let claims_bytes = wire::claims_bytes(&claims)?;
  let proof_bytes = wire::proof_bytes(&proof)?;
  for (name, bytes) in [
    ("key.bin", &key_bytes),
    ("claims.bin", &claims_bytes),
    ("proof.bin", &proof_bytes),
  ] {
    fs::write(out.join(name), bytes)?;
  }
  let artifact = fs::read(&args[0])?;
  let package = WidePackage::decode(&artifact)?;
  let trace = package.trace.ok_or("missing trace")?;
  let mut program = package.program.check_with(Bn254)?;
  program.track_depth(&trace)?;
  let plan = TracePlan::new(Arc::new(program), trace)?;
  let mut hints = HintChannels::new();
  aiur::library::u32::register(&mut hints, Bn254)?;
  aiur::library::u64::register(&mut hints, Bn254)?;
  fq::register(&mut hints)?;
  g1::register(&mut hints)?;
  wire::register(&mut hints)?;
  wire::Inputs::new(
    key_bytes.clone(),
    claims_bytes.clone(),
    proof_bytes.clone(),
    vec![],
  )?
  .register(&mut hints)?;
  let mut maps = MapOverrides::new();
  aiur::library::u8::register_maps(plan.program(), &mut maps)?;
  let public: Vec<_> = wire::digest_words(blake3::hash(&key_bytes).as_bytes())
    .into_iter()
    .chain(wire::digest_words(blake3::hash(&claims_bytes).as_bytes()))
    .collect();
  let record = plan
    .program()
    .prepare_hint_channels(&[], &hints)?
    .with_map_overrides(&maps)?
    .execute("KzgVerifier::verify_deferred", public.clone())?;
  assert_eq!(
    record.output,
    native_assignment.public_values()[public_locations.len()..]
  );
  let compiler = Compiler::new(&plan)?;
  let heights = compiler.row_counts(&record)?;
  let layout = plan.layout()?;
  let mut rows = vec![0usize; heights.len()];
  let mut calls = vec![];
  for (function, &chip) in plan.function_chips().iter().enumerate() {
    let count =
      record.queries.callable_rows(function).ok_or("missing function count")?;
    rows[layout.placements[chip].circuit] += count;
    calls.push(serde_json::json!({
      "name":plan.program().program().functions[function].name,
      "rows":count,
    }));
  }
  let memories: Vec<_> = record.memory.width_counts().collect();
  let mut circuits = vec![];
  for (index, ((name, c), height)) in
    compiler.names().iter().zip(compiler.inputs()).zip(&heights).enumerate()
  {
    let raw = if let Some(width) = name
      .strip_prefix("<ROM:")
      .and_then(|s| s.strip_suffix('>'))
      .and_then(|s| s.parse::<usize>().ok())
    {
      memories.iter().find(|(w, _)| *w == width).map_or(0, |(_, n)| *n)
    } else if c.preprocessed.is_some() {
      *height
    } else {
      rows[index]
    };
    let mut dimensions = dimensions(name, c, *height);
    dimensions["execution_rows"] = raw.into();
    dimensions["unpadded_main_cells"] = (raw * c.main_width).into();
    circuits.push(dimensions);
  }
  let point_count = proof
    .commitments
    .stage_1_trace
    .0
    .iter()
    .chain(&proof.commitments.stage_2_trace.0)
    .chain(&proof.commitments.quotient_chunks.0)
    .map(Vec::len)
    .sum::<usize>()
    + proof.opening_proof.0.len();
  let mut report = serde_json::json!({
    "format":"ix-matched-kzg-verifier-layout-v1",
    "scope":concat!(
      "Same natively verified development KZG proof and equal deferred pairing outputs. ",
      "Native key/shape and claim structure are compiler constants, with claim payloads public; ",
      "Aiur authenticates key and claims digests as public inputs. ",
      "Native lowering uses the production two-trace layout and lookup tuning with quotient budget 2. ",
      "Optional proving is a development regression, not an Init benchmark."
    ),
    "input":{
      "key_blake3":blake3::hash(&key_bytes).to_hex().as_str(),
      "claims_blake3":blake3::hash(&claims_bytes).to_hex().as_str(),
      "proof_blake3":blake3::hash(&proof_bytes).to_hex().as_str(),
      "proof_bytes":proof_bytes.len(),
      "proof_curve_points":point_count,
    },
    "native":{
      "frontend":stats(native_counts.stats),
      "phases":native_counts.phases.iter().map(|p|serde_json::json!({
        "phase":p.name,"cumulative":stats(p.stats)
      })).collect::<Vec<_>>(),
      "msm_terms":native_counts.msm_terms,
      "used_computation_rows":native_layout.used_rows,
      "totals":totals(&native_circuits),
      "circuits":native_circuits,
    },
    "aiur":{
      "artifact_blake3":blake3::hash(&artifact).to_hex().as_str(),
      "totals":totals(&circuits),
      "calls":calls,
      "circuits":circuits,
    },
    "outputs_equal":true,
  });
  fs::write(out.join("comparison.json"), serde_json::to_vec_pretty(&report)?)?;
  if args.len() == 4 {
    use ix_proof_compression::aiur_backend::kzg::Backend;
    let log: u32 = args[3].parse()?;
    let cap = 1usize.checked_shl(log).ok_or("KZG capacity overflow")?;
    let srs =
      Arc::new(Srs::unsafe_dev_setup(cap, b"matched-grouped-kzg-development"));
    let backend = Backend::new(&plan, KzgConfig::new(srs, 8))?;
    let public_args =
      plan.public_args(&record, "KzgVerifier::verify_deferred", &public)?;
    let witness =
      backend.generate(&record, "KzgVerifier::verify_deferred", &public)?;
    let proof = backend.prove(
      "KzgVerifier::verify_deferred",
      &public_args,
      &record.output,
      witness,
    )?;
    let key_bytes = backend.verifying_key()?.to_bytes()?;
    let key_pin = blake3::hash(&key_bytes);
    let key = VerifyingKey::from_bytes(&key_bytes, key_pin.as_bytes())?;
    let claim = backend.claim(
      "KzgVerifier::verify_deferred",
      &public_args,
      &record.output,
    )?;
    let bytes = key.encode_proof(&proof)?;
    key.verify_bytes(&claim, &bytes)?;
    let mut changed = claim;
    *changed.last_mut().ok_or("empty claim")? += Bn254.one();
    if key.verify_bytes(&changed, &bytes).is_ok() {
      return Err("KZG proof accepted changed output".into());
    }
    let points = proof
      .commitments
      .stage_1_trace
      .0
      .iter()
      .chain(&proof.commitments.stage_2_trace.0)
      .chain(&proof.commitments.quotient_chunks.0)
      .map(Vec::len)
      .sum::<usize>()
      + proof.opening_proof.0.len();
    fs::write(out.join("outer-key.bin"), &key_bytes)?;
    fs::write(out.join("outer-proof.bin"), &bytes)?;
    report["outer_proof"] = serde_json::json!({"scope":"Actual proof of this Aiur verifier execution using the existing column KZG PCS and explicit development setup; not Init","max_trace_height":cap,"key_blake3":key_pin.to_hex().as_str(),"proof_blake3":blake3::hash(&bytes).to_hex().as_str(),"proof_bytes":bytes.len(),"variable_g1_points":points,"portable_verification":true,"changed_output_rejected":true});
    fs::write(
      out.join("comparison.json"),
      serde_json::to_vec_pretty(&report)?,
    )?;
  }
  println!("matched verifier report: {}", out.display());
  Ok(())
}

fn stats(s: multi_stark::plonkish::CircuitStats) -> serde_json::Value {
  serde_json::json!({
    "values":s.values,"gates":s.gates,"lookups":s.lookups,
    "hash_compressions":s.hash_compressions,"hash_calls":s.hash_calls,
  })
}

fn dimensions(
  name: &str,
  input: &multi_stark::system::CircuitInputs<Scalar>,
  height: usize,
) -> serde_json::Value {
  let lookup = multi_stark::lookup::stage2_width(
    input.lookups.len(),
    input.lookup_group_size,
    1,
  );
  let quotient = quotient_columns(input);
  serde_json::json!({
    "name":name,"height":height,"main_width":input.main_width,
    "padded_main_cells":height*input.main_width,
    "padded_lookup_cells":height*lookup,
    "padded_quotient_cells":height*quotient,
    "fixed_cells":input.preprocessed.as_ref().map_or(0,|m|m.values.len()),
    "fixed_width":input.preprocessed.as_ref().map_or(0,|m|m.width),
    "lookups":input.lookups.len(),"lookup_group_size":input.lookup_group_size,
    "lookup_columns":lookup,"quotient_columns":quotient,
  })
}

fn totals(circuits: &[serde_json::Value]) -> serde_json::Value {
  let mut totals = serde_json::Map::new();
  for key in [
    "padded_main_cells",
    "unpadded_main_cells",
    "fixed_cells",
    "padded_lookup_cells",
    "padded_quotient_cells",
  ] {
    if circuits.iter().all(|c| c[key].is_u64()) {
      let total: u64 = circuits.iter().map(|c| c[key].as_u64().unwrap()).sum();
      totals.insert(key.into(), total.into());
    }
  }
  for (name, column) in [
    ("main_commitments", "main_width"),
    ("lookup_commitments", "lookup_columns"),
    ("quotient_commitments", "quotient_columns"),
  ] {
    let total: u64 = circuits
      .iter()
      .filter(|c| c["height"].as_u64().unwrap() != 0)
      .map(|c| c[column].as_u64().unwrap())
      .sum();
    totals.insert(name.into(), total.into());
  }
  totals.insert(
    "active_circuits".into(),
    circuits
      .iter()
      .filter(|c| c["height"].as_u64().unwrap() != 0)
      .count()
      .into(),
  );
  totals.insert(
    "maximum_main_height".into(),
    circuits
      .iter()
      .map(|c| c["height"].as_u64().unwrap())
      .max()
      .unwrap_or(0)
      .into(),
  );
  totals.into()
}

fn quotient_columns(
  input: &multi_stark::system::CircuitInputs<Scalar>,
) -> usize {
  let graph = input
    .compile_graph(&multi_stark::system::extension_params::<KzgConfig>())
    .unwrap();
  let degree = graph
    .max_constraint_degree
    .max(multi_stark::lookup::logup_max_degree(&graph, input.lookup_group_size))
    as usize;
  (degree.max(2) - 1).next_power_of_two()
}
