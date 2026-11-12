//! Execute and size a constrained fixed-anchor pairing check. Proving uses
//! the independently admitted Ignition parameters and records the full shape.

use aiur::{
  artifact::WidePackage, field::FieldBackend, hints::HintChannels,
  trace::TracePlan,
};
use ark_bn254::G1Affine;
use ark_ec::AffineRepr;
use ix_proof_compression::{
  aiur_backend::{
    Bn254, fq, g1,
    kzg::{Backend, Compiler},
    pairing,
    plonk::Exporter,
  },
  kzg::{KzgConfig, srs::gnark},
};
use p3_matrix::Matrix;
use std::{fs, path::PathBuf, sync::Arc, time::Instant};

#[cfg(feature = "plonk")]
#[path = "aiur_pairing_profile/plonk_cost.rs"]
mod plonk_cost;

fn main() -> Result<(), Box<dyn std::error::Error>> {
  let arguments: Vec<_> = std::env::args().skip(1).collect();
  if arguments.len() < 2 {
    return Err("usage: aiur_pairing_profile ARTIFACT NEW_OUTPUT [--ignition] [--prove-kzg] [--compile-plonk] [--estimate-plonk] [--chunks]".into());
  }
  for flag in &arguments[2..] {
    if !matches!(
      flag.as_str(),
      "--ignition"
        | "--prove-kzg"
        | "--compile-plonk"
        | "--estimate-plonk"
        | "--chunks"
    ) {
      return Err(format!("unknown pairing profile option: {flag}").into());
    }
  }
  let artifact = fs::read(&arguments[0])?;
  let out = PathBuf::from(&arguments[1]);
  fs::create_dir(&out)?;
  let ignition = arguments.iter().any(|arg| arg == "--ignition");
  let parameters = ix_proof_compression::pipeline::ignition_parameters()?;
  let (powers, anchors) = pairing::verifier_anchors(&parameters);
  let points = if ignition {
    [powers[1], -powers[0]]
  } else {
    let p = G1Affine::generator();
    [p, -p]
  };
  let expected_lines = pairing::fixed_lines(if ignition {
    anchors
  } else {
    [ark_bn254::G2Affine::generator(); 2]
  })?;
  let package = WidePackage::decode(&artifact)?;
  let fixed = package
    .program
    .tables
    .iter()
    .find(|table| table.name == "BN254Pairing::line_outputs")
    .ok_or("missing fixed pairing lines")?;
  let expected: Vec<Vec<_>> = expected_lines
    .iter()
    .map(|row| row.iter().map(|&v| Bn254.to_word(v)).collect())
    .collect();
  if fixed.rows != expected {
    return Err(
      "artifact line constants differ from independently expected anchors"
        .into(),
    );
  }
  let trace = package.trace.ok_or("missing compiler trace")?;
  let mut checked = package.program.check_with(Bn254)?;
  checked.track_depth(&trace)?;
  let plan = TracePlan::new(Arc::new(checked), trace)?;
  let mut hints = HintChannels::new();
  fq::register(&mut hints)?;
  g1::register(&mut hints)?;
  pairing::register(&mut hints)?;
  let executor = plan.program().prepare_hint_channels(&[], &hints)?;
  let chunks = arguments.iter().any(|arg| arg == "--chunks");
  let (entry, args) = if chunks {
    ("PairingTest::check_chunks", g1::encode_chunks(points)?.to_vec())
  } else {
    ("PairingTest::check", points.into_iter().flat_map(g1::encode).collect())
  };
  let start = Instant::now();
  let record = executor.execute(entry, args.clone())?;
  let execution = start.elapsed().as_secs_f64();
  let public = plan.public_args(&record, entry, &args)?;
  let compiler = Compiler::new(&plan)?;
  let start = Instant::now();
  let traces = compiler.generate(&record, entry, &args)?;
  let population = start.elapsed().as_secs_f64();
  let capacities: Vec<_> =
    traces.iter().map(|trace| trace.height().max(1)).collect();
  let cells: usize = traces.iter().map(|trace| trace.values.len()).sum();
  let shape:Vec<_>=traces.iter().zip(compiler.names()).map(|(trace,name)|serde_json::json!({"name":name,"height":trace.height(),"width":trace.width,"cells":trace.values.len()})).collect();
  let mut report = serde_json::json!({"format":"ix-aiur-pairing-cost-v1","artifact_blake3":blake3::hash(&artifact).to_hex().as_str(),"ignition_anchors":ignition,"compressed_chunks":chunks,"execution_seconds":execution,"population_seconds":population,"main_cells":cells,"main_field_bytes":cells*32,"circuits":shape});
  println!(
    "pairing execution={execution:.3}s population={population:.3}s main_cells={cells}"
  );
  fs::write(out.join("cost.json"), serde_json::to_vec_pretty(&report)?)?;
  drop(traces);
  if arguments.iter().any(|arg| arg == "--compile-plonk") {
    let exporter =
      Exporter::new(&plan, &capacities, entry, &public, &record.output)?;
    fs::write(out.join("schema.json"), serde_json::to_vec(exporter.schema())?)?;
    #[cfg(feature = "plonk")]
    {
      let start = Instant::now();
      let info = ix_proof_compression::aiur_backend::plonk::gnark::compile(
        exporter.schema(),
        &out.join("circuit.bin"),
      )?;
      report["plonk"] = serde_json::json!({"domain":info.domain,"constraints":info.constraints,"public_inputs":info.public_inputs,"commitments":info.commitments,"compile_seconds":start.elapsed().as_secs_f64()});
      fs::write(
        out.join("witness.json"),
        serde_json::to_vec(&exporter.witness(&record, &args)?)?,
      )?;
    }
    #[cfg(not(feature = "plonk"))]
    return Err("--compile-plonk requires the plonk feature".into());
  }
  if arguments.iter().any(|arg| arg == "--estimate-plonk") {
    let exporter =
      Exporter::new(&plan, &capacities, entry, &public, &record.output)?;
    #[cfg(feature = "plonk")]
    {
      report["plonk_estimate"] = plonk_cost::estimate(exporter.schema(), &out)?;
    }
    #[cfg(not(feature = "plonk"))]
    {
      let _ = exporter;
      return Err("--estimate-plonk requires the plonk feature".into());
    }
  }
  if arguments.iter().any(|arg| arg == "--prove-kzg") {
    let height = *capacities.iter().max().ok_or("empty trace capacity")?;
    let prefix = height.checked_mul(8).ok_or("SRS prefix overflow")?.max(2);
    let path = PathBuf::from(
      std::env::var_os("IX_KZG_SRS")
        .ok_or("IX_KZG_SRS must select admitted Ignition parameters")?,
    );
    let srs = gnark::load(&path, prefix, parameters.public_setup())?;
    if srs.g2 != anchors[0] || srs.tau_g2 != anchors[1] || srs.g1[..2] != powers
    {
      return Err("loaded SRS anchors differ from release parameters".into());
    }
    let backend = Backend::new(
      &plan,
      KzgConfig::with_max_trace_len(Arc::new(srs), height.max(2), 8),
    )?;
    let start = Instant::now();
    let witness = backend.generate(&record, entry, &args)?;
    let proof = backend.prove(entry, &public, &record.output, witness)?;
    let proving = start.elapsed().as_secs_f64();
    let start = Instant::now();
    backend.verify(entry, &public, &record.output, &proof)?;
    let verification = start.elapsed().as_secs_f64();
    let key = backend.verifying_key()?;
    let bytes = key.encode_proof(&proof)?;
    let claim = backend.claim(entry, &public, &record.output)?;
    key.verify_bytes(&claim, &bytes)?;
    let mut changed = public.clone();
    changed[0] += Bn254.one();
    if backend.verify(entry, &changed, &record.output, &proof).is_ok() {
      return Err("altered pairing operand verified".into());
    }
    fs::write(out.join("key.bin"), key.to_bytes()?)?;
    fs::write(out.join("proof.bin"), &bytes)?;
    report["kzg"] = serde_json::json!({"proving_seconds":proving,"verification_seconds":verification,"proof_bytes":bytes.len(),"srs_prefix":prefix});
  }
  fs::write(out.join("cost.json"), serde_json::to_vec_pretty(&report)?)?;
  Ok(())
}
