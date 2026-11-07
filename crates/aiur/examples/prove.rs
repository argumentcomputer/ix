//! Prove a Lean `export-trace` package. The default entry is its first selected
//! entrypoint. See design/multi-stark.md for the trust boundary and commands.
use aiur::field::FieldBackend;
use aiur::{
  Program,
  hints::HintEntry,
  trace::{
    TraceArtifact, TracePlan,
    stark::{Backend, Parameters, Proof},
  },
};
use multi_stark::p3_field::PrimeField64;
use multi_stark::p3_matrix::Matrix;
use serde::Deserialize;
use serde_json::json;
use std::{error::Error, time::Instant};

#[derive(Deserialize)]
struct Package {
  program: Program,
  #[serde(default)]
  hints: Vec<HintEntry>,
  #[serde(alias = "args")]
  address: Vec<u64>,
  trace: TraceArtifact,
}

fn main() -> Result<(), Box<dyn Error>> {
  let args: Vec<_> = std::env::args().collect();
  let path =
    args.get(1).ok_or("usage: prove PACKAGE.json [PROOF.bin] [REPORT.json]")?;
  let start = Instant::now();
  let package: Package = serde_json::from_slice(&std::fs::read(path)?)?;
  let program = package.program.check_field::<multi_stark::types::Val>()?;
  let address = program.field().decode(&package.address)?;
  let hints = program.prepare_hints(&package.hints)?;
  let plan = TracePlan::new(&program, package.trace)?;
  let entry =
    &program.program().entries.first().ok_or("no selected entrypoint")?.name;
  let prepare_seconds = start.elapsed().as_secs_f64();

  let mut parameters = Parameters::default();
  if let Ok(n) = std::env::var("AIUR_STARK_LOG_BLOWUP") {
    parameters.log_blowup = n.parse()?;
  }
  if let Ok(n) = std::env::var("AIUR_STARK_QUERIES") {
    parameters.num_queries = n.parse()?;
  }
  eprintln!("Setting up circuits and committing fixed tables...");
  let start = Instant::now();
  let backend = Backend::new(&plan, parameters)?;
  let setup_seconds = start.elapsed().as_secs_f64();

  let start = Instant::now();
  let record = hints.execute(entry, address.clone())?;
  let execution_seconds = start.elapsed().as_secs_f64();
  let reference = std::env::var_os("AIUR_WITNESS_REFERENCE").is_some();
  let (witness, generation_seconds, witness_seconds, check_seconds) =
    if reference {
      let start = Instant::now();
      let trace = plan.generate(&record, entry, &address, true)?;
      let generation_seconds = start.elapsed().as_secs_f64();
      let start = Instant::now();
      plan.check(&record, &trace, entry, &address)?;
      let check_seconds = start.elapsed().as_secs_f64();
      let start = Instant::now();
      let witness = backend.witness(&record, &trace)?;
      (
        witness,
        generation_seconds,
        start.elapsed().as_secs_f64(),
        check_seconds,
      )
    } else {
      let start = Instant::now();
      let witness = backend.generate(&record, entry, &address)?;
      let witness_seconds = start.elapsed().as_secs_f64();
      // Diagnostics remain outside witness/proving measurements. Check the
      // independent writer and compare every function column and count.
      let start = Instant::now();
      let trace = plan.generate_reference(&record, entry, &address, true)?;
      plan.check(&record, &trace, entry, &address)?;
      for (matrix, actual) in trace.matrices.iter().zip(&witness.traces) {
        if actual.width != matrix.width + 1 || actual.height() != matrix.height
        {
          return Err("fused witness shape differs from the reference".into());
        }
        for r in 0..matrix.height {
          let row = &actual.values[r * actual.width..(r + 1) * actual.width];
          if !row[..matrix.width]
            .iter()
            .copied()
            .eq(matrix.row(r).iter().copied())
            || row[matrix.width].as_canonical_u64() != matrix.multiplicities[r]
          {
            return Err("fused witness differs from the reference".into());
          }
        }
      }
      (witness, 0.0, witness_seconds, start.elapsed().as_secs_f64())
    };
  let statistics = backend.statistics();
  let circuits: Vec<_> = statistics
    .iter()
    .zip(&witness.traces)
    .map(|(s, t)| {
      let mut value = serde_json::to_value(s).unwrap();
      value["height"] = json!(t.height());
      value
    })
    .collect();
  let stage1_words: usize = witness.traces.iter().map(|t| t.values.len()).sum();
  let output = record.output.clone();
  drop(record);
  eprintln!(
    "Proving {} active circuits ({} stage-1 words)...",
    witness.traces.iter().filter(|t| t.height() > 0).count(),
    stage1_words
  );
  let start = Instant::now();
  let proof = backend.prove(entry, &address, &output, witness)?;
  let prove_seconds = start.elapsed().as_secs_f64();
  let bytes = proof.to_bytes()?;
  let proof = Proof::from_bytes(&bytes)?;
  eprintln!("Verifying serialized proof ({} bytes)...", bytes.len());
  let start = Instant::now();
  backend.verify(entry, &address, &output, &proof)?;
  let verify_seconds = start.elapsed().as_secs_f64();
  if let Some(path) = args.get(2) {
    std::fs::write(path, &bytes)?;
  }
  let report = json!({
      "entry": entry, "args": address, "output": output, "parameters": parameters,
      "prepare_seconds": prepare_seconds, "setup_seconds": setup_seconds,
      "execution_seconds": execution_seconds, "generation_seconds": generation_seconds,
      "check_seconds": check_seconds, "witness_seconds": witness_seconds,
      "witness_mode": if reference { "reference" } else { "fused" },
      "prove_seconds": prove_seconds, "verify_seconds": verify_seconds,
      "proof_bytes": bytes.len(), "stage1_words": stage1_words,
      "verified": true, "circuits": circuits,
  });
  if let Some(path) = args.get(3) {
    serde_json::to_writer_pretty(
      std::io::BufWriter::new(std::fs::File::create(path)?),
      &report,
    )?;
  }
  // Circuit details go in the report; stdout is a short timing summary.
  let mut summary = report;
  summary.as_object_mut().unwrap().remove("circuits");
  println!("{}", serde_json::to_string_pretty(&summary)?);
  Ok(())
}
