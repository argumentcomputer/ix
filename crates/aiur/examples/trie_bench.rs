//! Bytecode-only, hint-free persistent trie benchmark.
use aiur::field::FieldBackend;
use aiur::{
  Program,
  trace::{
    TraceArtifact, TracePlan,
    stark::{Backend, Parameters, Proof},
  },
};
use multi_stark::p3_matrix::Matrix;
use serde::Deserialize;
use serde_json::json;
use std::{error::Error, time::Instant};

#[path = "../../../tools/bench/profile.rs"]
mod profile;

#[derive(Deserialize)]
struct Package {
  program: Program,
  trace: TraceArtifact,
}
#[derive(Deserialize)]
struct Fixture {
  args: Vec<u64>,
  expected: Vec<u64>,
}

fn main() -> Result<(), Box<dyn Error>> {
  let cli: Vec<_> = std::env::args().collect();
  if cli.len() != 5 {
    return Err(
            "usage: trie_bench PACKAGE.json FIXTURE.json prove|execute|witness SAMPLES".into(),
        );
  }
  let mode = &cli[3];
  let samples: usize = cli[4].parse()?;
  if !["prove", "execute", "witness"].contains(&mode.as_str()) || samples == 0 {
    return Err("invalid mode or sample count".into());
  }
  let start = Instant::now();
  let package: Package = serde_json::from_slice(&std::fs::read(&cli[1])?)?;
  let fixture: Fixture = serde_json::from_slice(&std::fs::read(&cli[2])?)?;
  let program = package.program.check_field::<multi_stark::types::Val>()?;
  let args = program.field().decode(&fixture.args)?;
  let expected = program.field().decode(&fixture.expected)?;
  assert!(program.program().functions.iter().all(|f| {
    f.code
      .iter()
      .all(|op| !matches!(op, aiur::bytecode::Instruction::Hint { .. }))
  }));
  let plan = TracePlan::new(&program, package.trace)?;
  let entry = &program.program().entries[0].name;
  let prepare_seconds = start.elapsed().as_secs_f64();
  let parameters = Parameters::default();
  let start = Instant::now();
  let backend = Backend::new(&plan, parameters)?;
  let setup_seconds = start.elapsed().as_secs_f64();
  let profiler = profile::Profiler::from_env()?;
  let mut times = vec![];
  if mode == "execute" {
    for sample in 0..samples + 2 {
      let guard = if sample >= 2 {
        profiler.as_ref().map(|p| p.start("execute", sample - 2)).transpose()?
      } else {
        None
      };
      let start = Instant::now();
      let record = program.execute(entry, args.clone())?;
      let elapsed = start.elapsed().as_secs_f64();
      drop(guard);
      assert_eq!(record.output, expected);
      if sample >= 2 {
        times.push(elapsed);
      }
    }
    println!(
      "{}",
      json!({"engine": "new-aiur-bytecode", "mode": mode, "seconds": times, "output": expected})
    );
    return Ok(());
  }
  let start = Instant::now();
  let record = program.execute(entry, args.clone())?;
  let execution_seconds = start.elapsed().as_secs_f64();
  assert_eq!(record.output, expected);
  let counts = json!({"function_queries": record.queries.len(), "memory_queries": record.memory.len(), "instructions": record.instructions});
  let mut raw_rows = std::collections::HashMap::new();
  for key in record.queries.keys() {
    *raw_rows
      .entry(program.program().functions[key.function].name.clone())
      .or_insert(0usize) += 1;
  }
  for cell in record.memory.iter() {
    *raw_rows.entry(format!("<ROM:{}>", cell.cell.value.len())).or_insert(0) +=
      1;
  }
  let mut last = None;
  for sample in 0..if mode == "witness" { samples + 2 } else { 1 } {
    let guard = if mode == "witness" && sample >= 2 {
      profiler.as_ref().map(|p| p.start("witness", sample - 2)).transpose()?
    } else {
      None
    };
    let start = Instant::now();
    let witness = backend.generate(&record, entry, &args)?;
    let elapsed = start.elapsed().as_secs_f64();
    drop(guard);
    if mode == "prove" || sample >= 2 {
      times.push(elapsed);
    }
    last = Some(witness);
  }
  let witness = last.unwrap();
  let statistics = backend.statistics();
  let circuits: Vec<_> = statistics
    .iter()
    .zip(&witness.traces)
    .map(|(s, t)| {
      let mut value = serde_json::to_value(s).unwrap();
      value["height"] = json!(t.height());
      value["rows"] =
        json!(raw_rows.get(s.name.as_str()).copied().unwrap_or(0));
      value
    })
    .collect();
  let stage1_words: usize = witness.traces.iter().map(|t| t.values.len()).sum();
  drop(record);
  let start = Instant::now();
  let proof = backend.prove(entry, &args, &expected, witness)?;
  let prove_seconds = start.elapsed().as_secs_f64();
  let bytes = proof.to_bytes()?;
  let proof = Proof::from_bytes(&bytes)?;
  let start = Instant::now();
  backend.verify(entry, &args, &expected, &proof)?;
  let verify_seconds = start.elapsed().as_secs_f64();
  println!(
    "{}",
    json!({"engine": "new-aiur-bytecode", "mode": mode, "args": args, "output": expected,
        "prepare_seconds": prepare_seconds, "setup_seconds": setup_seconds,
        "execution_seconds": execution_seconds, "witness_seconds": times[0], "seconds": times,
        "prove_seconds": prove_seconds, "verify_seconds": verify_seconds, "proof_bytes": bytes.len(),
        "counts": counts, "stage1_words": stage1_words, "circuits": circuits, "verified": true})
  );
  Ok(())
}
