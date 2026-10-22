//! Repeated witness preparation over an immutable execution record.
//! CPU profiles exclude setup, execution, warmups, diagnostics and destruction.
use aiur::field::FieldBackend;
use aiur::{
  Program,
  hints::HintEntry,
  trace::{
    TraceArtifact, TracePlan,
    stark::{Backend, Parameters},
  },
};
use serde::Deserialize;
use serde_json::json;
use std::{error::Error, time::Instant};

#[path = "../../../tools/bench/profile.rs"]
mod profile;

use ixvm as ixvm_hints;

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
  let path = args.get(1).ok_or("usage: witness PACKAGE.json [SAMPLES]")?;
  let samples =
    args.get(2).map(|s| s.parse::<usize>()).transpose()?.unwrap_or(10);
  if samples == 0 {
    return Err("SAMPLES must be positive".into());
  }
  let package: Package = serde_json::from_slice(&std::fs::read(path)?)?;
  let program = package.program.check_field::<multi_stark::types::Val>()?;
  let address = program.field().decode(&package.address)?;
  let hints = ixvm_hints::prepare(&program, &package.hints)?;
  let plan = TracePlan::new(&program, package.trace)?;
  let entry = &program.program().entries.first().ok_or("missing entry")?.name;
  let backend = Backend::new(&plan, Parameters::default())?;
  let record = hints.execute(entry, address.clone())?;
  let compared_providers =
    std::env::var_os("AIUR_CHECK_HINT_PROVIDERS").is_some();
  if compared_providers {
    let data_record =
      program.prepare_hints(&package.hints)?.execute(entry, address.clone())?;
    assert_eq!(record.output, data_record.output);
    assert_eq!(record.instructions, data_record.instructions);
    assert_eq!(record.queries, data_record.queries);
    assert_eq!(
      serde_json::to_value(&record.memory)?,
      serde_json::to_value(&data_record.memory)?
    );
  }
  let profiler = profile::Profiler::from_env()?;
  let reference = std::env::var_os("AIUR_WITNESS_REFERENCE").is_some();
  let mut seconds = vec![];
  let mut last = None;
  for sample in 0..samples + 2 {
    let guard = if sample >= 2 {
      profiler.as_ref().map(|p| p.start("witness", sample - 2)).transpose()?
    } else {
      None
    };
    let start = Instant::now();
    let trace = if reference {
      Some(plan.generate(&record, entry, &address, true)?)
    } else {
      None
    };
    let witness = if let Some(trace) = &trace {
      backend.witness(&record, trace)?
    } else {
      backend.generate(&record, entry, &address)?
    };
    let elapsed = start.elapsed().as_secs_f64();
    drop(guard);
    if sample >= 2 {
      seconds.push(elapsed);
    }
    last = Some(witness);
  }
  let witness = last.unwrap();
  let trace = plan.generate_reference(&record, entry, &address, true)?;
  plan.check(&record, &trace, entry, &address)?;
  let expected = backend.witness(&record, &trace)?;
  for (got, expected) in witness.traces.iter().zip(&expected.traces) {
    if got.width != expected.width || got.values != expected.values {
      return Err("fused witness differs from the reference trace".into());
    }
  }
  let words: usize = witness.traces.iter().map(|t| t.values.len()).sum();
  let proof = backend.prove(entry, &address, &record.output, witness)?;
  backend.verify(entry, &address, &record.output, &proof)?;
  println!(
    "{}",
    json!({"witness_seconds": seconds, "stage1_words": words, "verified": true,
            "reference": reference, "compared_reference": true, "compared_providers": compared_providers})
  );
  Ok(())
}
