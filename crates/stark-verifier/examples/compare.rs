//! Same bytecode benchmark contract as Benchmarks.CompareAiur for legacy.
use aiur::{
  field::FieldBackend,
  library::io::Invocation,
  trace::{
    TraceArtifact, TracePlan,
    stark::{Backend, Parameters},
  },
};
use multi_stark::{batch::Retention, p3_matrix::Matrix, types::Val};
use serde_json::json;
use std::{error::Error, time::Instant};

#[derive(serde::Deserialize)]
struct Package {
  program: aiur::Program,
  trace: TraceArtifact,
}

fn main() -> Result<(), Box<dyn Error>> {
  let thp_disabled = ix_bench::configure_benchmark_memory()?;
  let cli: Vec<_> = std::env::args().collect();
  if cli.len() < 5 {
    return Err(
      "usage: compare PACKAGE INPUT OUTPUT SAMPLES [--ungrouped] [--prove] [--counts-only] [--groups FILE]"
        .into(),
    );
  }
  let mut package: Package = aiur::decode_artifact(&std::fs::read(&cli[1])?)?;
  let invocation: Invocation =
    serde_json::from_slice(&std::fs::read(&cli[2])?)?;
  let samples: usize = cli[4].parse()?;
  if samples == 0 {
    return Err("zero benchmark samples".into());
  }
  if cli.iter().any(|a| a == "--ungrouped") {
    package.trace.groups.clear();
  }
  if let Some(at) = cli.iter().position(|a| a == "--groups") {
    let path = cli.get(at + 1).ok_or("missing groups path")?;
    package.trace.groups = aiur::decode_artifact(&std::fs::read(path)?)?;
  }
  let counts_only = cli.iter().any(|a| a == "--counts-only");
  let reuse_execution =
    std::env::var("IX_BENCH_REUSE_EXECUTION").is_ok_and(|v| v == "1");
  let functions: Vec<_> = package
    .program
    .functions
    .iter()
    .map(|f| {
      let plan = package
        .trace
        .functions
        .iter()
        .find(|p| p.name == f.name)
        .ok_or("missing function plan")?;
      Ok((f.name.clone(), plan.chip.clone()))
    })
    .collect::<Result<_, &str>>()?;
  let start = Instant::now();
  let program = package.program.check_field::<Val>()?;
  let args = program.field().decode(&invocation.args)?;
  let hints = if invocation.entry.starts_with("IxVM::") {
    ixvm::prepare_streams(&program, &invocation.streams)?
  } else {
    stark_verifier::prepare(&program, &invocation.streams)?
  };
  let prepare = start.elapsed().as_secs_f64();
  let start = Instant::now();
  let plan = TracePlan::new(&program, package.trace)?;
  let backend = Backend::for_batch(&plan, Parameters::default())?;
  let setup = start.elapsed().as_secs_f64();
  let mut times = vec![];
  let mut circuits = vec![];
  let mut proof_report = serde_json::Value::Null;
  let mut function_rows = vec![];
  let mut cached_record = None;
  let mut initial_execute = None;
  let iterations = if counts_only { 1 } else { samples + 2 };
  for sample in 0..iterations {
    let (record, execute) = if let Some(record) = cached_record.take() {
      (record, None)
    } else {
      let start = Instant::now();
      let record = hints.execute(&invocation.entry, args.clone())?;
      let execute = start.elapsed().as_secs_f64();
      initial_execute.get_or_insert(execute);
      (record, Some(execute))
    };
    if counts_only {
      let mut counts = vec![0_usize; functions.len()];
      for key in record.queries.keys() {
        if let Some(count) = counts.get_mut(key.function) {
          *count += 1;
        }
      }
      function_rows = functions.iter().enumerate().map(|(i, (name, chip))| {
        json!({"name": name, "chip": chip, "rows": counts[i]})
      }).collect();
      break;
    }
    let start = Instant::now();
    let witness = backend.generate(&record, &invocation.entry, &args)?;
    let trace = start.elapsed().as_secs_f64();
    if sample >= 2 {
      times.push(
        json!({"execute_seconds":execute,"trace_with_lookups_seconds":trace}),
      );
    }
    if sample == samples + 1 {
      for (i, (shape, matrix)) in
        backend.statistics().iter().zip(&witness.traces).enumerate()
      {
        let mut row = serde_json::to_value(shape)?;
        row["index"] = json!(i);
        row["height"] = json!(matrix.height());
        row["cells"] = json!(matrix.values.len());
        row["fft_cost"] = json!(ix_bench::fft_cost(
          shape.stage1_width,
          shape.stage2_width,
          shape.quotient_degree,
          matrix.height(),
          1
        ));
        circuits.push(row);
      }
    }
    drop(witness);
    if sample == samples + 1 && cli.iter().any(|a| a == "--prove") {
      let start = Instant::now();
      let traces =
        backend.generate_stage_1(&record, &invocation.entry, &args)?;
      let output = record.output.clone();
      drop(record);
      let proof = backend.prove_batch_stage_1(
        &invocation.entry,
        &args,
        &output,
        traces,
        1 << 30,
        Retention::Retain,
      )?;
      let seconds = start.elapsed().as_secs_f64();
      proof_report = json!({"prove_including_trace_seconds":seconds,"bytes":proof.to_bytes()?.len(),"verified":true});
      if cli.iter().any(|a| a == "--save-proof") {
        let directory = std::path::PathBuf::from(format!("{}.inner", cli[3]));
        std::fs::create_dir_all(&directory)?;
        let key = backend.verifying_key_bytes()?;
        let claim = backend.claim(&invocation.entry, &args, &output)?;
        let claims = stark_verifier::claims_bytes(&[claim]);
        let bytes = proof.to_bytes()?;
        std::fs::write(directory.join("key.bin"), &key)?;
        std::fs::write(directory.join("claims.bin"), &claims)?;
        std::fs::write(directory.join("proof.bin"), &bytes)?;
        std::fs::write(
          directory.join("input.json"),
          serde_json::to_vec(&stark_verifier::invocation(
            &key, &claims, &bytes,
          ))?,
        )?;
      }
    } else if reuse_execution {
      cached_record = Some(record);
    }
  }
  let report = json!({"backend":"new-bytecode","thp_disabled":thp_disabled,"prepare_seconds":prepare,"setup_seconds":setup,"reused_execution":reuse_execution,"initial_execute_seconds":initial_execute,"samples":times,"circuits":circuits,"function_rows":function_rows,"proof":proof_report});
  std::fs::write(&cli[3], serde_json::to_vec_pretty(&report)?)?;
  println!("Wrote {}", cli[3]);
  Ok(())
}
