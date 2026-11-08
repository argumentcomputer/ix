//! Bytecode benchmark of an exported Aiur artifact: execution, trace and
//! optional proving timings, and every circuit's shape and FFT cost.
use aiur::{
  artifact::{Package, decode_groups},
  field::FieldBackend,
  library::io::Invocation,
  trace::{
    TracePlan,
    stark::{Backend, Parameters},
  },
};
use multi_stark::{batch::Retention, p3_matrix::Matrix, types::Val};
use serde_json::json;
use std::{error::Error, time::Instant};

fn main() -> Result<(), Box<dyn Error>> {
  let thp_disabled = configure_benchmark_memory()?;
  let cli: Vec<_> = std::env::args().collect();
  if cli.len() < 5 {
    return Err(
      "usage: compare PACKAGE INPUT OUTPUT SAMPLES [--ungrouped] [--prove] [--counts-only] [--groups FILE] [--parameters LOG_BLOWUP,QUERIES,COMMIT_POW,QUERY_POW [--below-floor]]"
        .into(),
    );
  }
  let (package, digest) = Package::load(cli[1].as_ref())?;
  eprintln!("artifact {}: blake3 {digest}", cli[1]);
  let (program, mut trace) = package.traced()?;
  let invocation = Invocation::load(cli[2].as_ref())?;
  let samples: usize = cli[4].parse()?;
  if samples == 0 {
    return Err("zero benchmark samples".into());
  }
  if cli.iter().any(|a| a == "--ungrouped") {
    trace.groups.clear();
  }
  if let Some(at) = cli.iter().position(|a| a == "--groups") {
    let path = cli.get(at + 1).ok_or("missing groups path")?;
    trace.groups = decode_groups(&std::fs::read(path)?)?;
  }
  let counts_only = cli.iter().any(|a| a == "--counts-only");
  let reuse_execution =
    std::env::var("IX_BENCH_REUSE_EXECUTION").is_ok_and(|v| v == "1");
  let functions: Vec<_> = program
    .functions
    .iter()
    .map(|f| {
      let plan = trace
        .functions
        .iter()
        .find(|p| p.name == f.name)
        .ok_or("missing function plan")?;
      Ok((f.name.clone(), plan.chip.clone()))
    })
    .collect::<Result<_, &str>>()?;
  let start = Instant::now();
  let mut program = program.check_field::<Val>()?;
  program.track_depth(&trace)?;
  let args = program.field().decode(&invocation.args)?;
  let hints = if invocation.entry.starts_with("IxVM::") {
    ixvm::prepare_streams(&program, &invocation.streams)?
  } else {
    stark_verifier::prepare(&program, &invocation.streams)?
  };
  let prepare = start.elapsed().as_secs_f64();
  let start = Instant::now();
  let plan = TracePlan::new(&program, trace)?;
  let parameters = match cli.iter().position(|a| a == "--parameters") {
    None => Parameters::default(),
    Some(at) => {
      let values: Vec<usize> = cli
        .get(at + 1)
        .ok_or("missing parameters")?
        .split(',')
        .map(str::parse)
        .collect::<Result<_, _>>()?;
      let [log_blowup, num_queries, commit_pow, query_pow] = values[..] else {
        return Err("expected four comma-separated parameters".into());
      };
      Parameters {
        log_blowup,
        num_queries,
        commit_proof_of_work_bits: commit_pow,
        query_proof_of_work_bits: query_pow,
      }
    },
  };
  // Below-floor parameters only measure the cost of weaker settings.
  let backend = if cli.iter().any(|a| a == "--below-floor") {
    Backend::for_batch_below_floor(&plan, parameters)?
  } else {
    Backend::for_batch(&plan, parameters)?
  };
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
        row["fft_cost"] = json!(fft_cost(
          shape.stage1_width,
          shape.stage2_width,
          shape.quotient_degree,
          matrix.height(),
          parameters.log_blowup
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
      let start = Instant::now();
      backend.verify_batch(&invocation.entry, &args, &output, &proof)?;
      let verify = start.elapsed().as_secs_f64();
      proof_report = json!({"prove_including_trace_seconds":seconds,"verify_seconds":verify,"bytes":proof.to_bytes()?.len(),"shards":proof.proofs.len(),"verified":true});
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
        stark_verifier::invocation(&key, &claims, &bytes)
          .store(&directory.join("input.ixi"))?;
      }
    } else if reuse_execution {
      cached_record = Some(record);
    }
  }
  let report = json!({"backend":"new-bytecode","parameters":parameters,"thp_disabled":thp_disabled,"prepare_seconds":prepare,"setup_seconds":setup,"reused_execution":reuse_execution,"initial_execute_seconds":initial_execute,"samples":times,"circuits":circuits,"function_rows":function_rows,"proof":proof_report});
  std::fs::write(&cli[3], serde_json::to_vec_pretty(&report)?)?;
  println!("Wrote {}", cli[3]);
  Ok(())
}

/// The Goldilocks FFT model of the retired `Aiur.Statistics.fftCost`: two
/// extension limbs, inverse/forward trace transforms, and quotient
/// transforms. This is a work estimate, not elapsed time; height is already
/// padded.
#[allow(clippy::cast_precision_loss)] // Approximate work, not an exact cell count.
fn fft_cost(
  stage1: usize,
  stage2: usize,
  quotient_degree: usize,
  height: usize,
  log_blowup: usize,
) -> f64 {
  let transform = |n: usize| {
    if n == 0 { 0.0 } else { n as f64 * f64::from(n.max(2).ilog2()) }
  };
  let blowup = 1usize << log_blowup;
  (blowup + 1) as f64 * (stage1 + stage2) as f64 * transform(height)
    + 2.0 * transform(quotient_degree * height)
    + (2 * quotient_degree) as f64 * transform(blowup * height)
}

/// Optional process-local control for comparing allocation-heavy small runs.
/// Query arenas may request huge pages; faulting a 2 MiB page for a tiny
/// function can dominate execution. Never changes the machine's THP policy.
fn configure_benchmark_memory() -> Result<bool, String> {
  let disable = std::env::var("IX_BENCH_NO_THP").as_deref() == Ok("1");
  if disable {
    #[cfg(target_os = "linux")]
    // SAFETY: this prctl changes only the calling process's huge-page policy.
    if unsafe { libc::prctl(libc::PR_SET_THP_DISABLE, 1, 0, 0, 0) } != 0 {
      return Err(std::io::Error::last_os_error().to_string());
    }
    #[cfg(not(target_os = "linux"))]
    return Err("IX_BENCH_NO_THP requires Linux".into());
  }
  Ok(disable)
}
