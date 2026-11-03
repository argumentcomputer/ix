//! `stark-verifier-native compare PACKAGE INPUT [RUNS]`: execute one
//! recursive invocation with the interpreter and with the generated kernel,
//! require identical records, and report the median time of each.
//!
//! `stark-verifier-native prove PACKAGE INPUT`, with a package exported with
//! its circuits (`stark-export export-trace`), also proves both records under
//! one plan and requires identical proof bytes.
//!
//! `stark-verifier-native advice PACKAGE INPUT` binds the invocation through
//! the reference field-element arenas and through compact advice, requires
//! identical records from the interpreter and the generated kernel, and
//! reports preparation times and retained bytes.
//!
//! `stark-verifier-native fixture DIR LOG_ROWS WIDTH QUERIES` writes a
//! natively verified proof of a synthetic one-circuit system of the given
//! size, and its recursive invocation, as workloads for `compare`.
use aiur::field::FieldBackend;
use aiur::native::Kernel;
use aiur::native::record_diff;
use multi_stark::types::Val;
use stark_verifier_native::{Aggregation, Verifier};
use std::{error::Error, time::Instant};

#[derive(serde::Deserialize)]
struct Package {
  program: aiur::Program,
}

fn median(mut samples: Vec<f64>) -> f64 {
  samples.sort_by(f64::total_cmp);
  samples[samples.len() / 2]
}

fn main() -> Result<(), Box<dyn Error>> {
  let cli: Vec<String> = std::env::args().collect();
  if cli.get(1).map(String::as_str) == Some("fixture") && cli.len() == 6 {
    return fixture(
      std::path::Path::new(&cli[2]),
      cli[3].parse()?,
      cli[4].parse()?,
      cli[5].parse()?,
    );
  }
  if cli.get(1).map(String::as_str) == Some("prove") && cli.len() == 4 {
    return prove(&cli[2], &cli[3]);
  }
  if cli.get(1).map(String::as_str) == Some("advice") && cli.len() == 4 {
    return advice(&cli[2], &cli[3]);
  }
  if cli.get(1).map(String::as_str) != Some("compare") || cli.len() < 4 {
    return Err(
      "usage: stark-verifier-native compare PACKAGE INPUT [RUNS] | \
       advice PACKAGE INPUT | fixture DIR LOG_ROWS WIDTH QUERIES"
        .into(),
    );
  }
  let runs: usize = cli.get(4).map_or(Ok(3), |s| s.parse())?;
  let package: Package = aiur::decode_artifact(&std::fs::read(&cli[2])?)?;
  let program = package.program.check_field::<Val>()?;
  let invocation: stark_verifier::Invocation =
    serde_json::from_slice(&std::fs::read(&cli[3])?)?;
  let args = program.field().decode(&invocation.args)?;
  let hints = stark_verifier::prepare(&program, &invocation.streams)?;
  let run = if invocation.entry == "MultiStark::ix_aggr" {
    compare::<Aggregation>
  } else {
    compare::<Verifier>
  };
  let (reference, interpreted, generated) =
    run(&hints, &invocation.entry, &args, runs)?;
  let (queries, cells, instructions, table_calls, function_calls) = reference;
  let (i, n) = (median(interpreted), median(generated));
  println!(
    "records identical over {runs} runs: {queries} queries, {cells} ROM cells, \
     {instructions} instructions, {function_calls} function calls, {table_calls} table calls"
  );
  println!("interpreter {i:.4}s, native {n:.4}s, speedup {:.2}x", i / n);
  Ok(())
}

type Hints<'a> = aiur::hints::PreparedHints<'a, aiur::field::NativeField<Val>>;
type Timings = ((usize, usize, u64, u64, u64), Vec<f64>, Vec<f64>);

fn compare<K: Kernel>(
  hints: &Hints<'_>,
  entry: &str,
  args: &[Val],
  runs: usize,
) -> Result<Timings, Box<dyn Error>> {
  let native = hints.bind_native::<K>()?;
  let mut interpreted = vec![];
  let mut generated = vec![];
  let mut reference = None;
  for _ in 0..runs {
    let start = Instant::now();
    let a = hints.execute(entry, args.to_vec())?;
    interpreted.push(start.elapsed().as_secs_f64());
    let start = Instant::now();
    let b = native.execute(entry, args.to_vec())?;
    generated.push(start.elapsed().as_secs_f64());
    record_diff(&a, &b)?;
    let functions = hints.program().program().functions.len();
    let (mut table_calls, mut function_calls) = (0u64, 0u64);
    for (key, value) in a.queries.iter() {
      if key.function >= functions {
        table_calls += value.multiplicity;
      } else {
        function_calls += value.multiplicity;
      }
    }
    reference.get_or_insert((
      a.queries.len(),
      a.memory.len(),
      a.instructions,
      table_calls,
      function_calls,
    ));
  }
  Ok((reference.ok_or("no runs")?, interpreted, generated))
}

/// Columns are `WIDTH` pairs (x, x²) and a selector; the first row's first
/// pair is pulled as the single claim.
fn fixture(
  dir: &std::path::Path,
  log_rows: usize,
  width: usize,
  queries: usize,
) -> Result<(), Box<dyn Error>> {
  use multi_stark::{
    batch::ShardInput,
    expr::Expr,
    lookup::Lookup,
    p3_field::PrimeCharacteristicRing,
    p3_matrix::dense::RowMajorMatrix,
    system::{CircuitInputs, System, SystemWitness},
    types::{CommitmentParameters, FriParameters, GoldilocksBlake3Config},
  };
  std::fs::create_dir_all(dir)?;
  let cp = CommitmentParameters { log_blowup: 1, cap_height: 0 };
  let fp = FriParameters {
    log_final_poly_len: 0,
    max_log_arity: 1,
    num_queries: queries,
    commit_proof_of_work_bits: 0,
    query_proof_of_work_bits: 0,
  };
  let columns = 2 * width + 1;
  let col = |i: usize| Expr::main(u32::try_from(i).expect("column index"));
  let selector = col(2 * width);
  let one = Expr::constant(Val::ONE);
  let constraints =
    (0..width).map(|i| col(2 * i) * col(2 * i) - col(2 * i + 1)).collect();
  let inputs = vec![CircuitInputs {
    main_width: columns,
    constraints,
    lookups: vec![Lookup::pull(
      selector,
      vec![one, Expr::constant(Val::ZERO), col(0), col(1)],
    )],
    ..Default::default()
  }];
  let (system, pk) = System::new(GoldilocksBlake3Config::new(cp, fp), inputs);
  let rows = 1usize << log_rows;
  let mut values = Vec::with_capacity(rows * columns);
  for row in 0..rows {
    for i in 0..width {
      let x = Val::from_u64((row * width + i + 3) as u64);
      values.extend([x, x * x]);
    }
    values.push(if row == 0 { Val::ONE } else { Val::ZERO });
  }
  let claims = vec![vec![Val::ONE, Val::ZERO, values[0], values[1]]];
  let witness = SystemWitness::from_stage_1(
    vec![RowMajorMatrix::new(values, columns)],
    &system,
  );
  let proof = system.prove_batch(
    &pk,
    vec![ShardInput { claims: claims.clone(), witness }],
    vec![],
  );
  system
    .verify_batch(&proof)
    .map_err(|e| format!("fixture failed native verification: {e:?}"))?;
  let key = stark_key::to_bytes(&system, cp, fp);
  let claims = stark_verifier::claims_bytes(&claims);
  let proof = proof.to_bytes()?;
  std::fs::write(
    dir.join("input.json"),
    serde_json::to_vec(&stark_verifier::invocation(&key, &claims, &proof))?,
  )?;
  println!("wrote a {}-byte proof to {}", proof.len(), dir.display());
  Ok(())
}

#[derive(serde::Deserialize)]
struct TracePackage {
  program: aiur::Program,
  trace: aiur::trace::TraceArtifact,
}

fn prove(package: &str, input: &str) -> Result<(), Box<dyn Error>> {
  use aiur::trace::{
    TracePlan,
    stark::{Backend, Parameters, planning::Options},
  };
  let package: TracePackage = aiur::decode_artifact(&std::fs::read(package)?)?;
  let program = package.program.check_field::<Val>()?;
  let plan = TracePlan::new(&program, package.trace)?;
  let backend =
    Backend::for_batch_on_device(&plan, Parameters::default(), None)?;
  let invocation: stark_verifier::Invocation =
    serde_json::from_slice(&std::fs::read(input)?)?;
  let entry = invocation.entry.as_str();
  let args = program.field().decode(&invocation.args)?;
  let hints = stark_verifier::prepare(&program, &invocation.streams)?;
  let interpreted = hints.execute(entry, args.clone())?;
  let generated = if entry == "MultiStark::ix_aggr" {
    hints.bind_native::<Aggregation>()?.execute(entry, args.clone())?
  } else {
    hints.bind_native::<Verifier>()?.execute(entry, args.clone())?
  };
  record_diff(&interpreted, &generated)?;
  // One plan for both: it depends on resident memory as well as the record.
  let batch = backend.plan_batch(&interpreted, &Options::default())?;
  if !batch.fits {
    return Err("the proving plan does not fit the default budget".into());
  }
  let mut proofs = vec![];
  for record in [&interpreted, &generated] {
    let start = Instant::now();
    let layout = batch
      .layout
      .as_ref()
      .ok_or("the proving plan has no incremental layout")?;
    let proof = backend.prove_incremental(
      record,
      entry,
      &args,
      &[],
      layout,
      batch.retention(),
    )?;
    backend.verify_batch(entry, &args, &[], &proof)?;
    proofs.push((proof.to_bytes()?, start.elapsed().as_secs_f64()));
  }
  if proofs[0].0 != proofs[1].0 {
    return Err("proofs from the two records differ".into());
  }
  println!(
    "identical verified proofs ({} bytes, {} trace shards): {:.2}s and {:.2}s",
    proofs[0].0.len(),
    batch.shards,
    proofs[0].1,
    proofs[1].1
  );
  Ok(())
}

fn advice(package: &str, input: &str) -> Result<(), Box<dyn Error>> {
  use aiur::{library::advice::Advice, native::outcome_diff};
  let package: Package = aiur::decode_artifact(&std::fs::read(package)?)?;
  let program = package.program.check_field::<Val>()?;
  let start = Instant::now();
  let invocation: stark_verifier::Invocation =
    serde_json::from_slice(&std::fs::read(input)?)?;
  let parse = start.elapsed().as_secs_f64();
  let (entry, streams) = (&invocation.entry, &invocation.streams);
  let field = program.field();
  let args = field.decode(&invocation.args)?;
  let values: usize = streams.0.iter().map(|s| s.values.len()).sum();

  let start = Instant::now();
  let arenas = streams.prepare(field)?;
  let arena_time = start.elapsed().as_secs_f64();
  let arena_bytes = arenas.retained_bytes();
  drop(arenas);
  let start = Instant::now();
  let reference = stark_verifier::prepare_reference(&program, streams)?;
  let reference_time = start.elapsed().as_secs_f64();

  let start = Instant::now();
  let advice = Advice::from_streams(field, streams)?;
  let advice_time = start.elapsed().as_secs_f64();
  let compact = stark_verifier::prepare_advice(&program, &advice)?;
  let compact_time = start.elapsed().as_secs_f64();
  let bytes = advice.retained_bytes();
  drop(advice);
  println!(
    "{} streams, {values} values; parsing took {parse:.3}s",
    streams.0.len()
  );
  println!(
    "reference: arenas {arena_time:.3}s, full preparation \
     {reference_time:.3}s, {arena_bytes} payload bytes"
  );
  println!(
    "compact: advice {advice_time:.3}s, full preparation {compact_time:.3}s, \
     {} payload bytes, {} metadata bytes",
    bytes.payload, bytes.metadata
  );

  let expected = reference.execute(entry, args.clone());
  drop(reference);
  outcome_diff(&expected, &compact.execute(entry, args.clone()))
    .map_err(|e| format!("compact interpreter: {e}"))?;
  let native = if entry == "MultiStark::ix_aggr" {
    compact.bind_native::<Aggregation>()?.execute(entry, args)
  } else {
    compact.bind_native::<Verifier>()?.execute(entry, args)
  };
  outcome_diff(&expected, &native)
    .map_err(|e| format!("compact native: {e}"))?;
  match &expected {
    Ok(record) => println!(
      "identical records: {} queries, {} ROM cells, {} instructions",
      record.queries.len(),
      record.memory.len(),
      record.instructions
    ),
    Err(e) => println!("identical failures: {e}"),
  }
  Ok(())
}
