//! `ixvm-native bind PACKAGE`: check that the generated kernel was emitted
//! from exactly this package's program and runtime ABI.
//!
//! `ixvm-native compare PACKAGE INPUT [RUNS]`: execute one IxVM invocation
//! (an Ixon `.ixi` invocation, as the prover host receives it) with the interpreter and with
//! the generated kernel, require identical records, and report both times.
//!
//! `ixvm-native prove PACKAGE INPUT`: also prove both records under one plan
//! and require identical, verified proofs.
//!
//! `ixvm-native advice PACKAGE INPUT`: bind the invocation through the
//! reference field-element arenas and through compact advice, require
//! identical records (or identical failures) from the interpreter and the
//! generated kernel, and report preparation times and retained bytes.
use aiur::field::FieldBackend;
use aiur::native::record_diff;
use multi_stark::types::Val;
use std::{error::Error, time::Instant};

/// Why `prove` refuses a program with depth circuits.
const DEPTH: &str = "generated executors do not record call heights, so their \
  records cannot be proven against a program with depth circuits";

fn median(mut samples: Vec<f64>) -> f64 {
  samples.sort_by(f64::total_cmp);
  samples[samples.len() / 2]
}

fn main() -> Result<(), Box<dyn Error>> {
  let cli: Vec<String> = std::env::args().collect();
  let usage = "usage: ixvm-native bind PACKAGE | compare|prove|advice PACKAGE INPUT \
     [RUNS]";
  let mode = cli.get(1).ok_or(usage)?.as_str();
  let (package, _) = aiur::artifact::Package::load(std::path::Path::new(
    cli.get(2).ok_or(usage)?,
  ))?;
  let program = package.program.check_field::<Val>()?;
  if mode == "bind" {
    program.prepare_hints(&[])?.bind_native::<formal_generated::Ixvm>()?;
    let plan = program.native_plan();
    println!(
      "bound: {} functions, {} dispatch entries, fingerprint {}",
      plan.functions.len(),
      plan.functions.iter().map(|f| f.entries.len()).sum::<usize>(),
      program.native_fingerprint()
    );
    return Ok(());
  }
  if mode == "prove" {
    let trace = package.trace.ok_or("package has no circuits")?;
    let mut program = program;
    program.track_depth(&trace)?;
    if program.records_depth() {
      return Err(DEPTH.into());
    }
    return prove(&program, trace, cli.get(3).ok_or(usage)?);
  }
  if mode == "advice" {
    return advice(&program, cli.get(3).ok_or(usage)?);
  }
  if mode != "compare" {
    return Err(usage.into());
  }
  let runs: usize = cli.get(4).map_or(Ok(3), |s| s.parse())?;
  let invocation: aiur::library::io::Invocation =
    aiur::library::io::Invocation::load(std::path::Path::new(
      cli.get(3).ok_or(usage)?,
    ))?;
  let args = program.field().decode(&invocation.args)?;
  let hints = ixvm::prepare_streams(&program, &invocation.streams)?;
  let start = Instant::now();
  hints.bind_native::<formal_generated::Ixvm>()?;
  let first_bind = start.elapsed().as_secs_f64();
  let start = Instant::now();
  let native = hints.bind_native::<formal_generated::Ixvm>()?;
  let bind = start.elapsed().as_secs_f64();
  let (mut interpreted, mut generated) = (vec![], vec![]);
  let mut summary = None;
  for _ in 0..runs {
    let start = Instant::now();
    let a = hints.execute(&invocation.entry, args.clone());
    interpreted.push(start.elapsed().as_secs_f64());
    let start = Instant::now();
    let b = native.execute(&invocation.entry, args.clone());
    generated.push(start.elapsed().as_secs_f64());
    summary = Some(match (a, b) {
      (Ok(a), Ok(b)) => {
        record_diff(&a, &b)?;
        let functions = program.program().functions.len();
        let (mut calls, mut words) = (0u64, 0u64);
        for (key, value) in a.queries.iter() {
          if key.function < functions {
            calls += value.multiplicity;
            words += value.multiplicity * key.args.len() as u64;
          }
        }
        let tenths = words * 10 / calls.max(1);
        format!(
          "records identical over {runs} runs: {} queries, {} ROM cells, \
           {} instructions, {calls} function calls of {}.{} argument words \
           on average, {} native stack bytes",
          a.queries.len(),
          a.memory.len(),
          a.instructions,
          tenths / 10,
          tenths % 10,
          b.native_stack_bytes
        )
      },
      (Err(a), Err(b)) => {
        if (&a.function, a.instruction, &a.message)
          != (&b.function, b.instruction, &b.message)
        {
          return Err(format!("different failures: {a} and {b}").into());
        }
        format!("both executors rejected the claim over {runs} runs: {a}")
      },
      (Ok(_), Err(e)) => return Err(format!("only native failed: {e}").into()),
      (Err(e), Ok(_)) => {
        return Err(format!("only the interpreter failed: {e}").into());
      },
    });
  }
  let (i, n) = (median(interpreted), median(generated));
  println!("{}", summary.ok_or("no runs")?);
  println!(
    "interpreter {i:.4}s, native {n:.4}s, speedup {:.2}x; binding took \
     {first_bind:.4}s, then {bind:.4}s once the fingerprint is known",
    i / n
  );
  Ok(())
}

fn prove(
  program: &aiur::bytecode::CheckedProgram<aiur::field::NativeField<Val>>,
  trace: aiur::trace::TraceArtifact,
  input: &str,
) -> Result<(), Box<dyn Error>> {
  use aiur::trace::{
    TracePlan,
    stark::{Backend, Parameters, planning::Options},
  };
  let plan = TracePlan::new(program, trace)?;
  let backend =
    Backend::for_batch_on_device(&plan, Parameters::default(), None)?;
  let invocation: aiur::library::io::Invocation =
    aiur::library::io::Invocation::load(std::path::Path::new(input))?;
  let entry = invocation.entry.as_str();
  let args = program.field().decode(&invocation.args)?;
  let hints = ixvm::prepare_streams(program, &invocation.streams)?;
  let interpreted = hints.execute(entry, args.clone())?;
  let generated = hints
    .bind_native::<formal_generated::Ixvm>()?
    .execute(entry, args.clone())?;
  record_diff(&interpreted, &generated)?;
  // One plan for both: it depends on resident memory as well as the record.
  let batch = backend.plan_batch(&interpreted, &Options::default())?;
  if !batch.fits {
    return Err("the proving plan does not fit the default budget".into());
  }
  let mut proofs = vec![];
  for record in [&interpreted, &generated] {
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
    proofs.push(proof.to_bytes()?);
  }
  if proofs[0] != proofs[1] {
    return Err("proofs from the two records differ".into());
  }
  println!(
    "identical verified proofs ({} bytes, {} trace shards)",
    proofs[0].len(),
    batch.shards
  );
  Ok(())
}

type Program = aiur::bytecode::CheckedProgram<aiur::field::NativeField<Val>>;

fn advice(program: &Program, input: &str) -> Result<(), Box<dyn Error>> {
  use aiur::{library::advice::Advice, native::outcome_diff};
  let start = Instant::now();
  let invocation: aiur::library::io::Invocation =
    aiur::library::io::Invocation::load(std::path::Path::new(input))?;
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
  let reference = ixvm::prepare_streams_reference(program, streams)?;
  let reference_time = start.elapsed().as_secs_f64();

  let start = Instant::now();
  let advice = Advice::from_streams(field, streams)?;
  let advice_time = start.elapsed().as_secs_f64();
  let compact = ixvm::prepare_advice(program, &advice)?;
  let compact_time = start.elapsed().as_secs_f64();
  let bytes = advice.retained_bytes();
  let byte_channels = (0..256).filter(|&c| advice.is_byte_channel(c)).count();
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
     {} payload bytes ({byte_channels} byte channels incl. unused), {} \
     metadata bytes",
    bytes.payload, bytes.metadata
  );

  let start = Instant::now();
  let expected = reference.execute(entry, args.clone());
  let interpreted = start.elapsed().as_secs_f64();
  drop(reference);
  let outcome = match &expected {
    Ok(record) => format!(
      "identical records: {} queries, {} ROM cells, {} instructions",
      record.queries.len(),
      record.memory.len(),
      record.instructions
    ),
    Err(e) => format!("identical failures: {e}"),
  };
  let start = Instant::now();
  outcome_diff(&expected, &compact.execute(entry, args.clone()))
    .map_err(|e| format!("compact interpreter: {e}"))?;
  let compact_interpreted = start.elapsed().as_secs_f64();
  let native = compact.bind_native::<formal_generated::Ixvm>()?;
  let start = Instant::now();
  outcome_diff(&expected, &native.execute(entry, args))
    .map_err(|e| format!("compact native: {e}"))?;
  let compact_native = start.elapsed().as_secs_f64();
  println!("{outcome}");
  println!(
    "reference interpreter {interpreted:.3}s; compact interpreter \
     {compact_interpreted:.3}s, native {compact_native:.3}s (each including \
     its comparison)"
  );
  Ok(())
}
