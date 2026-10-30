//! Bytecode-only IxVM with value hints and constrained recursive calls.
use aiur::field::FieldBackend;
use aiur::{
  Program,
  hints::HintEntry,
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

use ixvm as ixvm_hints;

#[derive(Deserialize)]
struct Package {
  program: Program,
  trace: TraceArtifact,
  hints: Vec<HintEntry>,
  address: Vec<u64>,
}
fn main() -> Result<(), Box<dyn Error>> {
  let cli: Vec<_> = std::env::args().collect();
  if cli.len() != 5 {
    return Err(
            "usage: ixvm_bench PACKAGE.json FIXTURE.json prove|execute|witness|functions SAMPLES"
                .into(),
        );
  }
  let mode = &cli[3];
  let samples: usize = cli[4].parse()?;
  if !["prove", "execute", "witness", "functions"].contains(&mode.as_str())
    || samples == 0
  {
    return Err("invalid mode or sample count".into());
  }
  let start = Instant::now();
  let package: Package = serde_json::from_slice(&std::fs::read(&cli[1])?)?;
  let fixture: serde_json::Value =
    serde_json::from_slice(&std::fs::read(&cli[2])?)?;
  let args: Vec<u64> = serde_json::from_value(fixture["address"].clone())?;
  assert_eq!(args, package.address);
  let program = package.program.check_field::<multi_stark::types::Val>()?;
  let args = program.field().decode(&args)?;
  let hints = ixvm_hints::prepare(&program, &package.hints)?;
  let function_chips: Vec<_> =
    package.trace.functions.iter().map(|f| f.chip.clone()).collect();
  let plan = TracePlan::new(&program, package.trace)?;
  let entry = &program.program().entries[0].name;
  let prepare_seconds = start.elapsed().as_secs_f64();
  let parameters = Parameters::default();
  let start = Instant::now();
  let backend = Backend::new(&plan, parameters)?;
  let setup_seconds = start.elapsed().as_secs_f64();
  let profiler = profile::Profiler::from_env()?;
  let mut times = vec![];
  if mode == "functions" {
    #[cfg(not(feature = "function-profile"))]
    return Err("functions mode requires --features function-profile".into());
    #[cfg(feature = "function-profile")]
    {
      use aiur::function_profile::FunctionProfiler;
      let baseline = hints.execute(entry, args.clone())?;
      let fingerprint = execution_fingerprint(&baseline);
      drop(baseline);
      let count = program.program().functions.len();
      let mut profiles = vec![];
      for sample in 0..samples + 2 {
        let mut profile = FunctionProfiler::new(count);
        let start = Instant::now();
        let record =
          hints.execute_profiled(entry, args.clone(), &mut profile)?;
        let seconds = start.elapsed().as_secs_f64();
        assert!(record.output.is_empty());
        assert!(profile.is_complete());
        if sample == 2 {
          assert_eq!(execution_fingerprint(&record), fingerprint);
        }
        let mut queries = vec![0; count];
        for key in record.queries.keys().filter(|k| k.function < count) {
          queries[key.function] += 1;
        }
        let functions: Vec<_> = profile
                    .functions
                    .iter()
                    .enumerate()
                    .map(|(id, t)| {
                        assert_eq!(t.calls - t.cache_hits, queries[id]);
                        json!({"id": id, "calls": t.calls, "cache_hits": t.cache_hits,
                        "queries": queries[id], "self_ns": t.self_ns,
                        "inclusive_ns": t.inclusive_ns, "cached_ns": t.cached_ns})
                    })
                    .collect();
        if sample >= 2 {
          #[cfg(feature = "function-profile-ops")]
          let operations = Some(&profile.operations);
          #[cfg(not(feature = "function-profile-ops"))]
          let operations: Option<()> = None;
          profiles.push(json!({"seconds": seconds, "functions": functions, "operations": operations}));
        }
      }
      let names: Vec<_> =
        program.program().functions.iter().map(|f| &f.name).collect();
      println!(
        "{}",
        json!({"engine": "new-aiur-bytecode", "mode": mode,
                "record_matches_unprofiled": true, "record_fingerprint": fingerprint,
                "names": names, "profiles": profiles})
      );
      return Ok(());
    }
  }
  if mode == "execute" {
    for sample in 0..samples + 2 {
      let guard = if sample >= 2 {
        profiler.as_ref().map(|p| p.start("execute", sample - 2)).transpose()?
      } else {
        None
      };
      let start = Instant::now();
      let record = hints.execute(entry, args.clone())?;
      let elapsed = start.elapsed().as_secs_f64();
      drop(guard);
      assert!(record.output.is_empty());
      if sample >= 2 {
        times.push(elapsed);
      }
    }
    println!(
      "{}",
      json!({"engine": "new-aiur-bytecode", "mode": mode, "seconds": times, "output": Vec::<u64>::new()})
    );
    return Ok(());
  }
  let start = Instant::now();
  let record = hints.execute(entry, args.clone())?;
  let execution_seconds = start.elapsed().as_secs_f64();
  assert!(record.output.is_empty());
  let mut checked_scope = std::collections::BTreeMap::new();
  for (name, module) in [
    ("run_check_transitive", "KernelClaim"),
    ("run_check", "KernelClaim"),
    ("load_verified_constant", "Ingress"),
    ("load_verified_blob", "Ingress"),
  ] {
    let mut addresses = std::collections::BTreeSet::new();
    let full_name = format!("{module}::{name}");
    let old_name = format!("IxVM::{name}");
    for (key, _) in record.queries.iter() {
      let callable = program.callable_name(key.function);
      if callable == Some(full_name.as_str())
        || callable == Some(old_name.as_str())
      {
        let cell = record
          .memory
          .get_by_width(32, program.field().to_u64(key.args[0]) as usize)
          .ok_or("missing address cell")?;
        assert_eq!(cell.cell.value.len(), 32);
        addresses.insert(
          cell
            .cell
            .value
            .iter()
            .map(|x| format!("{:02x}", program.field().to_u64(*x)))
            .collect::<String>(),
        );
      }
    }
    checked_scope.insert(name, addresses);
  }
  let mut counted = vec![
    (0usize, 0u64);
    program.program().functions.len()
      + program.program().maps.len()
  ];
  for (key, q) in record.queries.iter() {
    counted[key.function].0 += 1;
    counted[key.function].1 += q.multiplicity;
  }
  let mut function_counts = vec![];
  for (id, (queries, uses)) in counted.into_iter().enumerate() {
    function_counts.push(json!({"id": id, "name": program.callable_name(id), "queries": queries,
            "constrained_rows": queries, "uses": uses, "map": id >= program.program().functions.len()}));
  }
  let counts = json!({"queries": record.queries.len(), "function_queries": record.queries.keys().filter(|k| k.function < program.program().functions.len()).count(), "map_queries": record.queries.keys().filter(|k| k.function >= program.program().functions.len()).count(), "memory_queries": record.memory.len(), "instructions": record.instructions});
  let mut raw_rows = std::collections::HashMap::new();
  for key in record.queries.keys() {
    if let Some(chip) = function_chips.get(key.function) {
      *raw_rows.entry(chip.clone()).or_insert(0usize) += 1;
    }
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
      value["rows"] = json!(if s.preprocessed_height > 0 {
        s.preprocessed_height
      } else {
        raw_rows.get(s.name.as_str()).copied().unwrap_or(0)
      });
      value
    })
    .collect();
  let stage1_words: usize = witness.traces.iter().map(|t| t.values.len()).sum();
  // Compare before/after implementations outside all measured intervals.
  let record_fingerprint = execution_fingerprint(&record);
  let trace_fingerprint = {
    use std::hash::{Hash, Hasher};
    let mut hash = std::collections::hash_map::DefaultHasher::new();
    for trace in &witness.traces {
      trace.width.hash(&mut hash);
      trace.values.hash(&mut hash);
    }
    hash.finish()
  };
  drop(record);
  let start = Instant::now();
  let proof = backend.prove(entry, &args, &[], witness)?;
  let prove_seconds = start.elapsed().as_secs_f64();
  let bytes = proof.to_bytes()?;
  let proof = Proof::from_bytes(&bytes)?;
  let start = Instant::now();
  backend.verify(entry, &args, &[], &proof)?;
  let verify_seconds = start.elapsed().as_secs_f64();
  println!(
    "{}",
    json!({"engine": "new-aiur-bytecode", "mode": mode, "args": args, "output": Vec::<u64>::new(),
        "prepare_seconds": prepare_seconds, "setup_seconds": setup_seconds,
        "execution_seconds": execution_seconds, "witness_seconds": times[0], "seconds": times,
        "prove_seconds": prove_seconds, "verify_seconds": verify_seconds, "proof_bytes": bytes.len(),
        "counts": counts, "function_counts": function_counts, "checked_scope": checked_scope, "stage1_words": stage1_words, "circuits": circuits, "verified": true,
        "record_fingerprint": record_fingerprint, "trace_fingerprint": trace_fingerprint})
  );
  Ok(())
}

fn execution_fingerprint<B: FieldBackend>(record: &aiur::Execution<B>) -> u64 {
  use std::hash::{Hash, Hasher};
  let mut hash = std::collections::hash_map::DefaultHasher::new();
  for (input, output) in record.queries.iter() {
    input.function.hash(&mut hash);
    input.args.hash(&mut hash);
    output.output.hash(&mut hash);
    output.multiplicity.hash(&mut hash);
  }
  serde_json::to_vec(&record.memory).unwrap().hash(&mut hash);
  record.output.hash(&mut hash);
  record.instructions.hash(&mut hash);
  hash.finish()
}
