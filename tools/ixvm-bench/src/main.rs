//! Interpret the Lean-exported ixvm bytecode. CPU witness generation only.
use aiur::synthesis::{AiurProof, AiurSystem};
use multi_stark::{
  p3_field::PrimeField64,
  types::{CommitmentParameters, FriParameters},
};
use serde::Deserialize;
use serde_json::{Value, json};
use std::{
  collections::BTreeMap,
  error::Error,
  sync::{Arc, Mutex},
  time::Instant,
};
use tracing::{
  Subscriber,
  span::{Attributes, Id},
};
use tracing_subscriber::{
  Layer, layer::Context, prelude::*, registry::LookupSpan,
};
mod input;
mod profile;

type Timings = Arc<Mutex<BTreeMap<String, (usize, f64)>>>;
struct PhaseTimes(Timings);
impl<S: Subscriber + for<'a> LookupSpan<'a>> Layer<S> for PhaseTimes {
  fn on_new_span(&self, _: &Attributes<'_>, id: &Id, ctx: Context<'_, S>) {
    ctx.span(id).unwrap().extensions_mut().insert(Instant::now());
  }
  fn on_close(&self, id: Id, ctx: Context<'_, S>) {
    let span = ctx.span(&id).unwrap();
    let elapsed =
      span.extensions().get::<Instant>().unwrap().elapsed().as_secs_f64();
    let mut times = self.0.lock().unwrap();
    let item = times.entry(span.name().to_owned()).or_default();
    item.0 += 1;
    item.1 += elapsed;
  }
}

fn run() -> Result<(), Box<dyn Error>> {
  let cli: Vec<_> = std::env::args().collect();
  if cli.len() != 5 {
    return Err("usage: ix-ixvm-bench PACKAGE.json FIXTURE.json prove|execute|witness|functions SAMPLES".into());
  }
  let mode = &cli[3];
  let samples: usize = cli[4].parse()?;
  if !["prove", "execute", "witness", "validate", "functions"]
    .contains(&mode.as_str())
    || samples == 0
  {
    return Err("invalid mode or sample count".into());
  }
  // This flag would omit lookup payloads and make witness times incomparable.
  if std::env::var("AIUR_TRACE_ONLY_LOOKUPS").is_ok_and(|v| v == "1") {
    return Err("trace-only lookups are forbidden in this benchmark".into());
  }
  let spans = Timings::default();
  tracing_subscriber::registry()
    .with(PhaseTimes(spans.clone()).with_filter(
      tracing_subscriber::filter::filter_fn(|m| {
        matches!(
          m.name(),
          "aiur/witness"
            | "stark/stage1_commit"
            | "stark/stage2_commit"
            | "stark/lookup_construction"
            | "stark/quotient"
            | "stark/fri_open"
        )
      }),
    ))
    .init();
  let start = Instant::now();
  let wire = std::fs::read_to_string(&cli[1])?;
  let mut reader = serde_json::Deserializer::from_str(&wire);
  reader.disable_recursion_limit();
  let data = Value::deserialize(&mut reader)?;
  let fixture: Value = serde_json::from_slice(&std::fs::read(&cli[2])?)?;
  let program = input::program(&data);
  let entry = input::n(&data["entry"]);
  let args = input::gs(&fixture["address"]);
  let expected = vec![];
  let mut io = input::witness(&fixture);
  let prepare_seconds = start.elapsed().as_secs_f64();
  let start = Instant::now();
  let system = AiurSystem::build(
    program,
    CommitmentParameters { log_blowup: 1, cap_height: 0 },
    FriParameters {
      log_final_poly_len: 0,
      max_log_arity: 1,
      num_queries: 64,
      commit_proof_of_work_bits: 0,
      query_proof_of_work_bits: 0,
    },
  );
  let setup_seconds = start.elapsed().as_secs_f64();
  let profiler = profile::Profiler::from_env()?;
  if mode == "validate" {
    let mut cases = vec![];
    for entry_name in [
      "verify_transitive",
      "verify_constant",
      "verify_serde",
      "check_port_cases",
    ] {
      let entry = input::n(&data["entries"][entry_name]);
      let args =
        if entry_name == "check_port_cases" { vec![] } else { args.clone() };
      let result = system.toplevel().execute(entry, args, &mut io);
      cases.push(json!({"entry": entry_name, "accepted": result.is_ok(), "error": result.err().map(|e| e.to_string())}));
    }
    let entry = input::n(&data["entries"]["verify_constant"]);
    for kind in
      ["corrupted-bytes", "wrong-address", "invalid-proof", "missing-bytes"]
    {
      let mut fixture = fixture.clone();
      let target = fixture["constants"]
        .as_array()
        .unwrap()
        .iter()
        .position(|c| c["address"] == fixture["address"])
        .unwrap();
      match kind {
        "corrupted-bytes" => {
          fixture["constants"][target]["bytes"][0] = json!(
            fixture["constants"][target]["bytes"][0].as_u64().unwrap() ^ 1
          );
        },
        "wrong-address" => {
          fixture["address"][0] =
            json!(fixture["address"][0].as_u64().unwrap() ^ 1);
          fixture["constants"][target]["address"] = fixture["address"].clone();
        },
        "invalid-proof" => {
          fixture["address"] = fixture["invalidProof"]["address"].clone();
        },
        "missing-bytes" => {
          fixture["constants"][target]["bytes"].as_array_mut().unwrap().clear();
        },
        _ => unreachable!(),
      }
      let mut io = input::witness(&fixture);
      let result = system.toplevel().execute(
        entry,
        input::gs(&fixture["address"]),
        &mut io,
      );
      cases.push(json!({"negative": kind, "accepted": result.is_ok(), "error": result.err().map(|e| e.to_string())}));
    }
    let serde_entry = input::n(&data["entries"]["verify_serde"]);
    let mut serde_failures = vec![];
    for row in fixture["constants"].as_array().unwrap() {
      if let Err(error) = system.toplevel().execute(
        serde_entry,
        input::gs(&row["address"]),
        &mut io,
      ) {
        serde_failures
          .push(json!({"address": row["address"], "error": error.to_string()}));
      }
    }
    println!(
      "{}",
      json!({"cases": cases, "serde_cases": fixture["constants"].as_array().unwrap().len(), "serde_failures": serde_failures})
    );
    return Ok(());
  }
  let mut seconds = vec![];
  if mode == "functions" {
    #[cfg(not(feature = "function-profile"))]
    return Err("functions mode requires --features function-profile".into());
    #[cfg(feature = "function-profile")]
    {
      use aiur::function_profile::FunctionProfiler;
      let (baseline, output) =
        system.toplevel().execute(entry, args.clone(), &mut io)?;
      assert_eq!(output, expected);
      let fingerprint = execution_fingerprint(&baseline);
      drop(baseline);
      let mut profiles = vec![];
      for sample in 0..samples + 2 {
        let mut profile =
          FunctionProfiler::new(system.toplevel().functions.len());
        let start = Instant::now();
        let (record, output) = system.toplevel().execute_profiled(
          entry,
          args.clone(),
          &mut io,
          &mut profile,
        )?;
        let seconds = start.elapsed().as_secs_f64();
        assert_eq!(output, expected);
        assert!(profile.is_complete());
        if sample == 2 {
          assert_eq!(execution_fingerprint(&record), fingerprint);
        }
        let functions: Vec<_> = profile
          .functions
          .iter()
          .enumerate()
          .map(|(id, t)| {
            json!({"id": id, "calls": t.calls, "cache_hits": t.cache_hits,
            "queries": record.function_queries[id].len(), "self_ns": t.self_ns,
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
      println!(
        "{}",
        json!({"engine": "ix-bytecode", "mode": mode,
        "record_matches_unprofiled": true, "record_fingerprint": fingerprint,
        "names": data["names"], "profiles": profiles})
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
      let (record, output) =
        system.toplevel().execute(entry, args.clone(), &mut io)?;
      let elapsed = start.elapsed().as_secs_f64();
      drop(guard);
      assert_eq!(output, expected);
      if sample >= 2 {
        seconds.push(elapsed);
      }
      drop(record);
    }
    println!(
      "{}",
      json!({"engine": "ix-bytecode", "mode": mode, "seconds": seconds, "output": []})
    );
    return Ok(());
  }
  let start = Instant::now();
  let (record, output) =
    system.toplevel().execute(entry, args.clone(), &mut io)?;
  let execution_seconds = start.elapsed().as_secs_f64();
  assert_eq!(output, expected);
  let mut checked_scope = std::collections::BTreeMap::new();
  for name in [
    "run_check_transitive",
    "run_check",
    "load_verified_constant",
    "load_verified_blob",
  ] {
    let mut addresses = std::collections::BTreeSet::new();
    for (i, queries) in record.function_queries.iter().enumerate() {
      if data["names"][i].as_array().unwrap().iter().any(|n| n == name) {
        for (key, _) in queries.iter() {
          let address =
            key[0].as_canonical_u64() as usize - record.pointer_base;
          let (values, _) = record.memory_queries[&32]
            .get_index(address)
            .ok_or("missing address cell")?;
          addresses.insert(
            values
              .iter()
              .map(|x| format!("{:02x}", x.as_canonical_u64()))
              .collect::<String>(),
          );
        }
      }
    }
    checked_scope.insert(name, addresses);
  }
  let function_counts: Vec<_> = record.function_queries.iter().enumerate().map(|(i, q)| {
    let constrained = q.iter().filter(|(_, r)| r.multiplicity.as_canonical_u64() != 0).count();
    json!({"id": i, "names": data["names"][i], "queries": q.len(), "constrained_rows": constrained,
      "unconstrained_rows": q.len() - constrained,
      "uses": q.iter().map(|(_, r)| r.multiplicity.as_canonical_u64()).sum::<u64>()})
  }).collect();
  let counts = json!({"function_queries": record.function_queries.iter().map(|q| q.len()).sum::<usize>(), "memory_queries": record.memory_queries.values().map(|q| q.len()).sum::<usize>()});
  let plan = system.single_shard_plan(&record);
  if mode == "witness" {
    for sample in 0..samples + 2 {
      let guard = if sample >= 2 {
        profiler.as_ref().map(|p| p.start("witness", sample - 2)).transpose()?
      } else {
        None
      };
      let start = Instant::now();
      let plan = system.single_shard_plan(&record);
      let index = system.row_index(&record, &plan);
      let witness = system.shard_witness(&record, &io, &plan, &index, 0);
      let elapsed = start.elapsed().as_secs_f64();
      drop(guard);
      std::hint::black_box(&witness);
      if sample >= 2 {
        seconds.push(elapsed);
      }
    }
  }
  let mut names: Vec<_> = data["circuits"]
    .as_array()
    .unwrap()
    .iter()
    .map(|c| c["name"].as_str().unwrap().to_owned())
    .collect();
  names.extend(
    system.toplevel().memory_sizes.iter().map(|w| format!("memory_{w}")),
  );
  names.extend(["Bytes1".into(), "Bytes2".into()]);
  let circuits: Vec<_> = system.circuit_shapes().iter().zip(&plan.shards[0].rows).zip(names).map(|((s, rows), name)| {
        let height = if s.preprocessed_height > 0 { s.preprocessed_height } else if rows.is_empty() { 0 } else { rows.len().next_power_of_two() };
        json!({"name": name, "height": height, "rows": rows.len(), "stage1_width": s.main_width, "stage2_width": s.stage2_width,
            "preprocessed_width": s.preprocessed_width, "preprocessed_height": s.preprocessed_height, "quotient_degree": s.quotient_degree})
    }).collect();
  let stage1_words: usize = circuits
    .iter()
    .map(|c| input::n(&c["height"]) * input::n(&c["stage1_width"]))
    .sum();
  let start = Instant::now();
  let (claim, proof) =
    system.prove_from_execution(entry, &args, &io, record, &output);
  let witness_and_prove_seconds = start.elapsed().as_secs_f64();
  let spans = spans.lock().unwrap().clone();
  let (calls, witness_seconds) = spans["aiur/witness"];
  assert_eq!(calls, 1);
  let bytes = proof.to_bytes().map_err(|e| format!("{e:?}"))?;
  let proof = AiurProof::from_bytes(&bytes).map_err(|e| format!("{e:?}"))?;
  let start = Instant::now();
  system.verify(&claim, &proof).map_err(|e| format!("{e:?}"))?;
  let verify_seconds = start.elapsed().as_secs_f64();
  println!(
    "{}",
    json!({"engine": "ix-bytecode", "mode": mode, "args": fixture["address"], "output": output.iter().map(|x| x.as_canonical_u64()).collect::<Vec<_>>(),
        "prepare_seconds": prepare_seconds, "setup_seconds": setup_seconds, "execution_seconds": execution_seconds,
        "witness_seconds": witness_seconds, "seconds": seconds, "witness_and_prove_seconds": witness_and_prove_seconds,
        "prove_seconds": witness_and_prove_seconds - witness_seconds, "verify_seconds": verify_seconds,
        "proof_bytes": bytes.len(), "stage1_words": stage1_words, "counts": counts, "function_counts": function_counts, "checked_scope": checked_scope, "circuits": circuits, "spans": spans, "verified": true})
  );
  Ok(())
}

#[cfg(feature = "function-profile")]
// Compare all function/ROM keys, outputs and multiplicities. Gadget counters
// are not part of this fingerprint; profiling never modifies their operations.
fn execution_fingerprint(record: &aiur::execute::QueryRecord) -> u64 {
  use std::hash::{Hash, Hasher};
  let mut hash = std::collections::hash_map::DefaultHasher::new();
  let mut add_table = |table: &aiur::querymap::QueryMap| {
    table.len().hash(&mut hash);
    for (i, (key, query)) in table.iter().enumerate() {
      key
        .iter()
        .map(|v| v.as_canonical_u64())
        .collect::<Vec<_>>()
        .hash(&mut hash);
      table
        .output_at(i)
        .iter()
        .map(|v| v.as_canonical_u64())
        .collect::<Vec<_>>()
        .hash(&mut hash);
      query.multiplicity.as_canonical_u64().hash(&mut hash);
    }
  };
  for table in &record.function_queries {
    add_table(table);
  }
  for table in record.memory_queries.values() {
    add_table(table);
  }
  hash.finish()
}

fn main() -> Result<(), Box<dyn Error>> {
  stacker::grow(64 * 1024 * 1024, run)
}

#[cfg(all(test, feature = "function-profile"))]
#[test]
fn function_profile_preserves_nested_calls_and_memo_hits() {
  use aiur::{
    bytecode::{Block, Ctrl, Function, FunctionLayout, Op, Toplevel},
    execute::IOBuffer,
  };
  use multi_stark::p3_field::PrimeCharacteristicRing;
  let make = |body, entry| Function {
    body,
    entry,
    constrained: true,
    layout: FunctionLayout {
      input_size: 1,
      selectors: 1,
      auxiliaries: 3,
      lookups: 3,
    },
  };
  let top = Toplevel {
    functions: vec![
      make(
        Block {
          ops: vec![
            Op::Call(1, vec![0], 1, false),
            Op::Call(1, vec![0], 1, false),
          ],
          ctrl: Ctrl::Return(0, vec![2]),
        },
        true,
      ),
      make(
        Block {
          ops: vec![Op::Const(aiur::G::ONE), Op::Add(0, 1)],
          ctrl: Ctrl::Return(0, vec![2]),
        },
        false,
      ),
    ],
    memory_sizes: vec![],
    circuits: vec![],
  };
  let mut io = IOBuffer { data: Default::default(), map: Default::default() };
  let args = vec![aiur::G::from_u32(3)];
  let (normal, expected) = top.execute(0, args.clone(), &mut io).unwrap();
  let mut profile = aiur::function_profile::FunctionProfiler::new(2);
  let (measured, actual) =
    top.execute_profiled(0, args, &mut io, &mut profile).unwrap();
  assert_eq!(actual, expected);
  assert_eq!(actual, vec![aiur::G::from_u32(4)]);
  assert_eq!(execution_fingerprint(&normal), execution_fingerprint(&measured));
  assert!(profile.is_complete());
  let (root, child) = (&profile.functions[0], &profile.functions[1]);
  assert_eq!((root.calls, root.cache_hits), (1, 0));
  assert_eq!((child.calls, child.cache_hits), (2, 1));
  assert_eq!(root.inclusive_ns, root.self_ns + child.self_ns);
  assert_eq!(child.inclusive_ns, child.self_ns);
  assert!(child.cached_ns <= child.self_ns);
}
