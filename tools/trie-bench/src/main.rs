//! Interpret the Lean-exported trie bytecode. CPU witness generation only.
use aiur::{
  execute::IOBuffer,
  synthesis::{AiurProof, AiurSystem},
};
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
    return Err("usage: ix-trie-bench PACKAGE.json FIXTURE.json prove|execute|witness SAMPLES".into());
  }
  let mode = &cli[3];
  let samples: usize = cli[4].parse()?;
  if !["prove", "execute", "witness"].contains(&mode.as_str()) || samples == 0 {
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
  let args = input::gs(&fixture["args"]);
  let expected = input::gs(&fixture["expected"]);
  let mut io = IOBuffer { map: Default::default(), data: Default::default() };
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
  let mut seconds = vec![];
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
      json!({"engine": "ix-bytecode", "mode": mode, "seconds": seconds, "output": fixture["expected"]})
    );
    return Ok(());
  }
  let start = Instant::now();
  let (record, output) =
    system.toplevel().execute(entry, args.clone(), &mut io)?;
  let execution_seconds = start.elapsed().as_secs_f64();
  assert_eq!(output, expected);
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
    json!({"engine": "ix-bytecode", "mode": mode, "args": fixture["args"], "output": output.iter().map(|x| x.as_canonical_u64()).collect::<Vec<_>>(),
        "prepare_seconds": prepare_seconds, "setup_seconds": setup_seconds, "execution_seconds": execution_seconds,
        "witness_seconds": witness_seconds, "seconds": seconds, "witness_and_prove_seconds": witness_and_prove_seconds,
        "prove_seconds": witness_and_prove_seconds - witness_seconds, "verify_seconds": verify_seconds,
        "proof_bytes": bytes.len(), "stage1_words": stage1_words, "counts": counts, "circuits": circuits, "spans": spans, "verified": true})
  );
  Ok(())
}

fn main() -> Result<(), Box<dyn Error>> {
  stacker::grow(64 * 1024 * 1024, run)
}
