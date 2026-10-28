//! Reproducible legacy bytecode measurements, excluding Lean marshalling,
//! compilation, IO construction, and system setup from execution timings.
use super::{
  lean_unbox_nat_as_usize, protocol::ffi_catch_unwind_except,
  toplevel::decode_toplevel,
};
use crate::lean::LeanAiurToplevel;
use aiur::{
  G,
  execute::{IOBuffer, IOKeyInfo},
  synthesis::AiurSystem,
};
use lean_ffi::object::{
  LeanBorrowed, LeanByteArray, LeanExcept, LeanNat, LeanOwned, LeanString,
};
use multi_stark::{
  p3_field::{PrimeCharacteristicRing, PrimeField64},
  p3_matrix::Matrix,
  types::{CommitmentParameters, FriParameters},
};
use serde_json::{Value, json};
use std::time::Instant;

fn words(value: &Value) -> Result<Vec<G>, String> {
  value
    .as_array()
    .ok_or("expected field array")?
    .iter()
    .map(|x| {
      let n =
        x.as_u64().filter(|&x| x < G::ORDER_U64).ok_or("invalid field")?;
      Ok(G::from_u64(n))
    })
    .collect()
}

fn buffer(value: &Value) -> Result<IOBuffer, String> {
  let mut io = IOBuffer { data: Default::default(), map: Default::default() };
  for stream in value.as_array().ok_or("expected streams")? {
    let channel =
      G::from_u64(stream["channel"].as_u64().ok_or("missing channel")?);
    let key = words(&stream["key"])?;
    let values = words(&stream["values"])?;
    let arena = io.data.entry(channel).or_default();
    let info = IOKeyInfo { idx: arena.len(), len: values.len() };
    arena.extend(values);
    if io.map.insert((channel, key), info).is_some() {
      return Err("duplicate stream".into());
    }
  }
  Ok(io)
}

#[unsafe(no_mangle)]
extern "C" fn rs_aiur_benchmark(
  top: LeanAiurToplevel<LeanBorrowed<'_>>,
  function: LeanNat<LeanBorrowed<'_>>,
  input: LeanByteArray<LeanBorrowed<'_>>,
  samples: LeanNat<LeanBorrowed<'_>>,
  prove: bool,
) -> LeanExcept<LeanOwned> {
  ffi_catch_unwind_except("legacy benchmark", || {
    let run = || -> Result<Value, String> {
      let thp_disabled = ix_bench::configure_benchmark_memory()?;
      let reuse_execution =
        std::env::var("IX_BENCH_REUSE_EXECUTION").is_ok_and(|v| v == "1");
      let input: Value =
        serde_json::from_slice(input.as_bytes()).map_err(|e| e.to_string())?;
      let args = words(&input["args"])?;
      let function = lean_unbox_nat_as_usize(function.inner());
      let samples = lean_unbox_nat_as_usize(samples.inner());
      if samples == 0 {
        return Err("zero benchmark samples".into());
      }
      let top = decode_toplevel(&top);
      let start = Instant::now();
      let system = AiurSystem::build(
        top,
        CommitmentParameters { log_blowup: 1, cap_height: 0 },
        FriParameters {
          log_final_poly_len: 0,
          max_log_arity: 1,
          num_queries: 64,
          commit_proof_of_work_bits: 0,
          query_proof_of_work_bits: 0,
        },
      );
      let setup = start.elapsed().as_secs_f64();
      let mut times = vec![];
      let mut circuits = vec![];
      let mut proof_report = Value::Null;
      let mut cached_execution = None;
      let mut initial_execute = None;
      for sample in 0..samples + 2 {
        let (record, output, io, execute) =
          if let Some((record, output, io)) = cached_execution.take() {
            (record, output, io, None)
          } else {
            let mut io = buffer(&input["streams"])?;
            let start = Instant::now();
            let (record, output) = system
              .toplevel()
              .execute(function, args.clone(), &mut io)
              .map_err(|e| e.to_string())?;
            let execute = start.elapsed().as_secs_f64();
            initial_execute.get_or_insert(execute);
            (record, output, io, Some(execute))
          };
        let start = Instant::now();
        let plan = system.single_shard_plan(&record);
        let index = system.row_index(&record, &plan);
        let witness = system.shard_witness(&record, &io, &plan, &index, 0);
        let trace = start.elapsed().as_secs_f64();
        if sample >= 2 {
          times.push(json!({"execute_seconds":execute,"trace_with_lookups_seconds":trace}));
        }
        if sample == samples + 1 {
          for (i, (shape, matrix)) in
            system.circuit_shapes().iter().zip(&witness.traces).enumerate()
          {
            let members = system
              .toplevel()
              .circuits
              .get(i)
              .map(|c| c.members.clone())
              .unwrap_or_default();
            circuits.push(json!({"index":i,"members":members,"height":matrix.height(),
              "stage1_width":shape.main_width,"stage2_width":shape.stage2_width,
              "preprocessed_width":shape.preprocessed_width,"preprocessed_height":shape.preprocessed_height,
              "quotient_degree":shape.quotient_degree,"cells":matrix.values.len(),
              "fft_cost":ix_bench::fft_cost(shape.main_width,shape.stage2_width,shape.quotient_degree,matrix.height(),1)}));
          }
        }
        drop(witness);
        if prove && sample == samples + 1 {
          let start = Instant::now();
          let (claim, proof) =
            system.prove_from_execution(function, &args, &io, record, &output);
          system
            .verify(&claim, &proof)
            .map_err(|e| format!("legacy proof rejected: {e:?}"))?;
          let seconds = start.elapsed().as_secs_f64();
          proof_report = json!({"prove_including_trace_seconds":seconds,"bytes":proof.to_bytes().map_err(|e|e.to_string())?.len(),"verified":true});
        } else if reuse_execution {
          cached_execution = Some((record, output, io));
        }
      }
      Ok(
        json!({"backend":"legacy-bytecode","thp_disabled":thp_disabled,"setup_seconds":setup,"reused_execution":reuse_execution,"initial_execute_seconds":initial_execute,"samples":times,"circuits":circuits,"proof":proof_report}),
      )
    };
    match run() {
      Ok(report) => LeanExcept::ok(LeanString::new(&report.to_string())),
      Err(error) => LeanExcept::error_string(&error),
    }
  })
}
