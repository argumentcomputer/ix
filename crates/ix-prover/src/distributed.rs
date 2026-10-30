//! One claim, multiple execution records. Only unit calls are deferred. Each
//! record owns a disjoint ROM interval, and the batch balances calls across it.
use super::{
  Field, Package, Program, output,
  protocol::{Job, Kind, read_json},
};
use aiur::{
  Execution, QueryInput,
  execute::Partition,
  field::FieldBackend,
  library::io::Invocation,
  trace::{
    TracePlan,
    stark::{
      Backend, Parameters, StreamPlan,
      planning::{self, Options, RecordShape},
    },
  },
};
use multi_stark::{batch::Retention, p3_field::PrimeField64, types::Val};
use rayon::prelude::*;
use record_pool::{BudgetError, RecordPool};
use rustc_hash::FxHashMap;
use serde::{Deserialize, Serialize};
use serde_json::json;
use std::{
  path::{Path, PathBuf},
  time::{Duration, Instant},
};

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Worker {
  input: PathBuf,
  owned: Vec<Vec<u64>>,
}
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Spec {
  invocation: Invocation,
  workers: Vec<Worker>,
  exec_jobs: usize,
  #[serde(default)]
  cells: usize,
  #[serde(default)]
  exec_only: bool,
  #[serde(default)]
  texray: bool,
}
#[derive(Serialize)]
struct Measured {
  shape: RecordShape,
  queries: usize,
  instructions: u64,
  record_bytes: usize,
  execution_seconds: f64,
  #[serde(skip)]
  deferred: Vec<(Vec<Val>, u64)>,
  #[serde(skip)]
  edges: Vec<(Vec<Val>, Vec<Val>)>,
  #[serde(skip)]
  own_counts: Vec<u64>,
}

fn record(
  program: &Program,
  spec: &Spec,
  worker: usize,
  function: usize,
  pool: &RecordPool,
) -> Result<(Execution<Field>, usize, f64), String> {
  let _span = tracing_texray::examine(tracing::info_span!(
    "aiur.distributed.execute",
    worker
  ))
  .entered();
  loop {
    let reservation = loop {
      if let Some(r) = pool.try_admit().map_err(|e| e.to_string())? {
        break r;
      }
      std::thread::sleep(Duration::from_millis(5));
    };
    let source = &spec.workers[worker];
    let stride = (program.field().modulus() - 1) / spec.workers.len() as u64;
    let run = || -> Result<Execution<Field>, super::PrepFailure> {
      let bytes = std::fs::metadata(&source.input)
        .map_err(|e| super::PrepFailure::Other(e.to_string()))?
        .len();
      reservation.reserve(
        usize::try_from(bytes.saturating_mul(8)).unwrap_or(usize::MAX),
      )?;
      let input: Invocation =
        read_json(&source.input).map_err(super::PrepFailure::Other)?;
      let args = program
        .field()
        .decode(&spec.invocation.args)
        .map_err(super::PrepFailure::Other)?;
      let owned = source
        .owned
        .iter()
        .map(|a| program.field().decode(a))
        .collect::<Result<Vec<_>, _>>()
        .map_err(super::PrepFailure::Other)?;
      let hints = ixvm::prepare_streams(program, &input.streams)
        .map_err(super::PrepFailure::Other)?;
      hints
        .execute_partition(
          (worker == 0).then_some((spec.invocation.entry.as_str(), args)),
          Partition {
            function,
            owned,
            memory_start: stride * worker as u64,
            memory_end: stride * (worker as u64 + 1),
          },
          Some(&reservation),
        )
        .map_err(|e| {
          e.resource.map_or_else(
            || super::PrepFailure::Other(e.to_string()),
            super::PrepFailure::Resource,
          )
        })
    };
    let start = Instant::now();
    match run() {
      Ok(record) => {
        reservation.finish_execution();
        return Ok((
          record,
          reservation.bytes(),
          start.elapsed().as_secs_f64(),
        ));
      },
      Err(super::PrepFailure::Resource(BudgetError::Cancelled)) => continue,
      Err(super::PrepFailure::Resource(e)) => return Err(e.to_string()),
      Err(super::PrepFailure::Other(e)) => return Err(e),
    }
  }
}

/// No deferred-call cycle may be hidden by splitting a record. Local cycles
/// are caught by the interpreter; this checks the combined owned-call graph.
fn acyclic(
  nodes: usize,
  edges: impl Iterator<Item = (usize, usize)>,
) -> Result<(), String> {
  let mut graph = vec![Vec::new(); nodes];
  let mut incoming = vec![0usize; nodes];
  for (a, b) in edges {
    graph[a].push(b);
    incoming[b] += 1;
  }
  let mut ready: Vec<_> = (0..nodes).filter(|&i| incoming[i] == 0).collect();
  let mut count = 0;
  while let Some(i) = ready.pop() {
    count += 1;
    for &j in &graph[i] {
      incoming[j] -= 1;
      if incoming[j] == 0 {
        ready.push(j);
      }
    }
  }
  if count == nodes {
    Ok(())
  } else {
    Err("recursive owned-call cycle crosses worker records".into())
  }
}

pub fn run(
  artifact: &Path,
  specification: &Path,
  out: &Path,
  options_path: &Path,
) -> Result<(), String> {
  let spec: Spec = read_json(specification)?;
  super::tracing(spec.texray)?;
  let package: Package =
    aiur::decode_artifact(&std::fs::read(artifact).map_err(|e| e.to_string())?)
      .map_err(|e| e.to_string())?;
  let program = package.program.check_field::<Val>()?;
  let plan = TracePlan::new(&program, package.trace)?;
  let options: Options = read_json(options_path)?;
  options.validate()?;
  let backend =
    Backend::for_batch_on_device(&plan, Parameters::default(), options.device)?;
  if spec.workers.is_empty()
    || spec.exec_jobs == 0
    || spec.invocation.entry != "IxVM::verify_claim"
    || spec.invocation.args.len() != 8
  {
    return Err("invalid distributed IxVM specification".into());
  }
  let function = program
    .program()
    .functions
    .iter()
    // Retain compatibility with cached artifacts from before the module split.
    .position(|f| {
      matches!(f.name.as_str(), "IxVMCompat::check_owned" | "IxVM::check_owned")
    })
    .ok_or("IxVM artifact has no check_owned callable")?;
  let mut owners = FxHashMap::default();
  let mut keys = Vec::new();
  for (worker, source) in spec.workers.iter().enumerate() {
    for key in &source.owned {
      if key.len() != 32 || key.iter().any(|&x| x > 255) {
        return Err("owned address must contain 32 bytes".into());
      }
      let key = program.field().decode(key)?;
      if owners.insert(key.clone(), (worker, keys.len())).is_some() {
        return Err("a constant has multiple owners".into());
      }
      keys.push(key);
    }
  }
  let budget = options
    .max_ram_bytes
    .or_else(planning::available_memory)
    .unwrap_or(8 << 30);
  let remaining = budget
    .checked_sub(planning::resident_memory().saturating_mul(5) / 4)
    .ok_or("distributed budget is below resident setup")?;
  let records_bytes =
    usize::try_from(remaining / 2).map_err(|_| "record pool overflow")?;
  if records_bytes == 0 {
    return Err("no record capacity remains".into());
  }
  let limit = std::env::var("AIUR_RECORD_MAX_BYTES")
    .ok()
    .map(|s| s.parse::<usize>())
    .transpose()
    .map_err(|e| e.to_string())?
    .unwrap_or(128usize << 30)
    .min(records_bytes);
  if limit == 0 {
    return Err("record limit must be positive".into());
  }
  let pool = RecordPool::new(
    records_bytes,
    (records_bytes / spec.exec_jobs).clamp(1, 16 << 20),
  )
  .with_record_limit(limit);
  let executors = rayon::ThreadPoolBuilder::new()
    .num_threads(spec.exec_jobs.min(spec.workers.len()))
    .build()
    .map_err(|e| e.to_string())?;
  // The first pass retains only call counts, graph edges and trace shapes.
  // Every worker's record is released before another needs its capacity.
  let measured = executors.install(|| {
    (0..spec.workers.len())
      .into_par_iter()
      .map(|worker| {
        let (record, bytes, seconds) =
          record(&program, &spec, worker, function, &pool)?;
        let own_counts = spec.workers[worker]
          .owned
          .iter()
          .map(|key| {
            let args = program.field().decode(key)?;
            Ok(
              record
                .queries
                .get(&QueryInput { function, args })
                .ok_or("missing owned query")?
                .multiplicity,
            )
          })
          .collect::<Result<Vec<_>, String>>()?;
        Ok(Measured {
          shape: backend.record_shape(&record)?,
          queries: record.queries.len(),
          instructions: record.instructions,
          record_bytes: bytes,
          execution_seconds: seconds,
          own_counts,
          deferred: record
            .deferred_calls()
            .map(|(k, n)| (k.to_vec(), n))
            .collect(),
          edges: record
            .partition_edges()
            .map(|(a, b)| (a.to_vec(), b.to_vec()))
            .collect(),
        })
      })
      .collect::<Result<Vec<_>, String>>()
  })?;
  let mut incoming =
    vec![FxHashMap::<Vec<Val>, u64>::default(); spec.workers.len()];
  let mut edges = Vec::new();
  for worker in &measured {
    for (key, count) in &worker.deferred {
      let &(owner, _) = owners.get(key).ok_or("deferred call has no owner")?;
      let value = incoming[owner].entry(key.clone()).or_default();
      *value = value
        .checked_add(*count)
        .filter(|&n| n < Val::ORDER_U64)
        .ok_or("deferred count overflow")?;
    }
    for (a, b) in &worker.edges {
      edges.push((
        owners.get(a).ok_or("unknown caller owner")?.1,
        owners.get(b).ok_or("unknown callee owner")?.1,
      ));
    }
  }
  acyclic(keys.len(), edges.into_iter())?;
  for (i, worker) in spec.workers.iter().enumerate() {
    for (key, count) in worker.owned.iter().zip(&measured[i].own_counts) {
      let key = program.field().decode(key)?;
      if count
        .checked_add(incoming[i].get(&key).copied().unwrap_or(0))
        .is_none_or(|n| n == 0 || n >= Val::ORDER_U64)
      {
        return Err(
          "owned query is unused or its count exceeds the field".into(),
        );
      }
    }
  }
  let mut local = options.clone();
  local.max_ram_bytes = Some(remaining / 2);
  local.retention = planning::RetentionPolicy::Regenerate;
  let widths: Vec<_> = backend
    .statistics()
    .iter()
    .map(|s| s.stage1_width + s.stage2_width + s.preprocessed_width)
    .collect();
  let fixed: Vec<_> =
    backend.statistics().iter().map(|s| s.preprocessed_height != 0).collect();
  let mut plans = Vec::new();
  let mut pieces = Vec::new();
  for (worker, m) in measured.iter().enumerate() {
    let mut batch = backend.plan_heights(&m.shape.heights, &local, 0)?;
    if !batch.fits {
      return Err(format!("worker {worker} does not fit its prover workspace"));
    }
    if spec.cells != 0 {
      loop {
        let cells: u128 = m
          .shape
          .heights
          .iter()
          .zip(&widths)
          .zip(&fixed)
          .map(|((&h, &w), &f)| {
            (if f { h } else { h.min(batch.max_rows) }) as u128 * w as u128
          })
          .sum();
        if cells <= spec.cells as u128 {
          break;
        }
        if batch.max_rows == 1 {
          return Err("cell budget is below the fixed-table floor".into());
        }
        let limited =
          Options { max_rows: Some(batch.max_rows / 2), ..local.clone() };
        batch = backend.plan_heights(&m.shape.heights, &limited, 0)?;
      }
    }
    pieces.extend((0..batch.shards).map(|shard| (worker, shard)));
    plans.push(batch);
  }
  let job = Job {
    id: "distributed".into(),
    artifact: artifact.into(),
    input: specification.into(),
    output: out.into(),
    options,
    priority: false,
  };
  let stream = backend.plan_stream(
    &measured
      .iter()
      .zip(&plans)
      .map(|(m, p)| (m.shape.heights.as_slice(), p.max_rows))
      .collect::<Vec<_>>(),
    &Options { max_ram_bytes: local.max_ram_bytes, ..job.options.clone() },
  )?;
  if !stream.fits {
    return Err("retained distributed batch exceeds the workspace budget; use --retention regenerate or increase RAM".into());
  }
  let mut report = json!({"verified":false,"distributed":true,"workers":measured,"plans":plans,
    "stream":stream,"exec_jobs":spec.exec_jobs,"shards":pieces.len(),
    "cross_record_calls":incoming.iter().map(|m| m.values().map(|&n| u128::from(n)).sum::<u128>()).sum::<u128>()});
  output::report(&job, Kind::Ixvm, &report)?;
  if spec.exec_only {
    println!("{report}");
    return Ok(());
  }
  let args = program.field().decode(&spec.invocation.args)?;
  let mut cached = None;
  let mut traces = Vec::new();
  let start = Instant::now();
  let _span =
    tracing_texray::examine(tracing::info_span!("aiur.distributed.prove"))
      .entered();
  let proof = backend.prove_streamed_stage_1(
    &spec.invocation.entry,
    &args,
    &[],
    StreamPlan {
      shards: pieces.len(),
      retention: if stream.retention == planning::RetentionPolicy::Retain {
        Retention::Retain
      } else {
        Retention::Regenerate
      },
      memory_intervals: measured
        .iter()
        .flat_map(|m| m.shape.memory_intervals.iter().copied())
        .collect(),
    },
    |piece| {
      let (worker, shard) = pieces[piece];
      if cached != Some(worker) {
        // Release the previous record's matrices before replaying the next one.
        traces.clear();
        let (mut record, _, _) =
          record(&program, &spec, worker, function, &pool)?;
        for (key, count) in &incoming[worker] {
          record.absorb_deferred(function, key, *count)?;
        }
        if backend.record_shape(&record)? != measured[worker].shape {
          return Err("worker trace shape changed on replay".into());
        }
        traces = tracing::info_span!("aiur.distributed.trace", worker)
          .in_scope(|| {
            if worker == 0 {
              backend.generate_stage_1(&record, &spec.invocation.entry, &args)
            } else {
              backend.generate_record_stage_1(&record)
            }
          })?;
        cached = Some(worker);
      }
      backend.slice_stage_1(&traces, shard, plans[worker].max_rows)
    },
  )?;
  report["proving_seconds"] = start.elapsed().as_secs_f64().into();
  report["record_peak_bytes"] = pool.stats().peak_reserved.into();
  let report = output::proof(
    &job,
    Kind::Ixvm,
    &backend,
    &spec.invocation.entry,
    &args,
    &proof,
    report,
  )?;
  println!("{report}");
  Ok(())
}

#[cfg(test)]
mod tests {
  use super::*;
  #[test]
  fn cross_record_cycles_and_shared_dags() {
    assert!(acyclic(4, [(0, 1), (0, 2), (1, 3), (2, 3)].into_iter()).is_ok());
    assert!(acyclic(3, [(0, 1), (1, 2), (2, 1)].into_iter()).is_err());
    assert!(acyclic(1, [(0, 0)].into_iter()).is_err());
  }
}
