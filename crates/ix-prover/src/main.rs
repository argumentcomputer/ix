//! Resident host for the formal IxVM and recursive verifier. The application
//! submits ready jobs; CPU execution is shared and each prover owns its backend.
//! Spool files transport control messages only. Execution records stay in memory.
mod distributed;
mod output;
mod protocol;

use aiur::{
  Execution,
  bytecode::CheckedProgram,
  field::{FieldBackend, NativeField},
  library::io::Invocation,
  trace::{
    TracePlan,
    stark::{Backend, Parameters, planning},
  },
};
use multi_stark::types::Val;
use protocol::{Config, Job, Kind, atomic_json, read_json};
use record_pool::{
  BudgetError, RecordPool, RecordReservation, queue::WorkQueue,
};
use serde_json::{Value, json};
use std::{
  collections::{HashSet, VecDeque},
  fs,
  path::{Path, PathBuf},
  sync::{Condvar, Mutex, mpsc},
  time::{Duration, Instant},
};

type Field = NativeField<Val>;
type Program = CheckedProgram<Field>;
type Prover<'a, 'p> = Backend<'a, 'p, Field>;

struct Prepared {
  job: Job,
  artifact: usize,
  entry: String,
  args: Vec<Val>,
  record: Execution<Field>,
  report: Value,
}
struct Prep {
  job: Job,
  artifact: usize,
  reservation: RecordReservation,
}
enum Event {
  Done(Job, u32, Value, bool),
  Retry(Job),
  Prepared,
}

struct Log {
  file: Mutex<fs::File>,
  start: Instant,
}
impl Log {
  fn event(&self, mut event: Value) {
    use std::io::Write;
    event["elapsed_seconds"] = self.start.elapsed().as_secs_f64().into();
    if let Ok(mut file) = self.file.lock() {
      let _ = writeln!(file, "{event}");
    }
  }
}

fn fail(error: impl Into<String>) -> Value {
  let error: String = error.into();
  json!({"verified":false, "error":error})
}

fn tracing(enabled: bool) -> Result<(), String> {
  use tracing_subscriber::{layer::SubscriberExt, util::SubscriberInitExt};
  if enabled {
    tracing_subscriber::Registry::default()
      .with(tracing_texray::TeXRayLayer::new().track_ram().streaming())
      .try_init()
      .map_err(|e| e.to_string())?;
  }
  Ok(())
}

fn prepare(
  program: &Program,
  kind: Kind,
  task: Prep,
) -> Result<Prepared, Box<(Job, u32, Value, bool)>> {
  let Prep { job, artifact, reservation } = task;
  let _span =
    tracing_texray::examine(tracing::info_span!("aiur.execute", id = %job.id))
      .entered();
  let run = || -> Result<Prepared, PrepFailure> {
    job.options.validate().map_err(PrepFailure::Other)?;
    // Reserve advice while parsing it, before either its decoded vectors or
    // hint arenas are allocated. It remains charged alongside the record.
    let bytes = fs::metadata(&job.input)
      .map_err(|e| PrepFailure::Other(e.to_string()))?
      .len();
    reservation.reserve(
      usize::try_from(bytes.saturating_mul(8)).unwrap_or(usize::MAX),
    )?;
    let input: Invocation =
      read_json(&job.input).map_err(PrepFailure::Other)?;
    let valid = match kind {
      Kind::Ixvm => {
        input.entry == "IxVM::verify_claim" && input.args.len() == 8
      },
      Kind::Recursion => {
        ["MultiStark::verify_multi_stark_proof", "MultiStark::ix_aggr"]
          .contains(&input.entry.as_str())
          && input.args.len() == 16
      },
    };
    if !valid {
      return Err(PrepFailure::Other("wrong application entrypoint".into()));
    }
    let args =
      program.field().decode(&input.args).map_err(PrepFailure::Other)?;
    let start = Instant::now();
    let hints = match kind {
      Kind::Ixvm => ixvm::prepare_streams(program, &input.streams),
      Kind::Recursion => stark_verifier::prepare(program, &input.streams),
    }
    .map_err(PrepFailure::Other)?;
    let record = hints
      .execute_reserved(&input.entry, args.clone(), &reservation)
      .map_err(|e| {
        e.resource.map_or_else(
          || PrepFailure::Other(e.to_string()),
          PrepFailure::Resource,
        )
      })?;
    if !record.output.is_empty() {
      return Err(PrepFailure::Other("verifier returned a value".into()));
    }
    reservation.finish_execution();
    let report = json!({"verified":false, "execution_seconds":start.elapsed().as_secs_f64(),
      "queries":record.queries.len(), "instructions":record.instructions, "record_bytes":reservation.bytes()});
    Ok(Prepared {
      job: job.clone(),
      artifact,
      entry: input.entry,
      args,
      record,
      report,
    })
  };
  match run() {
    Ok(prepared) => Ok(prepared),
    Err(PrepFailure::Resource(BudgetError::Cancelled)) => {
      Err(Box::new((job, 75, fail("record memory contention"), true)))
    },
    Err(PrepFailure::Resource(error)) => Err(Box::new((
      job,
      75,
      json!({"verified":false,"can_split":true,
      "error":error.to_string(),"record_budget_exceeded":matches!(error, BudgetError::Exceeded{..})}),
      false,
    ))),
    Err(PrepFailure::Other(error)) => {
      Err(Box::new((job, 1, fail(error), false)))
    },
  }
}
enum PrepFailure {
  Resource(BudgetError),
  Other(String),
}
impl From<BudgetError> for PrepFailure {
  fn from(e: BudgetError) -> Self {
    Self::Resource(e)
  }
}

/// The prover workspace, shared by the lanes through reservations. Every
/// lane plans within an equal share, so ordinary jobs never wait for each
/// other. A recursive job that its share would split into more shards may
/// plan within the whole workspace instead: every further level of a proof
/// tree verifies each shard of its children, so splitting one near the root
/// makes the levels above it larger. Such a job waits until its reservation
/// is free. Reservations are granted in request order, so a waiting job is
/// not overtaken by later small ones.
struct Workspace {
  total: u64,
  share: u64,
  state: Mutex<WorkspaceState>,
  released: Condvar,
}
struct WorkspaceState {
  free: u64,
  next: u64,
  serving: u64,
}
struct WorkspaceReservation<'a> {
  workspace: &'a Workspace,
  bytes: u64,
}
impl Workspace {
  fn new(total: u64, lanes: usize) -> Self {
    Self {
      total,
      share: total / lanes.max(1) as u64,
      state: Mutex::new(WorkspaceState { free: total, next: 0, serving: 0 }),
      released: Condvar::new(),
    }
  }
  fn reserve(&self, bytes: u64) -> WorkspaceReservation<'_> {
    let bytes = bytes.min(self.total);
    let mut state = self.state.lock().unwrap_or_else(|e| e.into_inner());
    let ticket = state.next;
    state.next += 1;
    while state.serving != ticket || state.free < bytes {
      state = self.released.wait(state).unwrap_or_else(|e| e.into_inner());
    }
    state.free -= bytes;
    state.serving += 1;
    self.released.notify_all();
    WorkspaceReservation { workspace: self, bytes }
  }
}
impl Drop for WorkspaceReservation<'_> {
  fn drop(&mut self) {
    let mut state =
      self.workspace.state.lock().unwrap_or_else(|e| e.into_inner());
    state.free += self.bytes;
    self.workspace.released.notify_all();
  }
}

/// Thread pools a lane proves on: its own, and for CPU controllers with
/// several lanes one spanning every lane's threads, for jobs that borrowed
/// the whole workspace and therefore run while the other lanes wait.
struct Pools<'a> {
  lane: &'a rayon::ThreadPool,
  wide: Option<&'a rayon::ThreadPool>,
}

fn prove(
  backend: &Prover<'_, '_>,
  kind: Kind,
  prepared: Prepared,
  workspace: &Workspace,
  pools: &Pools<'_>,
  lane: usize,
  device: Option<i32>,
) -> (Job, u32, Value) {
  let Prepared { job, entry, args, record, mut report, .. } = prepared;
  let effective_device = job.options.device.or(device);
  let result = (|| -> Result<(), String> {
    let plan = |budget: u64| {
      let mut options = job.options.clone();
      options.device = effective_device;
      options.max_ram_bytes =
        Some(options.max_ram_bytes.unwrap_or(budget).min(budget));
      backend.plan_record(&record, &options, 0)
    };
    let narrow = plan(workspace.share)?;
    let wide = match kind {
      Kind::Recursion if workspace.total > workspace.share => {
        Some(plan(workspace.total)?).filter(|wide| {
          wide.fits && (!narrow.fits || wide.shards < narrow.shards)
        })
      },
      _ => None,
    };
    let borrowed = wide.is_some();
    let batch = wide.unwrap_or(narrow);
    report["plan"] = serde_json::to_value(&batch).map_err(|e| e.to_string())?;
    report["lane"] = lane.into();
    report["device"] = effective_device.into();
    report["borrowed_workspace"] = borrowed.into();
    if !batch.fits {
      return Ok(());
    }
    let waited = Instant::now();
    let _reservation = workspace
      .reserve(batch.generation_peak_bytes.max(batch.proving_peak_bytes));
    report["workspace_wait_seconds"] = waited.elapsed().as_secs_f64().into();
    let pool =
      if borrowed { pools.wide.unwrap_or(pools.lane) } else { pools.lane };
    pool.install(|| {
      let start = Instant::now();
      let traces = tracing_texray::examine(
        tracing::info_span!("aiur.trace", id = %job.id),
      )
      .in_scope(|| backend.prepare_stage_1(&record, &entry, &args))?;
      if traces.cells() != batch.stage1_cells {
        return Err("generated trace differs from resource plan".into());
      }
      report["trace_seconds"] = start.elapsed().as_secs_f64().into();
      drop(record);
      let start = Instant::now();
      let proof = tracing_texray::examine(
        tracing::info_span!("aiur.prove", id = %job.id, lane),
      )
      .in_scope(|| {
        backend.prove_stage_one(
          &entry,
          &args,
          &[],
          traces,
          batch.max_rows,
          batch.retention(),
        )
      })?;
      report["proving_seconds"] = start.elapsed().as_secs_f64().into();
      report = output::proof(
        &job,
        kind,
        backend,
        &entry,
        &args,
        &proof,
        report.take(),
      )?;
      Ok(())
    })
  })();
  match result {
    Ok(()) if report["verified"] == true => (job, 0, report),
    Ok(()) => {
      let _ = output::report(&job, kind, &report);
      (job, 75, report)
    },
    Err(error) => {
      report["error"] = error.into();
      let _ = output::report(&job, kind, &report);
      (job, 1, report)
    },
  }
}

struct Shutdown<'a> {
  pool: &'a RecordPool,
  prep: &'a WorkQueue<Prep>,
  records: &'a WorkQueue<Prepared>,
}

fn parent_gone(pid: Option<u32>) -> bool {
  #[cfg(target_os = "linux")]
  {
    pid.is_some_and(|pid| !Path::new(&format!("/proc/{pid}")).exists())
  }
  #[cfg(not(target_os = "linux"))]
  {
    let _ = pid;
    false
  }
}
impl Drop for Shutdown<'_> {
  fn drop(&mut self) {
    self.pool.shutdown();
    self.prep.close();
    self.records.close();
  }
}

fn serve(config: &Config, dir: &Path) -> Result<(), String> {
  tracing(config.texray)?;
  if config.artifacts.is_empty()
    || config.devices.is_empty()
    || config.exec_jobs == 0
    || config.threads_per_prover == 0
    || config.max_ram_bytes == 0
    || config.record_limit_bytes == Some(0)
  {
    return Err("artifacts, lanes, execution threads, prover threads and RAM must be positive".into());
  }
  let mut seen_devices = HashSet::new();
  if config.devices.iter().any(Option::is_some)
    && config.devices.iter().any(Option::is_none)
  {
    return Err("controller cannot mix CPU lanes and CUDA lanes".into());
  }
  // Lanes own distinct devices. Tests on a single GPU may share one between
  // lanes to exercise concurrent multi-lane proving in one process.
  let shared = std::env::var("IX_PROVER_SHARED_DEVICES").as_deref() == Ok("1");
  for device in &config.devices {
    planning::Options { device: *device, ..Default::default() }.validate()?;
    if let Some(device) = device
      && !seen_devices.insert(device)
      && !shared
    {
      return Err("duplicate GPU lane".into());
    }
  }
  fs::create_dir_all(dir.join("pending")).map_err(|e| e.to_string())?;
  fs::create_dir_all(dir.join("done")).map_err(|e| e.to_string())?;
  let log = Log {
    file: Mutex::new(
      fs::File::create(dir.join("events.jsonl")).map_err(|e| e.to_string())?,
    ),
    start: Instant::now(),
  };
  let mut programs = Vec::new();
  let mut artifacts = Vec::new();
  for artifact in &config.artifacts {
    let (package, digest) = aiur::artifact::Package::load(&artifact.path)?;
    eprintln!("artifact {}: blake3 {digest}", artifact.path.display());
    let (program, trace) = package.traced()?;
    programs.push(program.check_field::<Val>()?);
    artifacts.push(trace);
  }
  let plans = programs
    .iter()
    .zip(artifacts)
    .map(|(p, a)| TracePlan::new(p, a))
    .collect::<Result<Vec<_>, _>>()?;
  let paths = config
    .artifacts
    .iter()
    .map(|a| fs::canonicalize(&a.path).map_err(|e| e.to_string()))
    .collect::<Result<Vec<_>, _>>()?;
  let mut lanes = Vec::new();
  for device in &config.devices {
    lanes.push(
      plans
        .iter()
        .map(|p| {
          Backend::for_batch_on_device(p, Parameters::default(), *device)
        })
        .collect::<Result<Vec<_>, _>>()?,
    );
  }
  let static_bytes = planning::resident_memory();
  let remaining = config
    .max_ram_bytes
    .checked_sub(static_bytes.saturating_mul(5) / 4)
    .ok_or("RAM budget cannot hold resident artifacts and prover systems")?;
  let records_bytes =
    usize::try_from(remaining / 2).ok().ok_or("record pool overflow")?;
  if records_bytes == 0 {
    return Err("no record capacity remains".into());
  }
  let workspace = Workspace::new(remaining / 2, config.devices.len());
  // CPU lanes borrowing the whole workspace also borrow the waiting lanes'
  // threads. CUDA lanes keep their own: the device does the heavy work.
  let wide = (config.devices.len() > 1
    && config.devices.iter().all(Option::is_none))
  .then(|| {
    rayon::ThreadPoolBuilder::new()
      .num_threads(
        config.threads_per_prover.saturating_mul(config.devices.len()),
      )
      .build()
      .map_err(|e| e.to_string())
  })
  .transpose()?;
  let capacity =
    config.exec_jobs.saturating_add(config.devices.len().saturating_mul(2));
  let pool = RecordPool::new(
    records_bytes,
    (records_bytes / capacity).clamp(1, 16 << 20),
  )
  .with_record_limit(
    config
      .record_limit_bytes
      .unwrap_or(128usize << 30)
      .min(records_bytes)
      .max(1),
  );
  let prep_queue = WorkQueue::<Prep>::new(config.exec_jobs);
  let records = WorkQueue::<Prepared>::new(capacity);
  let (send, receive) = mpsc::channel();
  std::thread::scope(|scope| -> Result<(), String> {
    // Drop before scoped joins even if a later worker setup fails.
    let _shutdown =
      Shutdown { pool: &pool, prep: &prep_queue, records: &records };
    for executor in 0..config.exec_jobs {
      let (programs, kinds, log, send, prep_queue, records) = (
        &programs,
        &config.artifacts,
        &log,
        send.clone(),
        &prep_queue,
        &records,
      );
      scope.spawn(move || {
        while let Some(task) = prep_queue.pop() {
          log.event(json!({"phase":"execute", "id":task.job.id, "executor":executor}));
          let id = task.artifact;
          match prepare(&programs[id], kinds[id].kind, task) {
            Ok(prepared) => {
              log.event(json!({"phase":"prepared", "id":prepared.job.id, "record_bytes":prepared.report["record_bytes"]}));
              let _ = send.send(Event::Prepared);
              let priority = prepared.job.priority;
              if records.push(prepared, priority).is_err() { break; }
            },
            Err(failure) => {
              let (job, code, report, retry) = *failure;
              if retry { let _ = send.send(Event::Retry(job)); }
              else { let _ = output::report(&job, kinds[id].kind, &report); let _ = send.send(Event::Done(job, code, report, true)); }
            },
          }
        }
      });
    }
    for (lane, backends) in lanes.into_iter().enumerate() {
      let (kinds, log, records, send, threads, device, workspace, wide) = (
        &config.artifacts,
        &log,
        &records,
        send.clone(),
        config.threads_per_prover,
        config.devices[lane],
        &workspace,
        wide.as_ref(),
      );
      let rayon = rayon::ThreadPoolBuilder::new()
        .num_threads(threads)
        .build()
        .map_err(|e| e.to_string())?;
      scope.spawn(move || {
        let pools = Pools { lane: &rayon, wide };
        while let Some(prepared) = records.pop_matching(|r| {
          r.job.options.device.is_none() || r.job.options.device == device
        }) {
          log.event(json!({"phase":"prove", "id":prepared.job.id, "lane":lane, "device":device}));
          let id = prepared.artifact;
          let (job, code, report) = prove(
            &backends[id],
            kinds[id].kind,
            prepared,
            workspace,
            &pools,
            lane,
            device,
          );
          let _ = send.send(Event::Done(job, code, report, false));
        }
      });
    }
    atomic_json(
      &dir.join("ready.json"),
      &json!({"ready":true, "lanes":config.devices, "executors":config.exec_jobs,
      "static_bytes":static_bytes, "record_budget_bytes":records_bytes, "workspace_per_lane_bytes":workspace.share,
      "workspace_bytes":workspace.total}),
    )?;
    let mut pending = VecDeque::new();
    let mut seen = HashSet::new();
    let mut active = 0;
    let mut preparing = 0;
    loop {
      if dir.join("stop").exists() || parent_gone(config.parent_pid) {
        break;
      }
      for event in receive.try_iter() {
        match event {
          Event::Prepared => preparing -= 1,
          Event::Retry(job) => {
            active -= 1;
            preparing -= 1;
            log.event(json!({"phase":"retry", "id":job.id}));
            pending.push_front(job);
          },
          Event::Done(job, code, report, failed_preparation) => {
            active -= 1;
            if failed_preparation {
              preparing -= 1;
            }
            log.event(json!({"phase":"done", "id":job.id, "status":code, "report":report}));
            atomic_json(
              &dir.join("done").join(format!("{}.json", job.id)),
              &json!({"status":code,"report":report}),
            )?;
          },
        }
      }
      let mut files = fs::read_dir(dir.join("pending"))
        .map_err(|e| e.to_string())?
        .filter_map(Result::ok)
        .map(|e| e.path())
        .filter(|p| p.extension().is_some_and(|s| s == "json"))
        .collect::<Vec<_>>();
      files.sort();
      for path in files {
        let job: Job = read_json(&path)?;
        if job.id.is_empty()
          || job.id.len() > 128
          || !job
            .id
            .bytes()
            .all(|b| b.is_ascii_alphanumeric() || b == b'-' || b == b'_')
          || !seen.insert(job.id.clone())
        {
          return Err("invalid or duplicate job ID".into());
        }
        fs::remove_file(path).map_err(|e| e.to_string())?;
        log.event(
          json!({"phase":"queued", "id":job.id, "priority":job.priority}),
        );
        if job.priority {
          let index = pending
            .iter()
            .position(|p: &Job| !p.priority)
            .unwrap_or(pending.len());
          pending.insert(index, job);
        } else {
          pending.push_back(job);
        }
      }
      while active < capacity
        && preparing < config.exec_jobs
        && !pending.is_empty()
      {
        let Some(reservation) = pool.try_admit().map_err(|e| e.to_string())?
        else {
          break;
        };
        let job = pending.pop_front().unwrap();
        if job.options.device.is_some()
          && !config.devices.contains(&job.options.device)
        {
          atomic_json(
            &dir.join("done").join(format!("{}.json", job.id)),
            &json!({"status":1,"report":fail("requested CUDA device is not a controller lane")}),
          )?;
          continue;
        }
        let artifact = fs::canonicalize(&job.artifact)
          .ok()
          .and_then(|p| paths.iter().position(|a| *a == p));
        let Some(artifact) = artifact else {
          atomic_json(
            &dir.join("done").join(format!("{}.json", job.id)),
            &json!({"status":1,"report":fail("artifact was not loaded by this controller")}),
          )?;
          continue;
        };
        let priority = job.priority;
        prep_queue
          .push(Prep { job, artifact, reservation }, priority)
          .ok()
          .ok_or("execution queue closed")?;
        active += 1;
        preparing += 1;
      }
      std::thread::sleep(Duration::from_millis(10));
    }
    Ok(())
  })?;
  let stats = pool.stats();
  atomic_json(
    &dir.join("summary.json"),
    &json!({"record_peak_bytes":stats.peak_reserved,
    "record_reserved_bytes":stats.reserved,"record_waits":stats.waits,
    "record_wait_seconds":stats.wait_time.as_secs_f64(),"record_retries":stats.retries}),
  )?;
  Ok(())
}

fn main() {
  let args: Vec<_> = std::env::args_os().collect();
  let result = if args.len() == 4 && args[1] == "serve" {
    let dir = PathBuf::from(&args[3]);
    read_json(Path::new(&args[2]))
      .and_then(|config| serve(&config, &dir))
      .inspect_err(|error| {
        let _ = atomic_json(&dir.join("failed.json"), &fail(error));
      })
  } else if args.len() == 6 && args[1] == "distributed" {
    distributed::run(
      Path::new(&args[2]),
      Path::new(&args[3]),
      Path::new(&args[4]),
      Path::new(&args[5]),
    )
  } else {
    Err("usage: ix-prover serve CONFIG.json SPOOL_DIRECTORY | distributed ARTIFACT SPEC OUTPUT OPTIONS".into())
  };
  if let Err(error) = result {
    eprintln!("ix-prover: {error}");
    std::process::exit(1);
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  /// A request larger than what is free waits for a release, and a later
  /// request that would fit does not overtake it.
  #[test]
  fn workspace_reservations_are_granted_in_order() {
    let workspace = Workspace::new(100, 2);
    assert_eq!(workspace.share, 50);
    let queued = |count| {
      while workspace.state.lock().unwrap().next < count {
        std::thread::yield_now();
      }
    };
    let first = workspace.reserve(60);
    let (granted, receive) = mpsc::channel();
    std::thread::scope(|scope| {
      let send = granted.clone();
      let workspace = &workspace;
      scope.spawn(move || {
        let _whole = workspace.reserve(100);
        send.send("whole").unwrap();
      });
      queued(2);
      let send = granted.clone();
      scope.spawn(move || {
        let _small = workspace.reserve(10);
        send.send("small").unwrap();
      });
      queued(3);
      std::thread::sleep(Duration::from_millis(50));
      assert!(receive.try_recv().is_err(), "granted before the release");
      drop(first);
      assert_eq!(receive.recv().unwrap(), "whole");
      assert_eq!(receive.recv().unwrap(), "small");
    });
    assert_eq!(workspace.state.lock().unwrap().free, 100);
    // A request is never larger than the workspace.
    assert_eq!(workspace.reserve(u64::MAX).bytes, 100);
  }
}
