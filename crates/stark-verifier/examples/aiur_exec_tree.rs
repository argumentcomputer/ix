//! Prove an `AiurExec::aiur_exec` aggregation tree over `N` program proofs the
//! way `ix prove --aggregate` proves an environment (`docs/aiur-gpu-proving.md`
//! §3): one resident prover per visible GPU, executions on host threads
//! admitted by predicted record from one record pool, and each join
//! dispatched as soon as both of its children are proven, so execution
//! overlaps the devices' proving.
//!
//! ```text
//! aiur_exec_tree AX.ixa IDENTITY_DIR PROGRAMS_DIR WORK_DIR N
//!                [--max-ram GIB] [--exec-jobs N] [--deadline SECONDS]
//! ```
//!
//! Leaf `i` proves `PROGRAMS_DIR/step-iii` (a `batch_root` directory) into
//! `WORK_DIR/L0-iii`; level `d` joins adjacent nodes of level `d - 1` into
//! `WORK_DIR/Ld-kkk` and carries an odd last node up unchanged. Node
//! directories are those of `aiur_exec`, so its `wrap` and `root` take the
//! top node. A node whose `proof.bin` exists is verified natively and reused:
//! rerunning resumes. With `--deadline`, no execution starts after that many
//! seconds; the run finishes what it started and exits with status 75.
//!
//! Host budget (`docs/prover-resource-defaults.md` §4): `--max-ram`, else
//! `MemTotal` less 20%. Each lane's prover workspace for shards of
//! `AIUR_TRACE_SHARD_MAX_CELLS` cells and the resident bytes measured after
//! loading are set aside; the rest is the record pool. The pool is sized
//! for three executions per GPU plus one queued and one proving record per
//! lane; its share of that is each fixed admission's initial grant and the
//! overshoot buffer. Up to three executions per GPU are admitted whenever a
//! share is free; more only while their charges fit (§5.5). An execution is
//! charged the larger of its inputs' records measured in this run, else the
//! largest record measured so far, else 44 GiB. Proofs are planned as trace
//! shards within the lane workspace and proven streamed on the device, with
//! the next shard's witness built on the lane's feed meanwhile.
//! `AIUR_GPU_TRACE` selects device trace population as for `ix prove`.
use aiur::{
  artifact::Package,
  budget::{BudgetError, RecordPool, RecordReservation},
  bytecode::CheckedProgram,
  field::{FieldBackend, NativeField},
  library::io::{Stream, Streams},
  trace::{
    TracePlan,
    stark::{
      Backend, BatchProof, Parameters, ShardFeed, planning,
      streaming::HostPrepared,
    },
  },
};
use multi_stark::{p3_field::PrimeField64, types::Val};
use serde_json::json;
use std::{
  collections::VecDeque,
  error::Error,
  fs,
  path::{Path, PathBuf},
  sync::{Mutex, mpsc},
  time::{Duration, Instant},
};

const ENTRY: &str = "AiurExec::aiur_exec";
const OUT_BYTES: usize = 104;
const MODEL_WORDS: usize = 331;
const DATA_WORDS: usize = 381;
const GIB: usize = 1 << 30;
/// Executions per GPU admitted whenever a share is free
/// (`EXECUTIONS_PER_GPU` in `crates/ixon/src/shard.rs`).
const EXECUTIONS_PER_GPU: usize = 3;
/// The charge of an execution before any record is measured
/// (`AGGREGATION_RECORD_BYTES` in the aggregate controller).
const DEFAULT_RECORD_BYTES: usize = 44 << 30;
/// The default per-record ceiling (`AIUR_RECORD_MAX_BYTES`).
const DEFAULT_RECORD_MAX_BYTES: usize = 128 << 30;

type F = NativeField<Val>;
type Element = <F as FieldBackend>::Element;
type Prover = Backend<'static, 'static, F>;
type R<T> = Result<T, Box<dyn Error + Send + Sync>>;

fn digest_words(bytes: &[u8]) -> Vec<u64> {
  stark_verifier::digest_words(bytes)
}

fn stream(channel: u64, key: Vec<u64>, bytes: &[u8]) -> Stream {
  Stream { channel, key, values: bytes.iter().map(|&b| u64::from(b)).collect() }
}

fn claims_bytes(claim: &[u64]) -> Vec<u8> {
  let mut out = 1u64.to_le_bytes().to_vec();
  out.extend_from_slice(&(claim.len() as u64).to_le_bytes());
  for w in claim {
    out.extend_from_slice(&w.to_le_bytes());
  }
  out
}

fn decode_one_claim(bytes: &[u8]) -> R<Vec<u64>> {
  let claims = stark_verifier::compress_wrap::decode_claims(bytes)?;
  if claims.len() != 1 {
    return Err("expected exactly one claim".into());
  }
  Ok(claims[0].iter().map(|v| v.as_canonical_u64()).collect())
}

fn out_claim(count: u64, first: &[u8; 32], last: &[u8; 32], data: &[u8; 32]) -> Vec<u8> {
  let mut out = count.to_le_bytes().to_vec();
  out.extend_from_slice(first);
  out.extend_from_slice(last);
  out.extend_from_slice(data);
  out
}

fn parse_out(bytes: &[u8]) -> R<(u64, [u8; 32], [u8; 32], [u8; 32])> {
  if bytes.len() != OUT_BYTES {
    return Err("output claim is not 104 bytes".into());
  }
  let a = |i: usize| -> [u8; 32] { bytes[8 + 32 * i..8 + 32 * (i + 1)].try_into().unwrap() };
  Ok((u64::from_le_bytes(bytes[..8].try_into()?), a(0), a(1), a(2)))
}

fn node_hash(left: &[u8; 32], right: &[u8; 32]) -> [u8; 32] {
  let mut pre = vec![1u8];
  pre.extend_from_slice(left);
  pre.extend_from_slice(right);
  *blake3::hash(&pre).as_bytes()
}

struct Identity {
  allowed: Vec<u8>,
  vk: Vec<u8>,
  program_vk: Vec<u8>,
}

enum Kind {
  Leaf(PathBuf),
  Join(usize, usize),
}

struct Node {
  name: String,
  dir: PathBuf,
  kind: Kind,
  parent: Option<usize>,
  done: bool,
  /// The record measured when this run executed the node.
  record: Option<usize>,
}

/// Leaves, then adjacent joins level by level; an odd last node is carried
/// up. The last node is the top.
fn tree(work: &Path, programs: &Path, n: usize) -> Vec<Node> {
  let mut nodes: Vec<Node> = (0..n)
    .map(|i| Node {
      name: format!("L0-{i:03}"),
      dir: work.join(format!("L0-{i:03}")),
      kind: Kind::Leaf(programs.join(format!("step-{i:03}"))),
      parent: None,
      done: false,
      record: None,
    })
    .collect();
  let mut level: Vec<usize> = (0..n).collect();
  let mut depth = 0;
  while level.len() > 1 {
    depth += 1;
    let mut next = Vec::new();
    for (k, pair) in level.chunks_exact(2).enumerate() {
      let id = nodes.len();
      let name = format!("L{depth}-{k:03}");
      nodes[pair[0]].parent = Some(id);
      nodes[pair[1]].parent = Some(id);
      nodes.push(Node {
        dir: work.join(&name),
        name,
        kind: Kind::Join(pair[0], pair[1]),
        parent: None,
        done: false,
        record: None,
      });
      next.push(id);
    }
    if level.len() % 2 == 1 {
      next.push(*level.last().unwrap());
    }
    level = next;
  }
  nodes
}

/// The node's input streams and its output claim, as `aiur_exec` builds them.
fn node_streams(id: &Identity, nodes: &[Node], node: usize) -> R<(Vec<Stream>, Vec<u8>)> {
  match &nodes[node].kind {
    Kind::Leaf(program) => {
      if fs::read(program.join("root-vk.bin"))? != id.program_vk {
        return Err("the program proof is under another key".into());
      }
      let claims = fs::read(program.join("root-claims.bin"))?;
      let claim = decode_one_claim(&claims)?;
      if claim.len() != 2 + 2 * MODEL_WORDS + DATA_WORDS {
        return Err("program claim has the wrong length".into());
      }
      let bytes = |w: &[u64]| w.iter().flat_map(|v| v.to_le_bytes()).collect::<Vec<u8>>();
      let m0 = &claim[2..2 + MODEL_WORDS];
      let data = &claim[2 + MODEL_WORDS..2 + MODEL_WORDS + DATA_WORDS];
      let m1 = &claim[2 + MODEL_WORDS + DATA_WORDS..];
      let out = out_claim(
        1,
        blake3::hash(&bytes(m0)).as_bytes(),
        blake3::hash(&bytes(m1)).as_bytes(),
        blake3::hash(&bytes(data)).as_bytes(),
      );
      let streams = vec![
        stream(3, vec![0], &id.allowed),
        stream(6, vec![0], &[0]),
        stream(1, vec![0], &id.program_vk),
        stream(0, vec![0], &fs::read(program.join("root-proof.bin"))?),
        stream(2, vec![0], &claims),
        stream(2, vec![2], &out),
      ];
      Ok((streams, out))
    },
    Kind::Join(l, r) => {
      let (left, right) = (&nodes[*l].dir, &nodes[*r].dir);
      let (lo, ro) = (fs::read(left.join("out.bin"))?, fs::read(right.join("out.bin"))?);
      let (lc, lf, ll, ld) = parse_out(&lo)?;
      let (rc, rf, rl, rd) = parse_out(&ro)?;
      if ll != rf {
        return Err("the chains do not meet".into());
      }
      let out = out_claim(lc + rc, &lf, &rl, &node_hash(&ld, &rd));
      let streams = vec![
        stream(3, vec![0], &id.allowed),
        stream(6, vec![0], &[1]),
        stream(1, vec![1], &id.vk),
        stream(0, vec![0], &fs::read(left.join("proof.bin"))?),
        stream(2, vec![0], &fs::read(left.join("claims.bin"))?),
        stream(0, vec![1], &fs::read(right.join("proof.bin"))?),
        stream(2, vec![1], &fs::read(right.join("claims.bin"))?),
        stream(2, vec![2], &out),
        stream(4, digest_words(&lo), &lo),
        stream(4, digest_words(&ro), &ro),
      ];
      Ok((streams, out))
    },
  }
}

/// One resident prover on one device, and the threads that build its next
/// trace shard while it proves the current one.
struct Lane {
  prover: Prover,
  feed: ShardFeed,
  device: i32,
}

struct Context {
  program: &'static CheckedProgram<F>,
  package_digest: String,
  identity: Identity,
  lanes: Vec<Lane>,
  workspace: usize,
}

impl Context {
  fn args(&self, out: &[u8]) -> R<Vec<Element>> {
    let mut args = digest_words(&self.identity.allowed);
    args.extend(digest_words(out));
    Ok(self.program.field().decode(&args)?)
  }

  fn options(&self, lane: &Lane) -> planning::Options {
    planning::Options {
      device: Some(lane.device),
      max_ram_bytes: Some(self.workspace as u64),
      ..Default::default()
    }
  }

  /// Verifies a finished node directory against its output claim.
  fn verify_dir(&self, dir: &Path) -> R<()> {
    let out = fs::read(dir.join("out.bin"))?;
    let args = self.args(&out)?;
    let bytes = fs::read(dir.join("proof.bin"))?;
    let proof = BatchProof::from_bytes(&bytes).map_err(|e| e.to_string())?;
    let prover = &self.lanes[0].prover;
    prover.verify_batch(ENTRY, &args, &[], &proof)?;
    let claim: Vec<u64> =
      prover.claim(ENTRY, &args, &[])?.iter().map(|v| v.as_canonical_u64()).collect();
    if fs::read(dir.join("claims.bin"))? != claims_bytes(&claim) {
      return Err(format!("{}: claims.bin is not the proof's claim", dir.display()).into());
    }
    Ok(())
  }
}

/// An executed node waiting for a lane.
struct Job {
  node: usize,
  dir: PathBuf,
  name: String,
  out: Vec<u8>,
  prepared: HostPrepared<F>,
  reservation: RecordReservation,
  record_bytes: usize,
  predicted_bytes: usize,
  execution_seconds: f64,
  executed_at: Instant,
}

enum Event {
  Executed { node: usize, record_bytes: usize },
  Proved { node: usize },
  Requeue { node: usize },
  Failed { node: usize, error: String },
}

/// Executes `node` under `reservation` and prepares its record on the host.
fn execute(
  ctx: &Context,
  node: usize,
  name: String,
  dir: PathBuf,
  streams: Vec<Stream>,
  out: Vec<u8>,
  reservation: RecordReservation,
  predicted_bytes: usize,
) -> Result<Job, (bool, String)> {
  let other = |e: String| (false, e);
  let start = Instant::now();
  let args = ctx.args(&out).map_err(|e| other(e.to_string()))?;
  let hints = stark_verifier::prepare(ctx.program, &Streams(streams)).map_err(other)?;
  let record = hints.execute_reserved(ENTRY, args.clone(), &reservation).map_err(|e| {
    let cancelled = matches!(e.resource, Some(BudgetError::Cancelled));
    (cancelled, format!("execution failed: {e}"))
  })?;
  drop(hints);
  if !record.output.is_empty() {
    return Err(other("the aggregator returned a value".into()));
  }
  let execution_seconds = start.elapsed().as_secs_f64();
  let lane = &ctx.lanes[0];
  // Planning as the prover will decides device population before the host
  // part counts ranges; the prover plans again and recounts on a difference.
  let _ = lane.prover.plan_record(&record, &ctx.options(lane), 0);
  let prepared = lane.prover.prepare_host(record, ENTRY, &args).map_err(other)?;
  reservation.reserve(prepared.retained_bytes()).map_err(|e| other(e.to_string()))?;
  reservation.finish_execution();
  let record_bytes = reservation.bytes();
  Ok(Job {
    node,
    dir,
    name,
    out,
    prepared,
    reservation,
    record_bytes,
    predicted_bytes,
    execution_seconds,
    executed_at: Instant::now(),
  })
}

/// Proves jobs on `lane` until the queue closes.
fn prove_loop(
  ctx: &Context,
  lane: &Lane,
  jobs: &Mutex<mpsc::Receiver<Job>>,
  events: mpsc::Sender<Event>,
) {
  loop {
    let job = match jobs.lock().unwrap().recv() {
      Ok(job) => job,
      Err(_) => return,
    };
    let node = job.node;
    let event = match prove(ctx, lane, job) {
      Ok(()) => Event::Proved { node },
      Err(e) => Event::Failed { node, error: e.to_string() },
    };
    if events.send(event).is_err() {
      return;
    }
  }
}

fn prove(ctx: &Context, lane: &Lane, job: Job) -> R<()> {
  let Job {
    dir,
    name,
    out,
    prepared,
    reservation,
    record_bytes,
    predicted_bytes,
    execution_seconds,
    executed_at,
    ..
  } = job;
  let queued_seconds = executed_at.elapsed().as_secs_f64();
  let start = Instant::now();
  let batch = lane.prover.plan_record(prepared.record(), &ctx.options(lane), 0)?;
  if !batch.fits {
    return Err(format!(
      "{name}: no trace-shard plan fits the {}-byte lane workspace (generation peak {}, proving peak {})",
      ctx.workspace, batch.generation_peak_bytes, batch.proving_peak_bytes
    )
    .into());
  }
  let layout = batch.layout.as_ref().ok_or("the proving plan has no incremental layout")?;
  let run = lane.prover.prove_prepared(
    &prepared,
    &[],
    layout,
    batch.retention(),
    batch.pipelined.then_some(&lane.feed),
  )?;
  let prove_seconds = start.elapsed().as_secs_f64();
  let args = prepared.args().to_vec();
  drop(prepared);
  drop(reservation);
  let start = Instant::now();
  lane.prover.verify_batch(ENTRY, &args, &[], &run.proof)?;
  let verify_seconds = start.elapsed().as_secs_f64();
  let claim: Vec<u64> =
    lane.prover.claim(ENTRY, &args, &[])?.iter().map(|v| v.as_canonical_u64()).collect();
  let raw = run.proof.to_bytes().map_err(|e| e.to_string())?;
  let partial = dir.with_extension("partial");
  let _ = fs::remove_dir_all(&partial);
  fs::create_dir_all(&partial)?;
  fs::write(partial.join("claims.bin"), claims_bytes(&claim))?;
  fs::write(partial.join("out.bin"), &out)?;
  let report = json!({
    "node": name,
    "package_blake3": ctx.package_digest,
    "prover": "aiur_exec_tree: resident device prover, planned trace shards, streamed",
    "device": lane.device,
    "execution_seconds": execution_seconds,
    "record_bytes": record_bytes,
    "predicted_record_bytes": predicted_bytes,
    "queued_seconds": queued_seconds,
    "prove_seconds": prove_seconds,
    "trace_seconds": run.trace_seconds,
    "proving_seconds": run.proving_seconds,
    "population_stall_seconds": run.population.stall_seconds,
    "pipelined": run.population.pipelined,
    "trace_shards": run.proof.proofs.len(),
    "shard_cells": batch.shard_cells,
    "planned_device_peak_bytes": batch.device_peak_bytes,
    "planned_host_peak_bytes": batch.proving_peak_bytes,
    "verify_seconds": verify_seconds,
    "proof_bytes": raw.len(),
    "process_peak_rss_bytes": planning::peak_resident_memory(),
  });
  fs::write(partial.join("report.json"), serde_json::to_vec_pretty(&report)?)?;
  fs::write(partial.join("proof.bin"), &raw)?;
  let _ = fs::remove_dir_all(&dir);
  fs::rename(&partial, &dir)?;
  eprintln!("[tree] proved {report}");
  Ok(())
}

fn flag<T: std::str::FromStr>(args: &[String], name: &str) -> R<Option<T>> {
  match args.iter().position(|a| a == name) {
    None => Ok(None),
    Some(i) => {
      let value = args.get(i + 1).ok_or(format!("{name} needs a value"))?;
      Ok(Some(value.parse().map_err(|_| format!("{name}: bad value {value}"))?))
    },
  }
}

fn gib(bytes: usize) -> String {
  format!("{:.1}", bytes as f64 / GIB as f64)
}

fn main() {
  match run() {
    Ok(code) => std::process::exit(code),
    Err(e) => {
      eprintln!("aiur_exec_tree: {e}");
      std::process::exit(1);
    },
  }
}

fn run() -> R<i32> {
  let args: Vec<String> = std::env::args().collect();
  let [_, ax, id_dir, programs, work, n, ..] = &args[..] else {
    return Err("usage: aiur_exec_tree AX.ixa IDENTITY_DIR PROGRAMS_DIR WORK_DIR N [--max-ram GIB] [--exec-jobs N] [--deadline SECONDS]".into());
  };
  let n: usize = n.parse()?;
  let max_ram: Option<usize> = flag(&args, "--max-ram")?;
  let exec_jobs: Option<usize> = flag(&args, "--exec-jobs")?;
  let deadline: Option<f64> = flag(&args, "--deadline")?;
  let begun = Instant::now();
  let (work, programs, id_dir) = (Path::new(work), Path::new(programs), Path::new(id_dir));
  fs::create_dir_all(work)?;

  let (package, digest) = Package::load(ax.as_ref())?;
  let (program, trace) = package.traced()?;
  let mut program = program.check_field::<Val>()?;
  program.track_depth(&trace)?;
  let program: &'static CheckedProgram<F> = Box::leak(Box::new(program));
  let plan: &'static TracePlan<'static, F> = Box::leak(Box::new(TracePlan::new(program, trace)?));
  let identity = Identity {
    allowed: fs::read(id_dir.join("allowed.bin"))?,
    vk: fs::read(id_dir.join("vk.bin"))?,
    program_vk: fs::read(id_dir.join("program-vk.bin"))?,
  };
  let gpus = planning::gpu_count();
  if gpus == 0 {
    return Err("no visible GPU in this build or host".into());
  }
  let first = match std::env::var("MULTI_STARK_CUDA_DEVICE") {
    Ok(v) => v.parse::<i32>()?,
    Err(_) => 0,
  };
  let lanes = (0..gpus)
    .map(|i| -> R<Lane> {
      let device = first + i as i32;
      let prover = Backend::for_batch_on_device(plan, Parameters::default(), Some(device))?;
      if prover.verifying_key_bytes()? != identity.vk {
        return Err("the aggregator's key differs from the identity's vk.bin".into());
      }
      Ok(Lane { prover, feed: ShardFeed::matching_current()?, device })
    })
    .collect::<R<Vec<_>>>()?;

  let cells = planning::configured_cells()? as usize;
  // The lane workspace of the aggregate controller (`lanes::cell_workspace`).
  let workspace = (cells * 16 + (256 << 20)) * 43 / 40;
  let limit = match max_ram {
    Some(g) => g * GIB,
    None => planning::default_budget().ok_or("cannot read MemTotal; pass --max-ram")? as usize,
  };
  let resident = planning::resident_memory() as usize;
  let records = limit
    .checked_sub(workspace * gpus + resident)
    .filter(|&r| r > 0)
    .ok_or("the host budget cannot hold the lanes' workspaces")?;
  let held = EXECUTIONS_PER_GPU * gpus + 2 * gpus;
  let share = (limit - workspace * gpus) / held;
  let share = share.min(records);
  let record_max = match std::env::var("AIUR_RECORD_MAX_BYTES") {
    Ok(v) => v.parse::<usize>()?,
    Err(_) => DEFAULT_RECORD_MAX_BYTES,
  };
  let pool = RecordPool::new(records, share).with_record_limit(record_max).with_buffer(share);
  let cores = std::thread::available_parallelism().map_or(1, usize::from);
  let executors = exec_jobs.unwrap_or(cores).max(1);
  eprintln!(
    "[resources] budget {} GiB ({}), {gpus} GPU lane(s), cells {cells}, workspace {} GiB/lane, resident {} GiB, record pool {} GiB, {held} records held, share {} GiB, record ceiling {} GiB, {executors} executor threads",
    gib(limit),
    if max_ram.is_some() { "--max-ram" } else { "MemTotal less 20%" },
    gib(workspace),
    gib(resident),
    gib(records),
    gib(share),
    gib(record_max.min(records)),
  );
  let ctx = Context { program, package_digest: digest.to_string(), identity, lanes, workspace };

  let mut nodes = tree(work, programs, n);
  let mut reused = 0;
  let start = Instant::now();
  for node in nodes.iter_mut() {
    if node.dir.join("proof.bin").exists() {
      ctx.verify_dir(&node.dir).map_err(|e| format!("{}: {e}", node.name))?;
      node.done = true;
      reused += 1;
    }
  }
  eprintln!(
    "[tree] {} nodes, {reused} reused and verified in {:.1}s",
    nodes.len(),
    start.elapsed().as_secs_f64()
  );
  let top = nodes.len() - 1;
  let ready_now = |nodes: &[Node], i: usize| {
    !nodes[i].done
      && match nodes[i].kind {
        Kind::Leaf(_) => true,
        Kind::Join(l, r) => nodes[l].done && nodes[r].done,
      }
  };
  // Joins first, deepest last-ready order otherwise.
  let mut ready: VecDeque<usize> =
    (0..nodes.len()).filter(|&i| ready_now(&nodes, i)).collect();
  ready.make_contiguous().sort_by_key(|&i| matches!(nodes[i].kind, Kind::Leaf(_)));

  let (job_tx, job_rx) = mpsc::sync_channel::<Job>(gpus);
  let job_rx = Mutex::new(job_rx);
  let (event_tx, events) = mpsc::channel::<Event>();
  let mut failures = Vec::new();
  let mut stopped = false;
  let mut proved = 0usize;
  let (mut executing, mut awaiting_proof, mut peak_executing) = (0usize, 0usize, 0usize);
  let mut largest: Option<usize> = None;
  let mut measured: Vec<(usize, usize)> = Vec::new();
  std::thread::scope(|scope| -> R<()> {
    for lane in &ctx.lanes {
      let (ctx, jobs, events) = (&ctx, &job_rx, event_tx.clone());
      scope.spawn(move || prove_loop(ctx, lane, jobs, events));
    }
    loop {
      if deadline.is_some_and(|d| begun.elapsed().as_secs_f64() > d) && !stopped {
        eprintln!("[tree] deadline reached; finishing started work");
        stopped = true;
      }
      while !stopped && executing < executors {
        let Some(&node) = ready.front() else { break };
        let predicted = match nodes[node].kind {
          Kind::Join(l, r) => match (nodes[l].record, nodes[r].record) {
            (Some(a), Some(b)) => a.max(b),
            _ => largest.unwrap_or(DEFAULT_RECORD_BYTES),
          },
          Kind::Leaf(_) => largest.unwrap_or(DEFAULT_RECORD_BYTES),
        };
        let floor = executing < EXECUTIONS_PER_GPU * gpus;
        let Some(reservation) = pool.admit(predicted, floor)? else { break };
        ready.pop_front();
        let (streams, out) = match node_streams(&ctx.identity, &nodes, node) {
          Ok(x) => x,
          Err(e) => {
            failures.push(format!("{}: {e}", nodes[node].name));
            stopped = true;
            break;
          },
        };
        executing += 1;
        peak_executing = peak_executing.max(executing);
        eprintln!(
          "[tree] execute {} charged {} GiB ({} executing, {} awaiting proof, pool {} GiB used)",
          nodes[node].name,
          gib(predicted),
          executing,
          awaiting_proof,
          gib(pool.usage().used),
        );
        let (ctx, jobs, events) = (&ctx, job_tx.clone(), event_tx.clone());
        let (name, dir) = (nodes[node].name.clone(), nodes[node].dir.clone());
        scope.spawn(move || {
          let event = match execute(ctx, node, name, dir, streams, out, reservation, predicted) {
            Ok(job) => {
              let record_bytes = job.record_bytes;
              eprintln!(
                "[tree] executed {} in {:.1}s, record {} GiB",
                job.name,
                job.execution_seconds,
                gib(record_bytes)
              );
              // Reported before the queue takes the record, so a proving
              // failure always follows its execution's event.
              let _ = events.send(Event::Executed { node, record_bytes });
              match jobs.send(job) {
                Ok(()) => return,
                Err(_) => Event::Failed { node, error: "prover queue closed".into() },
              }
            },
            Err((true, _)) => Event::Requeue { node },
            Err((false, error)) => Event::Failed { node, error },
          };
          let _ = events.send(event);
        });
      }
      if executing == 0 && awaiting_proof == 0 && (stopped || ready.is_empty()) {
        break;
      }
      let event = match events.recv_timeout(Duration::from_millis(500)) {
        Ok(event) => event,
        Err(mpsc::RecvTimeoutError::Timeout) => continue,
        Err(e) => return Err(e.to_string().into()),
      };
      match event {
        Event::Executed { node, record_bytes } => {
          executing -= 1;
          awaiting_proof += 1;
          nodes[node].record = Some(record_bytes);
          largest = Some(largest.map_or(record_bytes, |l| l.max(record_bytes)));
          measured.push((node, record_bytes));
        },
        Event::Proved { node } => {
          awaiting_proof -= 1;
          proved += 1;
          nodes[node].done = true;
          if let Some(parent) = nodes[node].parent
            && ready_now(&nodes, parent)
          {
            ready.push_front(parent);
          }
        },
        Event::Requeue { node } => {
          executing -= 1;
          eprintln!("[tree] {} cancelled for memory contention; requeued", nodes[node].name);
          ready.push_back(node);
        },
        Event::Failed { node, error } => {
          if nodes[node].record.is_some() {
            awaiting_proof -= 1;
          } else {
            executing -= 1;
          }
          failures.push(format!("{}: {error}", nodes[node].name));
          stopped = true;
        },
      }
    }
    drop(job_tx);
    Ok(())
  })?;
  let stats = pool.stats();
  eprintln!(
    "[tree] {proved} proved this run in {:.1}s; at most {peak_executing} executions at once; pool peak {} GiB, {} waits ({:.0}s), {} freezes ({:.0}s), {} cancellations",
    begun.elapsed().as_secs_f64(),
    gib(stats.peak_reserved),
    stats.waits,
    stats.wait_time.as_secs_f64(),
    stats.freezes,
    stats.frozen_time.as_secs_f64(),
    stats.retries,
  );
  if !failures.is_empty() {
    return Err(failures.join("; ").into());
  }
  if nodes[top].done {
    println!("{}", nodes[top].dir.display());
    Ok(0)
  } else {
    Ok(75)
  }
}
