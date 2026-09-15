//! `ix prove --lanes N`: prove a partition on N GPUs in one process, one
//! resident worker per device, and fold the result to one root proof.
//!
//! Every worker owns its device for the life of the run: an IxVM prover
//! system and an aggregation prover system built on that device
//! ([`AiurSystem::on_device`]), a pool of `--exec-jobs` preparation
//! threads (CPU: a claim's execution and planning, or a join's advice and
//! execution), and one proving thread (GPU). A bounded hand-off of one
//! prepared item between them keeps each worker executing its next task
//! while it proves the current one, and bounds what a worker holds to
//! `--exec-jobs` executions, one prepared item and one proof.
//!
//! The scheduler on the calling thread holds the plan and one ready
//! queue. A claim is ready from the start; a join is ready when both its
//! children have proofs; the root is ready when its children have proofs
//! and every claim is done. Each event from a worker (an item prepared, a
//! preparation that failed, a proof finished) frees capacity, and the
//! scheduler refills every worker with a ready join first, then the next
//! claim, so joins bubble up while claims are still proving and the only
//! serial work left at the end is the chain from the last claim to the
//! root. Nothing is assigned ahead of time and nothing is spawned.
//!
//! Memory is enforced where it is consumed: every execution, a claim's, a
//! join's or the root's, runs under a record cap that is its equal share
//! of the record budget ([`aiur::execute::set_record_byte_cap`]); one that
//! reaches its share reruns alone on a drained worker under the whole
//! budget, and one that fails even alone stops the run naming itself. Every proof is persisted
//! as it lands (claims to the store and the shard-proof index, joins to
//! the aggregate cache), so rerunning the same command resumes from what
//! was persisted; the persisted artifacts are not the coordination path.

use std::collections::VecDeque;
use std::sync::{Mutex, mpsc};
use std::time::Instant;

use aiur::execute::set_record_byte_cap;
use aiur::synthesis::ShardRetention as Retention;
use ixvm_codegen::aiur_ixvm_runner::execute_ixvm;
use ixvm_codegen::aiur_ixvm_witness::build_shard_check_env_witness;

use super::*;

pub struct Config {
  pub lanes: usize,
  /// The host budget of one worker, bytes; 0 detects (against the whole
  /// box, which is wrong beside other workers, so the run warns).
  pub max_ram_bytes: usize,
  /// Preparation threads per worker: claim executions ahead of the prover.
  pub exec_jobs: usize,
  pub structural_above: usize,
  pub cache_fri_bytes: Vec<u8>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Work {
  Claim(usize),
  Join(usize),
  Root,
}

/// What a worker's preparation threads receive.
enum Prep {
  Claim { shard: usize, cap: Option<usize> },
  Join { slot: usize, children: Vec<Arc<Slot>>, cap: Option<usize> },
  Root { slot: usize, children: Vec<Arc<Slot>>, cap: Option<usize> },
}

/// What a preparation thread hands its worker's proving thread.
enum Item {
  Claim {
    shard: usize,
    claim: Claim,
    claim_bytes: Vec<u8>,
    prepared: Box<PreparedProve>,
  },
  Join {
    slot: usize,
    staged: Box<StagedSlot>,
  },
  Root {
    slot: usize,
    staged: Box<StagedSlot>,
  },
}

/// What workers report to the scheduler.
enum Event {
  Prepared {
    worker: usize,
  },
  PrepFailed {
    worker: usize,
    work: Work,
    over_budget: Option<(usize, usize)>,
    error: String,
  },
  Proven {
    worker: usize,
    work: Work,
    result: Result<Arc<Slot>, String>,
  },
  RootProven {
    worker: usize,
    result: Result<String, String>,
  },
}

struct WorkerHandle {
  prep: mpsc::Sender<Prep>,
  preparing: usize,
  waiting: usize,
  /// An over-share unit of work is rerunning alone here; nothing else is
  /// sent until it is proven.
  alone: bool,
}

/// The shard-proof index entry of a claim, written like Stage 1 writes it.
fn index_claim(
  index_dir: &Path,
  claim_bytes: &[u8],
  address: &Address,
) -> Result<(), String> {
  fs::create_dir_all(index_dir)
    .map_err(|error| format!("create {}: {error}", index_dir.display()))?;
  let digest = Address::hash(claim_bytes);
  let temporary =
    index_dir.join(format!("{}.tmp.{}", digest.hex(), std::process::id()));
  fs::write(&temporary, format!("{}\n", address.hex()))
    .and_then(|()| fs::rename(&temporary, index_dir.join(digest.hex())))
    .map_err(|error| format!("shard-proof index: {error}"))
}

/// A claim's proof from the shard-proof index, verified natively against
/// the claim this run expects, as a raw leaf slot; `None` when absent or
/// not acceptable, never an error.
fn resume_leaf(
  ctx: ProveContext<'_>,
  index_dir: &Path,
  slot_index: usize,
  shard: usize,
) -> Option<Slot> {
  let spec = &ctx.specs[slot_index];
  let statement = &ctx.prepared[shard].statement;
  let digest = Address::hash(&statement.claim_bytes);
  let raw = fs::read_to_string(index_dir.join(digest.hex())).ok()?;
  let address = Address::from_hex(raw.trim())?;
  let bytes = read_store(ctx.store_dir, &address).ok()?;
  if Address::hash(&bytes) != address {
    return None;
  }
  let wrapper = decode_wrapper(&bytes).ok()?;
  if wrapper.claim != statement.claim {
    return None;
  }
  let proof = AiurProof::from_bytes(&wrapper.proof).ok()?;
  let inner = inner_claim(ctx.verify_idx, &statement.claim_bytes);
  ctx.ixvm_system.verify(&inner, &proof).ok()?;
  Some(Slot {
    kind: ChildKind::Ixvm,
    statement: spec.statement.clone(),
    outer_claim: inner.clone(),
    proof,
    proof_address: Some(address),
    claims_bytes: serialize_claims(&[&inner]),
  })
}

/// One worker's preparation thread: takes tasks from the worker's shared
/// queue, does their CPU half, and hands the result to the proving thread.
fn prepare_loop(
  ctx: ProveContext<'_>,
  worker: usize,
  env: &ixon::Env,
  owned: &[Vec<Address>],
  max_ram_bytes: Option<usize>,
  prep: &Mutex<mpsc::Receiver<Prep>>,
  items: &mpsc::SyncSender<Item>,
  events: &mpsc::Sender<Event>,
) {
  loop {
    let task = {
      let Ok(guard) = prep.lock() else { return };
      guard.recv()
    };
    let Ok(task) = task else { return };
    match task {
      Prep::Claim { shard, cap } => {
        set_record_byte_cap(cap);
        let outcome = (|| -> Result<Item, (Option<(usize, usize)>, String)> {
          let (claim, input, mut io) =
            build_shard_check_env_witness(env, &owned[shard])
              .map_err(|e| (None, format!("witness build: {e}")))?;
          let prepared = ctx.ixvm_system.prepare_ixvm_within_budget(
            ctx.verify_idx,
            &input,
            &mut io,
            |toplevel, fun_idx, input, io_buffer| {
              execute_ixvm(toplevel, fun_idx, input, io_buffer)
            },
            max_ram_bytes,
            true,
            Some(Retention::Regenerate),
          );
          let prepared = match prepared {
            Ok(prepared) => prepared,
            Err(GatedProve::Failed(
              aiur::execute::ExecError::RecordBudgetExceeded { bytes, cap },
            )) => return Err((Some((bytes, cap)), String::new())),
            Err(GatedProve::Failed(error)) => {
              return Err((None, format!("execution failed: {error}")));
            },
            Err(GatedProve::Split { peak, .. }) => {
              return Err((
                None,
                format!(
                  "no trace-shard count fits the budget (whole-execution peak {peak} B) — raise --max-ram"
                ),
              ));
            },
            Err(_) => {
              return Err((None, "execution did not prepare a proof".into()));
            },
          };
          let mut claim_bytes = Vec::new();
          claim.put(&mut claim_bytes);
          Ok(Item::Claim {
            shard,
            claim,
            claim_bytes,
            prepared: Box::new(prepared),
          })
        })();
        set_record_byte_cap(None);
        match outcome {
          Ok(item) => {
            // Reported before the prover can see the item, so its proof
            // never precedes this in the scheduler's event order.
            let _ = events.send(Event::Prepared { worker });
            if items.send(item).is_err() {
              return;
            }
          },
          Err((over_budget, error)) => {
            let _ = events.send(Event::PrepFailed {
              worker,
              work: Work::Claim(shard),
              over_budget,
              error,
            });
          },
        }
      },
      Prep::Join { slot, children, cap }
      | Prep::Root { slot, children, cap } => {
        let is_root =
          matches!(ctx.specs.get(slot).map(|s| s.op), Some(PlanOp::Join(..)))
            && slot + 1 == ctx.specs.len();
        set_record_byte_cap(cap);
        let outcome = prepare_slot(ctx, slot, &children);
        set_record_byte_cap(None);
        match outcome {
          Ok(staged) => {
            let item = if is_root {
              Item::Root { slot, staged: Box::new(staged) }
            } else {
              Item::Join { slot, staged: Box::new(staged) }
            };
            let _ = events.send(Event::Prepared { worker });
            if items.send(item).is_err() {
              return;
            }
          },
          Err(failure) => {
            let (over_budget, error) = match failure {
              PrepareFailure::OverRecordCap { bytes, cap } => {
                (Some((bytes, cap)), String::new())
              },
              PrepareFailure::Other(error) => (None, error),
            };
            let _ = events.send(Event::PrepFailed {
              worker,
              work: if is_root { Work::Root } else { Work::Join(slot) },
              over_budget,
              error,
            });
          },
        }
      },
    }
  }
}

/// One worker's proving thread: proves prepared items in the order they
/// arrive, persists each proof, and reports it.
fn prove_loop(
  ctx: ProveContext<'_>,
  worker: usize,
  prepared_run: &PreparedRun,
  leaf_slot: &[usize],
  index_dir: &Path,
  items: mpsc::Receiver<Item>,
  events: &mpsc::Sender<Event>,
) {
  for item in items {
    match item {
      Item::Claim { shard, claim, claim_bytes, prepared } => {
        let result = (|| -> Result<Arc<Slot>, String> {
          let (_, proof, _) = ctx.ixvm_system.prove_prepared(*prepared);
          let proof_bytes = proof
            .to_bytes()
            .map_err(|e| format!("proof serialization: {e}"))?;
          let wrapper = IxonProof::new(claim, proof_bytes);
          let mut wrapper_bytes = Vec::new();
          wrapper.put(&mut wrapper_bytes);
          write_store(ctx.store_dir, &claim_bytes)?;
          let address = write_store(ctx.store_dir, &wrapper_bytes)?;
          index_claim(index_dir, &claim_bytes, &address)?;
          let inner = inner_claim(ctx.verify_idx, &claim_bytes);
          Ok(Arc::new(Slot {
            kind: ChildKind::Ixvm,
            statement: ctx.specs[leaf_slot[shard]].statement.clone(),
            outer_claim: inner.clone(),
            proof,
            proof_address: Some(address),
            claims_bytes: serialize_claims(&[&inner]),
          }))
        })();
        let _ = events.send(Event::Proven {
          worker,
          work: Work::Claim(shard),
          result,
        });
      },
      Item::Join { slot, staged } => {
        let result = finish_slot(ctx, slot, *staged);
        let _ =
          events.send(Event::Proven { worker, work: Work::Join(slot), result });
      },
      Item::Root { slot, staged } => {
        let result = (|| -> Result<String, String> {
          let root = finish_slot(ctx, slot, *staged)?;
          validate_root_statement(prepared_run, &root.statement)?;
          // Wrap until the final proof is a single trace shard.
          let mut wrapped: Option<AiurProof> = None;
          loop {
            let current = wrapped.as_ref().unwrap_or(&root.proof);
            let shards = current.preamble.headers.len();
            if shards <= 1 {
              break;
            }
            let next = wrap_root(ctx, &root, current)?;
            if next.preamble.headers.len() >= shards {
              break;
            }
            wrapped = Some(next);
          }
          let proof = wrapped.as_ref().unwrap_or(&root.proof);
          ctx.aggr_system.verify(&root.outer_claim, proof).map_err(
            |error| {
              format!("aggregate root proof failed verification: {error:?}")
            },
          )?;
          let address = match (&wrapped, &root.proof_address) {
            (None, Some(address)) => address.clone(),
            _ => persist_wrapper(ctx.store_dir, &root.statement, proof)?,
          };
          Ok(address.hex())
        })();
        let _ = events.send(Event::RootProven { worker, result });
      },
    }
  }
}

/// The whole run. Prints progress on stderr and returns the verified
/// root address.
/// The composed verdict: every claim proof the run holds, proved or
/// reused, verified natively against its claim, in parallel. Returns the
/// failures and the number of claims without a proof to verify: claims
/// retired under a cached join whose proof the index no longer holds,
/// which rest on that join's own native verification when it was loaded.
fn composed_verdict(
  ixvm: &AiurSystem,
  verify_idx: usize,
  prepared: &PreparedRun,
  leaves: &[Option<Arc<Slot>>],
) -> (Vec<String>, usize) {
  let failures = leaves
    .par_iter()
    .enumerate()
    .filter_map(|(shard, slot)| {
      let slot = slot.as_ref()?;
      let inner =
        inner_claim(verify_idx, &prepared.shards[shard].statement.claim_bytes);
      ixvm.verify(&inner, &slot.proof).err().map(|error| {
        format!(
          "claim {}: proof fails verification: {error:?}",
          prepared.shards[shard].original_id
        )
      })
    })
    .collect();
  (failures, leaves.iter().filter(|slot| slot.is_none()).count())
}

pub fn run(
  cfg: &Config,
  ixvm: &AiurSystem,
  aggr: &AiurSystem,
  env: &ixon::Env,
  manifest_path: &Path,
  verify_idx: usize,
  aggr_idx: usize,
) -> Result<String, String> {
  crate::profile::init();
  let say = |m: &str| eprintln!("[lanes] {m}");
  if cfg.cache_fri_bytes.len() != 40 {
    return Err("aggregate cache FRI serialization must be 40 bytes".into());
  }
  let started = Instant::now();
  let manifest_bytes = fs::read(manifest_path).map_err(|error| {
    format!("read manifest {}: {error}", manifest_path.display())
  })?;
  let manifest = ShardManifest::from_bytes(&manifest_bytes)
    .map_err(|error| format!("manifest parse failed: {error}"))?;
  let prepared = prepare_run(env, &manifest)?;
  let ixvm_vk = aiur::vk_codec::aiur_system_to_bytes(ixvm)
    .map_err(|error| format!("IxVM VK serialization failed: {error}"))?;
  let aggr_vk = aiur::vk_codec::aiur_system_to_bytes(aggr)
    .map_err(|error| format!("ixAggr VK serialization failed: {error}"))?;
  let allowed = allowed_blob(&ixvm_vk, verify_idx, &aggr_vk, aggr_idx);
  let specs = build_specs(
    &prepared,
    verify_idx,
    aggr_idx,
    cfg.structural_above,
    true,
    &aggr_vk,
    &allowed,
    &cfg.cache_fri_bytes,
  )?;
  let count = specs.len();
  let root_slot = count.checked_sub(1).ok_or("empty plan")?;
  let PlanOp::Join(root_left, root_right) = specs[root_slot].op else {
    return Err("the manifest has one shard; there is nothing to join".into());
  };
  let shards = prepared.shards.len();
  let mut leaf_slot = vec![usize::MAX; shards];
  for (index, spec) in specs.iter().enumerate() {
    if let PlanOp::Leaf(shard) = spec.op {
      leaf_slot[shard] = index;
    }
  }
  let owned: Vec<Vec<Address>> = prepared
    .shards
    .iter()
    .map(|shard| {
      let mut leaves = Vec::new();
      shard.statement.subjects.collect_leaves(&mut leaves);
      leaves.sort_unstable();
      leaves
    })
    .collect();

  let home = std::env::var_os("HOME").ok_or("no HOME environment variable")?;
  let ix_root = PathBuf::from(home).join(".ix");
  let store_dir = ix_root.join("store");
  let cache_root = std::env::var_os("AIUR_LANES_CACHE_DIR")
    .map_or_else(|| ix_root.join("cache"), PathBuf::from);
  let cache_dir = cache_root.join("aggregate");
  let index_dir = cache_root.join("shard-proofs");
  fs::create_dir_all(&cache_dir)
    .map_err(|error| format!("create {}: {error}", cache_dir.display()))?;

  // Budgets, from first principles: each claim execution ahead gets an
  // equal share of the host budget less the prover's working set (two
  // shard witnesses at the cell budget plus staging) and the items a
  // worker may hold beside its executions (one prepared, one proving).
  let max_ram_bytes = if cfg.max_ram_bytes > 0 {
    Some(cfg.max_ram_bytes)
  } else {
    say("warning: no --max-ram; each worker budgets against the whole box");
    super::super::protocol::detected_ram_budget()
  };
  // Preparation threads per worker: the flag, or the worker's share of
  // the cores when it is 0.
  let exec_jobs = if cfg.exec_jobs == 0 {
    let cores = thread::available_parallelism().map_or(1, usize::from);
    (cores / cfg.lanes.max(1)).max(1)
  } else {
    cfg.exec_jobs
  };
  let cells = super::super::protocol::trace_shard_max_cells();
  let record_budget =
    max_ram_bytes.map(|b| super::super::protocol::record_budget(b, cells));
  let share = max_ram_bytes
    .map(|b| super::super::protocol::record_share(b, cells, exec_jobs + 2));
  if let (Some(budget), Some(share)) = (record_budget, share) {
    say(&format!(
      "record budget {} GiB per worker: {} GiB per execution with {exec_jobs} ahead; an execution over its share reruns alone",
      format_gib(budget),
      format_gib(share)
    ));
  }

  // A prover pair per device, sharing the bytecode of the systems the
  // CLI built. The verifying keys must not depend on the device: every
  // cache key and claim binding is derived from them.
  say(&format!("building {} resident workers", cfg.lanes));
  let systems: Vec<(AiurSystem, AiurSystem)> = (0..cfg.lanes)
    .map(|g| {
      let device =
        i32::try_from(g).map_err(|error| format!("lane {g}: {error}"))?;
      Ok((ixvm.on_device(device), aggr.on_device(device)))
    })
    .collect::<Result<_, String>>()?;
  for (g, (worker_ixvm, worker_aggr)) in systems.iter().enumerate() {
    let same =
      aiur::vk_codec::aiur_system_to_bytes(worker_ixvm).ok().as_deref()
        == Some(ixvm_vk.as_slice())
        && aiur::vk_codec::aiur_system_to_bytes(worker_aggr).ok().as_deref()
          == Some(aggr_vk.as_slice());
    if !same {
      return Err(format!(
        "the verifying key of the prover on device {g} differs from device 0's"
      ));
    }
  }

  let contexts: Vec<ProveContext<'_>> = systems
    .iter()
    .map(|(worker_ixvm, worker_aggr)| ProveContext {
      specs: &specs,
      prepared: &prepared.shards,
      proofs: None,
      owner_by_address: &prepared.owner_by_address,
      ixvm_system: worker_ixvm,
      aggr_system: worker_aggr,
      ixvm_vk: &ixvm_vk,
      aggr_vk: &aggr_vk,
      allowed: &allowed,
      verify_idx,
      aggr_idx,
      store_dir: &store_dir,
      cache_dir: Some(&cache_dir),
      reprove_slot: None,
      write_outputs: true,
      wrap_budget: max_ram_bytes,
      range_width: 0,
      range_jobs: 1,
    })
    .collect();

  // Resume: cached joins from the root down retire their subtrees;
  // indexed claim proofs stand in for their claims.
  let mut slots: Vec<Option<Arc<Slot>>> = vec![None; count];
  let mut retired = vec![false; count];
  for index in (0..root_slot).rev() {
    let spec = &specs[index];
    if retired[index] || spec.kind != ChildKind::Aggr {
      continue;
    }
    let Some((proof, address)) = load_cached(contexts[0], index, spec) else {
      continue;
    };
    slots[index] = Some(Arc::new(Slot {
      kind: ChildKind::Aggr,
      statement: spec.statement.clone(),
      outer_claim: spec.outer_claim.clone(),
      proof,
      proof_address: Some(address),
      claims_bytes: serialize_claims(&[&spec.outer_claim]),
    }));
    let mut stack = match spec.op {
      PlanOp::Join(l, r) => vec![l, r],
      PlanOp::Leaf(_) => Vec::new(),
    };
    while let Some(slot) = stack.pop() {
      if retired[slot] {
        continue;
      }
      retired[slot] = true;
      if let PlanOp::Join(l, r) = specs[slot].op {
        stack.push(l);
        stack.push(r);
      }
    }
  }
  let mut claim_done = vec![false; shards];
  let resumed: Vec<Option<Slot>> = (0..shards)
    .into_par_iter()
    // A claim retired under a cached join is still loaded when the index
    // holds its proof, so the composed verdict can verify it independently.
    .map(|shard| resume_leaf(contexts[0], &index_dir, leaf_slot[shard], shard))
    .collect();
  let mut reused = 0usize;
  for (shard, slot) in resumed.into_iter().enumerate() {
    if let Some(slot) = slot {
      slots[leaf_slot[shard]] = Some(Arc::new(slot));
      claim_done[shard] = true;
      reused += 1;
    } else if retired[leaf_slot[shard]] {
      claim_done[shard] = true;
    }
  }
  let cached_joins = slots
    .iter()
    .enumerate()
    .filter(|(i, s)| {
      s.is_some() && *i != root_slot && !matches!(specs[*i].op, PlanOp::Leaf(_))
    })
    .count();
  say(&format!(
    "{shards} claims ({reused} reused from the index, {} retired under cached joins without an indexed proof), {} joins ({cached_joins} cached)",
    claim_done.iter().filter(|d| **d).count() - reused,
    count - shards
  ));

  let (events_tx, events_rx) = mpsc::channel::<Event>();
  let (result, unproven) = thread::scope(
    |scope| -> Result<(String, usize), String> {
      let mut workers: Vec<WorkerHandle> = Vec::with_capacity(cfg.lanes);
      for (g, &ctx) in contexts.iter().enumerate() {
        let (prep_tx, prep_rx) = mpsc::channel::<Prep>();
        let prep_rx = Arc::new(Mutex::new(prep_rx));
        let (item_tx, item_rx) = mpsc::sync_channel::<Item>(1);
        for _ in 0..exec_jobs {
          let prep_rx = Arc::clone(&prep_rx);
          let item_tx = item_tx.clone();
          let events = events_tx.clone();
          let (env, owned) = (env, &owned);
          scope.spawn(move || {
            prepare_loop(
              ctx,
              g,
              env,
              owned,
              max_ram_bytes,
              &prep_rx,
              &item_tx,
              &events,
            );
          });
        }
        drop(item_tx);
        let events = events_tx.clone();
        let (prepared_run, leaf_slot, index_dir) =
          (&prepared, &leaf_slot, &index_dir);
        scope.spawn(move || {
          prove_loop(
            ctx,
            g,
            prepared_run,
            leaf_slot,
            index_dir,
            item_rx,
            &events,
          );
        });
        workers.push(WorkerHandle {
          prep: prep_tx,
          preparing: 0,
          waiting: 0,
          alone: false,
        });
      }
      drop(events_tx);

      let mut claim_queue: VecDeque<usize> =
        (0..shards).filter(|&s| !claim_done[s]).collect();
      let mut alone_queue: VecDeque<Work> = VecDeque::new();
      let work_name = |work: Work| match work {
        Work::Claim(shard) => {
          format!("claim {}", prepared.shards[shard].original_id)
        },
        Work::Join(slot) => format!("join {slot}"),
        Work::Root => "root".to_string(),
      };
      let mut dispatched: FxHashSet<usize> = FxHashSet::default();
      let mut root_dispatched = false;
      let mut root_address: Option<String> = None;
      let mut failure: Option<String> = None;
      let mut verdict: Option<
        thread::ScopedJoinHandle<'_, (Vec<String>, usize)>,
      > = None;
      let ready_join = |slots: &[Option<Arc<Slot>>],
                        dispatched: &FxHashSet<usize>| {
        (0..root_slot).find(|&index| {
          !retired[index]
            && slots[index].is_none()
            && !dispatched.contains(&index)
            && match specs[index].op {
              PlanOp::Join(l, r) => slots[l].is_some() && slots[r].is_some(),
              PlanOp::Leaf(_) => false,
            }
        })
      };
      loop {
        if failure.is_none() {
          // An over-share claim reruns alone on worker 0 once it drains; the
          // other workers carry on, and worker 0 takes no new claims meanwhile.
          let drain = !alone_queue.is_empty();
          if drain {
            let worker = &mut workers[0];
            if !worker.alone && worker.preparing == 0 && worker.waiting == 0 {
              let work = alone_queue.pop_front().expect("nonempty");
              say(&format!(
                "worker 0: {} rerunning alone under the whole record budget",
                work_name(work)
              ));
              let children_of = |slot: usize| {
                let PlanOp::Join(l, r) = specs[slot].op else { unreachable!() };
                vec![slots[l].clone().unwrap(), slots[r].clone().unwrap()]
              };
              let prep = match work {
                Work::Claim(shard) => Prep::Claim { shard, cap: record_budget },
                Work::Join(slot) => Prep::Join {
                  slot,
                  children: children_of(slot),
                  cap: record_budget,
                },
                Work::Root => Prep::Root {
                  slot: root_slot,
                  children: children_of(root_slot),
                  cap: record_budget,
                },
              };
              let _ = worker.prep.send(prep);
              worker.preparing += 1;
              worker.alone = true;
            }
          }
          // Each unit of work goes to the least-loaded worker with a free
          // preparation slot, joins before the root before claims, so a
          // ready join lands on an idle device rather than queueing behind
          // the claims of whichever worker comes first.
          loop {
            let least_loaded = |exclude_draining: bool| {
              workers
                .iter()
                .enumerate()
                .filter(|(g, w)| {
                  !w.alone
                    && w.preparing < exec_jobs
                    && !(exclude_draining && drain && *g == 0)
                })
                .min_by_key(|(g, w)| (w.preparing + w.waiting, *g))
                .map(|(g, _)| g)
            };
            if let Some(index) = ready_join(&slots, &dispatched) {
              let Some(g) = least_loaded(false) else { break };
              let PlanOp::Join(l, r) = specs[index].op else { unreachable!() };
              let children =
                vec![slots[l].clone().unwrap(), slots[r].clone().unwrap()];
              let _ = workers[g].prep.send(Prep::Join {
                slot: index,
                children,
                cap: share,
              });
              dispatched.insert(index);
              workers[g].preparing += 1;
              continue;
            }
            if !root_dispatched
              && claim_done.iter().all(|d| *d)
              && slots[root_left].is_some()
              && slots[root_right].is_some()
            {
              let Some(g) = least_loaded(false) else { break };
              let children = vec![
                slots[root_left].clone().unwrap(),
                slots[root_right].clone().unwrap(),
              ];
              let _ = workers[g].prep.send(Prep::Root {
                slot: root_slot,
                children,
                cap: share,
              });
              root_dispatched = true;
              workers[g].preparing += 1;
              say(&format!(
                "worker {g}: root at +{}s",
                started.elapsed().as_secs()
              ));
              // Every claim is done once the root is dispatched, so the
              // composed verdict (CPU) runs beside the root's wraps (GPU). A
              // claim retired under a cached join has a proof here only if
              // the index still holds it.
              let leaves: Vec<Option<Arc<Slot>>> =
                (0..shards).map(|s| slots[leaf_slot[s]].clone()).collect();
              let prepared_run = &prepared;
              verdict = Some(scope.spawn(move || {
                composed_verdict(ixvm, verify_idx, prepared_run, &leaves)
              }));
              break;
            }
            let Some(&shard) = claim_queue.front() else { break };
            let Some(g) = least_loaded(true) else { break };
            claim_queue.pop_front();
            let _ = workers[g].prep.send(Prep::Claim { shard, cap: share });
            workers[g].preparing += 1;
          }
        }
        if root_address.is_some() {
          break;
        }
        let busy: usize = workers.iter().map(|w| w.preparing + w.waiting).sum();
        if failure.is_some() && busy == 0 {
          break;
        }
        if busy == 0 {
          failure =
            Some("scheduler stalled: nothing runs and nothing is ready".into());
          break;
        }
        let event = events_rx
          .recv()
          .map_err(|error| format!("worker channel closed: {error}"))?;
        match event {
          Event::Prepared { worker } => {
            workers[worker].preparing -= 1;
            workers[worker].waiting += 1;
          },
          Event::PrepFailed { worker, work, over_budget, error } => {
            workers[worker].preparing -= 1;
            let was_alone =
              std::mem::replace(&mut workers[worker].alone, false);
            match over_budget {
              Some((bytes, cap)) if !was_alone => {
                say(&format!(
                  "worker {worker}: {} reached {bytes} B, over its {cap} B share; queued to rerun alone",
                  work_name(work)
                ));
                alone_queue.push_back(work);
              },
              Some((bytes, cap)) => {
                let remedy = match work {
                  Work::Claim(_) => "cut this shard finer or raise --max-ram",
                  Work::Join(_) | Work::Root => "raise --max-ram",
                };
                failure = Some(format!(
                  "{}: record reached {bytes} B, over the whole record budget of {cap} B even alone; {remedy}",
                  work_name(work)
                ));
              },
              None => failure = Some(format!("{}: {error}", work_name(work))),
            }
          },
          Event::Proven { worker, work, result } => {
            workers[worker].waiting -= 1;
            workers[worker].alone = false;
            match (work, result) {
              (Work::Claim(shard), Ok(slot)) => {
                slots[leaf_slot[shard]] = Some(slot);
                claim_done[shard] = true;
                say(&format!(
                  "worker {worker}: claim {} proven at +{}s ({} left)",
                  prepared.shards[shard].original_id,
                  started.elapsed().as_secs(),
                  claim_done.iter().filter(|d| !**d).count()
                ));
              },
              (Work::Join(slot), Ok(proof)) => {
                slots[slot] = Some(proof);
                say(&format!(
                  "worker {worker}: join {slot} published at +{}s",
                  started.elapsed().as_secs()
                ));
              },
              (Work::Claim(shard), Err(error)) => {
                failure = Some(format!(
                  "claim {}: {error}",
                  prepared.shards[shard].original_id
                ));
              },
              (Work::Join(slot), Err(error)) => {
                failure = Some(format!("join {slot}: {error}"))
              },
              (Work::Root, _) => {
                unreachable!("the root reports through RootProven")
              },
            }
          },
          Event::RootProven { worker, result } => {
            workers[worker].waiting -= 1;
            match result {
              Ok(address) => {
                say(&format!(
                  "worker {worker}: root proven at +{}s",
                  started.elapsed().as_secs()
                ));
                root_address = Some(address);
              },
              Err(error) => failure = Some(format!("root: {error}")),
            }
          },
        }
      }
      // Closing the task queues ends the workers.
      workers.clear();
      if let Some(error) = failure {
        return Err(format!(
          "{error}; rerun the same command to resume from what was persisted"
        ));
      }
      let root = root_address.ok_or_else(|| "no root proof".to_string())?;
      let handle = verdict.ok_or_else(|| {
        "the root was proven before the composed verdict started".to_string()
      })?;
      let (failures, unproven) = handle.join().map_err(|payload| {
        format!("composed verdict thread panicked: {}", panic_text(&payload))
      })?;
      if failures.is_empty() {
        Ok((root, unproven))
      } else {
        Err(failures.join("; "))
      }
    },
  )?;

  let coverage = if unproven == 0 {
    String::new()
  } else {
    format!(
      " ({unproven} claims retired under verified cached joins have no indexed proof)"
    )
  };
  say(&format!(
    "root {result} verified; composed verdict OK{coverage}; end to end {}s",
    started.elapsed().as_secs()
  ));
  Ok(result)
}

/// `AiurSystem.proveLanes`: the whole multi-device run.
#[unsafe(no_mangle)]
extern "C" fn rs_aiur_prove_lanes(
  ixvm_system: LeanExternal<AiurSystem, LeanBorrowed<'_>>,
  aggr_system: LeanExternal<AiurSystem, LeanBorrowed<'_>>,
  env_handle: LeanExternal<EnvHandle, LeanBorrowed<'_>>,
  manifest_path: LeanString<LeanBorrowed<'_>>,
  verify_idx: LeanNat<LeanBorrowed<'_>>,
  aggr_idx: LeanNat<LeanBorrowed<'_>>,
  lanes: LeanNat<LeanBorrowed<'_>>,
  max_ram_bytes: LeanNat<LeanBorrowed<'_>>,
  exec_jobs: LeanNat<LeanBorrowed<'_>>,
  structural_above: LeanNat<LeanBorrowed<'_>>,
  cache_fri_bytes: LeanByteArray<LeanBorrowed<'_>>,
) -> LeanExcept<LeanOwned> {
  let cfg = Config {
    lanes: lean_unbox_nat_as_usize(lanes.inner()),
    max_ram_bytes: lean_unbox_nat_as_usize(max_ram_bytes.inner()),
    exec_jobs: lean_unbox_nat_as_usize(exec_jobs.inner()),
    structural_above: lean_unbox_nat_as_usize(structural_above.inner()),
    cache_fri_bytes: cache_fri_bytes.as_bytes().to_vec(),
  };
  if cfg.lanes == 0 {
    return LeanExcept::error_string("at least one lane is required");
  }
  let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
    run(
      &cfg,
      ixvm_system.get(),
      aggr_system.get(),
      &env_handle.get().env,
      Path::new(manifest_path.as_str()),
      lean_unbox_nat_as_usize(verify_idx.inner()),
      lean_unbox_nat_as_usize(aggr_idx.inner()),
    )
  }));
  match result {
    Ok(Ok(root)) => LeanExcept::ok(LeanString::new(&root)),
    Ok(Err(error)) => LeanExcept::error_string(&error),
    Err(payload) => LeanExcept::error_string(&format!(
      "lane scheduler panicked: {}",
      panic_text(&payload)
    )),
  }
}
