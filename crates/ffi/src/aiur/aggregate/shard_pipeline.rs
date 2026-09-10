//! One proving consumer and at most one next execution in flight. Splits
//! are private balanced subtrees of flat joins: the published claim stays
//! byte-for-byte equal to the original manifest leaf.

use super::*;
use crate::aiur::protocol::decode_addr_lists;
use aiur::{
  bytecode::{FunIdx, Toplevel},
  execute::{ExecError, QueryRecord},
};
use ixvm_codegen::{
  aiur_ixvm_runner::execute_ixvm,
  aiur_ixvm_witness::build_shard_check_env_witness,
};
use lean_ffi::object::LeanIOResult;
use std::collections::VecDeque;

pub(super) type Executor = fn(
  &Toplevel,
  FunIdx,
  Vec<G>,
  &mut IOBuffer,
) -> Result<(QueryRecord, Vec<G>), ExecError>;

// Scheduling state, not a second prover API. Reuse the native executor's
// record/output and move the record into the existing prove_from_execution.
pub(super) struct Execution<'a> {
  system: &'a AiurSystem,
  fun_idx: usize,
  input: Vec<G>,
  io: IOBuffer,
  record: QueryRecord,
  output: Vec<G>,
}

impl<'a> Execution<'a> {
  pub(super) fn new(
    system: &'a AiurSystem,
    fun_idx: usize,
    input: Vec<G>,
    mut io: IOBuffer,
    executor: Executor,
  ) -> Result<Self, String> {
    let _span = tracing::info_span!("aiur/execute_ixvm").entered();
    let (record, output) =
      executor(system.toplevel(), fun_idx, input.clone(), &mut io)
        .map_err(|e| format!("native execution failed: {e:?}"))?;
    Ok(Self { system, fun_idx, input, io, record, output })
  }

  pub(super) fn peak(&self) -> usize {
    self.system.peak_prove_bytes(&self.record).peak
  }

  pub(super) fn prove(self) -> (Vec<G>, AiurProof) {
    let _span = tracing::info_span!("aiur/prove_prepared").entered();
    self.system.prove_from_execution(
      self.fun_idx,
      &self.input,
      &self.io,
      self.record,
      &self.output,
    )
  }
}

#[derive(Clone)]
enum Job {
  Shard { blocks: Vec<Address>, owned: Vec<Address> },
  Aggregate { left: Address, right: Option<Address> },
}

#[derive(Clone)]
struct Work {
  job: Job,
  statement: Arc<Statement>,
  original: usize,
  publish: bool,
}

impl Work {
  fn digest(&self) -> Address {
    Address::hash(&self.statement.claim_bytes)
  }

  fn ready(&self, slots: &FxHashMap<Address, Arc<Slot>>) -> bool {
    match &self.job {
      Job::Shard { .. } => true,
      Job::Aggregate { left, right } => {
        slots.contains_key(left)
          && right.as_ref().is_none_or(|r| slots.contains_key(r))
      },
    }
  }
}

#[allow(clippy::large_enum_variant)]
enum Prepared<'a> {
  Execute(Execution<'a>),
  Reused(Arc<Slot>),
  Split(Vec<Vec<Address>>),
  WrapChildren,
}

struct Pipeline<'a> {
  ctx: ProveContext<'a>,
  env: &'a ixon::Env,
  verify_idx: usize,
  max_ram: usize,
  index: Option<&'a Path>,
  plans: &'a Path,
  skip_proven: bool,
  lookahead: bool,
  keep_going: bool,
}

fn shard_statement(
  env: &ixon::Env,
  owned: &[Address],
) -> Result<Arc<Statement>, String> {
  let mut sorted = owned.to_vec();
  sorted.sort_unstable();
  let (_, frontier) = ixon::shard_claim::shard_check_env_claim(env, owned)
    .ok_or("shard owns no constants")?;
  Ok(Statement::new(
    SubjectTree::canonical(sorted, ShardSet(Vec::new()))?,
    CanonicalTree::from_sorted(frontier)?,
  ))
}

/// Local children share an original manifest owner. Discharge by actual
/// subject membership, including at intermediate joins, not that owner id.
fn flat_join(
  left: &Arc<Statement>,
  right: &Arc<Statement>,
) -> Result<Arc<Statement>, String> {
  let subjects = SubjectTree::flat(&left.subjects, &right.subjects)?;
  let leaves = &subjects
    .canonical_tree()
    .ok_or("healing requires canonical subjects")?
    .leaves;
  let remaining = merge_optional_sets(
    left.assumptions.as_deref(),
    right.assumptions.as_deref(),
  )
  .into_iter()
  .filter(|a| leaves.binary_search(a).is_err())
  .collect();
  Ok(Statement::new(subjects, CanonicalTree::from_sorted(remaining)?))
}

fn validate_parts(
  blocks: &[Address],
  parts: &[Vec<Address>],
) -> Result<(), String> {
  if parts.len() < 2 || parts.iter().any(Vec::is_empty) {
    return Err("split must have at least two nonempty parts".into());
  }
  let mut actual: Vec<_> = parts.iter().flatten().cloned().collect();
  let mut expected = blocks.to_vec();
  actual.sort_unstable();
  expected.sort_unstable();
  if actual != expected || !actual.windows(2).all(|w| w[0] < w[1]) {
    return Err(
      "split is not an exact disjoint cover of the original blocks".into(),
    );
  }
  Ok(())
}

fn cut(blocks: &[Address], count: usize) -> Result<Vec<Vec<Address>>, String> {
  if blocks.len() < 2 {
    return Err("indivisible block exceeds the RAM budget".into());
  }
  let count = count.clamp(2, blocks.len());
  Ok(
    (0..count)
      .map(|i| {
        blocks[i * blocks.len() / count..(i + 1) * blocks.len() / count]
          .to_vec()
      })
      .collect(),
  )
}

impl<'a> Pipeline<'a> {
  fn plan_path(&self, work: &Work) -> PathBuf {
    let mut key = b"ix-shard-splits-v2".to_vec();
    key.extend_from_slice(self.ctx.allowed);
    key.extend_from_slice(&self.max_ram.to_le_bytes());
    key.extend_from_slice(&work.statement.claim_bytes);
    self.plans.join(format!("{}.json", Address::hash(&key).hex()))
  }

  fn cached(&self, work: &Work) -> Option<Arc<Slot>> {
    if !self.skip_proven {
      return None;
    }
    let address = cache_address(self.index?, &work.digest())?;
    let result = (|| {
      let bytes = read_store(self.ctx.store_dir, &address)?;
      if Address::hash(&bytes) != address {
        return Err("store object hash mismatch".into());
      }
      let wrapper = decode_wrapper(&bytes)?;
      import_shard_proof(
        self.ctx.ixvm_system,
        self.ctx.aggr_system,
        self.verify_idx,
        self.ctx.aggr_idx,
        self.ctx.allowed,
        work.statement.clone(),
        &wrapper,
        Some(address),
      )
    })();
    match result {
      // A wrap must actually change the backend or a budget fallback loops.
      Ok(slot)
        if matches!(work.job, Job::Aggregate { right: None, .. })
          && slot.kind != ChildKind::Aggr =>
      {
        None
      },
      Ok(slot) => Some(slot),
      Err(e) => {
        eprintln!(
          "[shard-pipeline] ignored index entry {}: {e}",
          work.digest().hex()
        );
        None
      },
    }
  }

  fn over_budget(
    &self,
    work: &Work,
    slots: &FxHashMap<Address, Arc<Slot>>,
    parts: usize,
  ) -> Result<Prepared<'a>, String> {
    match &work.job {
      Job::Shard { blocks, .. } => Ok(Prepared::Split(cut(blocks, parts)?)),
      Job::Aggregate { left, right: Some(right) }
        if slots[left].kind == ChildKind::Ixvm
          || slots[right].kind == ChildKind::Ixvm =>
      {
        Ok(Prepared::WrapChildren)
      },
      Job::Aggregate { .. } => Err(format!(
        "flat healing proof cannot fit --max-ram for claim {}; increase the budget",
        work.digest().hex()
      )),
    }
  }

  fn prepare(
    &self,
    work: &Work,
    slots: &FxHashMap<Address, Arc<Slot>>,
  ) -> Result<Prepared<'a>, String> {
    if let Some(slot) = self.cached(work) {
      return Ok(Prepared::Reused(slot));
    }
    if !work.ready(slots) {
      return Err("healing job has an unavailable child proof".into());
    }
    if let Job::Shard { blocks, .. } = &work.job
      && self.skip_proven
      && let Ok(bytes) = fs::read(self.plan_path(work))
    {
      let hint = (|| {
        let hexes: Vec<Vec<String>> =
          serde_json::from_slice(&bytes).map_err(|e| e.to_string())?;
        let parts = hexes
          .into_iter()
          .map(|p| {
            p.into_iter()
              .map(|s| {
                Address::from_hex(&s)
                  .ok_or_else(|| "invalid block address".to_string())
              })
              .collect()
          })
          .collect::<Result<Vec<Vec<_>>, _>>()?;
        validate_parts(blocks, &parts)?;
        Ok::<_, String>(parts)
      })();
      match hint {
        Ok(parts) => {
          eprintln!("[shard-pipeline] restored split {}", work.digest().hex());
          return Ok(Prepared::Split(parts));
        },
        Err(e) => eprintln!("[shard-pipeline] ignored split journal: {e}"),
      }
    }
    let execution = match &work.job {
      Job::Shard { owned, .. } => {
        let (claim, input, io) =
          build_shard_check_env_witness(self.env, owned)?;
        if claim != work.statement.claim {
          return Err("prepared shard claim changed".into());
        }
        Execution::new(
          self.ctx.ixvm_system,
          self.verify_idx,
          input,
          io,
          execute_ixvm,
        )?
      },
      Job::Aggregate { left, right } => {
        let left = &slots[left];
        let right = right.as_ref().map(|r| slots[r].as_ref());
        let outer = aggregate_outer_claim(
          self.ctx.aggr_idx,
          self.ctx.allowed,
          &work.statement.claim_bytes,
        );
        let spec = SlotSpec {
          op: PlanOp::Leaf(0),
          statement: work.statement.clone(),
          subject_count: work.statement.subjects.count,
          structural: false,
          kind: ChildKind::Aggr,
          shape: Some(shape_code(left.kind, right.map(|r| r.kind))),
          outer_claim: outer.clone(),
          cache_key: work.digest(),
          ram_bytes: 0,
        };
        let (io, _) = aggregate_io(self.ctx, &spec, left, right)?;
        Execution::new(
          self.ctx.aggr_system,
          self.ctx.aggr_idx,
          outer[2..].to_vec(),
          io,
          execute_ix_aggr,
        )?
      },
    };
    let peak = execution.peak();
    eprintln!(
      "[shard-pipeline] shard {} claim {}: projected prove {} GiB, budget {} GiB",
      work.original,
      work.digest().hex(),
      format_gib(peak),
      format_gib(self.max_ram)
    );
    // Gate proving on the executed record's predicted peak. An oversized
    // record is dropped before its smaller parts are executed and checked.
    if peak > self.max_ram {
      let parts =
        execution.system.suggested_split_parts(&execution.record, self.max_ram);
      drop(execution);
      return self.over_budget(work, slots, parts);
    }
    Ok(Prepared::Execute(execution))
  }

  fn split(
    &self,
    work: &Work,
    parts: &[Vec<Address>],
  ) -> Result<Vec<Work>, String> {
    let Job::Shard { blocks, owned } = &work.job else {
      return Err("only shards can split".into());
    };
    validate_parts(blocks, parts)?;
    let mut owners = FxHashMap::default();
    for (i, part) in parts.iter().enumerate() {
      for block in part {
        owners.insert(block.clone(), i);
      }
    }
    let mut owned_parts = vec![Vec::new(); parts.len()];
    for address in owned {
      let constant =
        self.env.try_get_const(address).ok_or("missing owned constant")??;
      let block = projection_block(address, &constant);
      let owner = owners.get(&block).ok_or("split omitted an owned block")?;
      owned_parts[*owner].push(address.clone());
    }
    let children = parts
      .iter()
      .zip(owned_parts)
      .map(|(blocks, owned)| {
        Ok(Work {
          statement: shard_statement(self.env, &owned)?,
          job: Job::Shard { blocks: blocks.clone(), owned },
          original: work.original,
          publish: false,
        })
      })
      .collect::<Result<Vec<_>, String>>()?;
    let mut jobs = Vec::new();
    let root = append_balanced(&children, &mut jobs)?;
    if root.statement.claim_bytes != work.statement.claim_bytes {
      return Err("split healing would change the original claim bytes".into());
    }
    jobs.last_mut().ok_or("split produced no jobs")?.publish = work.publish;
    let hexes: Vec<Vec<_>> =
      parts.iter().map(|p| p.iter().map(Address::hex).collect()).collect();
    write_atomic(
      &self.plan_path(work),
      &serde_json::to_vec(&hexes).map_err(|e| e.to_string())?,
    )?;
    Ok(jobs)
  }

  fn persist(
    &self,
    work: &Work,
    outer: Vec<G>,
    proof: AiurProof,
  ) -> Result<Arc<Slot>, String> {
    let kind = match work.job {
      Job::Shard { .. } => ChildKind::Ixvm,
      Job::Aggregate { .. } => ChildKind::Aggr,
    };
    let expected = match kind {
      ChildKind::Ixvm => {
        inner_claim(self.verify_idx, &work.statement.claim_bytes)
      },
      ChildKind::Aggr => aggregate_outer_claim(
        self.ctx.aggr_idx,
        self.ctx.allowed,
        &work.statement.claim_bytes,
      ),
    };
    if outer != expected {
      return Err("prover returned a different public claim".into());
    }
    let system = if kind == ChildKind::Ixvm {
      self.ctx.ixvm_system
    } else {
      self.ctx.aggr_system
    };
    system
      .verify(&outer, &proof)
      .map_err(|e| format!("new shard proof failed verification: {e:?}"))?;
    let address = persist_wrapper(self.ctx.store_dir, &work.statement, &proof)?;
    if let Some(index) = self.index {
      write_atomic(
        &index.join(work.digest().hex()),
        format!("{}\n", address.hex()).as_bytes(),
      )?;
    }
    Ok(Arc::new(Slot {
      kind,
      statement: work.statement.clone(),
      claims_bytes: serialize_claims(&[&outer]),
      outer_claim: outer,
      proof,
      proof_address: Some(address),
    }))
  }

  fn run(&self, mut queue: VecDeque<Work>) -> Result<String, String> {
    // Ingress uses Rayon too. A small separate pool prevents it from taking
    // all witness/FFT workers while a STARK occupies the main pool.
    let pool = rayon::ThreadPoolBuilder::new()
      .num_threads(2)
      .build()
      .map_err(|e| e.to_string())?;
    let mut slots = FxHashMap::default();
    let mut pending = None;
    let mut completed = 0;
    let mut failures = Vec::new();
    let mut overlaps = 0;
    let mut reused = 0;
    loop {
      let (work, prepared) = if let Some(pending) = pending.take() {
        pending
      } else if let Some(work) = queue.pop_front() {
        let prepared = pool.install(|| self.prepare(&work, &slots));
        (work, prepared)
      } else {
        break;
      };
      let result = (|| -> Result<Option<Arc<Slot>>, String> {
        match prepared? {
          Prepared::Reused(slot) => {
            reused += 1;
            Ok(Some(slot))
          },
          Prepared::Split(parts) => {
            eprintln!(
              "[shard-pipeline] shard {}: splitting into {} parts",
              work.original,
              parts.len()
            );
            for child in self.split(&work, &parts)?.into_iter().rev() {
              queue.push_front(child);
            }
            Ok(None)
          },
          Prepared::WrapChildren => {
            let Job::Aggregate { left, right: Some(right) } = &work.job else {
              unreachable!()
            };
            queue.push_front(work.clone());
            for key in [right, left] {
              if slots[key].kind == ChildKind::Ixvm {
                queue.push_front(Work {
                  job: Job::Aggregate { left: key.clone(), right: None },
                  statement: slots[key].statement.clone(),
                  original: work.original,
                  publish: false,
                });
              }
            }
            eprintln!(
              "[shard-pipeline] wrapping raw children to reduce healing RAM"
            );
            Ok(None)
          },
          Prepared::Execute(execution) => {
            let prefetch = self.lookahead
              && queue.front().is_some_and(|next| next.ready(&slots));
            let (outer, proof) = if prefetch {
              let next = queue.pop_front().expect("prefetch has a next job");
              overlaps += 1;
              eprintln!(
                "[shard-pipeline] overlap: proving shard {}, preparing shard {}",
                work.original, next.original
              );
              let (proved, prepared) = thread::scope(|scope| {
                let producer =
                  scope.spawn(|| pool.install(|| self.prepare(&next, &slots)));
                let proved = execution.prove();
                let prepared = producer
                  .join()
                  .map_err(|p| {
                    format!("preparation panicked: {}", panic_text(&p))
                  })
                  .and_then(|result| result);
                (proved, prepared)
              });
              pending = Some((next, prepared));
              proved
            } else {
              execution.prove()
            };
            Ok(Some(self.persist(&work, outer, proof)?))
          },
        }
      })();
      match result {
        Ok(Some(slot)) => {
          if let Job::Aggregate { left, right } = &work.job {
            slots.remove(left);
            if let Some(right) = right {
              slots.remove(right);
            }
          }
          if work.publish {
            println!(
              "claim {}\n{}",
              work.digest().hex(),
              slot
                .proof_address
                .as_ref()
                .ok_or("published proof has no address")?
                .hex()
            );
            completed += 1;
          } else {
            slots.insert(work.digest(), slot);
          }
        },
        Ok(None) => {},
        Err(error) => {
          let error = format!("shard {}: {error}", work.original);
          eprintln!("[shard-pipeline] {error}");
          if !self.keep_going {
            return Err(error);
          }
          failures.push(error);
          queue.retain(|w| w.original != work.original);
          if pending.as_ref().is_some_and(|(w, _)| w.original == work.original)
          {
            pending = None;
          }
          slots.clear();
        },
      }
    }
    let summary = format!(
      "{completed} original shard(s) proven; {reused} cached proof(s); {overlaps} preparation overlap(s)"
    );
    if failures.is_empty() {
      Ok(summary)
    } else {
      Err(format!(
        "{summary}; {} failure(s): {}",
        failures.len(),
        failures.join("; ")
      ))
    }
  }
}

fn append_balanced(
  children: &[Work],
  jobs: &mut Vec<Work>,
) -> Result<Work, String> {
  if children.is_empty() {
    return Err("cannot join an empty partition".into());
  }
  if children.len() == 1 {
    jobs.push(children[0].clone());
    return Ok(children[0].clone());
  }
  let (left, right) = children.split_at(children.len() / 2);
  let left = append_balanced(left, jobs)?;
  let right = append_balanced(right, jobs)?;
  let work = Work {
    job: Job::Aggregate { left: left.digest(), right: Some(right.digest()) },
    statement: flat_join(&left.statement, &right.statement)?,
    original: left.original,
    publish: false,
  };
  jobs.push(work.clone());
  Ok(work)
}

/// How many NUMA lanes to prove on: `IX_PROVE_LANES=N` caps it (`0`/`off` =
/// one lane, i.e. the single pipeline above); default is one lane per domain
/// visible to this process (`crate::numa`), and never more lanes than
/// original shards.
fn numa_lane_count(shards: usize, max_ram: usize) -> usize {
  let numa = crate::numa::detect();
  let domains = numa.domains.len();
  let requested = match std::env::var("IX_PROVE_LANES") {
    Ok(v) if matches!(v.trim(), "off" | "0") => 1,
    Ok(v) => v.trim().parse::<usize>().unwrap_or(domains).max(1),
    Err(_) => domains,
  };
  if !numa.enabled() {
    return 1;
  }
  let mut lanes = requested.min(domains).min(shards.max(1));
  // Each lane needs its proving budget plus ~15 % for the overlapped
  // execution and the shared environment; never run more lanes than the
  // cgroup this process lives in can hold.
  if let Some(limit) = crate::numa::cgroup_memory_max() {
    let per_lane = max_ram / 100 * 115;
    let fit = (limit / per_lane.max(1)).max(1);
    if fit < lanes {
      eprintln!(
        "[shard-pipeline] cgroup memory limit {} GiB holds {fit} lane(s) at --max-ram {} GiB (+15 %); reducing from {lanes}",
        format_gib(limit),
        format_gib(max_ram),
      );
      lanes = fit;
    }
  }
  lanes
}

/// Longest-processing-time assignment of original shards to `lanes` queues.
/// Weighted by the manifest's measured prover peak when every selected shard
/// has one (prove time tracks peak: ~0.5 s/GiB), else by block count (over
/// ~80 shards per lane that proxy balances to within a few percent). Each
/// lane's queue keeps manifest order so lookahead prefetch stays predictable.
fn split_lanes(
  queue: VecDeque<Work>,
  lanes: usize,
  peaks: &FxHashMap<usize, usize>,
) -> Vec<VecDeque<Work>> {
  let mut indexed: Vec<(usize, Work)> = queue.into_iter().enumerate().collect();
  let all_measured = !indexed.is_empty()
    && indexed.iter().all(|(_, w)| peaks.contains_key(&w.original));
  let weight = |w: &Work| match &w.job {
    Job::Shard { blocks, .. } if all_measured => peaks[&w.original].max(1),
    Job::Shard { blocks, .. } => blocks.len().max(1),
    Job::Aggregate { .. } => 1,
  };
  indexed.sort_by_key(|(i, w)| (std::cmp::Reverse(weight(w)), *i));
  let mut load = vec![0usize; lanes];
  let mut assigned: Vec<Vec<(usize, Work)>> = vec![Vec::new(); lanes];
  for (i, w) in indexed {
    let k = (0..lanes).min_by_key(|&k| (load[k], k)).expect("lanes > 0");
    load[k] += weight(&w);
    assigned[k].push((i, w));
  }
  assigned
    .into_iter()
    .map(|mut lane| {
      lane.sort_by_key(|(i, _)| *i);
      lane.into_iter().map(|(_, w)| w).collect()
    })
    .collect()
}

impl Pipeline<'_> {
  /// One pipeline per NUMA domain inside this process: the environment and
  /// both systems are shared, each lane's proving threads and first-touch
  /// memory are confined to its domain (`crate::numa`), and each lane runs
  /// the single-lane pipeline over its own queue (lookahead, split healing,
  /// publication unchanged). Stdout lines (`claim …` + address) come from all
  /// lanes; each is one atomic `println!`.
  fn run_lanes(
    &self,
    queue: VecDeque<Work>,
    lanes: usize,
    peaks: &FxHashMap<usize, usize>,
  ) -> Result<String, String> {
    let numa = crate::numa::detect();
    let balanced_by = if !queue.is_empty()
      && queue.iter().all(|w| peaks.contains_key(&w.original))
    {
      "measured peak"
    } else {
      "block count"
    };
    let queues = split_lanes(queue, lanes, peaks);
    let described: Vec<String> = queues
      .iter()
      .zip(&numa.domains)
      .map(|(q, d)| format!("node {} ({} shards)", d.node, q.len()))
      .collect();
    eprintln!(
      "[shard-pipeline] numa: {lanes} lanes: {}; policy={:?}; balanced by {balanced_by}",
      described.join(", "),
      numa.policy
    );
    let pools = numa
      .domains
      .iter()
      .take(lanes)
      .map(|d| crate::numa::pool(numa, d))
      .collect::<Result<Vec<_>, _>>()?;
    let results: Vec<(u32, Result<String, String>)> = thread::scope(|scope| {
      let handles: Vec<_> = queues
        .into_iter()
        .zip(pools.iter())
        .zip(numa.domains.iter())
        .map(|((queue, pool), domain)| {
          scope.spawn(move || {
            crate::numa::pin_current_thread(domain, numa.policy);
            let result =
              std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                pool.install(|| self.run(queue))
              }))
              .unwrap_or_else(|p| {
                Err(format!("lane panicked: {}", panic_text(&p)))
              });
            (domain.node, result)
          })
        })
        .collect();
      handles
        .into_iter()
        .map(|h| {
          h.join().unwrap_or_else(|p| {
            (u32::MAX, Err(format!("lane thread panicked: {}", panic_text(&p))))
          })
        })
        .collect()
    });
    let mut summaries = Vec::new();
    let mut failures = Vec::new();
    for (node, result) in results {
      match result {
        Ok(summary) => summaries.push(format!("node {node}: {summary}")),
        Err(error) => failures.push(format!("node {node}: {error}")),
      }
    }
    let summary = summaries.join(" | ");
    if failures.is_empty() {
      Ok(summary)
    } else {
      Err(format!("{summary} | {}", failures.join(" | ")))
    }
  }
}

/// Explicit directories keep tests hermetic and make the native call's
/// persistence boundary identical to the CLI's existing store/index policy.
#[unsafe(no_mangle)]
extern "C" fn rs_aiur_shard_pipeline(
  ixvm_system: LeanExternal<AiurSystem, LeanBorrowed<'_>>,
  aggr_system: LeanExternal<AiurSystem, LeanBorrowed<'_>>,
  env_handle: LeanExternal<EnvHandle, LeanBorrowed<'_>>,
  blocks_blob: LeanByteArray<LeanBorrowed<'_>>,
  owned_blob: LeanByteArray<LeanBorrowed<'_>>,
  ids: LeanString<LeanBorrowed<'_>>,
  verify_idx: LeanNat<LeanBorrowed<'_>>,
  aggr_idx: LeanNat<LeanBorrowed<'_>>,
  max_ram: LeanNat<LeanBorrowed<'_>>,
  store: LeanString<LeanBorrowed<'_>>,
  index: LeanString<LeanBorrowed<'_>>,
  plans: LeanString<LeanBorrowed<'_>>,
  lookahead: bool,
  skip_proven: bool,
  keep_going: bool,
) -> LeanIOResult<LeanOwned> {
  let result = (|| -> Result<String, String> {
    let blocks = decode_addr_lists(blocks_blob.as_bytes())?;
    let owned = decode_addr_lists(owned_blob.as_bytes())?;
    // Each line is `id` or `id<TAB>measuredPeakBytes` (0 = unmeasured).
    let mut peaks: FxHashMap<usize, usize> = FxHashMap::default();
    let ids = ids
      .as_str()
      .lines()
      .map(|line| -> Result<usize, String> {
        let mut fields = line.split('\t');
        let id = fields
          .next()
          .unwrap_or("")
          .trim()
          .parse::<usize>()
          .map_err(|e| e.to_string())?;
        if let Some(peak) = fields.next()
          && let Ok(peak) = peak.trim().parse::<usize>()
          && peak > 0
        {
          peaks.insert(id, peak);
        }
        Ok(id)
      })
      .collect::<Result<Vec<_>, _>>()?;
    if blocks.is_empty()
      || blocks.len() != owned.len()
      || blocks.len() != ids.len()
    {
      return Err(
        "shard pipeline requires equally sized, nonempty block/owned/id lists"
          .into(),
      );
    }
    let max_ram = lean_unbox_nat_as_usize(max_ram.inner());
    if max_ram == 0 {
      return Err("shard pipeline requires positive --max-ram".into());
    }
    let ixvm = ixvm_system.get();
    let aggr = aggr_system.get();
    let env = &env_handle.get().env;
    let verify_idx = lean_unbox_nat_as_usize(verify_idx.inner());
    let aggr_idx = lean_unbox_nat_as_usize(aggr_idx.inner());
    let ixvm_vk = aiur::vk_codec::aiur_system_to_bytes(ixvm)?;
    let aggr_vk = aiur::vk_codec::aiur_system_to_bytes(aggr)?;
    let allowed = allowed_blob(&ixvm_vk, verify_idx, &aggr_vk, aggr_idx);
    let mut queue = VecDeque::new();
    let mut seen = FxHashSet::default();
    let mut seen_blocks = FxHashSet::default();
    for ((blocks, owned), id) in blocks.into_iter().zip(owned).zip(ids) {
      if !seen.insert(id) {
        return Err("duplicate original shard id".into());
      }
      if blocks.is_empty() {
        return Err("empty original shard".into());
      }
      let block_set: FxHashSet<_> = blocks.iter().collect();
      for block in &blocks {
        if !seen_blocks.insert(block.clone()) {
          return Err("selected shard block lists overlap".into());
        }
      }
      for address in &owned {
        let constant = env
          .try_get_const(address)
          .ok_or("owned constant is missing from the environment")??;
        if !block_set.contains(&projection_block(address, &constant)) {
          return Err(
            "owned constant belongs to a block outside its shard".into(),
          );
        }
      }
      queue.push_back(Work {
        statement: shard_statement(env, &owned)?,
        job: Job::Shard { blocks, owned },
        original: id,
        publish: true,
      });
    }
    let lanes = numa_lane_count(queue.len(), max_ram);
    let pipeline = Pipeline {
      ctx: ProveContext {
        specs: &[],
        prepared: &[],
        proofs: None,
        owner_by_address: &FxHashMap::default(),
        ixvm_system: ixvm,
        aggr_system: aggr,
        ixvm_vk: &ixvm_vk,
        aggr_vk: &aggr_vk,
        allowed: &allowed,
        aggr_idx,
        store_dir: Path::new(store.as_str()),
        cache_dir: None,
        reprove_slot: None,
        write_outputs: true,
      },
      env,
      verify_idx,
      max_ram,
      index: (!index.as_str().is_empty()).then(|| Path::new(index.as_str())),
      plans: Path::new(plans.as_str()),
      skip_proven,
      lookahead,
      keep_going,
    };
    if lanes <= 1 {
      return pipeline.run(queue);
    }
    pipeline.run_lanes(queue, lanes, &peaks)
  })();
  LeanIOResult::ok(match result {
    Ok(summary) => LeanExcept::ok(LeanString::new(&summary)),
    Err(error) => LeanExcept::error_string(&error),
  })
}

#[cfg(test)]
mod tests {
  use super::*;

  fn shard_work(id: usize, blocks: usize) -> Work {
    Work {
      job: Job::Shard {
        blocks: (0..blocks)
          .map(|i| {
            Address::hash(&((id as u64) * 1000 + i as u64).to_le_bytes())
          })
          .collect(),
        owned: Vec::new(),
      },
      statement: statement(&[Address::hash(&(id as u64).to_le_bytes())], &[]),
      original: id,
      publish: true,
    }
  }

  #[test]
  fn split_lanes_balances_by_block_count_and_keeps_order() {
    let queue: VecDeque<Work> =
      [(0, 5), (1, 1), (2, 4), (3, 1), (4, 3), (5, 2)]
        .into_iter()
        .map(|(id, b)| shard_work(id, b))
        .collect();
    let lanes = split_lanes(queue, 3, &FxHashMap::default());
    assert_eq!(lanes.len(), 3);
    let loads: Vec<usize> = lanes
      .iter()
      .map(|l| {
        l.iter()
          .map(|w| match &w.job {
            Job::Shard { blocks, .. } => blocks.len(),
            Job::Aggregate { .. } => 1,
          })
          .sum()
      })
      .collect();
    assert!(
      loads.iter().max().unwrap() - loads.iter().min().unwrap() <= 1,
      "{loads:?}"
    );
    for lane in &lanes {
      let ids: Vec<usize> = lane.iter().map(|w| w.original).collect();
      let mut sorted = ids.clone();
      sorted.sort_unstable();
      assert_eq!(ids, sorted);
    }
    assert_eq!(lanes.iter().map(VecDeque::len).sum::<usize>(), 6);
  }

  #[test]
  fn split_lanes_prefers_measured_peaks_when_all_present() {
    // Block counts say shard 0 is heaviest; measured peaks say shard 1 is.
    let queue: VecDeque<Work> = [(0, 9), (1, 1), (2, 1)]
      .into_iter()
      .map(|(id, b)| shard_work(id, b))
      .collect();
    let peaks: FxHashMap<usize, usize> =
      [(0, 100), (1, 500), (2, 100)].into_iter().collect();
    let lanes = split_lanes(queue, 2, &peaks);
    // LPT by peak: shard 1 (500) alone on one lane, 0 and 2 (100+100) together.
    let alone: Vec<&VecDeque<Work>> =
      lanes.iter().filter(|l| l.len() == 1).collect();
    assert_eq!(alone.len(), 1);
    assert_eq!(alone[0][0].original, 1);
  }
  use std::sync::atomic::{AtomicUsize, Ordering};

  fn address(n: usize) -> Address {
    Address::hash(&n.to_le_bytes())
  }

  fn statement(
    subjects: &[Address],
    assumptions: &[Address],
  ) -> Arc<Statement> {
    let mut subjects = subjects.to_vec();
    let mut assumptions = assumptions.to_vec();
    subjects.sort_unstable();
    assumptions.sort_unstable();
    Statement::new(
      SubjectTree::canonical(subjects, ShardSet(vec![])).unwrap(),
      CanonicalTree::from_sorted(assumptions).unwrap(),
    )
  }

  #[test]
  fn nested_flat_healing_keeps_external_and_unproven_sibling_assumptions() {
    // Exercise a canonical original larger than Stage 2's structural cutoff.
    let all: Vec<_> = (0..5000).map(address).collect();
    let outside = address(5000);
    let a = statement(
      &all[..2000],
      &[all[2000].clone(), all[4000].clone(), outside.clone()],
    );
    let b = statement(&all[2000..4000], &[all[0].clone()]);
    let c = statement(&all[4000..], std::slice::from_ref(&outside));
    let ab = flat_join(&a, &b).unwrap();
    assert_eq!(ab.assumptions.as_ref().unwrap().leaves.len(), 2);
    assert!(ab.assumptions.as_ref().unwrap().leaves.contains(&all[4000]));
    let healed = flat_join(&ab, &c).unwrap();
    let original = statement(&all, &[outside]);
    assert_eq!(healed.claim_bytes, original.claim_bytes);
    assert_eq!(
      Address::hash(&healed.claim_bytes),
      Address::hash(&original.claim_bytes)
    );
    assert!(healed.subjects.canonical_tree().is_some());
    assert!(flat_join(&a, &a).is_err());
  }

  #[test]
  fn split_hints_reject_missing_repeated_foreign_and_empty_blocks() {
    let blocks: Vec<_> = (0..5).map(address).collect();
    let parts = cut(&blocks, 3).unwrap();
    validate_parts(&blocks, &parts).unwrap();
    let mut bad = parts.clone();
    bad[0].clear();
    assert!(validate_parts(&blocks, &bad).is_err());
    let mut bad = parts.clone();
    bad[0][0] = address(100);
    assert!(validate_parts(&blocks, &bad).is_err());
    let mut bad = parts.clone();
    bad[0].push(blocks[0].clone());
    assert!(validate_parts(&blocks, &bad).is_err());
    assert!(validate_parts(&blocks, &parts[1..]).is_err());
    assert!(cut(&blocks[..1], 2).is_err());
    assert!(cut(&[], 2).is_err());
  }

  #[test]
  fn execution_moves_between_threads_without_reexecution_or_io_copy() {
    static CALLS: AtomicUsize = AtomicUsize::new(0);
    fn execute(
      top: &Toplevel,
      idx: FunIdx,
      args: Vec<G>,
      io: &mut IOBuffer,
    ) -> Result<(QueryRecord, Vec<G>), ExecError> {
      CALLS.fetch_add(1, Ordering::SeqCst);
      top.execute(idx, args, io)
    }
    let system = super::super::tests::transport_system(1);
    let mut io =
      IOBuffer { data: FxHashMap::default(), map: FxHashMap::default() };
    io.data.insert(G::ZERO, Vec::with_capacity(1024));
    let arena = io.data[&G::ZERO].as_ptr();
    let execution = thread::scope(|scope| {
      scope
        .spawn(|| {
          Execution::new(&system, 0, vec![G::ONE], io, execute).unwrap()
        })
        .join()
        .unwrap()
    });
    assert_eq!(execution.io.data[&G::ZERO].as_ptr(), arena);
    let (claim, proof) = execution.prove();
    system.verify(&claim, &proof).unwrap();
    assert_eq!(CALLS.load(Ordering::SeqCst), 1);
    let io = IOBuffer { data: FxHashMap::default(), map: FxHashMap::default() };
    drop(Execution::new(&system, 0, vec![G::ONE], io, execute).unwrap());
    assert_eq!(CALLS.load(Ordering::SeqCst), 2);
  }
}
