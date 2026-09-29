//! Aggregation scheduler.

use super::{
  format_gib, panic_text,
  plan::{PlanOp, SlotSpec},
  protocol::{ChildKind, serialize_claims},
  prove::{ProveContext, Slot, StagedSlot, finish_slot, prepare_slot},
  store::load_cached,
};
use std::{
  collections::VecDeque,
  sync::{Arc, mpsc},
  thread,
};

pub(super) fn dependencies_complete(
  spec: &SlotSpec,
  completed: &[bool],
) -> bool {
  match spec.op {
    PlanOp::Leaf(_) => true,
    PlanOp::Join(left, right) => completed[left] && completed[right],
  }
}

/// What preparing a slot yields: a slot complete already, or work for the
/// prover.
pub(super) enum Prepared<S, D> {
  Done(Arc<D>),
  Staged(S),
}

/// The per-slot work the scheduler drives. The production worker proves
/// aggregate slots; a test worker completes slots without recursive proofs.
pub(super) trait SlotWorker: Sync {
  type Staged: Send;
  type Done: Send + Sync;
  fn specs(&self) -> &[SlotSpec];
  /// The RAM a slot holds from admission to completion.
  fn weight(&self, index: usize) -> usize;
  /// A slot that only verifies: no record, no prover.
  fn verify_only(&self, index: usize) -> bool;
  /// The slot's result if a cache already holds it, checked before any
  /// slot is admitted.
  fn cached(&self, index: usize) -> Option<Arc<Self::Done>>;
  fn prepare(
    &self,
    index: usize,
    children: &[Arc<Self::Done>],
  ) -> Result<Prepared<Self::Staged, Self::Done>, String>;
  fn finish(
    &self,
    index: usize,
    staged: Self::Staged,
  ) -> Result<Arc<Self::Done>, String>;
}

struct ProveWorker<'a>(ProveContext<'a>);

impl SlotWorker for ProveWorker<'_> {
  type Staged = StagedSlot;
  type Done = Slot;

  fn specs(&self) -> &[SlotSpec] {
    self.0.specs
  }

  /// With trace shards each slot is held to its share of the budget inside
  /// its proof; the static per-shape weights describe whole CPU proofs and
  /// would keep every slot alone, so they gate nothing on that path.
  fn weight(&self, index: usize) -> usize {
    if self.0.wrap_budget.is_some() { 0 } else { self.0.specs[index].ram_bytes }
  }

  fn verify_only(&self, index: usize) -> bool {
    matches!(self.0.specs[index].op, PlanOp::Leaf(_))
      && self.0.specs[index].kind == ChildKind::Ixvm
  }

  fn cached(&self, index: usize) -> Option<Arc<Slot>> {
    let ctx = self.0;
    if ctx.reprove_slot.is_some() {
      return None;
    }
    let spec = &ctx.specs[index];
    if spec.kind != ChildKind::Aggr {
      return None;
    }
    let (proof, address) =
      load_cached(ctx.aggr_system, ctx.store_dir, ctx.cache_dir, index, spec)?;
    Some(Arc::new(Slot {
      kind: ChildKind::Aggr,
      statement: spec.statement.clone(),
      outer_claim: spec.outer_claim.clone(),
      proof,
      proof_address: Some(address),
      claims_bytes: serialize_claims(&[&spec.outer_claim]),
    }))
  }

  fn prepare(
    &self,
    index: usize,
    children: &[Arc<Slot>],
  ) -> Result<Prepared<StagedSlot, Slot>, String> {
    match prepare_slot(self.0, index, children).map_err(String::from)? {
      StagedSlot::Done(slot) => Ok(Prepared::Done(slot)),
      staged => Ok(Prepared::Staged(staged)),
    }
  }

  fn finish(
    &self,
    index: usize,
    staged: StagedSlot,
  ) -> Result<Arc<Slot>, String> {
    finish_slot(self.0, index, staged)
  }
}

pub(super) fn run_scheduler(
  ctx: ProveContext<'_>,
  jobs: usize,
  ahead: usize,
  budget: usize,
  active: &[bool],
) -> Result<Vec<Option<Arc<Slot>>>, String> {
  run_scheduler_with(jobs, ahead, budget, active, &ProveWorker(ctx))
}

/// What a scheduler thread reports: a slot prepared (or found complete
/// while preparing), or a slot proven.
enum SchedulerEvent<S, D> {
  /// A slot prepared (the flag: it was a verify-only leaf).
  Prepared(usize, bool, Result<Prepared<S, D>, String>),
  Finished(usize, Result<Arc<D>, String>),
}

/// Runs the slot plan with two lanes: `ahead` threads prepare ready slots
/// (children complete) — the CPU half: advice, execution, planning —
/// while `jobs` threads prove prepared slots — the GPU half — so a join
/// executes while the previous one proves. `ahead == 0` fuses the lanes:
/// each admitted slot prepares and proves on one thread, `jobs` at a
/// time. Slots are admitted bottom level first, then by index, so parents
/// become ready as early as possible; the RAM weights gate admission, a
/// slot's weight held from admission to completion. `active` selects the
/// slots to run; a slot under a cached ancestor is retired without a
/// result of its own.
pub(super) fn run_scheduler_with<W: SlotWorker>(
  jobs: usize,
  ahead: usize,
  budget: usize,
  active: &[bool],
  worker: &W,
) -> Result<Vec<Option<Arc<W::Done>>>, String> {
  if budget == 0 {
    return Err("aggregate scheduler RAM budget must be positive".into());
  }
  let specs = worker.specs();
  let count = specs.len();
  if active.len() != count {
    return Err("aggregate scheduler selection does not match the plan".into());
  }
  let target = active.iter().filter(|flag| **flag).count();
  let max_jobs = if jobs == 0 { count.max(1) } else { jobs.max(1) };
  let fused = ahead == 0;
  let max_ahead = if fused { max_jobs } else { ahead };
  // Raw leaves only verify: they hold no record and take no prover, so
  // they run beside both lanes, a core each.
  let max_verify = thread::available_parallelism().map_or(1, usize::from);
  let mut level = vec![0usize; count];
  for (index, spec) in specs.iter().enumerate() {
    if let PlanOp::Join(left, right) = spec.op {
      level[index] = 1 + level[left].max(level[right]);
    }
  }
  let (sender, receiver) =
    mpsc::channel::<SchedulerEvent<W::Staged, W::Done>>();
  thread::scope(|scope| -> Result<Vec<Option<Arc<W::Done>>>, String> {
    let mut slots: Vec<Option<Arc<W::Done>>> = vec![None; count];
    let mut completed = vec![false; count];
    let mut admitted = vec![false; count];
    let mut retired = vec![false; count];
    let mut completed_count = 0usize;
    // Cache check from the root down: a cached proof retires its whole
    // subtree, so a resumed run, or the final run over lanes' subtree
    // roots, loads and verifies only the highest cached proofs and never
    // visits what is under them. Specs are in post-order, so walking them
    // backwards meets every parent before its children.
    for index in (0..count).rev() {
      if !active[index] || completed[index] {
        continue;
      }
      let Some(slot) = worker.cached(index) else {
        continue;
      };
      slots[index] = Some(slot);
      let mut stack = vec![index];
      while let Some(slot) = stack.pop() {
        if completed[slot] {
          continue;
        }
        completed[slot] = true;
        admitted[slot] = true;
        retired[slot] = slot != index;
        completed_count += 1;
        if let PlanOp::Join(left, right) = specs[slot].op {
          stack.push(left);
          stack.push(right);
        }
      }
      eprintln!("[aggregate] slot {index}: cached; its subtree is not visited");
    }
    let mut verifying = 0usize;
    let mut preparing = 0usize;
    let mut proving = 0usize;
    let mut reserved = 0usize;
    let mut prepared: VecDeque<(usize, W::Staged)> = VecDeque::new();
    let mut failures: Vec<(usize, String)> = Vec::new();

    while completed_count < target {
      if failures.is_empty() {
        // Prover lane first: prepared slots, in the order prepared.
        while proving < max_jobs {
          let Some((index, staged)) = prepared.pop_front() else {
            break;
          };
          proving += 1;
          let sender = sender.clone();
          scope.spawn(move || {
            let result =
              std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                worker.finish(index, staged)
              }))
              .unwrap_or_else(|payload| {
                Err(format!(
                  "Rust proof worker panicked: {}",
                  panic_text(&payload)
                ))
              });
            let _ = sender.send(SchedulerEvent::Finished(index, result));
          });
        }
        // Prepare lane: ready slots, bottom level first; a prepared record
        // waiting for the prover counts against the lookahead, and raw
        // leaves have their own allowance.
        let mut ready: Vec<usize> = (0..count)
          .filter(|&index| {
            active[index]
              && !admitted[index]
              && dependencies_complete(&specs[index], &completed)
          })
          .collect();
        ready.sort_unstable_by_key(|&index| (level[index], index));
        for index in ready {
          let verify = worker.verify_only(index);
          if verify {
            if verifying >= max_verify {
              continue;
            }
          } else if preparing + prepared.len() >= max_ahead {
            continue;
          }
          let weight = worker.weight(index);
          let fits = reserved.saturating_add(weight) <= budget;
          if !fits && verifying + preparing + proving + prepared.len() != 0 {
            continue;
          }
          let children = match specs[index].op {
            PlanOp::Leaf(_) => Vec::new(),
            PlanOp::Join(left, right) => vec![
              slots[left].as_ref().expect("completed left slot").clone(),
              slots[right].as_ref().expect("completed right slot").clone(),
            ],
          };
          admitted[index] = true;
          if verify {
            verifying += 1;
          } else {
            preparing += 1;
          }
          reserved = reserved.saturating_add(weight);
          if !verify {
            let over = if weight > budget {
              "; over-budget slot runs alone"
            } else {
              ""
            };
            eprintln!(
              "[aggregate] slot {index}: admitted {} GiB; reserved {}/{} GiB; preparing {preparing}/{max_ahead} (queued {}), proving {proving}/{max_jobs}{over}",
              format_gib(weight),
              format_gib(reserved),
              format_gib(budget),
              prepared.len(),
            );
          }
          let sender = sender.clone();
          scope.spawn(move || {
            let result =
              std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                let prepared = worker.prepare(index, &children)?;
                match prepared {
                  Prepared::Staged(staged) if fused => {
                    worker.finish(index, staged).map(Prepared::Done)
                  },
                  prepared => Ok(prepared),
                }
              }))
              .unwrap_or_else(|payload| {
                Err(format!(
                  "Rust proof worker panicked: {}",
                  panic_text(&payload)
                ))
              });
            let _ =
              sender.send(SchedulerEvent::Prepared(index, verify, result));
          });
        }
      }

      if verifying + preparing + proving == 0 {
        if failures.is_empty() {
          if !prepared.is_empty() {
            continue;
          }
          failures.push((count, "aggregate scheduler deadlocked".into()));
        }
        break;
      }

      let event = receiver.recv().map_err(|error| {
        format!("aggregate scheduler channel closed: {error}")
      })?;
      let (index, outcome) = match event {
        SchedulerEvent::Prepared(index, verify, result) => {
          if verify {
            verifying -= 1;
          } else {
            preparing -= 1;
          }
          match result {
            Ok(Prepared::Done(slot)) => (index, Ok(slot)),
            Ok(Prepared::Staged(staged)) => {
              eprintln!(
                "[aggregate] slot {index}: prepared, waiting for the prover ({} queued)",
                prepared.len() + 1
              );
              prepared.push_back((index, staged));
              continue;
            },
            Err(error) => (index, Err(error)),
          }
        },
        SchedulerEvent::Finished(index, result) => {
          proving -= 1;
          (index, result)
        },
      };
      reserved = reserved.saturating_sub(worker.weight(index));
      match outcome {
        Ok(slot) => {
          slots[index] = Some(slot);
          completed[index] = true;
          completed_count += 1;
        },
        Err(error) => failures.push((index, error)),
      }
    }

    // A failure stops admission; what is running finishes, what is
    // prepared and unproven is dropped.
    while verifying + preparing + proving > 0 {
      let event = receiver.recv().map_err(|error| {
        format!("aggregate scheduler drain failed: {error}")
      })?;
      let (index, outcome) = match event {
        SchedulerEvent::Prepared(index, verify, result) => {
          if verify {
            verifying -= 1;
          } else {
            preparing -= 1;
          }
          match result {
            Ok(Prepared::Done(slot)) => (index, Ok(slot)),
            Ok(Prepared::Staged(_)) => continue,
            Err(error) => (index, Err(error)),
          }
        },
        SchedulerEvent::Finished(index, result) => {
          proving -= 1;
          (index, result)
        },
      };
      match outcome {
        Ok(slot) => {
          slots[index] = Some(slot);
          completed[index] = true;
        },
        Err(error) => failures.push((index, error)),
      }
    }
    if !failures.is_empty() {
      failures.sort_unstable_by_key(|(index, _)| *index);
      let (index, error) = failures.remove(0);
      return Err(if index < count {
        format!("slot {index}: {error}")
      } else {
        error
      });
    }
    // Every selected slot has a result, except those retired under a
    // cached ancestor, which have none of their own.
    if let Some(index) = (0..count)
      .find(|&index| active[index] && !retired[index] && slots[index].is_none())
    {
      return Err(format!("scheduler completed without slot {index}"));
    }
    Ok(slots)
  })
}
