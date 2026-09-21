//! Aggregation scheduler.

use super::{
  format_gib, panic_text,
  plan::{PlanOp, SlotSpec},
  prove::{ProveContext, Slot, prove_slot},
};
use std::{
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

pub(super) fn run_scheduler(
  ctx: ProveContext<'_>,
  jobs: usize,
  budget: usize,
) -> Result<Vec<Arc<Slot>>, String> {
  if budget == 0 {
    return Err("aggregate scheduler RAM budget must be positive".into());
  }
  let max_jobs = if jobs == 0 { ctx.specs.len().max(1) } else { jobs.max(1) };
  let (sender, receiver) = mpsc::channel();
  thread::scope(|scope| -> Result<Vec<Arc<Slot>>, String> {
    let mut slots: Vec<Option<Arc<Slot>>> = vec![None; ctx.specs.len()];
    let mut completed = vec![false; ctx.specs.len()];
    let mut in_flight = vec![false; ctx.specs.len()];
    let mut completed_count = 0usize;
    let mut active = 0usize;
    let mut reserved = 0usize;
    let mut failures: Vec<(usize, String)> = Vec::new();

    while completed_count < ctx.specs.len() {
      if failures.is_empty() && active < max_jobs {
        let mut ready: Vec<usize> = ctx
          .specs
          .iter()
          .enumerate()
          .filter_map(|(index, spec)| {
            (!completed[index]
              && !in_flight[index]
              && dependencies_complete(spec, &completed))
            .then_some(index)
          })
          .collect();
        ready.sort_unstable_by(|left, right| {
          ctx.specs[*right]
            .ram_bytes
            .cmp(&ctx.specs[*left].ram_bytes)
            .then_with(|| left.cmp(right))
        });
        for index in ready {
          if active >= max_jobs {
            break;
          }
          let weight = ctx.specs[index].ram_bytes;
          let fits = reserved.saturating_add(weight) <= budget;
          if !fits && active != 0 {
            continue;
          }
          let children = match ctx.specs[index].op {
            PlanOp::Leaf(_) => Vec::new(),
            PlanOp::Join(left, right) => vec![
              slots[left].as_ref().expect("completed left slot").clone(),
              slots[right].as_ref().expect("completed right slot").clone(),
            ],
          };
          in_flight[index] = true;
          active += 1;
          reserved = reserved.saturating_add(weight);
          let over =
            if weight > budget { "; over-budget slot runs alone" } else { "" };
          eprintln!(
            "[aggregate] slot {index}: admitted {} GiB; reserved {}/{} GiB; active {active}/{max_jobs}{over}",
            format_gib(weight),
            format_gib(reserved),
            format_gib(budget),
          );
          let sender = sender.clone();
          scope.spawn(move || {
            let result =
              std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                prove_slot(ctx, index, &children)
              }))
              .unwrap_or_else(|payload| {
                Err(format!(
                  "Rust proof worker panicked: {}",
                  panic_text(&payload)
                ))
              });
            let _ = sender.send((index, weight, result));
          });
        }
      }

      if active == 0 {
        if failures.is_empty() {
          failures
            .push((ctx.specs.len(), "aggregate scheduler deadlocked".into()));
        }
        break;
      }

      let (index, weight, result) = receiver.recv().map_err(|error| {
        format!("aggregate scheduler channel closed: {error}")
      })?;
      if !in_flight.get(index).copied().unwrap_or(false) {
        failures.push((index, "duplicate or unknown scheduler result".into()));
        continue;
      }
      in_flight[index] = false;
      active -= 1;
      reserved = reserved.saturating_sub(weight);
      match result {
        Ok(slot) => {
          slots[index] = Some(slot);
          completed[index] = true;
          completed_count += 1;
        },
        Err(error) => failures.push((index, error)),
      }
    }

    while active > 0 {
      let (index, weight, result) = receiver.recv().map_err(|error| {
        format!("aggregate scheduler drain failed: {error}")
      })?;
      if in_flight.get(index).copied().unwrap_or(false) {
        in_flight[index] = false;
        active -= 1;
        reserved = reserved.saturating_sub(weight);
      }
      match result {
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
      return Err(if index < ctx.specs.len() {
        format!("slot {index}: {error}")
      } else {
        error
      });
    }
    slots
      .into_iter()
      .enumerate()
      .map(|(index, slot)| {
        slot.ok_or_else(|| format!("scheduler completed without slot {index}"))
      })
      .collect()
  })
}
