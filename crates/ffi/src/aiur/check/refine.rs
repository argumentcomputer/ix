//! Early execution-limit retries for the native partition path. Split only
//! between blocks, never inside a mutual block. An aborted parent is NOT a
//! measured/proven claim: success requires every final child's execution.

use super::super::admission::Followups;
use super::*;
use rustc_hash::FxHashSet;

pub(super) struct Part {
  pub label: String,
  pub blocks: Vec<Address>,
  pub owned: Vec<Address>,
  pub result: ShardCheckResult,
}

struct Pending {
  origin: usize,
  label: String,
  blocks: Vec<Address>,
  owned: Vec<Address>,
  pressure_retries: usize,
  generation: usize,
}

pub(super) struct Runs {
  /// Indexed by original manifest id; None means unselected, not success.
  pub results: Vec<Option<ShardCheckResult>>,
  pub parts: Vec<Vec<Part>>,
  pub attempts: usize,
  pub max_generation: usize,
}

fn split(env: &Env, pending: Pending) -> Result<[Pending; 2], String> {
  let Pending { origin, label, mut blocks, owned, generation, .. } = pending;
  let right = blocks.split_off(blocks.len().div_ceil(2));
  if blocks.is_empty() || right.is_empty() {
    return Err(
      "execution refinement must strictly reduce a non-singleton block set"
        .into(),
    );
  }
  let left_set: FxHashSet<_> = blocks.iter().collect();
  let right_set: FxHashSet<_> = right.iter().collect();
  let mut left_owned = Vec::new();
  let mut right_owned = Vec::new();
  for addr in owned {
    let lc = env.consts.get(&addr).ok_or("refinement constant missing")?;
    let constant = lc.get()?;
    let block = match &constant.info {
      ConstantInfo::IPrj(p) => &p.block,
      ConstantInfo::CPrj(p) => &p.block,
      ConstantInfo::RPrj(p) => &p.block,
      ConstantInfo::DPrj(p) => &p.block,
      _ => &addr,
    };
    if left_set.contains(block) {
      left_owned.push(addr.clone());
    } else if right_set.contains(block) {
      right_owned.push(addr.clone());
    } else {
      return Err(format!("refinement lost ownership of {}", addr.hex()));
    }
  }
  Ok([
    Pending {
      origin,
      label: format!("{label}.0"),
      blocks,
      owned: left_owned,
      pressure_retries: 0,
      generation: generation + 1,
    },
    Pending {
      origin,
      label: format!("{label}.1"),
      blocks: right,
      owned: right_owned,
      pressure_retries: 0,
      generation: generation + 1,
    },
  ])
}

pub(super) fn run(
  env: &Env,
  manifest: &ShardManifest,
  owned: &[Vec<Address>],
  selection: Option<&[usize]>,
  gate: &Admission,
  pool: &rayon::ThreadPool,
  estimate: impl Fn(&[Address]) -> usize,
  execute: impl Fn(&[Address], &str) -> Result<ShardCheckResult, String> + Sync,
) -> Result<Runs, String> {
  if manifest.shards.len() != owned.len() {
    return Err("execution refinement ownership count mismatch".into());
  }
  let selected = select_shards(manifest.shards.len(), selection)?;
  let initial: Vec<_> = selected
    .iter()
    .map(|&origin| Pending {
      origin,
      label: origin.to_string(),
      blocks: manifest.shards[origin].blocks.clone(),
      owned: owned[origin].clone(),
      pressure_retries: 0,
      generation: 0,
    })
    .collect();
  let mut originals = vec![None; manifest.shards.len()];
  let mut parts: Vec<Vec<Part>> =
    (0..manifest.shards.len()).map(|_| Vec::new()).collect();
  let mut attempts = 0;
  let mut max_generation = 0;
  let mut outstanding = vec![0usize; manifest.shards.len()];
  for &id in &selected {
    outstanding[id] = 1;
  }
  let mut settled = 0;
  let started = Instant::now();
  eprintln!(
    "[ixvm_refine] completion-driven queue: {} source shard(s)",
    selected.len()
  );
  let work = |pending: &Pending| {
    eprintln!(
      "[ixvm_check] shard {} started ({} consts); attempt={} generation={}",
      pending.label,
      pending.owned.len(),
      pending.pressure_retries + 1,
      pending.generation
    );
    execute(&pending.owned, &pending.label)
  };
  let complete = |mut pending: Pending, result: ShardCheckResult| {
    attempts += 1;
    max_generation = max_generation.max(pending.generation);
    if result.resource_status > 2
      || (result.resource_status != 0
        && (result.error.is_empty() || result.peak_bytes != 0))
    {
      return Err("invalid resource-limited execution outcome".into());
    }
    if pending.generation == 0 {
      originals[pending.origin] = Some(result.clone());
    }
    if result.resource_status == 2 && pending.pressure_retries < 2 {
      eprintln!(
        "[ixvm_refine] shard {}: shared record budget exhausted; defer attempt {} until active records drain",
        pending.label,
        pending.pressure_retries + 2
      );
      pending.pressure_retries += 1;
      pending.generation += 1;
      Ok(Followups::AfterDrain(pending))
    } else if result.resource_status == 1 && pending.blocks.len() > 1 {
      eprintln!(
        "[ixvm_refine] shard {}: execution memory limit; split {} blocks into two",
        pending.label,
        pending.blocks.len()
      );
      outstanding[pending.origin] += 1;
      Ok(Followups::Ready(split(env, pending)?.into()))
    } else {
      outstanding[pending.origin] = outstanding[pending.origin]
        .checked_sub(1)
        .ok_or("execution refinement settled a claim twice")?;
      if outstanding[pending.origin] == 0 {
        settled += 1;
      }
      eprintln!(
        "[ixvm_check] {settled}/{} shards settled, {attempts} attempts, {:.1}s: shard {} {}",
        selected.len(),
        started.elapsed().as_secs_f64(),
        pending.label,
        if result.error.is_empty() { "ok" } else { &result.error }
      );
      parts[pending.origin].push(Part {
        label: pending.label,
        blocks: pending.blocks,
        owned: pending.owned,
        result,
      });
      Ok(Followups::Ready(Vec::new()))
    }
  };
  gate.dispatch(
    pool,
    initial,
    |pending| estimate(&pending.owned),
    work,
    complete,
  )?;
  if settled != selected.len() || outstanding.iter().any(|&n| n != 0) {
    return Err("execution refinement left work unsettled".into());
  }
  // Completion order is nondeterministic; report tree labels/ownership in
  // deterministic order, never arrival order or a compacted manifest index.
  for origin_parts in &mut parts {
    origin_parts.sort_unstable_by(|a, b| a.label.cmp(&b.label));
  }
  let results = originals
    .into_iter()
    .zip(&parts)
    .enumerate()
    .map(|(id, (original, settled))| {
      if selected.binary_search(&id).is_err() {
        if original.is_some() || !settled.is_empty() {
          return Err("execution refinement ran an unselected shard");
        }
        return Ok(None);
      }
      let mut result = original.ok_or("missing original shard result")?;
      if settled.is_empty() {
        return Err("execution refinement left a shard unchecked");
      }
      let failures: Vec<_> = settled
        .iter()
        .filter(|p| !p.result.error.is_empty())
        .map(|p| {
          format!(
            "shard {}: {}{}",
            p.label,
            p.result.error,
            if p.blocks.len() <= 1 && p.result.resource_status == 1 {
              "; single block cannot be split"
            } else {
              ""
            }
          )
        })
        .collect();
      result.error = failures.join("; ");
      // A retried original that finally passed has a real original record.
      // A split original has none: never fabricate its peak from child peaks.
      if settled.len() == 1 {
        result.peak_bytes = settled[0].result.peak_bytes;
        result.resource_status = settled[0].result.resource_status;
      }
      Ok(Some(result))
    })
    .collect::<Result<Vec<_>, &str>>()
    .map_err(str::to_owned)?;
  Ok(Runs { results, parts, attempts, max_generation })
}

pub(super) fn extend_report(report: &mut Value, runs: &Runs) {
  report["executed"] = json!(runs.attempts);
  report["scheduler"] = json!("completion-driven");
  // Keep the legacy key, but do not misrepresent a lineage depth as a barrier.
  report["waves"] = Value::Null;
  report["max_generation"] = json!(runs.max_generation);
  for (id, parts) in runs.parts.iter().enumerate() {
    let Some(result) = &runs.results[id] else { continue };
    if parts.len() == 1 && parts[0].result.resource_status == 0 {
      continue;
    }
    let leaf = &mut report["leaves"][id];
    leaf["resource_status"] = json!(result.resource_status);
    if parts.len() > 1 {
      leaf["status"] =
        json!(if result.error.is_empty() { "refined" } else { "failed" });
      leaf["predicted_peak_bytes"] = Value::Null;
    }
    leaf["parts"] = json!(parts.iter().map(|p| json!({
      "label": p.label, "blocks": p.blocks.iter().map(Address::hex).collect::<Vec<_>>(),
      "consts": p.owned.len(), "claim": p.result.claim.as_ref().map(Address::hex),
      "status": if p.result.error.is_empty() { "measured" } else { "failed" },
      "reason": p.result.error, "resource_status": p.result.resource_status,
      "predicted_peak_bytes": if p.result.resource_status == 0 { Some(p.result.peak_bytes) } else { None },
    })).collect::<Vec<_>>());
  }
}

#[cfg(test)]
mod tests;
