//! Production phase-1 family: all subsets for at most sixteen initial
//! members, otherwise the complete setPrec-least greedy chain.
//! Only the fixed entry is reachable from production tiered normalization;
//! configurable gates remain private for reference tests. No trace work.

use super::*;

const EXACT_COMPONENT_LIMIT: usize = 16;

pub(crate) fn optimize_family_with(
  w: u64,
  dag: &SharingDag,
  prep: &DagPrep,
  meter: &mut Meter<'_>,
) -> Result<(UniformSharingResult, UniformPlan), SharingError> {
  optimize_at(w, dag, prep, meter, EXACT_COMPONENT_LIMIT)
}

/// Explicit mask enumeration is the bounded exact evaluator: exactly 2^m
/// complete subsets, no recursive search, pruning or partial-state evaluation.
/// The greedy path evaluates each remaining one-member extension. Every count
/// has a feasible row before trimming, even when its delta is negative or tied.
pub(super) fn family_table(
  members: &[TermId],
  k: usize,
  mut cost: impl FnMut(&[TermId]) -> Result<i128, SharingError>,
) -> Result<CTable, SharingError> {
  if k > 24 {
    return Err(internal("unsupported K > 24"));
  }
  if !members.windows(2).all(|p| p[0] < p[1]) {
    return Err(internal("noncanonical component members"));
  }
  let mut rows: CTable = vec![None; members.len() + 1];
  if members.len() <= k {
    for mask in 0..(1u64 << members.len()) {
      let chosen: Vec<_> = members
        .iter()
        .enumerate()
        .filter_map(|(j, &t)| ((mask >> j) & 1 != 0).then_some(t))
        .collect();
      let d = cost(&chosen)?;
      let row = &mut rows[chosen.len()];
      if better(d, &chosen, row.as_ref()) {
        *row = Some((d, chosen));
      }
    }
  } else {
    let mut chosen = Vec::new();
    rows[0] = Some((cost(&chosen)?, chosen.clone()));
    for row in rows.iter_mut().skip(1) {
      let mut best = None;
      for &t in members {
        let Err(at) = chosen.binary_search(&t) else { continue };
        let mut next = chosen.clone();
        next.insert(at, t);
        let d = cost(&next)?;
        if better(d, &next, best.as_ref()) {
          best = Some((d, next));
        }
      }
      let next = best.ok_or_else(|| internal("invalid component members"))?;
      chosen = next.1.clone();
      *row = Some(next);
    }
  }
  Ok(rows)
}

pub(super) fn optimize_at(
  w: u64,
  dag: &SharingDag,
  prep: &DagPrep,
  meter: &mut Meter<'_>,
  k: usize,
) -> Result<(UniformSharingResult, UniformPlan), SharingError> {
  let stage = initial(w, dag, prep, meter)?;
  let n = dag.len();
  // Reuse the full-DAG stamp/value buffers across components. These are
  // scratch only; neither available bits nor chosen effects survive a row.
  let mut cx = CompCtx {
    up: &stage.up,
    #[cfg(any(test, feature = "sharing-reference"))]
    members: Vec::new(),
    area: Vec::new(),
    root_mult: Vec::new(),
    stored_in: Vec::new(),
    #[cfg(any(test, feature = "sharing-reference"))]
    phi0: 0,
    #[cfg(any(test, feature = "sharing-reference"))]
    slack: stage.slack,
    vals: vec![UVal::default(); n],
    stamp: vec![0; n],
    epoch: 0,
    avail: vec![false; n],
  };
  let mut results = Vec::with_capacity(stage.comps.len());
  for members in &stage.comps {
    cx.area = component_area(&stage.up, &prep.facts, members);
    let mut roots = std::collections::BTreeMap::<TermId, u128>::new();
    for &r in dag.roots() {
      if cx.area.binary_search(&r).is_ok() {
        *roots.entry(r).or_default() += 1;
      }
    }
    cx.root_mult = roots.into_iter().collect();
    cx.stored_in =
      cx.area.iter().copied().filter(|&t| stage.up.opaq[ix(t)]).collect();
    let (base, work) = cx.phi(&[])?;
    meter.work(work)?;
    let base = to_i(base)?;
    let rows = family_table(members, k, |chosen| {
      meter.state()?;
      for &t in chosen {
        cx.avail[ix(t)] = true;
      }
      let evaluated = cx.phi(chosen);
      for &t in chosen {
        cx.avail[ix(t)] = false;
      }
      let (value, work) = evaluated?;
      meter.work(work)?;
      to_i(value)?.checked_sub(base).ok_or_else(overflow)
    })?;
    let mut best: Option<Choice> = None;
    for row in &rows {
      let (delta, selected) =
        row.as_ref().ok_or_else(|| internal("missing count"))?;
      if better(*delta, selected, best.as_ref()) {
        best = Some((*delta, selected.clone()));
      }
    }
    let best = best.ok_or_else(|| internal("empty table"))?;
    let bound = best.0.checked_add(stage.slack).ok_or_else(overflow)?;
    let trimmed: CTable =
      rows.into_iter().map(|r| r.filter(|(d, _)| *d <= bound)).collect();
    results.push((best, trimmed));
  }
  drop(cx);
  // The reused combiner uses signed additions. Conservatively admit only
  // tables for which every prefix sum and final model addition fits i128;
  // this checked guard does not change the production numeric contract.
  let mut bound = 9u128; // largest TagN count header
  for table in results.iter().map(|(_, rows)| rows) {
    let magnitude =
      table.iter().flatten().map(|(d, _)| d.unsigned_abs()).max().unwrap_or(0);
    bound = bound.checked_add(magnitude).ok_or_else(overflow)?;
  }
  for value in dag
    .roots()
    .iter()
    .map(|&r| stage.up.base[ix(r)].cost)
    .chain(stage.cs.iter().map(|&c| stage.up.base[ix(c)].inl))
  {
    bound = bound.checked_add(value).ok_or_else(overflow)?;
  }
  let _ = to_i(bound)?;
  combine_uniform(w, dag, prep, meter, stage, results)
}
