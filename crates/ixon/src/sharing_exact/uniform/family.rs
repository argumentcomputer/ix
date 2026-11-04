//! Production phase-1 family: all subsets for at most sixteen initial
//! members, otherwise the complete setPrec-least greedy chain.
//! Only the fixed entry is reachable from production tiered normalization;
//! configurable gates remain private for reference tests. No trace work.

use super::*;
use crate::sharing_exact::Resource;

const EXACT_COMPONENT_LIMIT: usize = 16;

// The Lean familyCalls/familyStoredSum model, not measured native work.
// Greedy extensions reuse their winning cost here, but are charged as the
// reference recipe: all extensions followed by every emitted chain row.
fn family_calls(m: usize, k: usize) -> Option<u128> {
  let n = m as u128;
  if m <= k {
    1u128.checked_shl(u32::try_from(m).ok()?)
  } else {
    n.checked_mul(n.checked_add(1)?)?
      .checked_div(2)?
      .checked_add(n)?
      .checked_add(1)
  }
}

fn family_work(
  m: usize,
  k: usize,
  closure: usize,
  calls: u128,
) -> Option<u128> {
  let n = m as u128;
  let stored = if m <= k {
    n.checked_mul(1u128.checked_shl(u32::try_from(m.saturating_sub(1)).ok()?)?)?
  } else {
    let pairs = n.checked_mul(n.checked_add(1)?)?;
    pairs
      .checked_mul(n.checked_add(2)?)?
      .checked_div(6)?
      .checked_add(pairs / 2)?
  };
  calls.checked_add(1)?.checked_mul(closure as u128)?.checked_add(stored)
}

/// Check the mathematical precharge before narrowing it to the public u64
/// counter. Neither a charge nor an accumulated total may saturate into a
/// success at u64::MAX. Overflow here is the corresponding budget refusal.
fn charge(
  total: &mut u64,
  amount: Option<u128>,
  limit: u64,
  resource: Resource,
) -> Result<(), SharingError> {
  let next = amount.and_then(|n| n.checked_add(u128::from(*total)));
  let Some(next) = next.filter(|&n| n <= u128::from(limit)) else {
    return Err(Meter::exhausted(resource, limit));
  };
  *total = u64::try_from(next).expect("precharge checked against a u64 limit");
  Ok(())
}

/// Count members plus every ancestor, including ancestors above opaque
/// nodes. This is Lean SCtx.closure, not the smaller stopped evaluation area.
/// Width-local buffers are reused; each node/edge is visited at most once
/// per closure, with a complete stamp reset only when the epoch wraps.
struct ClosureCount {
  seen: Vec<u32>,
  epoch: u32,
  pending: Vec<TermId>,
}

impl ClosureCount {
  fn new(n: usize) -> Self {
    Self { seen: vec![0; n], epoch: 0, pending: Vec::new() }
  }

  fn count(&mut self, parents: &[Vec<TermId>], members: &[TermId]) -> usize {
    self.epoch = self.epoch.wrapping_add(1);
    if self.epoch == 0 {
      self.seen.fill(0);
      self.epoch = 1;
    }
    self.pending.clear();
    self.pending.extend_from_slice(members);
    let mut count = 0;
    while let Some(t) = self.pending.pop() {
      if self.seen[ix(t)] == self.epoch {
        continue;
      }
      self.seen[ix(t)] = self.epoch;
      count += 1;
      self.pending.extend_from_slice(&parents[ix(t)]);
    }
    count
  }
}

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
pub(super) fn family_table<D: Delta>(
  members: &[TermId],
  k: usize,
  mut cost: impl FnMut(&[TermId]) -> Result<D, SharingError>,
) -> Result<CTable<D>, SharingError> {
  if k > 24 {
    return Err(internal("unsupported K > 24"));
  }
  if !members.windows(2).all(|p| p[0] < p[1]) {
    return Err(internal("noncanonical component members"));
  }
  let mut rows: CTable<D> = vec![None; members.len() + 1];
  if members.len() <= k {
    for mask in 0..(1u64 << members.len()) {
      let chosen: Vec<_> = members
        .iter()
        .enumerate()
        .filter_map(|(j, &t)| ((mask >> j) & 1 != 0).then_some(t))
        .collect();
      let d = cost(&chosen)?;
      let row = &mut rows[chosen.len()];
      if better(&d, &chosen, row.as_ref()) {
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
        if better(&d, &next, best.as_ref()) {
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

/// The fixed-family optimum at width `w` with family bound `k`: computed in
/// `u128`/`i128` and, if a value leaves that range (`LengthOverflow`), again
/// in exact integers from the meter as it was before the first run, so the
/// counters and the result are those of one exact run (`arith`).
pub(super) fn optimize_at(
  w: u64,
  dag: &SharingDag,
  prep: &DagPrep,
  meter: &mut Meter<'_>,
  k: usize,
) -> Result<(UniformSharingResult, UniformPlan), SharingError> {
  let before = meter.stats.clone();
  match optimize_in::<Fast>(w, dag, prep, meter, k) {
    Err(SharingError::FormatBound(FormatBound::LengthOverflow)) => {
      meter.stats = before;
      optimize_in::<Exact>(w, dag, prep, meter, k)
    },
    result => result,
  }
}

/// [`optimize_at`] in the representation `A`.
pub(super) fn optimize_in<A: Arith>(
  w: u64,
  dag: &SharingDag,
  prep: &DagPrep,
  meter: &mut Meter<'_>,
  k: usize,
) -> Result<(UniformSharingResult, UniformPlan), SharingError> {
  if k > 24 {
    return Err(internal("unsupported K > 24"));
  }
  let stage = initial::<A>(w, dag, prep, meter)?;
  let n = dag.len();
  let mut closure = ClosureCount::new(n);
  // Reuse the full-DAG stamp/value buffers across components. These are
  // scratch only; neither available bits nor chosen effects survive a row.
  let mut cx = CompCtx::<A> {
    up: &stage.up,
    #[cfg(any(test, feature = "sharing-reference"))]
    members: Vec::new(),
    area: Vec::new(),
    root_mult: Vec::new(),
    stored_in: Vec::new(),
    #[cfg(any(test, feature = "sharing-reference"))]
    phi0: A::U::default(),
    #[cfg(any(test, feature = "sharing-reference"))]
    slack: stage.slack.clone(),
    vals: vec![UVal::default(); n],
    stamp: vec![0; n],
    epoch: 0,
    avail: vec![false; n],
  };
  let mut results = Vec::with_capacity(stage.comps.len());
  for members in &stage.comps {
    let calls = family_calls(members.len(), k);
    charge(
      &mut meter.stats.states_created,
      calls,
      meter.limits.max_states,
      Resource::States,
    )?;
    let closure_size = closure.count(&prep.facts.parents, members);
    charge(
      &mut meter.stats.work,
      calls.and_then(|n| family_work(members.len(), k, closure_size, n)),
      meter.limits.max_work,
      Resource::Work,
    )?;
    cx.area = component_area_with(
      &stage.up,
      &prep.facts,
      members,
      &mut cx.stamp,
      &mut cx.epoch,
      &mut closure.pending,
    );
    let mut roots = std::collections::BTreeMap::<TermId, u64>::new();
    for &r in dag.roots() {
      if cx.area.binary_search(&r).is_ok() {
        *roots.entry(r).or_default() += 1;
      }
    }
    cx.root_mult = roots.into_iter().map(|(r, m)| (r, A::u(m))).collect();
    cx.stored_in =
      cx.area.iter().copied().filter(|&t| stage.up.opaq[ix(t)]).collect();
    let (base, _) = cx.phi(&[])?;
    let base = A::signed(&base)?;
    let rows = family_table(members, k, |chosen| {
      for &t in chosen {
        cx.avail[ix(t)] = true;
      }
      let evaluated = cx.phi(chosen);
      for &t in chosen {
        cx.avail[ix(t)] = false;
      }
      let (value, _) = evaluated?;
      A::signed(&value)?.minus(&base)
    })?;
    let mut best: Option<Choice<A::S>> = None;
    for row in &rows {
      let (delta, selected) =
        row.as_ref().ok_or_else(|| internal("missing count"))?;
      if better(delta, selected, best.as_ref()) {
        best = Some((delta.clone(), selected.clone()));
      }
    }
    let best = best.ok_or_else(|| internal("empty table"))?;
    let bound = best.0.plus(&stage.slack)?;
    let trimmed: CTable<A::S> =
      rows.into_iter().map(|r| r.filter(|(d, _)| *d <= bound)).collect();
    results.push((best, trimmed));
  }
  drop(cx);
  combine_uniform(w, dag, prep, meter, stage, results)
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn logical_charges_count_the_reference_recipe() {
    for k in [0, 1, 16] {
      for m in 0..=18usize {
        let sizes: Vec<usize> = if m <= k {
          (0..1u64 << m).map(|s| s.count_ones() as usize).collect()
        } else {
          (1..=m)
            .flat_map(|q| std::iter::repeat_n(q, m - q + 1))
            .chain(0..=m)
            .collect()
        };
        let calls = sizes.len() as u128;
        assert_eq!(family_calls(m, k), Some(calls));
        for closure in [0, 1, 19, 203] {
          let work = closure + sizes.iter().map(|q| closure + q).sum::<usize>();
          assert_eq!(family_work(m, k, closure, calls), Some(work as u128));
        }
      }
    }
  }

  #[test]
  fn closure_charge_reuses_buffers_without_losing_ancestors() {
    let parents =
      vec![vec![2, 3], vec![3], vec![4], vec![4, 4], vec![5], vec![]];
    let mut counter = ClosureCount::new(parents.len());
    for mask in (0..64).chain((0..64).rev()) {
      let members: Vec<_> = (0..6).filter(|t| mask >> t & 1 != 0).collect();
      let mut expected = std::collections::BTreeSet::new();
      let mut pending = members.clone();
      while let Some(t) = pending.pop() {
        if expected.insert(t) {
          pending.extend_from_slice(&parents[ix(t)]);
        }
      }
      assert_eq!(counter.count(&parents, &members), expected.len());
      counter.epoch = u32::MAX; // same closure after the wrap/reset path
      assert_eq!(counter.count(&parents, &members), expected.len());
    }
    assert_eq!(counter.count(&parents, &[0]), 5);
  }

  #[test]
  fn precharges_never_saturate_into_success() {
    let mut total = 0;
    charge(&mut total, Some(u128::from(u64::MAX)), u64::MAX, Resource::States)
      .unwrap();
    assert_eq!(total, u64::MAX);
    for amount in [Some(1), Some(u128::MAX), None] {
      assert_eq!(
        charge(&mut total, amount, u64::MAX, Resource::States),
        Err(Meter::exhausted(Resource::States, u64::MAX))
      );
    }
    let calls = family_calls(usize::MAX, 0);
    assert!(charge(&mut 0, calls, u64::MAX, Resource::States).is_err());
    assert!(
      charge(
        &mut 0,
        calls.and_then(|n| family_work(usize::MAX, 0, 1, n)),
        u64::MAX,
        Resource::Work
      )
      .is_err()
    );
  }

  #[test]
  fn family_refusals_follow_state_then_closure_work_precharges() {
    let t2 = Expr::all(Expr::sort(0), Expr::all(Expr::sort(0), Expr::sort(0)));
    let roots = [Expr::all(t2.clone(), t2)];
    let limits = ExactSharingLimits::default();
    let dag = SharingDag::from_expanded_roots(&roots, &limits).unwrap();
    let prep = DagPrep::new(&dag);
    let stage =
      initial::<Fast>(3, &dag, &prep, &mut Meter::new(&limits)).unwrap();
    assert_eq!(stage.comps.len(), 1);
    assert_eq!(stage.comps[0].len(), 1);
    let closure =
      ClosureCount::new(dag.len()).count(&prep.facts.parents, &stage.comps[0]);
    assert_eq!(closure, 2);
    let run = |k, states, work| {
      let limits = ExactSharingLimits {
        max_states: states,
        max_work: work,
        ..limits.clone()
      };
      optimize_at(3, &dag, &prep, &mut Meter::new(&limits), k).map(|r| r.0)
    };
    for (states, work, resource) in [
      (0, 0, Resource::States),
      (1, 0, Resource::States),
      (2, 6, Resource::Work),
    ] {
      assert_eq!(
        run(16, states, work).unwrap_err(),
        Meter::exhausted(
          resource,
          if resource == Resource::States { states } else { work }
        )
      );
    }
    let exact = run(16, 2, limits.max_work).unwrap();
    let greedy = run(0, 3, limits.max_work).unwrap();
    assert_eq!(
      (&exact.stored, exact.model_len, &exact.component_tables),
      (&greedy.stored, greedy.model_len, &greedy.component_tables)
    );
    assert_eq!(exact.stats.states_created, 2);
    assert_eq!(greedy.stats.states_created, 3);
    assert_eq!(greedy.stats.work - exact.stats.work, 3);
  }
}
