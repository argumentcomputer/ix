//! Family normalization at a configurable exact-subset limit K, with a
//! component and row trace. It is a unit-test control, not the canonical rule
//! (which fixes K = 16 in `family.rs`) and not a totality claim. Initial
//! components alone decide the family. All subsets are evaluated for size <= K;
//! otherwise all counts of one greedy chain are retained. Arithmetic,
//! input/output and phase-2/3 limits still fail closed. No work/time limit
//! changes the family. The greedy tie is the existing `set_prec`.

use super::super::tiered::{
  ShareLayout, TieredSharingResult, finish_candidates, normalize_tiered_with,
  tiered_at_using,
};
use super::*;

/// Trace schema v1; streamed before slack filtering. Model work is not native
/// time or a proved operational cost. `closure` is the full upward closure.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Event {
  /// Cooperative observation/abort point, not part of the family trace.
  Progress,
  Input {
    input_visits: u64,
    interned_nodes: u64,
    dag_nodes: usize,
    edges: usize,
    roots: usize,
    table_entries: usize,
    refs: usize,
    univs: usize,
    level_args: usize,
    scalar_bits: u128,
    max_scalar_bits: u32,
  },
  Width {
    width: u64,
    certain: usize,
    uncertain: usize,
    components: usize,
    slack: i128,
  },
  Component {
    width: u64,
    index: usize,
    mode: &'static str,
    members: Vec<TermId>,
    area: usize,
    closure: usize,
  },
  Row {
    width: u64,
    index: usize,
    mode: &'static str,
    count: usize,
    delta: i128,
    selected: Vec<TermId>,
  },
}

type Observe<'a> = dyn FnMut(&Event) -> Result<(), SharingError> + 'a;

fn input_event(c: &Constant, dag: &SharingDag, m: &Meter<'_>) -> Event {
  let mut bits = 0u128;
  let mut max_bits = 0;
  let mut level_args = 0;
  for node in dag.nodes() {
    if let Node::Ref(_, us) | Node::Rec(_, us) = node {
      level_args += us.len();
    }
    for s in node.scalars() {
      let b = (u64::BITS - s.leading_zeros()).max(1);
      bits += u128::from(b);
      max_bits = max_bits.max(b);
    }
  }
  Event::Input {
    input_visits: m.stats.input_nodes,
    interned_nodes: m.stats.distinct_nodes,
    dag_nodes: dag.len(),
    edges: dag.nodes().iter().map(|n| n.children().as_slice().len()).sum(),
    roots: dag.roots().len(),
    table_entries: c.sharing.len(),
    refs: c.refs.len(),
    univs: c.univs.len(),
    level_args,
    scalar_bits: bits,
    max_scalar_bits: max_bits,
  }
}

fn closure_size(facts: &Facts, members: &[TermId]) -> usize {
  let mut seen: FxHashSet<TermId> = members.iter().copied().collect();
  let mut todo = members.to_vec();
  while let Some(t) = todo.pop() {
    for &p in &facts.parents[ix(t)] {
      if seen.insert(p) {
        todo.push(p);
      }
    }
  }
  seen.len()
}

fn component_event(
  w: u64,
  j: usize,
  mode: &'static str,
  members: &[TermId],
  area: usize,
  facts: &Facts,
) -> Event {
  Event::Component {
    width: w,
    index: j,
    mode,
    members: members.to_vec(),
    area,
    closure: closure_size(facts, members),
  }
}

fn width_event(w: u64, s: &Initial<'_>) -> Event {
  Event::Width {
    width: w,
    certain: s.cs.len(),
    uncertain: s.unc.len(),
    components: s.comps.len(),
    slack: s.slack,
  }
}

/// Classification and source metrics only: never calls component search,
/// convolution, knapsack, phase 2, or materialization. Serialized input bytes
/// (including unreachable entries and universe payloads) are supplied by the
/// runner, separately from these reachable-DAG/payload metrics.
pub(crate) fn classify(
  c: &Constant,
  limits: &ExactSharingLimits,
  observe: &mut Observe<'_>,
) -> Result<(), SharingError> {
  let mut m = Meter::new(limits);
  let dag = SharingDag::build(
    &constant_info_root_exprs(&c.info),
    Some(&c.sharing),
    &mut m,
  )?;
  observe(&input_event(c, &dag, &m))?;
  let prep = DagPrep::new(&dag);
  for w in 1..=3 {
    let stage = initial(w, &dag, &prep, &mut m)?;
    observe(&width_event(w, &stage))?;
    for (j, members) in stage.comps.iter().enumerate() {
      let area = component_area(&stage.up, &prep.facts, members);
      observe(&component_event(
        w,
        j,
        "classify",
        members,
        area.len(),
        &prep.facts,
      ))?;
    }
  }
  Ok(())
}

use super::family::family_table;

fn uniform_family(
  w: u64,
  dag: &SharingDag,
  prep: &DagPrep,
  meter: &mut Meter<'_>,
  k: usize,
  observe: &mut Observe<'_>,
) -> Result<(UniformSharingResult, UniformPlan), SharingError> {
  let stage = initial(w, dag, prep, meter)?;
  observe(&width_event(w, &stage))?;
  let n = dag.len();
  // Reuse the full-DAG stamp/value buffers across components. These are
  // scratch only; neither available bits nor chosen effects survive a row.
  let mut cx = CompCtx {
    up: &stage.up,
    members: Vec::new(),
    area: Vec::new(),
    root_mult: Vec::new(),
    stored_in: Vec::new(),
    phi0: 0,
    slack: stage.slack,
    vals: vec![UVal::default(); n],
    stamp: vec![0; n],
    epoch: 0,
    avail: vec![false; n],
  };
  let mut results = Vec::with_capacity(stage.comps.len());
  for (j, members) in stage.comps.iter().enumerate() {
    let mode = if members.len() <= k { "exact" } else { "greedy" };
    cx.area = component_area(&stage.up, &prep.facts, members);
    observe(&component_event(w, j, mode, members, cx.area.len(), &prep.facts))?;
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
    let mut evaluated_rows = 0u64;
    let rows = family_table(members, k, |chosen| {
      meter.state()?;
      if evaluated_rows.is_multiple_of(4096) {
        observe(&Event::Progress)?;
      }
      evaluated_rows += 1;
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
    for (count, row) in rows.iter().enumerate() {
      let (delta, selected) =
        row.as_ref().ok_or_else(|| internal("family trace: missing count"))?;
      observe(&Event::Row {
        width: w,
        index: j,
        mode,
        count,
        delta: *delta,
        selected: selected.clone(),
      })?;
      if better(*delta, selected, best.as_ref()) {
        best = Some((*delta, selected.clone()));
      }
    }
    let best = best.ok_or_else(|| internal("family trace: empty table"))?;
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

/// Test output only. Production phase 2/3 and all validation remain;
/// their resource/format errors are reported, not converted to a success.
/// No admitted family changes when a budget is exhausted. K is test
/// data (0..=24), NOT a format identifier or default compiler option.
pub(crate) fn normalize(
  c: &Constant,
  limits: &ExactSharingLimits,
  k: usize,
  observe: &mut Observe<'_>,
) -> Result<(Constant, TieredSharingResult), SharingError> {
  if k > 24 {
    return Err(internal("family trace: unsupported K > 24"));
  }
  normalize_tiered_with(c, limits, |dag| {
    let prep = DagPrep::new(dag);
    let mut candidates = Vec::with_capacity(3);
    for w in 1..=3 {
      let mut meter = Meter::new(limits);
      let out = tiered_at_using(
        ShareLayout::TagN,
        dag,
        &prep,
        &mut meter,
        w,
        |meter| uniform_family(w, dag, &prep, meter, k, observe),
      )?;
      candidates.push(Ok(out));
    }
    finish_candidates(ShareLayout::TagN, dag, &prep, limits, candidates)
  })
}

#[cfg(test)]
mod tests {
  use super::*;

  // Independent oracle: complete boolean-vector domain, lexicographically
  // ordered (false before true), then integer cost. No set_prec or family
  // helper participates in choosing a reference row. Odd seeds place the
  // members on both sides of the old 32-bit term-ID limit.
  #[test]
  fn family_trace_all_counts_oracle() {
    for n in 0..=7 {
      for seed in 0..20u64 {
        let base: TermId = if seed % 2 == 1 { (1 << 32) - 10 } else { 0 };
        let members: Vec<TermId> = (0..n).map(|j| base + 3 * j + 2).collect();
        let mut choices = Vec::new();
        for mask in 0..(1u64 << n) {
          let flags: Vec<bool> = (0..n).map(|j| (mask >> j) & 1 != 0).collect();
          let delta =
            i128::from((mask.wrapping_mul(17 + seed) ^ (mask >> 2)) % 11) - 7;
          choices.push((delta, flags));
        }
        choices.sort();
        let set = |flags: &[bool]| {
          members
            .iter()
            .zip(flags)
            .filter_map(|(&t, &b)| b.then_some(t))
            .collect::<Vec<_>>()
        };
        for k in 0..=n {
          let actual = family_table(&members, k, |s| {
            Ok(choices.iter().find(|(_, flags)| set(flags) == s).unwrap().0)
          })
          .unwrap();
          let mut previous = vec![false; n];
          for (count, row) in actual.iter().enumerate() {
            let expected = choices
              .iter()
              .find(|(_, flags)| {
                flags.iter().filter(|&&b| b).count() == count
                  && (n <= k
                    || previous.iter().zip(flags).all(|(&a, &b)| !a || b))
              })
              .unwrap();
            assert_eq!(
              row,
              &Some((expected.0, set(&expected.1))),
              "n={n} k={k} seed={seed}"
            );
            previous.clone_from(&expected.1);
          }
        }
      }
    }
  }

  #[test]
  fn family_trace_threshold_ties_and_refusals() {
    for n in [0usize, 1, 2, 12, 13, 16, 17] {
      let members: Vec<_> = (0..n).collect();
      for k in [0usize, 12, 16] {
        let mut calls = 0;
        let rows = family_table(&members, k, |_| {
          calls += 1;
          Ok(-3)
        })
        .unwrap();
        assert_eq!(calls, if n <= k { 1 << n } else { 1 + n * (n + 1) / 2 });
        for (q, row) in rows.iter().enumerate() {
          assert_eq!(row, &Some((-3, members[members.len() - q..].to_vec())));
        }
      }
    }
    assert!(family_table(&[2, 2], 2, |_| Ok(0)).is_err());
    assert!(family_table(&[2, 1], 2, |_| Ok(0)).is_err());
    assert!(family_table(&[], 25, |_| Ok(0)).is_err());
    assert!(family_table(&[1, 2], 0, |_| Err(overflow())).is_err());
  }
}
