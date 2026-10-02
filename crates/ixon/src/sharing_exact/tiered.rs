//! Tiered canonical sharing: uniform-width selection, slot allocation and
//! re-materialization under a Share layout.
//!
//! A rule-for-rule port of the Lean `Ix/Sharing/Exact/Tiered.lean`.
//!
//! The one layout, [`ShareLayout::TagN`], prices a Share at table index `i` by
//! the wire width of the TagN Share code ([`tagn_width`]: 1, 2, 3, 4, 5 or 9
//! bytes, the width of `TagN::put(4, 0xB, i)`). The output is written with that code,
//! so the model length and the serialized length agree, which is checked.
//!
//! **Width selection.** Phase 1 runs at each uniform width `w` in 1, 2, 3,
//! each result is carried through phases 2 and 3, and the construction
//! returns the candidate with the fewest final layout bytes; ties go to the
//! lower `w`, then `set_prec` on the stored set. An error at any width fails
//! the call. Each candidate is exact per phase as described below; the
//! final choice is the real-byte minimum over the three candidates, not a
//! global optimum. One candidate is `tiered_at` (Lean `tieredAtWidth`).
//!
//! **Phase 1 (selection).** The stored set and its bodies are the
//! uniform-`w` optimum ([`super::optimize_dag_uniform`]).
//!
//! **Phase 2 (slot allocation).** From the phase-1 output, `ref(t)` counts
//! the `Share(t)` in its entries and roots; `t` depends on `u` when `t`'s
//! phase-1 body contains `Share(u)`. The first tier is a maximum-`ref` set
//! of at most 8 stored terms closed under dependencies (ties: order stored
//! terms by `ref` descending then ID ascending, and prefer the set that
//! contains the first term where two sets differ), found by branch and
//! bound. The table is the first tier in pinned priority order, then the
//! rest in the Kahn priority order: repeatedly the available entry (every
//! entry its phase-1 body references already placed) with the largest
//! `ref`, ties by the smaller ID. If that order's reference cost
//! `sum ref(t) * width_at(index t)` exceeds the phase-1 order's, the phase-1
//! order is kept. The final order is checked to respect the dependencies.
//!
//! **Phase 3 (re-materialization).** Every entry is re-encoded with `C_M`
//! under the entries before it, priced by `width_at(index)`, and the roots
//! under all entries; byte-least ties. The result is checked to be no
//! longer (in layout bytes) than phase 1. The selection needs only the
//! lengths, so only the returned candidate's expressions are built; they are
//! measured and re-expanded (every candidate's limits are still checked with
//! the same counts; see [`Candidate`]).

use std::sync::Arc;

use rustc_hash::FxHashMap;

use super::cost::{Len, exprs_len_with, tag0_len};
use super::dag::{Node, SharingDag, TermId, ix};
use super::dict::{
  Evaluation, Hide, IncrementalCosts, Indices, LazyCosts, Materializer, Plan,
  PlanShares, Widths, eval_node,
};
use super::prof::{self, Phase};
use super::uniform::{
  DagPrep, UniformSharingResult, optimize_uniform_with, pinned_order, set_prec,
};
use super::{
  ExactSharingLimits, FormatBound, Meter, NormalizeBytesError, Parallelism,
  Resource, ResourceExhausted, SharingError, constant_fixed_len,
  constant_info_root_exprs, rebuild_constant_info,
};
use crate::constant::Constant;
use crate::expr::Expr;
use crate::tag::TagN;

fn internal(msg: impl Into<String>) -> SharingError {
  SharingError::Internal(msg.into())
}

fn overflow() -> SharingError {
  SharingError::FormatBound(FormatBound::LengthOverflow)
}

fn len64(n: usize) -> u64 {
  u64::try_from(n).unwrap_or(u64::MAX)
}

/// End (exclusive) of the 1-byte TagN Share rung (the Share flag is 4 bits,
/// so the payload has 4 bits; `TagN::end1(4)`).
pub const TAGN_RUNG1_END: u64 = TagN::end1(4);
/// End of the 2-byte rung (2 + 8 value bits; `TagN::end2(4)`).
pub const TAGN_RUNG2_END: u64 = TagN::end2(4);
/// End of the 3-byte rung (2 following bytes; `TagN::end3(4)`).
pub const TAGN_RUNG3_END: u64 = TagN::end3(4);
/// End of the 4-byte rung (3 following bytes; `TagN::end4(4)`).
pub const TAGN_RUNG4_END: u64 = TagN::end4(4);
/// End of the 5-byte rung (4 following bytes; `TagN::end5(4)`); every larger
/// `u64` index is in the 9-byte rung.
pub const TAGN_RUNG5_END: u64 = TagN::end5(4);

/// Byte width of the TagN Share at index `i` (`TagN::byte_width(4, i)`:
/// 1, 2, 3, 4, 5 or 9), as Lean's `tagNWidth`.
pub fn tagn_width(i: u64) -> u64 {
  len64(TagN::byte_width(4, i))
}

/// The Share width layout: the TagN Share code, the only wire code.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ShareLayout {
  /// The TagN Share code ([`tagn_width`]).
  TagN,
}

impl ShareLayout {
  /// Width of the Share at table index `i`.
  pub fn width_at(self, i: u64) -> u64 {
    match self {
      ShareLayout::TagN => tagn_width(i),
    }
  }

  /// First index whose width exceeds 2.
  pub fn tier2_end(self) -> u64 {
    match self {
      ShareLayout::TagN => TAGN_RUNG2_END,
    }
  }

  /// The layout of the wire Share code (TagN).
  pub fn wire() -> ShareLayout {
    ShareLayout::TagN
  }
}

/// Variable length of an encoding with every Share priced by `layout`.
pub fn layout_bytes(
  layout: ShareLayout,
  sharing: &[Arc<Expr>],
  roots: &[Arc<Expr>],
) -> Option<u64> {
  let price = |i: u64| layout.width_at(i);
  exprs_len_with(len64(sharing.len()), sharing.iter().chain(roots), &price)
}

/// All `Share` indices of an expression, with multiplicity, in left-to-right
/// pre-order.
#[cfg(test)]
pub(crate) fn share_indices(e: &Expr, out: &mut Vec<u64>) {
  let mut stack: Vec<&Expr> = vec![e];
  while let Some(x) = stack.pop() {
    if let Expr::Share(i) = x {
      out.push(*i);
    }
    for c in super::cost::expr_children(x).into_iter().rev().flatten() {
      stack.push(c.as_ref());
    }
  }
}

/// Real table indices priced by a layout.
struct LayoutIndex {
  index: Vec<Option<u64>>,
  layout: ShareLayout,
}

impl Widths for LayoutIndex {
  fn width(&self, t: TermId) -> Option<u64> {
    self.index[ix(t)].map(|i| self.layout.width_at(i))
  }
}

impl Indices for LayoutIndex {
  fn index(&self, t: TermId) -> Option<u64> {
    self.index[ix(t)]
  }
}

// ---------------------------------------------------------------------------
// First-tier allocation
// ---------------------------------------------------------------------------

/// Whether every term of `order` comes after all its dependencies (Lean
/// `respectsDeps`).
fn respects_deps(
  order: &[TermId],
  deps: &FxHashMap<TermId, Vec<TermId>>,
) -> bool {
  let pos: FxHashMap<TermId, usize> =
    order.iter().enumerate().map(|(i, &t)| (t, i)).collect();
  order.iter().enumerate().all(|(i, t)| {
    deps
      .get(t)
      .is_none_or(|ds| ds.iter().all(|d| pos.get(d).is_some_and(|&p| p < i)))
  })
}

/// The Kahn priority order of `rest` (Lean `kahnOrder`): repeatedly place
/// the available term (every dependency of it in `rest` already placed) of
/// the largest weight, ties by the smaller ID. Terms left over, which
/// acyclic dependencies never leave, follow in priority order.
pub(crate) fn kahn_order(
  weight: &FxHashMap<TermId, u64>,
  deps: &FxHashMap<TermId, Vec<TermId>>,
  rest: &[TermId],
) -> Vec<TermId> {
  let w = |t: TermId| weight.get(&t).copied().unwrap_or(0);
  let mut sorted = rest.to_vec();
  sorted.sort_by(|&a, &b| w(b).cmp(&w(a)).then(a.cmp(&b)));
  let m = sorted.len();
  let rank: FxHashMap<TermId, usize> =
    sorted.iter().enumerate().map(|(i, &t)| (t, i)).collect();
  let mut pend = vec![0usize; m];
  let mut users: Vec<Vec<usize>> = vec![Vec::new(); m];
  let mut seen: Vec<usize> = Vec::new();
  for (i, t) in sorted.iter().enumerate() {
    seen.clear();
    for d in deps.get(t).into_iter().flatten() {
      if let Some(&r) = rank.get(d)
        && !seen.contains(&r)
      {
        seen.push(r);
        pend[i] += 1;
        users[r].push(i);
      }
    }
  }
  let mut ready: std::collections::BTreeSet<usize> =
    (0..m).filter(|&i| pend[i] == 0).collect();
  let mut placed = vec![false; m];
  let mut out = Vec::with_capacity(m);
  while let Some(r) = ready.pop_first() {
    placed[r] = true;
    out.push(sorted[r]);
    for &u in &users[r] {
      pend[u] -= 1;
      if pend[u] == 0 {
        ready.insert(u);
      }
    }
  }
  out.extend((0..m).filter(|&i| !placed[i]).map(|i| sorted[i]));
  out
}

/// Maximum-weight dependency-closed set of at most `cap` stored terms, with
/// the tie order of the module docs. `deps[t]` are the terms `t`
/// references. Returns the set (ascending) and the states visited.
pub fn first_tier(
  stored: &[TermId],
  weight: &FxHashMap<TermId, u64>,
  deps: &FxHashMap<TermId, Vec<TermId>>,
  cap: usize,
  limits: &ExactSharingLimits,
) -> Result<(Vec<TermId>, u64), SharingError> {
  let w = |t: TermId| weight.get(&t).copied().unwrap_or(0);
  let mut items: Vec<TermId> = stored.to_vec();
  items.sort_by(|&a, &b| w(b).cmp(&w(a)).then(a.cmp(&b)));
  // Closures with early cutoff above `cap`, with the same pop budget as
  // the reference (`4 * |stored| + 4` pops).
  let mut closure: FxHashMap<TermId, Vec<TermId>> = FxHashMap::default();
  let fuel = stored.len().saturating_mul(4).saturating_add(4);
  // The visited set never exceeds `cap + 1` terms (the search stops there),
  // so it is a short vector.
  let mut seen: Vec<TermId> = Vec::new();
  let mut stack: Vec<TermId> = Vec::new();
  for &t in stored {
    seen.clear();
    stack.clear();
    stack.push(t);
    let mut ok = true;
    for _ in 0..fuel {
      let Some(u) = stack.pop() else { break };
      if seen.contains(&u) {
        continue;
      }
      seen.push(u);
      if seen.len() > cap {
        ok = false;
        break;
      }
      if let Some(ds) = deps.get(&u) {
        stack.extend_from_slice(ds);
      }
    }
    if ok {
      let mut cl: Vec<TermId> = seen.clone();
      cl.sort_unstable();
      closure.insert(t, cl);
    }
  }
  // Depth-first branch and bound, "include" before "exclude"; the first
  // maximum found wins ties, so later subtrees are pruned when their bound
  // does not exceed the best weight.
  // `excluded` holds the item positions decided "exclude" on the path, as a
  // bit set (a term is excluded exactly when its item position is).
  struct Frame {
    pos: usize,
    cur: u64,
    in_f: Vec<TermId>,
    excluded: Vec<u64>,
  }
  let item_pos: FxHashMap<TermId, usize> =
    items.iter().enumerate().map(|(i, &t)| (t, i)).collect();
  let is_excluded = |excluded: &[u64], u: &TermId| {
    item_pos.get(u).is_some_and(|&i| {
      excluded.get(i / 64).is_some_and(|w| w >> (i % 64) & 1 == 1)
    })
  };
  let mut best: Option<(u64, Vec<TermId>)> = None;
  let mut states: u64 = 0;
  let mut stack =
    vec![Frame { pos: 0, cur: 0, in_f: Vec::new(), excluded: Vec::new() }];
  while let Some(Frame { pos, cur, in_f, excluded }) = stack.pop() {
    states += 1;
    if states > limits.max_states {
      return Err(SharingError::ResourceExhausted(ResourceExhausted {
        resource: Resource::States,
        limit: limits.max_states,
      }));
    }
    let room = cap.saturating_sub(in_f.len());
    let mut bound = cur;
    let mut taken = 0usize;
    for &t in &items[pos.min(items.len())..] {
      if taken >= room {
        break;
      }
      if in_f.contains(&t) {
        continue;
      }
      bound = bound.saturating_add(w(t));
      taken += 1;
    }
    if let Some((b, _)) = &best
      && bound <= *b
    {
      continue;
    }
    if pos >= items.len() {
      if best.as_ref().is_none_or(|(b, _)| cur > *b) {
        best = Some((cur, in_f));
      }
      continue;
    }
    let t = items[pos];
    if in_f.contains(&t) {
      stack.push(Frame { pos: pos + 1, cur, in_f, excluded });
      continue;
    }
    let mut exclude = excluded.clone();
    if exclude.len() <= pos / 64 {
      exclude.resize(pos / 64 + 1, 0);
    }
    exclude[pos / 64] |= 1 << (pos % 64);
    let mut include: Option<Frame> = None;
    if let Some(cl) = closure.get(&t) {
      let new: Vec<TermId> =
        cl.iter().copied().filter(|u| !in_f.contains(u)).collect();
      if !cl.iter().any(|u| is_excluded(&excluded, u))
        && in_f.len() + new.len() <= cap
      {
        let add = new.iter().fold(0u64, |acc, &u| acc.saturating_add(w(u)));
        let mut in2 = in_f.clone();
        in2.extend_from_slice(&new);
        include = Some(Frame {
          pos: pos + 1,
          cur: cur.saturating_add(add),
          in_f: in2,
          excluded,
        });
      }
    }
    stack.push(Frame { pos: pos + 1, cur, in_f, excluded: exclude });
    if let Some(f) = include {
      stack.push(f);
    }
  }
  match best {
    Some((_, mut s)) => {
      s.sort_unstable();
      Ok((s, states))
    },
    None => Ok((Vec::new(), states)),
  }
}

/// Whether every stored term of `order` comes after all its stored
/// descendants (the order is closed under stored descendants). One pass in
/// increasing ID: the frontier of a term is the largest position among its
/// nearest stored descendants-or-self, and every stored term's children's
/// frontiers must be before it (then, by induction, every stored descendant
/// is).
fn descendant_closed(nodes: &[Node], order: &[TermId]) -> bool {
  #[cfg(test)]
  if FORCE_PER_PREFIX.with(std::cell::Cell::get) {
    return false;
  }
  let n = nodes.len();
  let mut pos: Vec<u64> = vec![u64::MAX; n];
  for (i, &t) in order.iter().enumerate() {
    pos[ix(t)] = len64(i);
  }
  // `frontier[x] = 0` for none, else the position plus one.
  let mut frontier: Vec<u64> = vec![0; n];
  for x in 0..n {
    let below = nodes[x]
      .children()
      .as_slice()
      .iter()
      .map(|&c| frontier[ix(c)])
      .max()
      .unwrap_or(0);
    if pos[x] == u64::MAX {
      frontier[x] = below;
    } else {
      if below > pos[x] {
        return false;
      }
      frontier[x] = pos[x] + 1;
    }
  }
  true
}

#[cfg(test)]
thread_local! {
  /// Test hook: take the per-prefix phase 3 even for closed orders.
  pub(crate) static FORCE_PER_PREFIX: std::cell::Cell<bool> =
    const { std::cell::Cell::new(false) };
}

/// The phase-3 decisions of every task of a candidate whose order is closed
/// under stored descendants, from the evaluation `costs` of the full
/// dictionary `dict`: entry `j` under `dict` with its own Share hidden, the
/// roots under `dict`. They equal the per-prefix decisions: the choice and
/// cost of a term read only the dictionary at and below it, and below entry
/// `j` the prefix `order[..j]` and the full dictionary agree (every stored
/// descendant is in the prefix, at the same index; the entry itself is
/// absent from one and hidden in the other).
#[allow(clippy::too_many_arguments)]
fn one_pass_plans(
  dag: &SharingDag,
  own: &[Len],
  order: &[TermId],
  dict: &LayoutIndex,
  costs: &[Len],
  mat: &mut Materializer,
  work: &mut u64,
) -> Result<Vec<Plan>, SharingError> {
  let nodes = dag.nodes();
  let mut plans = Vec::with_capacity(order.len() + 1);
  for t in order {
    let hide = Hide { inner: dict, hidden: *t };
    plans.push(mat.decide(
      nodes,
      own,
      &hide,
      costs,
      std::slice::from_ref(t),
      work,
    )?);
  }
  plans.push(mat.decide(nodes, own, dict, costs, dag.roots(), work)?);
  Ok(plans)
}

/// The phase-3 evaluation of the growing dictionary: [`LazyCosts`] when its
/// work argument applies, otherwise [`IncrementalCosts`]. Both give the
/// costs of the descendants of prepared targets and the work count of a
/// full evaluation of the current dictionary.
enum Phase3Eval<'a> {
  Lazy(LazyCosts<'a>),
  Eager(IncrementalCosts<'a>),
}

impl Phase3Eval<'_> {
  fn add<W: Widths>(&mut self, t: TermId, widths: &W) {
    match self {
      Phase3Eval::Lazy(e) => e.add(t, widths),
      Phase3Eval::Eager(e) => e.add(t, widths),
    }
  }

  fn prepare<W: Widths>(&mut self, targets: &[TermId], widths: &W) {
    if let Phase3Eval::Lazy(e) = self {
      e.prepare(targets, widths);
    }
  }

  fn costs(&self) -> &[Len] {
    match self {
      Phase3Eval::Lazy(e) => e.costs(),
      Phase3Eval::Eager(e) => e.costs(),
    }
  }

  fn work(&self) -> u64 {
    match self {
      Phase3Eval::Lazy(e) => e.work(),
      Phase3Eval::Eager(e) => e.work(),
    }
  }
}

// ---------------------------------------------------------------------------
// Result and driver
// ---------------------------------------------------------------------------

/// Statistics of the tiered construction.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TieredStats {
  pub layout: ShareLayout,
  /// Terms with in-degree >= 2 and unshared length >= 2.
  pub candidate_count: u64,
  /// Phase-1 uniform width of the returned candidate (the winning width).
  pub w: u64,
  /// Final layout length of every candidate run, as `(w, bytes)` in
  /// increasing `w` (one entry for a single candidate, `tiered_at`).
  pub candidate_lengths: Vec<(u64, u64)>,
  /// Per candidate run, in increasing `w`: `(w, phase-1 uniform-model
  /// length, states_created, work)`, the last two the totals charged to that
  /// candidate's meter. Diagnostic: the counts that the limits act on.
  pub candidate_meters: Vec<(u64, u64, u64, u64)>,
  /// Candidates whose phase 3 ran per prefix (their order is not closed
  /// under stored descendants); the others ran in one pass.
  pub per_prefix_candidates: u64,
  /// Phase-1 uniform-model length.
  pub phase1_model_bytes: u64,
  /// Phase-1 output priced by the layout (its own order).
  pub phase1_layout_bytes: u64,
  /// First-tier search states.
  pub slot_states: u64,
  pub first_tier: Vec<TermId>,
  /// The guard kept the phase-1 order.
  pub kept_phase1_order: bool,
  /// Reference cost `sum ref * width_at` of the phase-1 and final orders.
  pub phase1_ref_cost: u128,
  pub final_ref_cost: u128,
  /// Final length priced by the layout.
  pub phase3_layout_bytes: u64,
  /// `phase1_layout_bytes - phase3_layout_bytes`.
  pub savings: u64,
}

/// Tiered result.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TieredSharingResult {
  pub roots: Vec<Arc<Expr>>,
  pub sharing: Vec<Arc<Expr>>,
  pub table_terms: Vec<TermId>,
  /// Variable length priced by the layout.
  pub model_len: u64,
  /// Real variable length, serialized with the wire codec (`put_expr`).
  pub variable_len: u64,
  pub unshared_len: Option<u64>,
  pub phase1: UniformSharingResult,
  pub stats: TieredStats,
}

/// The tiered canonical construction on a DAG (Lean
/// `canonicalTieredCore`): phases 1-3 at each phase-1 width 1, 2 and 3,
/// returning the candidate with the fewest final layout bytes; ties go to
/// the lower width, then `set_prec` on the stored set. Each candidate runs
/// under its own meter with the same limits, and an error at any width
/// fails the whole call. `par` sets the thread budgets ([`Parallelism`]).
pub(crate) fn tiered(
  layout: ShareLayout,
  dag: &SharingDag,
  limits: &ExactSharingLimits,
  par: Parallelism,
) -> Result<TieredSharingResult, SharingError> {
  // The width-independent tables, shared by the three candidates.
  let prep = DagPrep::new(dag);
  let run = |w: u64| {
    let mut meter = Meter::with_parallelism(limits, par);
    tiered_at(layout, dag, &prep, &mut meter, w)
  };
  let candidates: Vec<Result<Candidate, SharingError>> = if par.widths <= 1 {
    // The sequential reference stops at the first failing width.
    let mut v = Vec::with_capacity(3);
    for w in 1..=3 {
      v.push(Ok(run(w)?));
    }
    v
  } else {
    super::par::map_ranges(3, par.widths, |r| {
      r.map(|i| run(len64(i) + 1)).collect()
    })
  };
  let mut best: Option<Candidate> = None;
  let mut lengths = Vec::with_capacity(3);
  let mut meters = Vec::with_capacity(3);
  let mut per_prefix = 0;
  for (w, c) in (1..=3).zip(candidates) {
    // In width order: the error of the lowest failing width, as above.
    let c = c?;
    per_prefix += u64::from(matches!(c.phase3, Phase3::Plans(_)));
    lengths.push((w, c.result.stats.phase3_layout_bytes));
    meters.extend_from_slice(&c.result.stats.candidate_meters);
    if best.as_ref().is_none_or(|b| tiered_better(&c.result, &b.result)) {
      best = Some(c);
    }
  }
  let best = best.ok_or_else(|| internal("no tiered candidate"))?;
  let mut best = finish(layout, dag, &prep, limits, best)?;
  best.stats.candidate_lengths = lengths;
  best.stats.candidate_meters = meters;
  best.stats.per_prefix_candidates = per_prefix;
  Ok(best)
}

/// A candidate before its expressions are built: the result with empty
/// `roots` and `sharing`, and the phase-3 decisions of every task (entry
/// `j` for `j < k`, then the roots).
///
/// Only the returned candidate is built ([`finish`]): the selection reads
/// the final length, the width and the stored set, which phase 3 computes
/// from the costs. Every limit of a candidate is still checked in
/// [`tiered_at`], in the same order and with the same counts (the work of
/// every task, the input nodes of the re-expansion check, which are the
/// expression nodes the build allocates, and the output length, which the
/// checks of [`finish`] prove equal to the evaluated length); the internal
/// consistency checks of the built expressions run on the returned
/// candidate.
pub(crate) struct Candidate {
  result: TieredSharingResult,
  phase3: Phase3,
}

/// How a candidate's phase-3 expressions are obtained.
enum Phase3 {
  /// The order is closed under stored descendants: every task is decided
  /// under the full dictionary (with the entry's own Share hidden), whose
  /// evaluation `costs` is kept.
  OnePass { costs: Vec<Len> },
  /// The per-prefix decisions of every task.
  Plans(Vec<Plan>),
}

/// Build the expressions of a candidate and check them: the layout price
/// against the evaluation, the re-expansion (same DAG, entries expanding to
/// the stored terms, as many expression nodes as counted) and the real
/// length.
fn finish(
  layout: ShareLayout,
  dag: &SharingDag,
  prep: &DagPrep,
  limits: &ExactSharingLimits,
  cand: Candidate,
) -> Result<TieredSharingResult, SharingError> {
  let Candidate { mut result, phase3 } = cand;
  let nodes = dag.nodes();
  let p = prof::scope(Phase::RematerializeBuild);
  let order = &result.table_terms;
  let k_entries = order.len();
  // Every Share of a task names an entry before it, whose index is its
  // position in the final order.
  let mut dict = LayoutIndex { index: vec![None; nodes.len()], layout };
  for (i, &t) in order.iter().enumerate() {
    dict.index[ix(t)] = Some(len64(i));
  }
  let mut mat = Materializer::new(nodes.len());
  let plans = match phase3 {
    Phase3::Plans(plans) => plans,
    Phase3::OnePass { costs } => {
      // The decisions of every task under the full dictionary (see
      // `one_pass_plans`), and their work.
      let mut work = 0u64;
      let plans = one_pass_plans(
        dag, &prep.own, order, &dict, &costs, &mut mat, &mut work,
      )?;
      let total = result
        .stats
        .candidate_meters
        .first()
        .map_or(0, |m| m.3)
        .saturating_add(work);
      if total > limits.max_work {
        return Err(SharingError::ResourceExhausted(ResourceExhausted {
          resource: Resource::Work,
          limit: limits.max_work,
        }));
      }
      if let Some(m) = result.stats.candidate_meters.first_mut() {
        m.3 = total;
      }
      plans
    },
  };
  let mut entries = Vec::with_capacity(k_entries);
  let mut roots = Vec::new();
  let mut allocated = 0u64;
  for (j, plan) in plans.iter().enumerate() {
    let mut es = mat.build(nodes, &dict, plan)?;
    allocated = allocated.saturating_add(plan.nodes);
    if j < k_entries {
      entries.push(es.pop().ok_or_else(|| internal("missing entry"))?);
    } else {
      roots = es;
    }
  }
  drop(p);
  let _p = prof::scope(Phase::RematerializeCheck);
  let predicted = result.model_len;
  // The layout price and the re-expansion check in one walk; when it
  // reports a mismatch or an overflow, the separate checks run.
  let price = |i: u64| layout.width_at(i);
  let fused = dag.check_and_measure(order, &entries, &roots, &price);
  let priced = match fused {
    Some((_, len)) => len,
    None => layout_bytes(layout, &entries, &roots).ok_or_else(overflow)?,
  };
  if priced != predicted {
    return Err(internal(format!(
      "layout length {priced} differs from the evaluation {predicted}"
    )));
  }
  match fused {
    Some((visited, _)) => {
      if visited != allocated {
        return Err(internal(format!(
          "the re-materialized expressions have {visited} nodes, {allocated} counted"
        )));
      }
    },
    None => dag.check_reexpansion(
      order,
      &entries,
      &roots,
      &ExactSharingLimits::unbounded(),
      "re-materialized encoding changes the expanded AST",
      "re-materialized entries do not expand to the stored terms",
    )?,
  }
  // The real length: Shares priced by the current wire codec, every other
  // header as written by `put_expr`. The TagN layout prices a Share at its
  // wire width (`TagN::byte_width(4, i)`), so this is `priced`.
  let measured = match layout {
    ShareLayout::TagN => priced,
  };
  if layout == ShareLayout::wire() && measured != predicted {
    return Err(internal(format!(
      "serialized length {measured} differs from the wire-layout price \
       {predicted}"
    )));
  }
  result.roots = roots;
  result.sharing = entries;
  result.variable_len = measured;
  Ok(result)
}

/// Whether candidate `a` beats `b` (Lean `tieredBetter`): fewer final layout
/// bytes, then the lower width, then `set_prec` on the stored set.
fn tiered_better(a: &TieredSharingResult, b: &TieredSharingResult) -> bool {
  let (x, y) = (&a.stats, &b.stats);
  x.phase3_layout_bytes < y.phase3_layout_bytes
    || (x.phase3_layout_bytes == y.phase3_layout_bytes
      && (x.w < y.w
        || (x.w == y.w && set_prec(&a.phase1.stored, &b.phase1.stored))))
}

/// One candidate of the tiered construction (Lean `tieredAtWidth`): phases
/// 1-3 with phase-1 uniform width `w`.
fn tiered_at(
  layout: ShareLayout,
  dag: &SharingDag,
  prep: &DagPrep,
  meter: &mut Meter<'_>,
  w: u64,
) -> Result<Candidate, SharingError> {
  let nodes = dag.nodes();
  let n = nodes.len();
  let p = prof::scope(Phase::Prep);
  let own = &prep.own;
  // The work of the evaluation `C_0` (`prep.base`), charged with phase 3.
  let work = prep.base.work();
  let facts = &prep.facts;
  let k = len64(
    (0..n)
      .filter(|&t| facts.deg[t] >= 2 && prep.base.costs[t] >= Len::new(2))
      .count(),
  );
  drop(p);
  // Phase 1.
  // Phase 1, without materializing its table: phase 2 reads only what the
  // phase-1 expressions contain, which the dry run reports from the same
  // decisions (`PlanShares`).
  let (u, shares) = optimize_uniform_with(w, dag, prep, meter, false)?;
  let shares = shares.ok_or_else(|| internal("phase 1 without its shares"))?;
  let p = prof::scope(Phase::Allocate);
  let order1 = u.table_terms.clone();
  // The phase-1 output priced by the layout. The TagN layout prices a Share
  // at its wire width, so this is the real length that phase 1 measured.
  let phase1_layout = match layout {
    ShareLayout::TagN => u.variable_len,
  };
  // Phase 2: reference counts (the Shares of each entry in all the phase-1
  // expression trees) and dependencies (the entries an entry's phase-1
  // expression shares, in pre-order of first occurrence).
  let mut weight: FxHashMap<TermId, u64> = FxHashMap::default();
  let mut deps: FxHashMap<TermId, Vec<TermId>> = FxHashMap::default();
  let PlanShares { refs, deps: entry_deps, .. } = shares;
  for ((&t, &r), ds) in order1.iter().zip(&refs).zip(entry_deps) {
    weight.insert(t, r);
    deps.insert(t, ds);
  }
  let mut stored = order1.clone();
  stored.sort_unstable();
  let cap = stored.len().min(8);
  let (tier, slot_states) =
    first_tier(&stored, &weight, &deps, cap, meter.limits())?;
  let rest: Vec<TermId> =
    stored.iter().copied().filter(|t| !tier.contains(t)).collect();
  let mut order2 = pinned_order(dag, &facts.deg, &tier);
  order2.extend(kahn_order(&weight, &deps, &rest));
  let ref_cost = |ord: &[TermId]| -> u128 {
    ord.iter().enumerate().fold(0u128, |acc, (i, t)| {
      let wt = u128::from(weight.get(t).copied().unwrap_or(0));
      acc.saturating_add(wt * u128::from(layout.width_at(len64(i))))
    })
  };
  let kept = ref_cost(&order2) > ref_cost(&order1);
  let order = if kept { order1.clone() } else { order2 };
  if !respects_deps(&order, &deps) {
    return Err(internal(
      "the allocated order places a body reference after its user",
    ));
  }
  drop(p);
  // Phase 3: each entry under the entries before it, priced by the layout,
  // then the roots under all entries.
  //
  // When the order is closed under stored descendants (always so far on
  // Init and Mathlib, but checked), the cost and choice of every term below
  // entry `j` are the same under the prefix `order[..j]` as under the full
  // dictionary (they read the dictionary only at and below the term; Lean
  // `gCost_local`), so one evaluation of the full dictionary gives every
  // task's length: entry `j` with its own Share hidden, the roots as they
  // are. The decisions and expressions are made for the returned candidate
  // only (`finish`). The work charged is the work done: the evaluation and
  // the hidden-top evaluations.
  //
  // Otherwise every task is evaluated under its prefix. Task `j < k` is
  // entry `j`, task `k` the roots; each depends only on the prefix
  // `order[..j]`, so the tasks run independently (see
  // `Parallelism::materialize`) and are combined in task order exactly as
  // the sequential loop proceeds. Task `j` is charged the work of a full
  // evaluation `all_costs` of the dictionary `order[..j]` plus its
  // materialization decisions. The evaluation is maintained from one prefix
  // to the next (`LazyCosts`, or `IncrementalCosts` when its work argument
  // does not apply), which yields the same costs for the materialized terms
  // and the same work count as evaluating every prefix from scratch; the
  // materialization decisions (`Materializer::decide`) are those of
  // `materialize`, with its work.
  let k_entries = order.len();
  let (phase3, predicted, allocated) = if descendant_closed(nodes, &order) {
    let p = prof::scope(Phase::RematerializeCosts);
    let mut dict = LayoutIndex { index: vec![None; n], layout };
    for (i, &t) in order.iter().enumerate() {
      dict.index[ix(t)] = Some(len64(i));
    }
    let eval = Evaluation::new(nodes, own, &dict);
    let mut w = eval.work();
    let mut predicted = Len::new(tag0_len(len64(k_entries)));
    for &t in &order {
      let hide = Hide { inner: &dict, hidden: t };
      let costs = &eval.costs;
      let (c, _) =
        eval_node(nodes, own, t, &hide, &|x| costs[ix(x)], false, &mut w);
      predicted = predicted.plus(c);
    }
    for &r in dag.roots() {
      predicted = predicted.plus(eval.costs[ix(r)]);
    }
    // The work counted before phase 3 (`C_0`) is charged with it.
    meter.work(work.saturating_add(w))?;
    drop(p);
    (Phase3::OnePass { costs: eval.costs }, predicted, None)
  } else {
    let phase3 = |range: std::ops::Range<usize>| {
      let p = prof::scope(Phase::RematerializeCosts);
      let mut dict = LayoutIndex { index: vec![None; n], layout };
      for (i, &t) in order[..range.start].iter().enumerate() {
        dict.index[ix(t)] = Some(len64(i));
      }
      // The evaluation of the empty prefix is `C_0`, the same for every
      // candidate.
      let start = if range.start == 0 {
        prep.base.clone()
      } else {
        Evaluation::new(nodes, own, &dict)
      };
      let mut eval = if LazyCosts::applies(&prep.base) {
        Phase3Eval::Lazy(LazyCosts::new(nodes, own, &prep.edges, start, &dict))
      } else {
        Phase3Eval::Eager(IncrementalCosts::new(nodes, own, &prep.edges, start))
      };
      let mut mat = Materializer::new(n);
      drop(p);
      let mut out: Vec<Result<(Plan, Len, u64), SharingError>> =
        Vec::with_capacity(range.len());
      for j in range.clone() {
        if j > range.start {
          let p = prof::scope(Phase::RematerializeCosts);
          let t = order[j - 1];
          dict.index[ix(t)] = Some(len64(j - 1));
          eval.add(t, &dict);
          drop(p);
        }
        let target = order.get(j).map(std::slice::from_ref);
        let p = prof::scope(Phase::RematerializeCosts);
        eval.prepare(target.unwrap_or(dag.roots()), &dict);
        drop(p);
        let _p = prof::scope(Phase::RematerializeBuild);
        let mut w = eval.work();
        let costs = eval.costs();
        if let Some(&t) = order.get(j) {
          let r = mat.decide(nodes, own, &dict, costs, &[t], &mut w);
          out.push(r.map(|plan| (plan, costs[ix(t)], w)));
        } else {
          let mut c = Len::ZERO;
          for &r in dag.roots() {
            c = c.plus(costs[ix(r)]);
          }
          let r = mat.decide(nodes, own, &dict, costs, dag.roots(), &mut w);
          out.push(r.map(|plan| (plan, c, w)));
        }
      }
      out
    };
    let tasks =
      super::par::map_ranges(k_entries + 1, meter.parallel.materialize, phase3);
    let mut plans = Vec::with_capacity(k_entries + 1);
    let mut predicted = Len::new(tag0_len(len64(k_entries)));
    // The work counted before phase 3 is charged with the first task, as the
    // sequential loop does.
    let mut carried = work;
    for task in tasks {
      let (plan, cost, w) = task?;
      plans.push(plan);
      predicted = predicted.plus(cost);
      meter.work(carried.saturating_add(w))?;
      carried = 0;
    }
    let allocated =
      plans.iter().fold(0u64, |acc, plan| acc.saturating_add(plan.nodes));
    (Phase3::Plans(plans), predicted, Some(allocated))
  };
  let _p = prof::scope(Phase::RematerializeCheck);
  let predicted = predicted.exact().ok_or_else(overflow)?;
  if predicted > phase1_layout {
    return Err(internal(format!(
      "re-materialization {predicted} is longer than phase 1 {phase1_layout}"
    )));
  }
  // The input nodes the re-expansion check of the built expressions
  // charges: one per expression node, all of them pointer-distinct (every
  // task builds fresh nodes). A serialized tree has at most two nodes per
  // byte (every node but an App writes at least one byte of its own, and an
  // App's argument starts with a byte no other App claims), so the count is
  // at most twice the length; only when that bound exceeds the limit are
  // the one-pass decisions made here to count exactly.
  let allocated = match allocated {
    Some(a) => Some(a),
    None if predicted.saturating_mul(2) > meter.limits().max_input_nodes => {
      let Phase3::OnePass { costs } = &phase3 else {
        return Err(internal("one-pass phase 3 without its evaluation"));
      };
      let mut dict = LayoutIndex { index: vec![None; n], layout };
      for (i, &t) in order.iter().enumerate() {
        dict.index[ix(t)] = Some(len64(i));
      }
      let mut scratch = 0u64;
      let plans = one_pass_plans(
        dag,
        own,
        &order,
        &dict,
        costs,
        &mut Materializer::new(n),
        &mut scratch,
      )?;
      Some(plans.iter().fold(0u64, |acc, plan| acc.saturating_add(plan.nodes)))
    },
    None => None,
  };
  if let Some(a) = allocated {
    dag.check_input_nodes(a, meter.limits())?;
  }
  // The real length equals the evaluated one (checked when the candidate
  // is built).
  let measured = predicted;
  meter.output(measured)?;
  let stats = TieredStats {
    layout,
    candidate_count: k,
    w,
    candidate_lengths: vec![(w, predicted)],
    candidate_meters: vec![(
      w,
      u.model_len,
      meter.stats.states_created,
      meter.stats.work,
    )],
    per_prefix_candidates: u64::from(matches!(phase3, Phase3::Plans(_))),
    phase1_model_bytes: u.model_len,
    phase1_layout_bytes: phase1_layout,
    slot_states,
    first_tier: tier,
    kept_phase1_order: kept,
    phase1_ref_cost: ref_cost(&order1),
    final_ref_cost: ref_cost(&order),
    phase3_layout_bytes: predicted,
    savings: phase1_layout - predicted,
  };
  let unshared_len = u.unshared_len;
  let result = TieredSharingResult {
    roots: Vec::new(),
    sharing: Vec::new(),
    table_terms: order,
    model_len: predicted,
    variable_len: measured,
    unshared_len,
    phase1: u,
    stats,
  };
  Ok(Candidate { result, phase3 })
}

/// Tiered canonical sharing of fully expanded roots under a layout.
pub fn canonical_sharing_tiered(
  layout: ShareLayout,
  roots: &[Arc<Expr>],
  limits: &ExactSharingLimits,
) -> Result<TieredSharingResult, SharingError> {
  let mut meter = Meter::new(limits);
  let p = prof::scope(Phase::Dag);
  let dag = SharingDag::build(roots, None, &mut meter)?;
  drop(p);
  let _p = prof::scope(Phase::Total);
  tiered(layout, &dag, limits, Parallelism::SEQUENTIAL)
}

/// Expand `c`'s table and re-share it with the tiered canonical
/// construction (the best of the phase-1 widths 1, 2 and 3).
pub fn normalize_constant_sharing_tiered(
  layout: ShareLayout,
  c: &Constant,
  limits: &ExactSharingLimits,
) -> Result<(Constant, TieredSharingResult), SharingError> {
  normalize_tiered_with(c, limits, |dag| {
    tiered(layout, dag, limits, Parallelism::SEQUENTIAL)
  })
}

/// [`normalize_constant_sharing_tiered`] with the thread budgets `par`
/// ([`Parallelism`]): the same bytes and result for every budget.
pub fn normalize_constant_sharing_tiered_par(
  layout: ShareLayout,
  c: &Constant,
  limits: &ExactSharingLimits,
  par: Parallelism,
) -> Result<(Constant, TieredSharingResult), SharingError> {
  normalize_tiered_with(c, limits, |dag| tiered(layout, dag, limits, par))
}

/// The single candidate with phase-1 width `w` ([`tiered_at`], Lean
/// `tieredAtWidth`) on `c`, for the tests of the width selection: the
/// canonical construction returns one of the candidates at `w = 1, 2, 3`.
#[cfg(test)]
pub(crate) fn normalize_constant_sharing_tiered_at_width(
  layout: ShareLayout,
  c: &Constant,
  limits: &ExactSharingLimits,
  w: u64,
) -> Result<(Constant, TieredSharingResult), SharingError> {
  normalize_tiered_with(c, limits, |dag| {
    let prep = DagPrep::new(dag);
    let c = tiered_at(layout, dag, &prep, &mut Meter::new(limits), w)?;
    finish(layout, dag, &prep, limits, c)
  })
}

/// Expand `c`'s table, run `run` on its DAG, and reassemble the Constant,
/// checking its serialized length against the result's accounting.
fn normalize_tiered_with(
  c: &Constant,
  limits: &ExactSharingLimits,
  run: impl FnOnce(&SharingDag) -> Result<TieredSharingResult, SharingError>,
) -> Result<(Constant, TieredSharingResult), SharingError> {
  let mut meter = Meter::new(limits);
  let p = prof::scope(Phase::Dag);
  let roots = constant_info_root_exprs(&c.info);
  let dag = SharingDag::build(&roots, Some(&c.sharing), &mut meter)?;
  drop(p);
  let fixed = constant_fixed_len(c).ok_or_else(overflow)?;
  let p = prof::scope(Phase::Total);
  let result = run(&dag)?;
  drop(p);
  let _p = prof::scope(Phase::Output);
  let info = rebuild_constant_info(&c.info, &result.roots)?;
  let out = Constant {
    info,
    sharing: result.sharing.clone(),
    refs: c.refs.clone(),
    univs: c.univs.clone(),
  };
  let mut bytes = Vec::new();
  out.put(&mut bytes);
  if u64::try_from(bytes.len()).ok() != fixed.checked_add(result.variable_len) {
    return Err(internal("tiered output length differs from its accounting"));
  }
  Ok((out, result))
}

/// Byte-level tiered normalization of exactly one serialized Constant.
pub fn normalize_constant_bytes_tiered(
  layout: ShareLayout,
  bytes: &[u8],
  limits: &ExactSharingLimits,
) -> Result<Vec<u8>, NormalizeBytesError> {
  let mut input = bytes;
  let c = Constant::get(&mut input).map_err(NormalizeBytesError::Decode)?;
  if !input.is_empty() {
    return Err(NormalizeBytesError::Decode(format!(
      "{} trailing bytes after the Constant",
      input.len()
    )));
  }
  let (out, _) = normalize_constant_sharing_tiered(layout, &c, limits)
    .map_err(NormalizeBytesError::Sharing)?;
  let mut buf = Vec::new();
  out.put(&mut buf);
  Ok(buf)
}
