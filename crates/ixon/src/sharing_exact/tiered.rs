//! Tiered canonical sharing: uniform-width selection, slot allocation and
//! re-materialization under a Share layout.
//!
//! A rule-for-rule port of W1's `Ix/Sharing/Exact/Tiered.lean`.
//!
//! Layouts ([`ShareLayout::width_at`], monotone, at least 1):
//! * `Tag4`: the Ixon Tag4 Share (1 byte below index 8, 2 below 256, ...),
//!   the serialized width.
//! * `TagN`: the nibble-bootstrapped Share code whose widths climb in rungs
//!   of 1, 2, 3, 5 and 9 bytes ([`tagn_width`]). No serializer uses it yet:
//!   the output is still written with Tag4 Shares and the model length
//!   reports the TagN price.
//!
//! **Width selection.** Phase 1 runs at each uniform width `w` in 1, 2, 3,
//! each result is carried through phases 2 and 3, and the construction
//! returns the candidate with the fewest final layout bytes; ties go to the
//! lower `w`, then `set_prec` on the stored set. An error at any width fails
//! the call. Each candidate is exact per phase as described below; the
//! final choice is the real-byte minimum over the three candidates, not a
//! global optimum. The nominal width from `K` (the number of terms with
//! compact in-degree at least 2 and unshared length at least 2; `w = 1` if
//! `K <= 8`, `2` if `K <= tier2_end`, else `3`) is only reported in the
//! statistics.
//! [`normalize_constant_sharing_tiered_at_width`] runs the single candidate
//! at one width (W1's `fixedWidth`).
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
//! rest in pinned order. If that order's reference cost
//! `sum ref(t) * width_at(index t)` exceeds the phase-1 order's, the phase-1
//! order is kept.
//!
//! **Phase 3 (re-materialization).** Every entry is re-encoded with `C_M`
//! under the entries before it, priced by `width_at(index)`, and the roots
//! under all entries; byte-least ties. The result is checked to be no
//! longer (in layout bytes) than phase 1, and is serialized, measured and
//! re-expanded.

use std::sync::Arc;

use rustc_hash::{FxHashMap, FxHashSet};

use super::cost::{Len, expr_len, expr_len_with, share_width, tag0_len};
use super::dag::{Node, SharingDag, TermId, ix};
use super::dict::{Indices, Widths, all_costs, materialize};
use super::uniform::{
  UniformSharingResult, graph_facts, optimize_uniform, pinned_order, set_prec,
  uniform_with_stored_set,
};
use super::{
  ExactSharingLimits, FormatBound, Meter, NormalizeBytesError, Resource,
  ResourceExhausted, SharingError, constant_fixed_len,
  constant_info_root_exprs, rebuild_constant_info,
};
use crate::constant::Constant;
use crate::expr::Expr;

fn internal(msg: impl Into<String>) -> SharingError {
  SharingError::Internal(msg.into())
}

fn overflow() -> SharingError {
  SharingError::FormatBound(FormatBound::LengthOverflow)
}

fn len64(n: usize) -> u64 {
  u64::try_from(n).unwrap_or(u64::MAX)
}

/// End (exclusive) of the 1-byte TagN rung.
pub const TAGN_RUNG1_END: u64 = 8;
/// End of the 2-byte rung (2 + 8 value bits).
pub const TAGN_RUNG2_END: u64 = TAGN_RUNG1_END + (1 << 10);
/// End of the 3-byte rung.
pub const TAGN_RUNG3_END: u64 = TAGN_RUNG2_END + (1 << 16);
/// End of the 5-byte rung; every larger `u64` index is in the 9-byte rung
/// (which ends at `TAGN_RUNG4_END + 2^64`).
pub const TAGN_RUNG4_END: u64 = TAGN_RUNG3_END + (1 << 32);

/// Byte width of the TagN Share at index `i`.
pub fn tagn_width(i: u64) -> u64 {
  if i < TAGN_RUNG1_END {
    1
  } else if i < TAGN_RUNG2_END {
    2
  } else if i < TAGN_RUNG3_END {
    3
  } else if i < TAGN_RUNG4_END {
    5
  } else {
    9
  }
}

/// A Share width layout.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ShareLayout {
  /// The Ixon Tag4 Share (the serialized width).
  Tag4,
  /// The TagN Share code ([`tagn_width`]).
  TagN,
}

impl ShareLayout {
  /// Width of the Share at table index `i`.
  pub fn width_at(self, i: u64) -> u64 {
    match self {
      ShareLayout::Tag4 => share_width(i),
      ShareLayout::TagN => tagn_width(i),
    }
  }

  /// First index whose width exceeds 2.
  pub fn tier2_end(self) -> u64 {
    match self {
      ShareLayout::Tag4 => 256,
      ShareLayout::TagN => TAGN_RUNG2_END,
    }
  }

  /// Nominal uniform width for `k` candidates (`k` up to 8 fit the 1-byte
  /// rung, up to `tier2_end` the 2-byte rung). The canonical construction
  /// tries every width instead (see the module doc); this is reported in the
  /// statistics.
  pub fn uniform_width(self, k: u64) -> u64 {
    if k <= 8 {
      1
    } else if k <= self.tier2_end() {
      2
    } else {
      3
    }
  }

  /// The layout code used at the FFI boundary: 0 = Tag4, 1 = TagN.
  pub fn from_code(code: u8) -> Option<ShareLayout> {
    match code {
      0 => Some(ShareLayout::Tag4),
      1 => Some(ShareLayout::TagN),
      _ => None,
    }
  }
}

/// Variable length of an encoding with every Share priced by `layout`.
pub fn layout_bytes(
  layout: ShareLayout,
  sharing: &[Arc<Expr>],
  roots: &[Arc<Expr>],
) -> Option<u64> {
  let price = |i: u64| layout.width_at(i);
  let mut total = tag0_len(len64(sharing.len()));
  for e in sharing.iter().chain(roots) {
    total = total.checked_add(expr_len_with(e, &price)?)?;
  }
  Some(total)
}

/// All `Share` indices of an expression, with multiplicity, in left-to-right
/// pre-order.
pub(crate) fn share_indices(e: &Expr, out: &mut Vec<u64>) {
  let mut stack: Vec<&Expr> = vec![e];
  while let Some(x) = stack.pop() {
    if let Expr::Share(i) = x {
      out.push(*i);
    }
    for c in x.children().into_iter().rev() {
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
  for &t in stored {
    let mut seen: FxHashSet<TermId> = FxHashSet::default();
    let mut stack: Vec<TermId> = vec![t];
    let mut ok = true;
    for _ in 0..fuel {
      let Some(u) = stack.pop() else { break };
      if !seen.insert(u) {
        continue;
      }
      if seen.len() > cap {
        ok = false;
        break;
      }
      if let Some(ds) = deps.get(&u) {
        stack.extend_from_slice(ds);
      }
    }
    if ok {
      let mut cl: Vec<TermId> = seen.into_iter().collect();
      cl.sort_unstable();
      closure.insert(t, cl);
    }
  }
  // Depth-first branch and bound, "include" before "exclude"; the first
  // maximum found wins ties, so later subtrees are pruned when their bound
  // does not exceed the best weight.
  struct Frame {
    pos: usize,
    cur: u64,
    in_f: Vec<TermId>,
    excluded: FxHashSet<TermId>,
  }
  let mut best: Option<(u64, Vec<TermId>)> = None;
  let mut states: u64 = 0;
  let mut stack = vec![Frame {
    pos: 0,
    cur: 0,
    in_f: Vec::new(),
    excluded: FxHashSet::default(),
  }];
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
    exclude.insert(t);
    let mut include: Option<Frame> = None;
    if let Some(cl) = closure.get(&t) {
      let new: Vec<TermId> =
        cl.iter().copied().filter(|u| !in_f.contains(u)).collect();
      if !cl.iter().any(|u| excluded.contains(u))
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

// ---------------------------------------------------------------------------
// Result and driver
// ---------------------------------------------------------------------------

/// Statistics of the tiered construction.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TieredStats {
  pub layout: ShareLayout,
  /// Terms with in-degree >= 2 and unshared length >= 2.
  pub candidate_count: u64,
  /// Nominal width for the candidate count ([`ShareLayout::uniform_width`]).
  pub nominal_w: u64,
  /// Phase-1 uniform width of the returned candidate (the winning width;
  /// 0 for the all-candidates experiment).
  pub w: u64,
  /// Final layout length of every candidate run, as `(w, bytes)` in
  /// increasing `w` (one entry for a single forced candidate).
  pub candidate_lengths: Vec<(u64, u64)>,
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
  /// Real (Tag4-serialized) variable length.
  pub variable_len: u64,
  pub unshared_len: Option<u64>,
  pub phase1: UniformSharingResult,
  pub stats: TieredStats,
}

/// The tiered canonical construction on a DAG (W1's
/// `canonicalTieredExpanded`): phases 1-3 at each phase-1 width 1, 2 and 3,
/// returning the candidate with the fewest final layout bytes; ties go to
/// the lower width, then `set_prec` on the stored set. Each candidate runs
/// under its own meter with the same limits, and an error at any width
/// fails the whole call.
pub(crate) fn tiered(
  layout: ShareLayout,
  dag: &SharingDag,
  limits: &ExactSharingLimits,
) -> Result<TieredSharingResult, SharingError> {
  let mut best: Option<TieredSharingResult> = None;
  let mut lengths = Vec::with_capacity(3);
  for w in 1..=3 {
    let c =
      tiered_at(layout, dag, &mut Meter::new(limits), Phase1Choice::Width(w))?;
    lengths.push((w, c.stats.phase3_layout_bytes));
    if best.as_ref().is_none_or(|b| tiered_better(&c, b)) {
      best = Some(c);
    }
  }
  let mut best = best.ok_or_else(|| internal("no tiered candidate"))?;
  best.stats.candidate_lengths = lengths;
  Ok(best)
}

/// Whether candidate `a` beats `b` (W1's `tieredBetter`): fewer final layout
/// bytes, then the lower width, then `set_prec` on the stored set.
fn tiered_better(a: &TieredSharingResult, b: &TieredSharingResult) -> bool {
  let (x, y) = (&a.stats, &b.stats);
  x.phase3_layout_bytes < y.phase3_layout_bytes
    || (x.phase3_layout_bytes == y.phase3_layout_bytes
      && (x.w < y.w
        || (x.w == y.w && set_prec(&a.phase1.stored, &b.phase1.stored))))
}

/// One phase-1 candidate, for the escape hatch and experiments.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Phase1Choice {
  /// The uniform optimum at width `w` (W1's `fixedWidth := some w`).
  Width(u64),
  /// Experiment: every candidate (compact in-degree >= 2, unshared length
  /// >= 2) stored, bodies materialized at uniform width 1 (the MSS set).
  AllCandidates,
}

/// The tiered construction with phase 1 chosen by `phase1`.
fn tiered_at(
  layout: ShareLayout,
  dag: &SharingDag,
  meter: &mut Meter<'_>,
  phase1: Phase1Choice,
) -> Result<TieredSharingResult, SharingError> {
  let nodes = dag.nodes();
  let n = nodes.len();
  let own: Vec<Len> = nodes.iter().map(Node::own_len).collect();
  let mut work = 0u64;
  let base = all_costs(nodes, &own, &super::dict::NoWidths, &mut work);
  let facts = graph_facts(dag);
  let k = len64(
    (0..n).filter(|&t| facts.deg[t] >= 2 && base[t] >= Len::new(2)).count(),
  );
  // Phase 1.
  let (w, u) = match phase1 {
    Phase1Choice::Width(w) => (w, optimize_uniform(w, dag, meter)?),
    Phase1Choice::AllCandidates => {
      let stored: Vec<TermId> = (0..n)
        .filter(|&t| facts.deg[t] >= 2 && base[t] >= Len::new(2))
        .map(|t| TermId::try_from(t).map_err(|_e| overflow()))
        .collect::<Result<_, _>>()?;
      (0, uniform_with_stored_set(1, dag, &stored, meter)?)
    },
  };
  let order1 = u.table_terms.clone();
  let entries1 = &u.sharing;
  let roots1 = &u.roots;
  let phase1_layout =
    layout_bytes(layout, entries1, roots1).ok_or_else(overflow)?;
  // Phase 2: reference counts and dependencies from the phase-1 output.
  let mut refs = vec![0u64; order1.len()];
  let mut idx = Vec::new();
  for e in entries1.iter().chain(roots1) {
    idx.clear();
    share_indices(e, &mut idx);
    for &i in &idx {
      if let Some(r) = usize::try_from(i).ok().and_then(|i| refs.get_mut(i)) {
        *r += 1;
      }
    }
  }
  let mut weight: FxHashMap<TermId, u64> = FxHashMap::default();
  let mut deps: FxHashMap<TermId, Vec<TermId>> = FxHashMap::default();
  for (i, &t) in order1.iter().enumerate() {
    weight.insert(t, refs[i]);
    idx.clear();
    if let Some(e) = entries1.get(i) {
      share_indices(e, &mut idx);
    }
    let mut ds: Vec<TermId> = Vec::new();
    for &j in &idx {
      if let Some(&d) = usize::try_from(j).ok().and_then(|j| order1.get(j))
        && !ds.contains(&d)
      {
        ds.push(d);
      }
    }
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
  order2.extend(pinned_order(dag, &facts.deg, &rest));
  let ref_cost = |ord: &[TermId]| -> u128 {
    ord.iter().enumerate().fold(0u128, |acc, (i, t)| {
      let wt = u128::from(weight.get(t).copied().unwrap_or(0));
      acc.saturating_add(wt * u128::from(layout.width_at(len64(i))))
    })
  };
  let kept = ref_cost(&order2) > ref_cost(&order1);
  let order = if kept { order1.clone() } else { order2 };
  // Phase 3: each entry under the entries before it, priced by the layout.
  let mut dict = LayoutIndex { index: vec![None; n], layout };
  let mut entries = Vec::with_capacity(order.len());
  let mut predicted = Len::new(tag0_len(len64(order.len())));
  for (i, &t) in order.iter().enumerate() {
    let costs = all_costs(nodes, &own, &dict, &mut work);
    let mut e = materialize(nodes, &own, &dict, &costs, &[t], &mut work)?;
    entries.push(e.pop().ok_or_else(|| internal("missing entry"))?);
    predicted = predicted.plus(costs[ix(t)]);
    dict.index[ix(t)] = Some(len64(i));
    meter.work(std::mem::take(&mut work))?;
  }
  let costs = all_costs(nodes, &own, &dict, &mut work);
  let roots = materialize(nodes, &own, &dict, &costs, dag.roots(), &mut work)?;
  for &r in dag.roots() {
    predicted = predicted.plus(costs[ix(r)]);
  }
  meter.work(work)?;
  let predicted = predicted.exact().ok_or_else(overflow)?;
  let priced = layout_bytes(layout, &entries, &roots).ok_or_else(overflow)?;
  if priced != predicted {
    return Err(internal(format!(
      "layout length {priced} differs from the evaluation {predicted}"
    )));
  }
  if predicted > phase1_layout {
    return Err(internal(format!(
      "re-materialization {predicted} is longer than phase 1 {phase1_layout}"
    )));
  }
  let mut check_meter = Meter::new(meter.limits());
  let (check, entry_ids) =
    SharingDag::build_full(&roots, Some(&entries), &mut check_meter)?;
  if check != *dag {
    return Err(internal("re-materialized encoding changes the expanded AST"));
  }
  if entry_ids
    .iter()
    .map(|x| x.unwrap_or(TermId::MAX))
    .ne(order.iter().copied())
  {
    return Err(internal(
      "re-materialized entries do not expand to the stored terms",
    ));
  }
  let mut measured = tag0_len(len64(entries.len()));
  for e in entries.iter().chain(&roots) {
    measured =
      expr_len(e).and_then(|l| measured.checked_add(l)).ok_or_else(overflow)?;
  }
  if layout == ShareLayout::Tag4 && measured != predicted {
    return Err(internal(format!(
      "serialized length {measured} differs from the Tag4 price {predicted}"
    )));
  }
  meter.output(measured)?;
  let stats = TieredStats {
    layout,
    candidate_count: k,
    nominal_w: layout.uniform_width(k),
    w,
    candidate_lengths: vec![(w, predicted)],
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
  Ok(TieredSharingResult {
    roots,
    sharing: entries,
    table_terms: order,
    model_len: predicted,
    variable_len: measured,
    unshared_len,
    phase1: u,
    stats,
  })
}

/// Tiered canonical sharing of fully expanded roots under a layout.
pub fn canonical_sharing_tiered(
  layout: ShareLayout,
  roots: &[Arc<Expr>],
  limits: &ExactSharingLimits,
) -> Result<TieredSharingResult, SharingError> {
  let mut meter = Meter::new(limits);
  let dag = SharingDag::build(roots, None, &mut meter)?;
  tiered(layout, &dag, limits)
}

/// Expand `c`'s table and re-share it with the tiered canonical
/// construction (the best of the phase-1 widths 1, 2 and 3).
pub fn normalize_constant_sharing_tiered(
  layout: ShareLayout,
  c: &Constant,
  limits: &ExactSharingLimits,
) -> Result<(Constant, TieredSharingResult), SharingError> {
  normalize_tiered_at(layout, c, limits, None)
}

/// Escape hatch (W1's `fixedWidth := some w`), not the canonical
/// construction: the single candidate with phase-1 width `w`. The canonical
/// construction returns one of the candidates at `w = 1, 2, 3`.
pub fn normalize_constant_sharing_tiered_at_width(
  layout: ShareLayout,
  c: &Constant,
  limits: &ExactSharingLimits,
  w: u64,
) -> Result<(Constant, TieredSharingResult), SharingError> {
  normalize_tiered_at(layout, c, limits, Some(Phase1Choice::Width(w)))
}

/// Experiment hook, not the canonical construction: the single candidate
/// chosen by `phase1`. The reported `stats.w` is 0 for
/// [`Phase1Choice::AllCandidates`].
pub fn normalize_constant_sharing_tiered_with(
  layout: ShareLayout,
  c: &Constant,
  limits: &ExactSharingLimits,
  phase1: Phase1Choice,
) -> Result<(Constant, TieredSharingResult), SharingError> {
  normalize_tiered_at(layout, c, limits, Some(phase1))
}

fn normalize_tiered_at(
  layout: ShareLayout,
  c: &Constant,
  limits: &ExactSharingLimits,
  phase1: Option<Phase1Choice>,
) -> Result<(Constant, TieredSharingResult), SharingError> {
  let mut meter = Meter::new(limits);
  let roots = constant_info_root_exprs(&c.info);
  let dag = SharingDag::build(&roots, Some(&c.sharing), &mut meter)?;
  let fixed = constant_fixed_len(c).ok_or_else(overflow)?;
  let result = match phase1 {
    None => tiered(layout, &dag, limits)?,
    Some(p) => tiered_at(layout, &dag, &mut Meter::new(limits), p)?,
  };
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
