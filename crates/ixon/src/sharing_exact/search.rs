//! Exact table selection and ordering (§6).
//!
//! A width state assigns each stored term the Share width of its index. By
//! §6.2 every future length depends only on the state, so histories reaching
//! one state merge: the state keeps its least accumulated body length `F`
//! and, among histories of that length, the least term-ID prefix. States are
//! sparse sorted `(term, width)` vectors, expanded layer by layer (layer `k`
//! holds states with `k` entries) in sorted key order, so work counters and
//! failures are deterministic.
//!
//! Candidates are the terms that some minimum may store: R1 drops terms with
//! one expanded occurrence and R2 terms whose inline encoding is one byte.
//! Both reductions strictly shorten any encoding that violates them, so they
//! preserve every minimum-length encoding and hence the canonical key.
//!
//! # Pruning
//!
//! A state is dropped only if a lower bound on every completion is strictly
//! above the length of a feasible encoding, so states that could tie the
//! minimum survive for the tie-break. Two bounds are used; either may prune.
//!
//! **Dictionary bound (§4.1).** At state `M` with `k` entries every later
//! entry has an index `>= k`, hence a Share width `>= share_width(k)`. Let
//! `M+` extend `M` with every absent candidate at width `share_width(k)`
//! (the plan's width 1 is the case `k < 8`). `C` is antitone in
//! availability and monotone in widths, later bodies cost `>= 0` and the
//! table count prefix never shrinks, so every completion has length at
//! least `F(M) + tag0(k) + sum C_{M+}(root)`. For a successor
//! `M + (t, share_width(k))` the same sum is still a lower bound, because
//! `t` keeps the width `M+` gave it and other widths only grow.
//!
//! **Materialization bound.** Let `E(M)` be the terms that occur in the
//! expansions of the entries of `M`. Those entries emit only terms of
//! `E(M)`. Every other term `t` must still have its constructor emitted
//! inline at least once, in a later entry or a root: follow any occurrence
//! through Shares until a representation emits it. Pick one such emission
//! per non-leaf `t` outside `E(M)`. It owns bytes no other picked emission
//! owns: `t`'s own bytes (Prj/Let headers, a Lam/All contract byte) and, at
//! each child position that holds a leaf, that leaf's inline encoding or a
//! Share (at least one byte for a candidate leaf; the inline length for any
//! other leaf, since only candidates are ever stored). An App/Lam/All node
//! that is never the same-family spine child of any parent starts a
//! telescope wherever it is emitted inline, so its picked emission also owns
//! one header byte (a "header top"). No other telescope header and no Share
//! byte at a non-leaf position is counted. Each root position adds bytes not
//! yet counted: a leaf root as a leaf position; a root in `E(M)` contains no
//! picked emission, so its whole representation, at least `C_{M+}(root)`;
//! an App/Lam/All root outside `E(M)` that is not a header top, its
//! telescope header or Share byte; any other root outside `E(M)`, a Share
//! or unpicked header byte at every position except possibly the one
//! holding its picked emission. The picked bytes lie outside the bodies
//! counted by `F(M)`, so `F(M) + tag0(k) + (picked) + (root bytes)` bounds
//! every completion.
//!
//! Both bounds hold for every completion by candidates, and every
//! minimum-length encoding is such a completion of each state on its path,
//! so no state on the path of a minimum is ever pruned.
//!
//! # Upper bounds
//!
//! The initial feasible length is the lesser of the unshared encoding and a
//! deterministic greedy table sequence. They only tighten pruning; neither is
//! returned unless the search certifies it.

use std::sync::Arc;

use rustc_hash::FxHashMap;

use super::cost::{Len, expr_len, share_width, sharing_table_len, tag0_len};
use super::dag::{Node, SharingDag, TermId, ix};
use super::dict::{
  DenseIndex, NoWidths, Widths, all_costs, eval_node, materialize,
};
use super::{
  ExactSharingLimits, ExactSharingResult, FormatBound, Meter, SharingError,
};
use crate::expr::Expr;

fn internal(msg: impl Into<String>) -> SharingError {
  SharingError::Internal(msg.into())
}

fn tid(i: usize) -> TermId {
  TermId::try_from(i).unwrap_or(TermId::MAX)
}

/// Per-DAG data shared by every state evaluation.
pub(crate) struct Prepared {
  pub(crate) own: Vec<Len>,
  /// `C` under the empty dictionary: the unshared standalone lengths.
  pub(crate) base: Vec<Len>,
  pub(crate) cands: Vec<TermId>,
  pub(crate) is_cand: Vec<bool>,
  /// Materialization-bound bytes of one picked emission of each non-leaf
  /// term (0 for leaves), and their sum.
  pub(crate) picked: Vec<Len>,
  pub(crate) picked_total: Len,
  /// Lower bound on the bytes at a position holding each leaf.
  pub(crate) leaf_pos: Vec<Len>,
  /// App/Lam/All nodes whose picked emission owns a telescope header.
  pub(crate) header_top: Vec<bool>,
  parent_start: Vec<usize>,
  parents: Vec<TermId>,
}

impl Prepared {
  fn parents_of(&self, t: TermId) -> &[TermId] {
    &self.parents[self.parent_start[ix(t)]..self.parent_start[ix(t) + 1]]
  }
}

/// Every candidate at one width.
struct Candidates<'a> {
  is_cand: &'a [bool],
  width: u64,
}

impl Widths for Candidates<'_> {
  fn width(&self, t: TermId) -> Option<u64> {
    self.is_cand[ix(t)].then_some(self.width)
  }
}

/// Expanded occurrence counts (saturating) of every term.
pub(crate) fn occurrences(dag: &SharingDag) -> Vec<u64> {
  let nodes = dag.nodes();
  let mut occ = vec![0u64; nodes.len()];
  for &r in dag.roots() {
    occ[ix(r)] = occ[ix(r)].saturating_add(1);
  }
  // Parents have larger IDs than children: a descending sweep sees each
  // node's final count before propagating it along every child edge.
  for t in (0..nodes.len()).rev() {
    let o = occ[t];
    if o == 0 {
      continue;
    }
    for &c in nodes[t].children().as_slice() {
      occ[ix(c)] = occ[ix(c)].saturating_add(o);
    }
  }
  occ
}

fn candidates_of(occ: &[u64], base: &[Len]) -> Vec<TermId> {
  (0..occ.len())
    .filter(|&t| occ[t] >= 2 && base[t] > Len::new(1))
    .map(tid)
    .collect()
}

/// The terms some minimum may store after reductions R1 (at least two
/// expanded occurrences) and R2 (inline encoding longer than one byte), in
/// term-ID order. Its length is the search's candidate count.
pub fn candidate_terms(dag: &SharingDag) -> Vec<TermId> {
  let own: Vec<Len> = dag.nodes().iter().map(Node::own_len).collect();
  let base = all_costs(dag.nodes(), &own, &NoWidths, &mut 0);
  candidates_of(&occurrences(dag), &base)
}

pub(crate) fn prepare(
  dag: &SharingDag,
  meter: &mut Meter<'_>,
) -> Result<Prepared, SharingError> {
  prepare_with(dag, meter, |_| true)
}

/// [`prepare`] keeping only the R1/R2 candidates accepted by `keep`.
pub(crate) fn prepare_with(
  dag: &SharingDag,
  meter: &mut Meter<'_>,
  keep: impl Fn(TermId) -> bool,
) -> Result<Prepared, SharingError> {
  let nodes = dag.nodes();
  let n = nodes.len();
  let own: Vec<Len> = nodes.iter().map(Node::own_len).collect();
  let mut work = 0u64;
  let base = all_costs(nodes, &own, &NoWidths, &mut work);
  let occ = occurrences(dag);
  let cands: Vec<TermId> =
    candidates_of(&occ, &base).into_iter().filter(|&t| keep(t)).collect();
  meter.candidates(u64::try_from(cands.len()).unwrap_or(u64::MAX))?;
  let mut is_cand = vec![false; n];
  for &t in &cands {
    is_cand[ix(t)] = true;
  }
  let leaf_pos: Vec<Len> =
    (0..n).map(|t| if is_cand[t] { Len::new(1) } else { base[t] }).collect();
  // A node that is never the same-family spine child of a parent starts a
  // telescope at every inline emission, so its picked emission owns that
  // telescope's header.
  let mut spine_child = vec![false; n];
  for node in nodes {
    let next = match node {
      Node::App(f, _) => Some(*f),
      Node::Lam(_, _, b) | Node::All(_, _, _, b) => Some(*b),
      _ => None,
    };
    if let Some(c) = next
      && nodes[ix(c)].family() == node.family()
    {
      spine_child[ix(c)] = true;
    }
  }
  let mut header_top = vec![false; n];
  let mut picked = vec![Len::ZERO; n];
  let mut picked_total = Len::ZERO;
  for (t, node) in nodes.iter().enumerate() {
    let kids = node.children();
    if kids.as_slice().is_empty() {
      continue;
    }
    let mut p = own[t];
    if node.family().is_some() && !spine_child[t] {
      header_top[t] = true;
      p = p.plus_u64(1);
    }
    for &c in kids.as_slice() {
      if nodes[ix(c)].children().as_slice().is_empty() {
        p = p.plus(leaf_pos[ix(c)]);
      }
    }
    picked[t] = p;
    picked_total = picked_total.plus(p);
  }
  // Distinct parents of every node, in CSR form.
  let mut count = vec![0usize; n + 1];
  for node in nodes {
    let kids = node.children();
    let kids = kids.as_slice();
    for (i, &c) in kids.iter().enumerate() {
      if !kids[..i].contains(&c) {
        count[ix(c)] += 1;
      }
    }
  }
  let mut parent_start = vec![0usize; n + 1];
  for i in 0..n {
    parent_start[i + 1] = parent_start[i] + count[i];
  }
  let mut fill = parent_start.clone();
  let mut parents = vec![0; parent_start[n]];
  for (p, node) in nodes.iter().enumerate() {
    let kids = node.children();
    let kids = kids.as_slice();
    for (i, &c) in kids.iter().enumerate() {
      if !kids[..i].contains(&c) {
        parents[fill[ix(c)]] = tid(p);
        fill[ix(c)] += 1;
      }
    }
  }
  meter.work(work)?;
  Ok(Prepared {
    own,
    base,
    cands,
    is_cand,
    picked,
    picked_total,
    leaf_pos,
    header_top,
    parent_start,
    parents,
  })
}

struct DenseWidths<'a>(&'a [u8]);

impl Widths for DenseWidths<'_> {
  fn width(&self, t: TermId) -> Option<u64> {
    match self.0[ix(t)] {
      0 => None,
      w => Some(u64::from(w)),
    }
  }
}

/// `M+`: the state's widths, and `plus` for every other candidate.
struct PlusWidths<'a> {
  m: &'a [u8],
  is_cand: &'a [bool],
  plus: u64,
}

impl Widths for PlusWidths<'_> {
  fn width(&self, t: TermId) -> Option<u64> {
    match self.m[ix(t)] {
      0 => self.is_cand[ix(t)].then_some(self.plus),
      w => Some(u64::from(w)),
    }
  }
}

/// Costs of one evaluated state.
struct StateCosts {
  /// `sum C_M(root)`.
  roots: Len,
  /// `sum C_{M+}(root)`: the dictionary bound's variable part.
  roots_plus: Len,
  /// Picked and root bytes of the materialization bound.
  materialization: Len,
}

/// Scratch space for evaluating one state at a time.
///
/// `C_M(t)` differs from the unshared `C(t)` only if `t` or a descendant is
/// stored, and `C_{M+}(t)` differs from its all-candidates value under the
/// same condition. Only those ancestors are recomputed.
struct StateEval<'p> {
  prep: &'p Prepared,
  nodes: &'p [Node],
  roots: &'p [TermId],
  width_m: Vec<u8>,
  stamp: Vec<u32>,
  covered: Vec<u32>,
  seen_root: Vec<u32>,
  epoch: u32,
  cost_m: Vec<Len>,
  cost_p: Vec<Len>,
  affected: Vec<TermId>,
  todo: Vec<TermId>,
  /// Width given to absent candidates by `M+`, and `C` under exactly that
  /// dictionary (every candidate at `plus`).
  plus: u64,
  plus_base: Vec<Len>,
}

impl<'p> StateEval<'p> {
  fn new(prep: &'p Prepared, dag: &'p SharingDag, work: &mut u64) -> Self {
    let n = dag.len();
    let plus_base = all_costs(
      dag.nodes(),
      &prep.own,
      &Candidates { is_cand: &prep.is_cand, width: 1 },
      work,
    );
    StateEval {
      prep,
      nodes: dag.nodes(),
      roots: dag.roots(),
      width_m: vec![0; n],
      stamp: vec![0; n],
      covered: vec![0; n],
      seen_root: vec![0; n],
      epoch: 0,
      cost_m: vec![Len::ZERO; n],
      cost_p: vec![Len::ZERO; n],
      affected: Vec::new(),
      todo: Vec::new(),
      plus: 1,
      plus_base,
    }
  }

  /// Switch `M+` to give absent candidates width `plus`.
  fn set_plus(&mut self, plus: u64, work: &mut u64) {
    if plus != self.plus {
      self.plus = plus;
      self.plus_base = all_costs(
        self.nodes,
        &self.prep.own,
        &Candidates { is_cand: &self.prep.is_cand, width: plus },
        work,
      );
    }
  }

  fn cost_m(&self, t: TermId) -> Len {
    if self.stamp[ix(t)] == self.epoch {
      self.cost_m[ix(t)]
    } else {
      self.prep.base[ix(t)]
    }
  }

  fn cost_p(&self, t: TermId) -> Len {
    if self.stamp[ix(t)] == self.epoch {
      self.cost_p[ix(t)]
    } else {
      self.plus_base[ix(t)]
    }
  }

  fn eval(&mut self, m: &[(TermId, u8)], work: &mut u64) -> StateCosts {
    if self.epoch == u32::MAX {
      self.stamp.fill(0);
      self.covered.fill(0);
      self.seen_root.fill(0);
      self.epoch = 0;
    }
    self.epoch += 1;
    let ep = self.epoch;
    // Ancestors of stored terms: the only terms whose costs change.
    self.affected.clear();
    for &(t, w) in m {
      self.width_m[ix(t)] = w;
      self.stamp[ix(t)] = ep;
      self.affected.push(t);
    }
    let mut i = 0;
    while i < self.affected.len() {
      let x = self.affected[i];
      i += 1;
      for &p in self.prep.parents_of(x) {
        *work = work.saturating_add(1);
        if self.stamp[ix(p)] != ep {
          self.stamp[ix(p)] = ep;
          self.affected.push(p);
        }
      }
    }
    self.affected.sort_unstable();
    for a in 0..self.affected.len() {
      let t = self.affected[a];
      let cm = eval_node(
        self.nodes,
        &self.prep.own,
        t,
        &DenseWidths(&self.width_m),
        &|c| self.cost_m(c),
        false,
        work,
      )
      .0;
      self.cost_m[ix(t)] = cm;
      let widths = PlusWidths {
        m: &self.width_m,
        is_cand: &self.prep.is_cand,
        plus: self.plus,
      };
      let cp = eval_node(
        self.nodes,
        &self.prep.own,
        t,
        &widths,
        &|c| self.cost_p(c),
        false,
        work,
      )
      .0;
      self.cost_p[ix(t)] = cp;
    }
    // E(M): descendants-or-self of stored terms, and their picked bytes.
    let mut covered_bytes = Len::ZERO;
    self.todo.clear();
    for &(t, _) in m {
      if self.covered[ix(t)] != ep {
        self.covered[ix(t)] = ep;
        self.todo.push(t);
      }
    }
    while let Some(x) = self.todo.pop() {
      *work = work.saturating_add(1);
      covered_bytes = covered_bytes.plus(self.prep.picked[ix(x)]);
      for &c in self.nodes[ix(x)].children().as_slice() {
        if self.covered[ix(c)] != ep {
          self.covered[ix(c)] = ep;
          self.todo.push(c);
        }
      }
    }
    let mut roots = Len::ZERO;
    let mut roots_plus = Len::ZERO;
    let mut root_bytes = Len::ZERO;
    for &r in self.roots {
      roots = roots.plus(self.cost_m(r));
      let cp = self.cost_p(r);
      roots_plus = roots_plus.plus(cp);
      let node = &self.nodes[ix(r)];
      let extra = if node.children().as_slice().is_empty() {
        self.prep.leaf_pos[ix(r)]
      } else if self.covered[ix(r)] == ep {
        cp
      } else if (node.family().is_some() && !self.prep.header_top[ix(r)])
        || self.seen_root[ix(r)] == ep
      {
        // An uncounted header or Share byte at this position.
        Len::new(1)
      } else {
        // Possibly the position of the picked emission: count nothing.
        self.seen_root[ix(r)] = ep;
        Len::ZERO
      };
      root_bytes = root_bytes.plus(extra);
    }
    // picked_total >= covered_bytes: E(M) is a set of distinct terms.
    let outside = Len::new(
      self.prep.picked_total.raw().saturating_sub(covered_bytes.raw()),
    );
    let materialization = if self.prep.picked_total.is_exact() {
      outside.plus(root_bytes)
    } else {
      Len::ZERO
    };
    StateCosts { roots, roots_plus, materialization }
  }

  fn reset(&mut self, m: &[(TermId, u8)]) {
    for &(t, _) in m {
      self.width_m[ix(t)] = 0;
    }
  }
}

type StateKey = Vec<(TermId, u8)>;

/// How a Share at table index `k` is priced.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum WidthModel {
  /// The real TagN width of index `k`.
  Ixon,
  /// Every Share costs `w` bytes (the uniform-width cost model).
  Uniform(u8),
}

impl WidthModel {
  pub(crate) fn width(self, k: u64) -> u64 {
    match self {
      WidthModel::Ixon => share_width(k),
      WidthModel::Uniform(w) => u64::from(w),
    }
  }
}

/// Whether `prefix ++ [t]` is lexicographically below `other` (same length).
fn extension_less(prefix: &[TermId], t: TermId, other: &[TermId]) -> bool {
  match prefix.cmp(&other[..prefix.len()]) {
    std::cmp::Ordering::Less => true,
    std::cmp::Ordering::Greater => false,
    std::cmp::Ordering::Equal => t < other[prefix.len()],
  }
}

/// Insert `(t, w)` into a sorted state key.
fn extend_key(key: &[(TermId, u8)], t: TermId, w: u8) -> StateKey {
  let pos = key.partition_point(|&(x, _)| x < t);
  let mut out = Vec::with_capacity(key.len() + 1);
  out.extend_from_slice(&key[..pos]);
  out.push((t, w));
  out.extend_from_slice(&key[pos..]);
  out
}

/// A feasible upper bound: starting from the empty table, repeatedly append
/// the candidate whose addition gives the shortest encoding, while that is
/// strictly shorter than the current one. Candidates are tried in term-ID
/// order and ties keep the first, so the result is deterministic. The value
/// is the exact length of a real table sequence.
fn greedy_upper_bound(
  eval: &mut StateEval<'_>,
  prep: &Prepared,
  meter: &mut Meter<'_>,
  model: WidthModel,
) -> Result<Len, SharingError> {
  let mut key: StateKey = Vec::new();
  let mut f = Len::ZERO;
  let mut k: u64 = 0;
  let mut work = 0u64;
  let costs = eval.eval(&key, &mut work);
  let mut current = f.plus(Len::new(tag0_len(0))).plus(costs.roots);
  let mut bodies: Vec<(TermId, Len)> =
    prep.cands.iter().map(|&t| (t, eval.cost_m(t))).collect();
  eval.reset(&key);
  meter.work(std::mem::take(&mut work))?;
  loop {
    let w = u8::try_from(model.width(k))
      .map_err(|_e| internal("share width exceeds u8"))?;
    let count = Len::new(tag0_len(k.saturating_add(1)));
    let mut step: Option<(Len, TermId, Len)> = None;
    for &(t, c) in &bodies {
      let nf = f.plus(c);
      let next = extend_key(&key, t, w);
      let total = nf.plus(count).plus(eval.eval(&next, &mut work).roots);
      eval.reset(&next);
      meter.work(std::mem::take(&mut work))?;
      if total < current && step.is_none_or(|(best, _, _)| total < best) {
        step = Some((total, t, nf));
      }
    }
    let Some((total, t, nf)) = step else {
      return Ok(current);
    };
    key = extend_key(&key, t, w);
    f = nf;
    k = k.saturating_add(1);
    current = total;
    eval.eval(&key, &mut work);
    bodies = prep
      .cands
      .iter()
      .filter(|&&x| eval.width_m[ix(x)] == 0)
      .map(|&x| (x, eval.cost_m(x)))
      .collect();
    eval.reset(&key);
    meter.work(std::mem::take(&mut work))?;
  }
}

/// The width-state dynamic program. Returns the least `(variable length,
/// term-ID sequence)` over all table sequences, or a resource error.
pub(crate) fn width_state_search(
  dag: &SharingDag,
  prep: &Prepared,
  mut ub: Len,
  meter: &mut Meter<'_>,
  model: WidthModel,
) -> Result<(Len, Vec<TermId>), SharingError> {
  let prune = meter.limits().lower_bound_pruning;
  let materialization = meter.limits().materialization_bound;
  let mut work = 0u64;
  let mut eval = StateEval::new(prep, dag, &mut work);
  meter.work(work)?;
  if prune && meter.limits().greedy_upper_bound && !prep.cands.is_empty() {
    let g = greedy_upper_bound(&mut eval, prep, meter, model)?;
    meter.stats.greedy_len = g.exact();
    ub = ub.min(g);
  }
  let mut best: Option<(Len, Vec<TermId>)> = None;
  let mut layer: Vec<(StateKey, Len, Vec<TermId>)> =
    vec![(Vec::new(), Len::ZERO, Vec::new())];
  meter.state()?;
  let mut k: u64 = 0;
  while !layer.is_empty() {
    meter.stats.layers += 1;
    meter.layer(u64::try_from(layer.len()).unwrap_or(u64::MAX))?;
    let count_k = Len::new(tag0_len(k));
    let count_next = Len::new(tag0_len(k.saturating_add(1)));
    let width_k = model.width(k);
    let width_next =
      u8::try_from(width_k).map_err(|_e| internal("share width exceeds u8"))?;
    let mut work = 0u64;
    eval.set_plus(width_k, &mut work);
    meter.work(work)?;
    let mut next: FxHashMap<StateKey, (Len, Vec<TermId>)> =
      FxHashMap::default();
    for (key, f, prefix) in layer {
      meter.stats.states_expanded += 1;
      let mut work = 0u64;
      let costs = eval.eval(&key, &mut work);
      meter.work(work)?;
      let dict_lower = f.plus(count_k).plus(costs.roots_plus);
      let mat_lower = if materialization {
        f.plus(count_k).plus(costs.materialization)
      } else {
        Len::ZERO
      };
      if prune && dict_lower.max(mat_lower) > ub {
        meter.stats.states_pruned += 1;
        eval.reset(&key);
        continue;
      }
      let total = f.plus(count_k).plus(costs.roots);
      let improves = match &best {
        None => true,
        Some((bt, bq)) => (total, &prefix) < (*bt, bq),
      };
      if improves {
        best = Some((total, prefix.clone()));
      }
      ub = ub.min(total);
      let lower_next = count_next.plus(costs.roots_plus);
      for &t in &prep.cands {
        if eval.width_m[ix(t)] != 0 {
          continue;
        }
        meter.transition()?;
        let nf = f.plus(eval.cost_m(t));
        if !nf.is_exact() || (prune && nf.plus(lower_next) > ub) {
          continue;
        }
        match next.entry(extend_key(&key, t, width_next)) {
          std::collections::hash_map::Entry::Vacant(v) => {
            meter.state()?;
            let mut np = prefix.clone();
            np.push(t);
            v.insert((nf, np));
          },
          std::collections::hash_map::Entry::Occupied(mut o) => {
            let (of, op) = o.get();
            if nf < *of || (nf == *of && extension_less(&prefix, t, op)) {
              let mut np = prefix.clone();
              np.push(t);
              o.insert((nf, np));
            }
          },
        }
      }
      eval.reset(&key);
    }
    let mut v: Vec<(StateKey, Len, Vec<TermId>)> =
      next.into_iter().map(|(key, (f, p))| (key, f, p)).collect();
    v.sort_unstable_by(|a, b| a.0.cmp(&b.0));
    layer = v;
    k = k.saturating_add(1);
  }
  best.ok_or_else(|| internal("every width state was pruned"))
}

/// Exact variable length of the table sequence `q` with every entry and
/// root at its minimum: `sum C_{q<i}(q_i) + tag0(|q|) + sum C_q(root)`.
pub fn sequence_len(
  dag: &SharingDag,
  q: &[TermId],
) -> Result<Len, SharingError> {
  let n = dag.len();
  let mut seen = vec![false; n];
  for &t in q {
    if ix(t) >= n || seen[ix(t)] {
      return Err(internal("sequence term out of range or repeated"));
    }
    seen[ix(t)] = true;
  }
  let own: Vec<Len> = dag.nodes().iter().map(Node::own_len).collect();
  let mut dict = DenseIndex::new(n);
  let mut work = 0u64;
  let k = u64::try_from(q.len()).map_err(|_e| internal("length"))?;
  let mut total = Len::new(tag0_len(k));
  for (i, &t) in q.iter().enumerate() {
    let costs = all_costs(dag.nodes(), &own, &dict, &mut work);
    total = total.plus(costs[ix(t)]);
    dict.set(t, u64::try_from(i).map_err(|_e| internal("index"))?);
  }
  let costs = all_costs(dag.nodes(), &own, &dict, &mut work);
  for &r in dag.roots() {
    total = total.plus(costs[ix(r)]);
  }
  Ok(total)
}

/// Materialize the canonical representation of table sequence `q`.
pub(crate) fn materialize_sequence(
  dag: &SharingDag,
  own: &[Len],
  q: &[TermId],
  meter: &mut Meter<'_>,
) -> Result<(Vec<Arc<Expr>>, Vec<Arc<Expr>>), SharingError> {
  let nodes = dag.nodes();
  let mut dict = DenseIndex::new(dag.len());
  let mut table = Vec::with_capacity(q.len());
  let mut work = 0u64;
  for (i, &t) in q.iter().enumerate() {
    let costs = all_costs(nodes, own, &dict, &mut work);
    let mut e = materialize(nodes, own, &dict, &costs, &[t], &mut work)?;
    table.push(e.pop().ok_or_else(|| internal("entry"))?);
    dict.set(t, u64::try_from(i).map_err(|_e| internal("index"))?);
    meter.work(std::mem::take(&mut work))?;
  }
  let costs = all_costs(nodes, own, &dict, &mut work);
  let roots = materialize(nodes, own, &dict, &costs, dag.roots(), &mut work)?;
  meter.work(work)?;
  Ok((roots, table))
}

/// Run the exact optimizer on `dag`. `fixed` is the byte length of the
/// non-sharing part of the enclosing Constant (0 for bare roots); it only
/// enters the output-size limit.
pub(crate) fn optimize(
  dag: &SharingDag,
  fixed: u64,
  meter: &mut Meter<'_>,
) -> Result<ExactSharingResult, SharingError> {
  let prep = prepare(dag, meter)?;
  let mut unshared = Len::new(tag0_len(0));
  for &r in dag.roots() {
    unshared = unshared.plus(prep.base[ix(r)]);
  }
  meter.stats.unshared_len = unshared.exact();
  let (total, q) =
    width_state_search(dag, &prep, unshared, meter, WidthModel::Ixon)?;
  let variable = total
    .exact()
    .ok_or(SharingError::FormatBound(FormatBound::LengthOverflow))?;
  let output = fixed
    .checked_add(variable)
    .filter(|&x| x != u64::MAX)
    .ok_or(SharingError::FormatBound(FormatBound::LengthOverflow))?;
  meter.output(output)?;
  let (roots, sharing) = materialize_sequence(dag, &prep.own, &q, meter)?;
  // Certification: the real encodings have the optimized length and expand,
  // under the backward-reference rule, to exactly the input DAG.
  let mut actual = sharing_table_len(&sharing)
    .ok_or(SharingError::FormatBound(FormatBound::LengthOverflow))?;
  for r in &roots {
    actual = expr_len(r)
      .and_then(|l| actual.checked_add(l))
      .ok_or(SharingError::FormatBound(FormatBound::LengthOverflow))?;
  }
  if actual != variable {
    return Err(internal(format!(
      "materialized length {actual} differs from optimized length {variable}"
    )));
  }
  let mut check_meter = Meter::new(meter.limits());
  let check = SharingDag::build(&roots, Some(&sharing), &mut check_meter)?;
  if check != *dag {
    return Err(internal("materialized encoding changes the expanded AST"));
  }
  Ok(ExactSharingResult {
    roots,
    sharing,
    table_terms: q,
    variable_len: variable,
    stats: meter.stats.clone(),
  })
}

/// Reference for the uniform-width model: the width-state search with every
/// Share priced `w`, over the R1/R2 candidates (optionally only those of
/// compact in-degree at least 2). Returns the minimum model length and the
/// least term-ID table sequence attaining it. Exponential; for tests.
pub(crate) fn uniform_reference_dag(
  dag: &SharingDag,
  w: u8,
  min_in_degree2: bool,
  meter: &mut Meter<'_>,
) -> Result<(u64, Vec<TermId>), SharingError> {
  if w == 0 {
    return Err(SharingError::FormatBound(FormatBound::UniformWidth { w: 0 }));
  }
  let mut deg = vec![0u64; dag.len()];
  for &r in dag.roots() {
    deg[ix(r)] += 1;
  }
  for node in dag.nodes() {
    for &c in node.children().as_slice() {
      deg[ix(c)] += 1;
    }
  }
  let prep = prepare_with(dag, meter, |t| !min_in_degree2 || deg[ix(t)] >= 2)?;
  let mut unshared = Len::new(tag0_len(0));
  for &r in dag.roots() {
    unshared = unshared.plus(prep.base[ix(r)]);
  }
  let (total, q) =
    width_state_search(dag, &prep, unshared, meter, WidthModel::Uniform(w))?;
  let total = total
    .exact()
    .ok_or(SharingError::FormatBound(FormatBound::LengthOverflow))?;
  Ok((total, q))
}

/// Reference optimum of the uniform-width model for fully expanded roots:
/// the width-state search with every Share priced `w` (`1..=255`), over the
/// R1/R2 candidates, or only those of compact in-degree at least 2. Returns
/// the minimum model length and the least term-ID table sequence attaining
/// it. Exponential in the candidates; intended for differential tests.
pub fn optimize_sharing_uniform_reference(
  w: u64,
  roots: &[Arc<Expr>],
  limits: &ExactSharingLimits,
  min_in_degree2: bool,
) -> Result<(u64, Vec<TermId>), SharingError> {
  let w = u8::try_from(w)
    .map_err(|_e| SharingError::FormatBound(FormatBound::UniformWidth { w }))?;
  let mut meter = Meter::new(limits);
  let dag = SharingDag::build(roots, None, &mut meter)?;
  uniform_reference_dag(&dag, w, min_in_degree2, &mut meter)
}
