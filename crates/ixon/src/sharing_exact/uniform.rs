//! Exact minimum sharing under a uniform Share width.
//!
//! This is a byte-for-byte port of W1's `Ix/Sharing/Exact/Uniform.lean`;
//! the rules below are pinned by that implementation.
//!
//! Cost model: every `Share` costs exactly `w >= 1` bytes regardless of its
//! index; the table count is an exact TagN; telescopes and every other byte
//! are as written by `put_expr`. The model length of a stored set `S` is
//! `tag0(|S|) + sum_{t in S} inl_S(t) + sum_roots C_S(r)`, where `inl_S(t)`
//! is `t`'s cost with an inline top. Order does not affect it: in any order
//! with stored descendants first each entry sees every stored term that can
//! occur inside it, and a Share's price does not depend on its index. Only
//! the set is chosen; the table order is then pinned (stored descendants
//! first, then larger in-degree, then smaller structural ID).
//!
//! # Canonical class and classification
//!
//! * `deg(t)`: compact in-degree, with edge multiplicity and root
//!   occurrences; head positions are the root occurrences and the edges
//!   that do not continue a telescope (an App as the function of
//!   an App, a Lam as the body of a Lam, an All as the body of an All);
//!   `occ(t)`: expanded occurrences; `size(t)`: unshared standalone length.
//! * The canonical result is the minimum over tables whose entries all have
//!   in-degree >= 2. In-degree-1 terms are left out by an exchange that never
//!   increases the length (store the single parent instead, or turn extra
//!   writes of a stored parent into Shares), so this class contains a
//!   global minimum; ties can also store an in-degree-1 term, which this
//!   definition excludes.
//! * CERTAIN-EXCLUDED when `(occ-1)*size < occ*w` (in no minimum).
//! * Candidates: in-degree >= 2 and not certain-excluded.
//! * CERTAIN-STORED (in every minimum of the restricted class) when the gain
//!   bound `g >= theta`, with `d`, `h` the visible counts and lower bounds
//!   computed bottom-up pricing every candidate child at `min(w, .)`, every
//!   other child at its inline bound and a header of at least 1 byte:
//!   non-telescope `g = (d-1)*inl - d*w`; telescope with `h >= 1`
//!   `g = (d-1)*b + (h-1) - d*w`; telescope with `h = 0`
//!   `g = (d-1)*b - tag4(spine length) - d*w`.
//!   Visible counts `(d, h)` for a maybe-stored set `M` (the candidates):
//!   one per root occurrence plus, per edge from `z` (head edges only for
//!   `h`), 1 if `z` is in `M`, else `min(d(z), 2^20)`.
//!   Threshold: with `theta_max = 1 + tag0_step_bound(#candidates)` (2 below
//!   4311826560 candidates), `theta = 1` when `tag0(#candidates) = tag0(#terms
//!   with g >= theta_max)`, else `theta = theta_max`.
//! * UNCERTAIN: the other candidates; LOW-DEGREE: the other terms.
//!
//! Certain-stored terms cost exactly `w` wherever they occur (`g >= 1`
//! forces their merged payload bound `>= w`), so costs above them are
//! evaluated with them as `w`-byte leaves that end telescopes.
//!
//! # Search
//!
//! Uncertain terms joined by a DAG path avoiding certain-stored terms form
//! a component; costs are sums of per-component functions. Each component
//! search returns, per chosen count, its best change within `slack =
//! tag0(|certain-stored| + |uncertain|) - tag0(|certain-stored|)` of its
//! optimum. The table-count prefix is the only coupling: when the combined
//! choice reaches a TagN bracket of 128 or more entries, a knapsack over
//! components checks the lower brackets.
//!
//! The component search is W1's reclassifying branch and bound. At each node
//! it (1) recomputes the bounds and visible counts over the component's
//! area with the members decided "not stored" removed from `M`, and forces
//! "stored" every undecided member with `g >= theta`; (2) bounds the node by
//! the cost with every undecided member available and its entry free,
//! pruning only when strictly above the best by more than `slack`; (3)
//! splits the undecided members into groups joined by DAG paths through
//! non-opaque terms (a decided-stored member is opaque when its `inl` (or,
//! for a telescope, merged) bound is at least `w`; groups below a stored
//! non-opaque member are joined), solving groups by memoized sub-searches
//! keyed by the group and the decisions that reach it; (4) branches on the
//! undecided member with the largest `|g|` (then the smaller ID), "stored"
//! first when `g > 0`. Per-count tables of groups combine by convolution.
//! The plain subset enumeration is kept as the reference
//! (`ExactSharingLimits::uniform_subset_search`).
//!
//! # Tie-break
//!
//! Among minimum-length sets the least in the order "the smaller structural
//! ID of the symmetric difference is not stored". It decomposes over
//! components and through the knapsack.
//!
//! # Numeric domain
//!
//! Lean uses unbounded `Nat`. Here every such quantity is a `u128`; if any
//! bound or cost saturates, the call fails with
//! [`FormatBound::LengthOverflow`] instead of guessing. The exclusion test is
//! evaluated exactly even when an occurrence count saturates.

use std::sync::Arc;

use rustc_hash::{FxHashMap, FxHashSet};

use super::cost::{Len, expr_len, tag0_len, tag4_len};
use super::dag::{Node, SharingDag, TermId, ix};
use super::dict::{UniformIndex, all_costs, materialize_dependent};
use super::{
  ExactSharingLimits, ExactSharingStats, FormatBound, Meter, SharingError,
  constant_fixed_len, constant_info_root_exprs, rebuild_constant_info,
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

fn tid(i: usize) -> TermId {
  TermId::try_from(i).unwrap_or(TermId::MAX)
}

fn u(x: u64) -> u128 {
  u128::from(x)
}

/// Classification of a term for the uniform-width search.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum UniformClass {
  /// Not certain-excluded, but in-degree below 2: never searched.
  LowDegree,
  CertainExcluded,
  CertainStored,
  Uncertain,
}

/// Uniform-width result: the encoding, its model and real lengths, and the
/// classification and search statistics.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct UniformSharingResult {
  /// Rewritten roots, in input order.
  pub roots: Vec<Arc<Expr>>,
  /// The table, in the pinned order.
  pub sharing: Vec<Arc<Expr>>,
  /// Term ID of each table entry, in the pinned order.
  pub table_terms: Vec<TermId>,
  /// Exact uniform-model variable length (count, entries, roots).
  pub model_len: u64,
  /// Real serialized variable length of the same output.
  pub variable_len: u64,
  /// Unshared variable length (`None` if it exceeds `u64`).
  pub unshared_len: Option<u64>,
  /// The stored set, ascending.
  pub stored: Vec<TermId>,
  pub certain_stored: Vec<TermId>,
  pub certain_excluded: Vec<TermId>,
  pub uncertain: Vec<TermId>,
  pub low_degree: Vec<TermId>,
  /// Components of the uncertain terms (each ascending, by first member).
  pub components: Vec<Vec<TermId>>,
  /// Component subsets evaluated.
  pub states_visited: u64,
  /// Whether the table-count knapsack chose a lower TagN bracket.
  pub lower_bracket: bool,
  pub stats: ExactSharingStats,
}

// ---------------------------------------------------------------------------
// Graph facts
// ---------------------------------------------------------------------------

fn spine_next(node: &Node) -> TermId {
  match node {
    Node::App(f, _) => *f,
    Node::Lam(_, _, b) | Node::All(_, _, _, b) => *b,
    _ => 0,
  }
}

fn side_child(node: &Node) -> TermId {
  match node {
    Node::App(_, a) => *a,
    Node::Lam(_, ty, _) | Node::All(_, _, ty, _) => *ty,
    _ => 0,
  }
}

fn side_extra(node: &Node) -> u128 {
  match node {
    Node::App(..) => 0,
    _ => 1,
  }
}

/// Bytes a non-telescope node writes itself, excluding its children.
fn own_bytes(node: &Node) -> Result<u128, SharingError> {
  match node.family() {
    Some(_) => Ok(0),
    None => node.own_len().exact().map(u).ok_or_else(overflow),
  }
}

/// Whether the edge from `parent` to its `i`-th child continues the
/// parent's telescope.
fn continuation_edge(parent: &Node, i: usize, child: &Node) -> bool {
  match (parent, child) {
    (Node::App(..), Node::App(..)) => i == 0,
    (Node::Lam(..), Node::Lam(..)) | (Node::All(..), Node::All(..)) => i == 1,
    _ => false,
  }
}

pub(crate) struct Facts {
  pub(crate) deg: Vec<u64>,
  occ: Vec<u128>,
  parents: Vec<Vec<TermId>>,
}

pub(crate) fn graph_facts(dag: &SharingDag) -> Facts {
  let nodes = dag.nodes();
  let n = nodes.len();
  let mut deg = vec![0u64; n];
  let mut parents: Vec<Vec<TermId>> = vec![Vec::new(); n];
  for &r in dag.roots() {
    deg[ix(r)] += 1;
  }
  for (t, node) in nodes.iter().enumerate() {
    let kids = node.children();
    for &c in kids.as_slice() {
      deg[ix(c)] += 1;
      if !parents[ix(c)].contains(&tid(t)) {
        parents[ix(c)].push(tid(t));
      }
    }
  }
  let mut occ = vec![0u128; n];
  for &r in dag.roots() {
    occ[ix(r)] = occ[ix(r)].saturating_add(1);
  }
  for t in (0..n).rev() {
    let o = occ[t];
    if o == 0 {
      continue;
    }
    for &c in nodes[t].children().as_slice() {
      occ[ix(c)] = occ[ix(c)].saturating_add(o);
    }
  }
  Facts { deg, occ, parents }
}

/// Spine lengths and natural tails, with spines ending at `stop` terms.
fn spine_tables(nodes: &[Node], stop: &[bool]) -> (Vec<u64>, Vec<TermId>) {
  let n = nodes.len();
  let mut len = vec![0u64; n];
  let mut tail: Vec<TermId> = vec![0; n];
  for (t, node) in nodes.iter().enumerate() {
    if node.family().is_some() {
      let nxt = spine_next(node);
      if nodes[ix(nxt)].family() == node.family() && !stop[ix(nxt)] {
        len[t] = len[ix(nxt)] + 1;
        tail[t] = tail[ix(nxt)];
      } else {
        len[t] = 1;
        tail[t] = nxt;
      }
    }
  }
  (len, tail)
}

// ---------------------------------------------------------------------------
// Truncated evaluation
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, Debug, Default)]
struct UVal {
  cost: u128,
  inl: u128,
  sides: u128,
  below: Option<TermId>,
}

/// Evaluation tables with `opaq` terms as `w`-byte leaves ending spines.
struct UPrep<'d> {
  nodes: &'d [Node],
  w: u128,
  opaq: Vec<bool>,
  t_len: Vec<u64>,
  t_tail: Vec<TermId>,
  base: Vec<UVal>,
}

impl<'d> UPrep<'d> {
  fn new(
    nodes: &'d [Node],
    w: u128,
    opaq: Vec<bool>,
  ) -> Result<Self, SharingError> {
    let (t_len, t_tail) = spine_tables(nodes, &opaq);
    let mut up = UPrep { nodes, w, opaq, t_len, t_tail, base: Vec::new() };
    let mut base: Vec<UVal> = Vec::with_capacity(nodes.len());
    for t in 0..nodes.len() {
      let (v, _) = up.node(&|c| base[ix(c)], &|_| false, tid(t))?;
      base.push(v);
    }
    up.base = base;
    Ok(up)
  }

  /// One term's value given its children's values; also the number of
  /// available spine descendants visited.
  fn node(
    &self,
    get: &dyn Fn(TermId) -> UVal,
    avail: &dyn Fn(TermId) -> bool,
    t: TermId,
  ) -> Result<(UVal, u64), SharingError> {
    let node = &self.nodes[ix(t)];
    let mut steps = 0u64;
    let mut v = UVal::default();
    if node.family().is_none() {
      let mut inl = own_bytes(node)?;
      for &c in node.children().as_slice() {
        inl = inl.saturating_add(get(c).cost);
      }
      v.inl = inl;
    } else {
      let nxt = spine_next(node);
      let same =
        self.nodes[ix(nxt)].family() == node.family() && !self.opaq[ix(nxt)];
      let s = side_extra(node)
        .saturating_add(get(side_child(node)).cost)
        .saturating_add(if same { get(nxt).sides } else { 0 });
      let bl = if same {
        if avail(nxt) { Some(nxt) } else { get(nxt).below }
      } else {
        None
      };
      let l = self.t_len[ix(t)];
      let mut best = u(tag4_len(l))
        .saturating_add(s)
        .saturating_add(get(self.t_tail[ix(t)]).cost);
      let mut cur = bl;
      for _ in 0..l {
        let Some(x) = cur else { break };
        steps += 1;
        let gx = get(x);
        let cand = u(tag4_len(l - self.t_len[ix(x)]))
          .saturating_add(s - gx.sides)
          .saturating_add(self.w);
        best = best.min(cand);
        cur = gx.below;
      }
      v.inl = best;
      v.sides = s;
      v.below = bl;
    }
    v.cost = if self.opaq[ix(t)] {
      self.w
    } else if avail(t) {
      self.w.min(v.inl)
    } else {
      v.inl
    };
    if v.inl == u128::MAX || v.sides == u128::MAX || v.cost == u128::MAX {
      return Err(overflow());
    }
    Ok((v, steps))
  }
}

// ---------------------------------------------------------------------------
// Classification
// ---------------------------------------------------------------------------

/// `(occ-1)*size < occ*w`, exactly, for `occ >= 1` (a saturated `occ`
/// stands for some value at least `u128::MAX`).
fn certainly_excluded(occ: u128, size: u128, w: u128) -> bool {
  if size <= w {
    return true;
  }
  match occ.checked_mul(size - w) {
    Some(x) => x < size,
    None => false,
  }
}

/// Lower bounds of the certain-stored test (W1's `UBounds`): `inl`, bytes
/// of a term written inline at a head position; `merged`, bytes of a
/// telescope node inside a telescope running through it (no header);
/// `head_lb`/`cont_lb`, the same at a head/continuation position when the
/// term may be a Share.
#[derive(Clone)]
pub(crate) struct Bounds {
  inl: Vec<u128>,
  merged: Vec<u128>,
  head_lb: Vec<u128>,
  cont_lb: Vec<u128>,
}

/// One step of the bounds (W1's `boundsStep`): `[inl, merged, head_lb,
/// cont_lb]` of `t` from its children's head/continuation bounds.
fn bound_step(
  nodes: &[Node],
  t: TermId,
  w: u128,
  maybe: bool,
  head: &dyn Fn(TermId) -> u128,
  cont: &dyn Fn(TermId) -> u128,
) -> Result<[u128; 4], SharingError> {
  let node = &nodes[ix(t)];
  let (i, m) = if node.family().is_none() {
    let mut i = own_bytes(node)?;
    for &c in node.children().as_slice() {
      i = i.saturating_add(head(c));
    }
    (i, i)
  } else {
    let nxt = spine_next(node);
    let rest = if nodes[ix(nxt)].family() == node.family() {
      cont(nxt)
    } else {
      head(nxt)
    };
    let m = side_extra(node)
      .saturating_add(head(side_child(node)))
      .saturating_add(rest);
    (m.saturating_add(1), m)
  };
  if i == u128::MAX {
    return Err(overflow());
  }
  let (hl, cl) = if maybe { (w.min(i), w.min(m)) } else { (i, m) };
  Ok([i, m, hl, cl])
}

fn uniform_bounds(
  nodes: &[Node],
  w: u128,
  maybe: &[bool],
) -> Result<Bounds, SharingError> {
  let n = nodes.len();
  let mut b = Bounds {
    inl: vec![0; n],
    merged: vec![0; n],
    head_lb: vec![0; n],
    cont_lb: vec![0; n],
  };
  for (t, &mb) in maybe[..n].iter().enumerate() {
    let v = {
      let (hl, cl) = (&b.head_lb, &b.cont_lb);
      bound_step(nodes, tid(t), w, mb, &|c| hl[ix(c)], &|c| cl[ix(c)])?
    };
    b.inl[t] = v[0];
    b.merged[t] = v[1];
    b.head_lb[t] = v[2];
    b.cont_lb[t] = v[3];
  }
  Ok(b)
}

/// Cap of the visible counts where they are passed on.
const VISIBLE_CAP: u64 = 1 << 20;

/// W1's `propagateCounts`: per term, root occurrences plus, over the edges
/// from each parent `y` (descending IDs), `weight(y, count of y)`; the second
/// array counts only head (non-continuation) edges.
fn propagate_counts(
  dag: &SharingDag,
  weight: &dyn Fn(usize, u64) -> u64,
) -> (Vec<u64>, Vec<u64>) {
  let nodes = dag.nodes();
  let n = nodes.len();
  let mut all = vec![0u64; n];
  let mut head = vec![0u64; n];
  for &r in dag.roots() {
    all[ix(r)] += 1;
    head[ix(r)] += 1;
  }
  for y in (0..n).rev() {
    let wy = weight(y, all[y]);
    let node = &nodes[y];
    for (i, &c) in node.children().as_slice().iter().enumerate() {
      all[ix(c)] = all[ix(c)].saturating_add(wy);
      if !continuation_edge(node, i, &nodes[ix(c)]) {
        head[ix(c)] = head[ix(c)].saturating_add(wy);
      }
    }
  }
  (all, head)
}

/// Visible counts: lower bounds `(d, h)` on the inline occurrences (all /
/// at head positions) of each term in every encoding of a set inside
/// `maybe` that does not store it.
fn visible_counts(dag: &SharingDag, maybe: &[bool]) -> (Vec<u64>, Vec<u64>) {
  propagate_counts(dag, &|y, c| if maybe[y] { 1 } else { c.min(VISIBLE_CAP) })
}

fn to_i(x: u128) -> Result<i128, SharingError> {
  i128::try_from(x).map_err(|_e| overflow())
}

/// The certain-stored gain bound (W1's `storedGainC`) with `d` inline
/// occurrences in all, `h` of them at head positions, and the term's bounds
/// `inl`/`merged`.
fn stored_gain(
  node: &Node,
  d: u64,
  h: u64,
  spine_len: u64,
  inl: u128,
  merged: u128,
  w: u128,
) -> Result<i128, SharingError> {
  let d = i128::from(d);
  let dw = d.checked_mul(to_i(w)?);
  let g = if node.family().is_none() {
    (d - 1).checked_mul(to_i(inl)?).zip(dw).and_then(|(x, y)| x.checked_sub(y))
  } else if h >= 1 {
    (d - 1)
      .checked_mul(to_i(merged)?)
      .and_then(|x| x.checked_add(i128::from(h) - 1))
      .zip(dw)
      .and_then(|(x, y)| x.checked_sub(y))
  } else {
    (d - 1)
      .checked_mul(to_i(merged)?)
      .and_then(|x| x.checked_sub(i128::from(tag4_len(spine_len))))
      .zip(dw)
      .and_then(|(x, y)| x.checked_sub(y))
  };
  g.ok_or_else(overflow)
}

// ---------------------------------------------------------------------------
// Components
// ---------------------------------------------------------------------------

fn uf_find(parent: &[usize], x: usize) -> usize {
  let mut cur = x;
  while parent[cur] != cur {
    cur = parent[cur];
  }
  cur
}

/// Components of the uncertain terms, joined by DAG paths that avoid
/// certain-stored terms; each sorted, sorted by their smallest term.
fn uncertain_components(
  dag: &SharingDag,
  cls: &[UniformClass],
) -> Vec<Vec<TermId>> {
  let nodes = dag.nodes();
  let n = nodes.len();
  let mut uf: Vec<usize> = (0..n).collect();
  let mut reps: Vec<Vec<usize>> = vec![Vec::new(); n];
  for t in 0..n {
    if cls[t] == UniformClass::CertainStored {
      continue;
    }
    let mut rs: Vec<usize> = Vec::new();
    for &c in nodes[t].children().as_slice() {
      for &r in &reps[ix(c)] {
        let fr = uf_find(&uf, r);
        if !rs.contains(&fr) {
          rs.push(fr);
        }
      }
    }
    if cls[t] == UniformClass::Uncertain {
      for &r in &rs {
        let a = uf_find(&uf, t);
        let b = uf_find(&uf, r);
        if a != b {
          if a < b {
            uf[b] = a;
          } else {
            uf[a] = b;
          }
        }
      }
      reps[t] = vec![t];
    } else {
      reps[t] = rs;
    }
  }
  let mut groups: std::collections::BTreeMap<usize, Vec<TermId>> =
    std::collections::BTreeMap::new();
  for (t, c) in cls.iter().enumerate() {
    if *c == UniformClass::Uncertain {
      groups.entry(uf_find(&uf, t)).or_default().push(tid(t));
    }
  }
  let mut comps: Vec<Vec<TermId>> = groups.into_values().collect();
  comps.sort_by_key(|c| c[0]);
  comps
}

/// Members and their ancestors, not continuing above an opaque term.
fn component_area(
  up: &UPrep<'_>,
  facts: &Facts,
  members: &[TermId],
) -> Vec<TermId> {
  let mut seen: FxHashSet<TermId> = members.iter().copied().collect();
  let mut stack: Vec<TermId> = members.to_vec();
  while let Some(t) = stack.pop() {
    if up.opaq[ix(t)] {
      continue;
    }
    for &q in &facts.parents[ix(t)] {
      if seen.insert(q) {
        stack.push(q);
      }
    }
  }
  let mut out: Vec<TermId> = seen.into_iter().collect();
  out.sort_unstable();
  out
}

/// `a` precedes `b` (both ascending) when the smallest term of their
/// symmetric difference is in `b`, i.e. `a` leaves it out.
pub(crate) fn set_prec(a: &[TermId], b: &[TermId]) -> bool {
  let (mut x, mut y) = (0, 0);
  loop {
    match (a.get(x), b.get(y)) {
      (Some(p), Some(q)) => {
        if p == q {
          x += 1;
          y += 1;
        } else {
          return q < p;
        }
      },
      (Some(_) | None, None) => return false,
      (None, Some(_)) => return true,
    }
  }
}

fn merge_sorted(a: &[TermId], b: &[TermId]) -> Vec<TermId> {
  let mut out: Vec<TermId> = a.iter().chain(b).copied().collect();
  out.sort_unstable();
  out
}

type Choice = (i128, Vec<TermId>);

fn better(delta: i128, set: &[TermId], cur: Option<&Choice>) -> bool {
  match cur {
    None => true,
    Some((d, s)) => delta < *d || (delta == *d && set_prec(set, s)),
  }
}

struct CompCtx<'a, 'd> {
  up: &'a UPrep<'d>,
  members: Vec<TermId>,
  area: Vec<TermId>,
  root_mult: Vec<(TermId, u128)>,
  stored_in: Vec<TermId>,
  phi0: u128,
  slack: i128,
  /// Scratch: values of area terms, valid where `stamp == epoch`.
  vals: Vec<UVal>,
  stamp: Vec<u32>,
  epoch: u32,
  avail: Vec<bool>,
}

impl CompCtx<'_, '_> {
  /// Cost of the component's parts with `avail` and `chosen` (entries of
  /// undecided members omitted), and the evaluation work.
  fn phi(&mut self, chosen: &[TermId]) -> Result<(u128, u64), SharingError> {
    if self.epoch == u32::MAX {
      self.stamp.fill(0);
      self.epoch = 0;
    }
    self.epoch += 1;
    let ep = self.epoch;
    let mut work = 0u64;
    for k in 0..self.area.len() {
      let t = self.area[k];
      let (v, s) = {
        let vals = &self.vals;
        let stamp = &self.stamp;
        let base = &self.up.base;
        let avail = &self.avail;
        let get = |c: TermId| {
          if stamp[ix(c)] == ep { vals[ix(c)] } else { base[ix(c)] }
        };
        let av = |c: TermId| avail[ix(c)];
        self.up.node(&get, &av, t)?
      };
      self.vals[ix(t)] = v;
      self.stamp[ix(t)] = ep;
      work = work.saturating_add(1 + s);
    }
    let get = |c: TermId| {
      if self.stamp[ix(c)] == ep {
        self.vals[ix(c)]
      } else {
        self.up.base[ix(c)]
      }
    };
    let mut total = 0u128;
    for &(r, m) in &self.root_mult {
      total = total.saturating_add(m.saturating_mul(get(r).cost));
    }
    for &c in &self.stored_in {
      total = total.saturating_add(get(c).inl);
    }
    for &x in chosen {
      total = total.saturating_add(get(x).inl);
    }
    if total == u128::MAX {
      return Err(overflow());
    }
    Ok((total, work))
  }

  /// Depth-first branch and bound over the members (ascending), "not
  /// stored" first. Returns the best choice and the best per set size.
  fn search(
    &mut self,
    meter: &mut Meter<'_>,
  ) -> Result<(Choice, Vec<Option<Choice>>), SharingError> {
    let mut best: Option<Choice> = None;
    let mut by_size: Vec<Option<Choice>> = Vec::new();
    // Frames: (next member index, chosen so far).
    let mut stack: Vec<(usize, Vec<TermId>)> = vec![(0, Vec::new())];
    while let Some((i, chosen)) = stack.pop() {
      meter.state()?;
      for (k, &m) in self.members.iter().enumerate() {
        self.avail[ix(m)] = k >= i || chosen.contains(&m);
      }
      let (phi, work) = self.phi(&chosen)?;
      meter.work(work)?;
      let delta = to_i(phi)? - to_i(self.phi0)?;
      if i >= self.members.len() {
        if better(delta, &chosen, best.as_ref()) {
          best = Some((delta, chosen.clone()));
        }
        let k = chosen.len();
        if by_size.len() <= k {
          by_size.resize(k + 1, None);
        }
        if better(delta, &chosen, by_size[k].as_ref()) {
          by_size[k] = Some((delta, chosen));
        }
        continue;
      }
      if let Some((b, _)) = &best
        && delta > b + self.slack
      {
        continue;
      }
      let t = self.members[i];
      let mut with = chosen.clone();
      with.push(t);
      stack.push((i + 1, with));
      stack.push((i + 1, chosen));
    }
    for &m in &self.members {
      self.avail[ix(m)] = false;
    }
    let best =
      best.ok_or_else(|| internal("component search found no choice"))?;
    Ok((best, by_size))
  }
}

// ---------------------------------------------------------------------------
// Reclassifying branch and bound with splitting (W1's `SCtx`)
// ---------------------------------------------------------------------------

/// Best `(delta, set)` per chosen count (index = set size).
type CTable = Vec<Option<Choice>>;

fn table_best(tb: &CTable) -> Option<i128> {
  tb.iter().flatten().map(|(d, _)| *d).min()
}

fn table_add(tb: &mut CTable, e: Choice) {
  let k = e.1.len();
  if tb.len() <= k {
    tb.resize(k + 1, None);
  }
  if better(e.0, &e.1, tb[k].as_ref()) {
    tb[k] = Some(e);
  }
}

fn table_trim(tb: CTable, slack: i128) -> CTable {
  match table_best(&tb) {
    None => tb,
    Some(b) => {
      tb.into_iter().map(|o| o.filter(|(d, _)| *d <= b + slack)).collect()
    },
  }
}

fn table_conv(a: &CTable, b: &CTable) -> CTable {
  let mut out: CTable = Vec::new();
  for (da, sa) in a.iter().flatten() {
    for (db, sb) in b.iter().flatten() {
      table_add(&mut out, (da + db, merge_sorted(sa, sb)));
    }
  }
  out
}

/// The undecided member to branch on: the largest `|gain|`, then the
/// smaller ID.
fn pick_branch(gains: &[(TermId, i128)]) -> Option<(TermId, i128)> {
  let mut acc: Option<(TermId, i128)> = None;
  for &(t, g) in gains {
    acc = match acc {
      None => Some((t, g)),
      Some((a, ga)) => {
        if g.unsigned_abs() > ga.unsigned_abs()
          || (g.unsigned_abs() == ga.unsigned_abs() && t < a)
        {
          Some((t, g))
        } else {
          acc
        }
      },
    };
  }
  acc
}

/// Bounds of the area under a maybe-stored predicate, over the root-level
/// bounds (W1's `SCtx.rebound`).
struct Overlay<'b> {
  base: &'b Bounds,
  vals: FxHashMap<TermId, [u128; 4]>,
}

impl Overlay<'_> {
  fn get(&self, t: TermId) -> [u128; 4] {
    match self.vals.get(&t) {
      Some(v) => *v,
      None => {
        let k = ix(t);
        [
          self.base.inl[k],
          self.base.merged[k],
          self.base.head_lb[k],
          self.base.cont_lb[k],
        ]
      },
    }
  }
}

struct SCtx<'a, 'd> {
  up: &'a UPrep<'d>,
  facts: &'a Facts,
  cand: &'a [bool],
  b0: &'a Bounds,
  vis0: &'a (Vec<u64>, Vec<u64>),
  spine_len: &'a [u64],
  dag_size: u64,
  members: Vec<TermId>,
  member_idx: FxHashMap<TermId, usize>,
  area: Vec<TermId>,
  area_idx: FxHashMap<TermId, usize>,
  /// Per area node: `(parent, edges, head edges)` per distinct parent.
  in_edges: Vec<Vec<(TermId, u64, u64)>>,
  root_occ: Vec<u64>,
  root_mult: Vec<(TermId, u128)>,
  stored_in: Vec<TermId>,
  slack: i128,
  theta: i128,
  memo: FxHashMap<Vec<u64>, CTable>,
  memo_hits: u64,
  vals: Vec<UVal>,
  stamp: Vec<u32>,
  epoch: u32,
}

impl SCtx<'_, '_> {
  /// The component cost with `avail` available and the entries of
  /// `stored`, and the evaluation work (W1's `SCtx.phi`).
  fn phi(
    &mut self,
    avail: &dyn Fn(TermId) -> bool,
    stored: &[TermId],
  ) -> Result<(u128, u64), SharingError> {
    if self.epoch == u32::MAX {
      self.stamp.fill(0);
      self.epoch = 0;
    }
    self.epoch += 1;
    let ep = self.epoch;
    let mut work = 0u64;
    for k in 0..self.area.len() {
      let t = self.area[k];
      let (v, s) = {
        let (vals, stamp, base) = (&self.vals, &self.stamp, &self.up.base);
        let get = |c: TermId| {
          if stamp[ix(c)] == ep { vals[ix(c)] } else { base[ix(c)] }
        };
        self.up.node(&get, avail, t)?
      };
      self.vals[ix(t)] = v;
      self.stamp[ix(t)] = ep;
      work = work.saturating_add(1 + s);
    }
    let get = |c: TermId| {
      if self.stamp[ix(c)] == ep {
        self.vals[ix(c)]
      } else {
        self.up.base[ix(c)]
      }
    };
    let mut total = 0u128;
    for &(r, m) in &self.root_mult {
      total = total.saturating_add(m.saturating_mul(get(r).cost));
    }
    for &c in self.stored_in.iter().chain(stored) {
      total = total.saturating_add(get(c).inl);
    }
    if total == u128::MAX {
      return Err(overflow());
    }
    Ok((total, work))
  }

  fn charge(meter: &mut Meter<'_>, work: u64) -> Result<(), SharingError> {
    meter.state()?;
    meter.work(work)
  }

  fn rebound(
    &self,
    ms: &dyn Fn(TermId) -> bool,
  ) -> Result<Overlay<'_>, SharingError> {
    let mut ov = Overlay { base: self.b0, vals: FxHashMap::default() };
    for &t in &self.area {
      let v = {
        let ovr = &ov;
        bound_step(
          self.up.nodes,
          t,
          self.up.w,
          ms(t),
          &|c| ovr.get(c)[2],
          &|c| ovr.get(c)[3],
        )?
      };
      ov.vals.insert(t, v);
    }
    Ok(ov)
  }

  fn revisible(
    &self,
    ms: &dyn Fn(TermId) -> bool,
  ) -> FxHashMap<TermId, (u64, u64)> {
    let mut vis: FxHashMap<TermId, (u64, u64)> = FxHashMap::default();
    for j in (0..self.area.len()).rev() {
      let y = self.area[j];
      let r = self.root_occ[j];
      let (mut d, mut h) = (r, r);
      for &(q, ma, mh) in &self.in_edges[j] {
        let wq = if ms(q) {
          1
        } else {
          vis.get(&q).map_or(self.vis0.0[ix(q)], |v| v.0).min(VISIBLE_CAP)
        };
        d = d.saturating_add(ma.saturating_mul(wq));
        h = h.saturating_add(mh.saturating_mul(wq));
      }
      vis.insert(y, (d, h));
    }
    vis
  }

  fn opaque_under(&self, b: &Overlay<'_>, t: TermId) -> bool {
    let v = b.get(t);
    if self.up.nodes[ix(t)].family().is_none() {
      v[0] >= self.up.w
    } else {
      v[1] >= self.up.w
    }
  }

  /// Groups of the undecided members (W1's `SCtx.groups`).
  fn groups(
    &self,
    opq: &dyn Fn(TermId) -> bool,
    avail_fixed: &dyn Fn(TermId) -> bool,
    und: &[TermId],
  ) -> Vec<Vec<TermId>> {
    let und_set: FxHashSet<TermId> = und.iter().copied().collect();
    let mut uf: Vec<usize> = (0..self.members.len()).collect();
    let mut reps: Vec<Vec<usize>> = vec![Vec::new(); self.area.len()];
    let union = |uf: &mut Vec<usize>, x: usize, y: usize| {
      let a = uf_find(uf, x);
      let b = uf_find(uf, y);
      if a != b {
        if a < b {
          uf[b] = a;
        } else {
          uf[a] = b;
        }
      }
    };
    for j in 0..self.area.len() {
      let y = self.area[j];
      if opq(y) {
        continue;
      }
      let mut rs: Vec<usize> = Vec::new();
      for &c in self.up.nodes[ix(y)].children().as_slice() {
        if let Some(&jc) = self.area_idx.get(&c) {
          for &r in &reps[jc] {
            let fr = uf_find(&uf, r);
            if !rs.contains(&fr) {
              rs.push(fr);
            }
          }
        }
      }
      if und_set.contains(&y) {
        let iy = self.member_idx.get(&y).copied().unwrap_or(0);
        for &r in &rs {
          union(&mut uf, iy, r);
        }
        reps[j] = vec![uf_find(&uf, iy)];
      } else if avail_fixed(y) && rs.len() > 1 {
        let r0 = rs[0];
        for &r in &rs {
          union(&mut uf, r0, r);
        }
        reps[j] = vec![uf_find(&uf, r0)];
      } else {
        reps[j] = rs;
      }
    }
    let mut groups: FxHashMap<usize, Vec<TermId>> = FxHashMap::default();
    for &t in und {
      let r = uf_find(&uf, self.member_idx.get(&t).copied().unwrap_or(0));
      groups.entry(r).or_default().push(t);
    }
    let mut gs: Vec<Vec<TermId>> = groups
      .into_values()
      .map(|mut g| {
        g.sort_unstable();
        g
      })
      .collect();
    gs.sort_by_key(|g| g[0]);
    gs
  }

  /// Memo key of a group and the decided members that reach it (W1's
  /// `SCtx.memoKey`).
  fn memo_key(
    &self,
    opq: &dyn Fn(TermId) -> bool,
    in_set: &FxHashSet<TermId>,
    out_set: &FxHashSet<TermId>,
    g: &[TermId],
  ) -> (Vec<u64>, FxHashSet<TermId>) {
    let code = |q: TermId| u64::from(q) * 3 + if opq(q) { 2 } else { 1 };
    let mut entries: Vec<u64> = Vec::new();
    let mut rel: FxHashSet<TermId> = FxHashSet::default();
    let mut down_start: Vec<TermId> = g.to_vec();
    let mut seen: FxHashSet<TermId> = g.iter().copied().collect();
    let mut stack: Vec<TermId> = g.to_vec();
    while let Some(y) = stack.pop() {
      for &q in &self.facts.parents[ix(y)] {
        if !self.area_idx.contains_key(&q) || !seen.insert(q) {
          continue;
        }
        if out_set.contains(&q) {
          entries.push(u64::from(q) * 3);
          rel.insert(q);
        } else if in_set.contains(&q) {
          entries.push(code(q));
          rel.insert(q);
          if !opq(q) {
            down_start.push(q);
          }
        }
        if !opq(q) {
          stack.push(q);
        }
      }
    }
    let mut seen: FxHashSet<TermId> = down_start.iter().copied().collect();
    let mut stack = down_start;
    while let Some(y) = stack.pop() {
      for &c in self.up.nodes[ix(y)].children().as_slice() {
        if !self.area_idx.contains_key(&c) || !seen.insert(c) {
          continue;
        }
        if !rel.contains(&c) {
          if out_set.contains(&c) {
            entries.push(u64::from(c) * 3);
            rel.insert(c);
          } else if in_set.contains(&c) {
            entries.push(code(c));
            rel.insert(c);
          }
        }
        if !opq(c) {
          stack.push(c);
        }
      }
    }
    entries.sort_unstable();
    let mut key: Vec<u64> = g.iter().map(|&t| u64::from(t)).collect();
    key.push(3 * self.dag_size + 3);
    key.extend(entries);
    (key, rel)
  }

  /// Exact table of a group under the decided members outside it (W1's
  /// `SCtx.solve`).
  fn solve(
    &mut self,
    meter: &mut Meter<'_>,
    g: &[TermId],
    in_all: &[TermId],
    out_all: &[TermId],
  ) -> Result<CTable, SharingError> {
    let out_set: FxHashSet<TermId> = out_all.iter().copied().collect();
    let in_set: FxHashSet<TermId> = in_all.iter().copied().collect();
    let key = {
      let cand = self.cand;
      let ms = |t: TermId| cand[ix(t)] && !out_set.contains(&t);
      let b = self.rebound(&ms)?;
      let opq = |t: TermId| {
        self.up.opaq[ix(t)] || (in_set.contains(&t) && self.opaque_under(&b, t))
      };
      self.memo_key(&opq, &in_set, &out_set, g).0
    };
    if let Some(tb) = self.memo.get(&key) {
      self.memo_hits += 1;
      return Ok(tb.clone());
    }
    let (phi0, work) = self.phi(&|t| in_set.contains(&t), in_all)?;
    Self::charge(meter, work.saturating_add(len64(self.area.len())))?;
    let tb = self.node(
      meter,
      phi0,
      in_all,
      out_all.to_vec(),
      out_all.len(),
      Vec::new(),
      g,
      Vec::new(),
    )?;
    let tb = table_trim(tb, self.slack);
    self.memo.insert(key, tb.clone());
    Ok(tb)
  }

  /// Branch-and-bound node of a group (W1's `SCtx.node`).
  #[allow(clippy::too_many_arguments)]
  fn node(
    &mut self,
    meter: &mut Meter<'_>,
    phi0: u128,
    in_ctx: &[TermId],
    out_all: Vec<TermId>,
    n_out_ctx: usize,
    local_in: Vec<TermId>,
    und: &[TermId],
    mut tb: CTable,
  ) -> Result<CTable, SharingError> {
    let out_set: FxHashSet<TermId> = out_all.iter().copied().collect();
    let cand = self.cand;
    let ms = |t: TermId| cand[ix(t)] && !out_set.contains(&t);
    // Reclassify.
    let (gains, opaque_in) = {
      let b = self.rebound(&ms)?;
      let vis = self.revisible(&ms);
      let mut gains: Vec<(TermId, i128)> = Vec::with_capacity(und.len());
      for &t in und {
        let (d, h) = vis
          .get(&t)
          .copied()
          .unwrap_or((self.vis0.0[ix(t)], self.vis0.1[ix(t)]));
        let v = b.get(t);
        let gt = stored_gain(
          &self.up.nodes[ix(t)],
          d,
          h,
          self.spine_len[ix(t)],
          v[0],
          v[1],
          self.up.w,
        )?;
        gains.push((t, gt));
      }
      // Opacity of every decided-stored member under these bounds (the
      // forced members included), for the split below.
      let mut opaque_in: FxHashSet<TermId> = FxHashSet::default();
      for &t in in_ctx
        .iter()
        .chain(&local_in)
        .chain(gains.iter().filter(|(_, g)| *g >= self.theta).map(|(t, _)| t))
      {
        if self.opaque_under(&b, t) {
          opaque_in.insert(t);
        }
      }
      (gains, opaque_in)
    };
    let forced: Vec<TermId> =
      gains.iter().filter(|(_, g)| *g >= self.theta).map(|(t, _)| *t).collect();
    let local_in = if forced.is_empty() {
      local_in
    } else {
      merge_sorted(&local_in, &forced)
    };
    let open: Vec<(TermId, i128)> =
      gains.into_iter().filter(|(_, g)| *g < self.theta).collect();
    let und: Vec<TermId> = open.iter().map(|(t, _)| *t).collect();
    let in_all: Vec<TermId> = in_ctx.iter().chain(&local_in).copied().collect();
    let in_set: FxHashSet<TermId> = in_all.iter().copied().collect();
    let und_set: FxHashSet<TermId> = und.iter().copied().collect();
    // Lower bound: every undecided member available, its entry free.
    let (phi, work) =
      self.phi(&|t| in_set.contains(&t) || und_set.contains(&t), &in_all)?;
    Self::charge(meter, work.saturating_add(2 * len64(self.area.len())))?;
    let delta = to_i(phi)? - to_i(phi0)?;
    if und.is_empty() {
      table_add(&mut tb, (delta, local_in));
      return Ok(tb);
    }
    if let Some(bd) = table_best(&tb)
      && delta > bd + self.slack
    {
      return Ok(tb);
    }
    // Split into independent groups.
    let opq = |t: TermId| {
      self.up.opaq[ix(t)] || (in_set.contains(&t) && opaque_in.contains(&t))
    };
    let avail_fixed = |t: TermId| in_set.contains(&t) && !opq(t);
    let groups = self.groups(&opq, &avail_fixed, &und);
    let route = if groups.len() > 1 {
      true
    } else if groups.len() == 1 {
      let (_, rel) = self.memo_key(&opq, &in_set, &out_set, &groups[0]);
      local_in.iter().any(|t| !rel.contains(t))
        || out_all[n_out_ctx..].iter().any(|t| !rel.contains(t))
    } else {
      false
    };
    if route {
      let (phi_none, work) = self.phi(&|t| in_set.contains(&t), &in_all)?;
      Self::charge(meter, work)?;
      let base = to_i(phi_none)? - to_i(phi0)?;
      let mut comb: CTable = vec![Some((base, local_in.clone()))];
      for grp in &groups {
        let sub = self.solve(meter, grp, &in_all, &out_all)?;
        comb = table_trim(table_conv(&comb, &sub), self.slack);
      }
      for e in comb.into_iter().flatten() {
        table_add(&mut tb, e);
      }
      return Ok(tb);
    }
    // Branch on the largest |gain|, "stored" first when it is positive.
    let Some((t, gt)) = pick_branch(&open) else {
      return Ok(tb);
    };
    let mut und2 = und.clone();
    if let Some(p) = und2.iter().position(|&x| x == t) {
      und2.remove(p);
    }
    let with_t = merge_sorted(&local_in, &[t]);
    let mut out_t = out_all.clone();
    out_t.push(t);
    if gt > 0 {
      let tb = self
        .node(meter, phi0, in_ctx, out_all, n_out_ctx, with_t, &und2, tb)?;
      self.node(meter, phi0, in_ctx, out_t, n_out_ctx, local_in, &und2, tb)
    } else {
      let tb = self.node(
        meter,
        phi0,
        in_ctx,
        out_t,
        n_out_ctx,
        local_in.clone(),
        &und2,
        tb,
      )?;
      self.node(meter, phi0, in_ctx, out_all, n_out_ctx, with_t, &und2, tb)
    }
  }
}

// ---------------------------------------------------------------------------
// Order and driver
// ---------------------------------------------------------------------------

/// First count with the same TagN (f = 0) width as `k` (`tag0_len`): the
/// start of `k`'s rung. Mirrors Lean `tag0BracketStart`.
fn tag0_bracket_start(k: u64) -> u64 {
  if k < TagN::end1(0) {
    0
  } else if k < TagN::end2(0) {
    TagN::end1(0)
  } else if k < TagN::end3(0) {
    TagN::end2(0)
  } else if k < TagN::end4(0) {
    TagN::end3(0)
  } else if k < TagN::end5(0) {
    TagN::end4(0)
  } else {
    TagN::end5(0)
  }
}

/// An upper bound on `tag0_len(k + 1) - tag0_len(k)` for every `k < n`: the
/// TagN (f = 0) width grows by one byte at 128, 16512, 82048 and 16859264,
/// and by four at 4311826560. Mirrors Lean `tag0StepBound`.
fn tag0_step_bound(n: u64) -> u64 {
  if n < TagN::end5(0) { 1 } else { 4 }
}

/// Pinned table order of a stored set: stored descendants first; among
/// ready terms the larger in-degree first, then the smaller ID.
pub(crate) fn pinned_order(
  dag: &SharingDag,
  deg: &[u64],
  stored: &[TermId],
) -> Vec<TermId> {
  let nodes = dag.nodes();
  let mut is_stored = vec![false; nodes.len()];
  for &t in stored {
    is_stored[ix(t)] = true;
  }
  // Nearest stored descendants of each stored term.
  let mut pending: Vec<usize> = Vec::with_capacity(stored.len());
  let mut dependents: FxHashMap<TermId, Vec<TermId>> = FxHashMap::default();
  for &t in stored {
    let mut seen: FxHashSet<TermId> = FxHashSet::default();
    let mut stack: Vec<TermId> = nodes[ix(t)].children().as_slice().to_vec();
    let mut deps = 0usize;
    while let Some(x) = stack.pop() {
      if !seen.insert(x) {
        continue;
      }
      if is_stored[ix(x)] {
        deps += 1;
        dependents.entry(x).or_default().push(t);
      } else {
        stack.extend_from_slice(nodes[ix(x)].children().as_slice());
      }
    }
    pending.push(deps);
  }
  let pos: FxHashMap<TermId, usize> =
    stored.iter().enumerate().map(|(k, &t)| (t, k)).collect();
  let mut heap: std::collections::BinaryHeap<(u64, std::cmp::Reverse<TermId>)> =
    std::collections::BinaryHeap::new();
  for (k, &t) in stored.iter().enumerate() {
    if pending[k] == 0 {
      heap.push((deg[ix(t)], std::cmp::Reverse(t)));
    }
  }
  let mut order = Vec::with_capacity(stored.len());
  while let Some((_, std::cmp::Reverse(t))) = heap.pop() {
    order.push(t);
    if let Some(ds) = dependents.get(&t) {
      for &d in ds {
        let k = pos[&d];
        pending[k] -= 1;
        if pending[k] == 0 {
          heap.push((deg[ix(d)], std::cmp::Reverse(d)));
        }
      }
    }
  }
  order
}

/// Exact uniform-width optimization of a DAG.
pub(crate) fn optimize_uniform(
  w: u64,
  dag: &SharingDag,
  meter: &mut Meter<'_>,
) -> Result<UniformSharingResult, SharingError> {
  if w == 0 {
    return Err(SharingError::FormatBound(FormatBound::UniformWidth { w }));
  }
  let wu = u(w);
  let nodes = dag.nodes();
  let n = nodes.len();
  let facts = graph_facts(dag);
  // Unshared sizes C_0 (no stop terms, nothing available).
  let empty = UPrep::new(nodes, wu, vec![false; n])?;
  let size: Vec<u128> = empty.base.iter().map(|v| v.cost).collect();
  let (spine_len, _) = spine_tables(nodes, &vec![false; n]);
  // Classes: certain-excluded, low degree, and the gain test on visible
  // counts with threshold theta.
  let ce: Vec<bool> =
    (0..n).map(|t| certainly_excluded(facts.occ[t], size[t], wu)).collect();
  let cand: Vec<bool> = (0..n).map(|t| !ce[t] && facts.deg[t] >= 2).collect();
  let bounds = uniform_bounds(nodes, wu, &cand)?;
  let vis0 = visible_counts(dag, &cand);
  let classify = |theta: i128| -> Result<Vec<UniformClass>, SharingError> {
    let mut cls = Vec::with_capacity(n);
    for t in 0..n {
      cls.push(if ce[t] {
        UniformClass::CertainExcluded
      } else if facts.deg[t] < 2 {
        UniformClass::LowDegree
      } else if stored_gain(
        &nodes[t],
        vis0.0[t],
        vis0.1[t],
        spine_len[t],
        bounds.inl[t],
        bounds.merged[t],
        wu,
      )? >= theta
      {
        UniformClass::CertainStored
      } else {
        UniformClass::Uncertain
      });
    }
    Ok(cls)
  };
  // theta = 1 + tag0_step_bound(#candidates) always holds (one more entry
  // grows the table count by at most that many bytes; 2 below 4311826560
  // candidates); 1 when every minimum lies in one count bracket.
  let n_cand = len64(cand.iter().filter(|&&c| c).count());
  let theta_max = i128::from(tag0_step_bound(n_cand)) + 1;
  let cls_max = classify(theta_max)?;
  let n_cs_max = len64(
    cls_max.iter().filter(|&&c| c == UniformClass::CertainStored).count(),
  );
  let theta: i128 =
    if tag0_len(n_cand) == tag0_len(n_cs_max) { 1 } else { theta_max };
  let cls = if theta == 1 { classify(1)? } else { cls_max };
  let pick = |c: UniformClass| -> Vec<TermId> {
    (0..n).filter(|&t| cls[t] == c).map(tid).collect()
  };
  let cs = pick(UniformClass::CertainStored);
  let ce_terms = pick(UniformClass::CertainExcluded);
  let unc = pick(UniformClass::Uncertain);
  let low = pick(UniformClass::LowDegree);
  meter.candidates(u64::try_from(cs.len() + unc.len()).unwrap_or(u64::MAX))?;
  let mut opaq = vec![false; n];
  for &t in &cs {
    opaq[ix(t)] = true;
  }
  let up = UPrep::new(nodes, wu, opaq)?;
  let comps = uncertain_components(dag, &cls);
  let k_cs = u64::try_from(cs.len()).unwrap_or(u64::MAX);
  let k_unc = u64::try_from(unc.len()).unwrap_or(u64::MAX);
  // Largest table-count difference between two candidate-only sets that
  // contain the certain-stored terms.
  let slack = i128::from(tag0_len(k_cs.saturating_add(k_unc)))
    - i128::from(tag0_len(k_cs));
  // Search each component (independent searches; see `Parallelism`).
  let search_one = |members: &Vec<TermId>,
                    meter: &mut Meter<'_>|
   -> Result<(Choice, CTable), SharingError> {
    let area = component_area(&up, &facts, members);
    let area_set: FxHashSet<TermId> = area.iter().copied().collect();
    let mut mult: std::collections::BTreeMap<TermId, u128> =
      std::collections::BTreeMap::new();
    for &r in dag.roots() {
      if area_set.contains(&r) {
        *mult.entry(r).or_default() += 1;
      }
    }
    let root_mult: Vec<(TermId, u128)> = mult.into_iter().collect();
    let stored_in: Vec<TermId> =
      area.iter().copied().filter(|&t| up.opaq[ix(t)]).collect();
    if meter.limits().uniform_subset_search {
      // The reference: plain subset enumeration.
      let mut cx = CompCtx {
        up: &up,
        members: members.clone(),
        area,
        root_mult,
        stored_in,
        phi0: 0,
        slack,
        vals: vec![UVal::default(); n],
        stamp: vec![0; n],
        epoch: 0,
        avail: vec![false; n],
      };
      let (phi0, _) = cx.phi(&[])?;
      cx.phi0 = phi0;
      return cx.search(meter);
    }
    let area_idx: FxHashMap<TermId, usize> =
      area.iter().enumerate().map(|(j, &t)| (t, j)).collect();
    let member_idx: FxHashMap<TermId, usize> =
      members.iter().enumerate().map(|(j, &t)| (t, j)).collect();
    let in_edges: Vec<Vec<(TermId, u64, u64)>> = area
      .iter()
      .map(|&y| {
        facts.parents[ix(y)]
          .iter()
          .map(|&q| {
            let node = &nodes[ix(q)];
            let (mut ma, mut mh) = (0u64, 0u64);
            for (i, &c) in node.children().as_slice().iter().enumerate() {
              if c == y {
                ma += 1;
                if !continuation_edge(node, i, &nodes[ix(y)]) {
                  mh += 1;
                }
              }
            }
            (q, ma, mh)
          })
          .collect()
      })
      .collect();
    let root_occ: Vec<u64> = area
      .iter()
      .map(|y| {
        root_mult
          .iter()
          .find(|(r, _)| r == y)
          .map_or(0, |(_, m)| u64::try_from(*m).unwrap_or(u64::MAX))
      })
      .collect();
    let mut cx = SCtx {
      up: &up,
      facts: &facts,
      cand: &cand,
      b0: &bounds,
      vis0: &vis0,
      spine_len: &spine_len,
      dag_size: len64(n),
      members: members.clone(),
      member_idx,
      area,
      area_idx,
      in_edges,
      root_occ,
      root_mult,
      stored_in,
      slack,
      theta,
      memo: FxHashMap::default(),
      memo_hits: 0,
      vals: vec![UVal::default(); n],
      stamp: vec![0; n],
      epoch: 0,
    };
    let tb = cx.solve(meter, members, &[], &[])?;
    let bd = table_best(&tb)
      .ok_or_else(|| internal("component search found no choice"))?;
    let mut best_set: Option<&Vec<TermId>> = None;
    for (d, s) in tb.iter().flatten() {
      if *d == bd && best_set.is_none_or(|a| set_prec(s, a)) {
        best_set = Some(s);
      }
    }
    let bs = best_set
      .cloned()
      .ok_or_else(|| internal("component search found no choice"))?;
    Ok(((bd, bs), tb))
  };
  let budget = meter.parallel.components;
  let mut results: Vec<(Choice, CTable)> = Vec::with_capacity(comps.len());
  if budget <= 1 {
    for members in &comps {
      results.push(search_one(members, meter)?);
    }
  } else {
    // Each component on its own meter; the counts are added in component
    // order afterwards (`Meter::absorb`), then the results are used in the
    // same order as sequentially.
    let limits = meter.limits();
    let outs = super::par::map_ranges(comps.len(), budget, |r| {
      r.map(|j| {
        let mut m = Meter::new(limits);
        let res = search_one(&comps[j], &mut m);
        (res, m.stats)
      })
      .collect()
    });
    for (res, stats) in outs {
      meter.absorb(&stats)?;
      results.push(res?);
    }
  }
  let states_visited = meter.stats.states_created;
  // Combine: per-component optima, unless a lower count bracket is shorter.
  let mut chosen_x: Vec<TermId> = Vec::new();
  let mut chosen_delta: i128 = 0;
  for ((d, s), _) in &results {
    chosen_x = merge_sorted(&chosen_x, s);
    chosen_delta += d;
  }
  let len_u64 = |v: usize| u64::try_from(v).unwrap_or(u64::MAX);
  let k0 = k_cs.saturating_add(len_u64(chosen_x.len()));
  let start = tag0_bracket_start(k0);
  let mut lower_bracket = false;
  if start > k_cs {
    let cap = usize::try_from(start - 1 - k_cs).map_err(|_e| overflow())?;
    let cells = (results.len() + 1).saturating_mul(cap + 1);
    if u64::try_from(cells).unwrap_or(u64::MAX) > meter.limits().max_states {
      return Err(SharingError::ResourceExhausted(super::ResourceExhausted {
        resource: super::Resource::States,
        limit: meter.limits().max_states,
      }));
    }
    let mut dp: Vec<Option<Choice>> = vec![None; cap + 1];
    dp[0] = Some((0, Vec::new()));
    for (_, by_size) in &results {
      let mut ndp: Vec<Option<Choice>> = vec![None; cap + 1];
      for c in 0..dp.len() {
        let Some((d, s)) = &dp[c] else { continue };
        for (k, opt) in by_size.iter().enumerate() {
          let Some((dk, sk)) = opt else { continue };
          if c + k > cap {
            continue;
          }
          let cand = (d + dk, merge_sorted(s, sk));
          if better(cand.0, &cand.1, ndp[c + k].as_ref()) {
            ndp[c + k] = Some(cand);
          }
        }
      }
      dp = ndp;
    }
    for (c, entry) in dp.iter().enumerate() {
      let Some((d, s)) = entry else { continue };
      let l = d + i128::from(tag0_len(k_cs + len_u64(c)));
      let l0 =
        chosen_delta + i128::from(tag0_len(k_cs + len_u64(chosen_x.len())));
      if l < l0 || (l == l0 && set_prec(s, &chosen_x)) {
        chosen_x = s.clone();
        chosen_delta = *d;
        lower_bracket = true;
      }
    }
  }
  // Model length from the truncated evaluation.
  let mut base_total = 0u128;
  for &r in dag.roots() {
    base_total = base_total.saturating_add(up.base[ix(r)].cost);
  }
  for &c in &cs {
    base_total = base_total.saturating_add(up.base[ix(c)].inl);
  }
  if base_total == u128::MAX {
    return Err(overflow());
  }
  let k = k_cs + len_u64(chosen_x.len());
  let model = to_i(base_total)? + chosen_delta + i128::from(tag0_len(k));
  let model = u64::try_from(model).map_err(|_e| overflow())?;
  if model == u64::MAX {
    return Err(overflow());
  }
  meter.output(model)?;
  // Materialize in the pinned order with the full evaluation and check.
  let stored = merge_sorted(&cs, &chosen_x);
  let order = pinned_order(dag, &facts.deg, &stored);
  if order.len() != stored.len() {
    return Err(internal("pinned order dropped a stored term"));
  }
  let mut index: Vec<Option<u64>> = vec![None; n];
  for (pos, &t) in order.iter().enumerate() {
    index[ix(t)] = Some(len_u64(pos));
  }
  let dict = UniformIndex { index, width: w };
  let own: Vec<Len> = nodes.iter().map(Node::own_len).collect();
  let mut work = 0u64;
  let costs = all_costs(nodes, &own, &dict, &mut work);
  let (entries, roots, predicted) = materialize_dependent(
    nodes,
    &own,
    &dict,
    &costs,
    &order,
    dag.roots(),
    &mut work,
  )?;
  meter.work(work)?;
  let predicted = predicted.plus_u64(tag0_len(k));
  if predicted != Len::new(model) {
    return Err(internal(format!(
      "uniform model length {model} differs from the full evaluation {predicted:?}"
    )));
  }
  let mut check_meter = Meter::new(meter.limits());
  let (check, entry_ids) =
    SharingDag::build_full(&roots, Some(&entries), &mut check_meter)?;
  if check != *dag {
    return Err(internal("materialized encoding changes the expanded AST"));
  }
  if entry_ids
    .iter()
    .map(|x| x.unwrap_or(TermId::MAX))
    .ne(order.iter().copied())
  {
    return Err(internal(
      "materialized entries do not expand to the stored terms",
    ));
  }
  let mut measured = tag0_len(k);
  for e in entries.iter().chain(&roots) {
    measured =
      expr_len(e).and_then(|l| measured.checked_add(l)).ok_or_else(overflow)?;
  }
  let base_len = all_costs(nodes, &own, &super::dict::NoWidths, &mut work);
  let mut unshared = Len::new(tag0_len(0));
  for &r in dag.roots() {
    unshared = unshared.plus(base_len[ix(r)]);
  }
  Ok(UniformSharingResult {
    roots,
    sharing: entries,
    table_terms: order,
    model_len: model,
    variable_len: measured,
    unshared_len: unshared.exact(),
    stored,
    certain_stored: cs,
    certain_excluded: ce_terms,
    uncertain: unc,
    low_degree: low,
    components: comps,
    states_visited,
    lower_bracket,
    stats: meter.stats.clone(),
  })
}

/// Experiment hook (not an optimizer): the uniform-`w` encoding of a given
/// stored set, materialized in the pinned order like the optimum. Every
/// stored term must have compact in-degree >= 2 or be referenced; the
/// classification fields of the result are empty.
pub(crate) fn uniform_with_stored_set(
  w: u64,
  dag: &SharingDag,
  stored: &[TermId],
  meter: &mut Meter<'_>,
) -> Result<UniformSharingResult, SharingError> {
  let nodes = dag.nodes();
  let n = nodes.len();
  let facts = graph_facts(dag);
  let len_u64 = |v: usize| u64::try_from(v).unwrap_or(u64::MAX);
  let order = pinned_order(dag, &facts.deg, stored);
  if order.len() != stored.len() {
    return Err(internal("pinned order dropped a stored term"));
  }
  let k = len_u64(order.len());
  let mut index: Vec<Option<u64>> = vec![None; n];
  for (pos, &t) in order.iter().enumerate() {
    index[ix(t)] = Some(len_u64(pos));
  }
  let dict = UniformIndex { index, width: w };
  let own: Vec<Len> = nodes.iter().map(Node::own_len).collect();
  let mut work = 0u64;
  let costs = all_costs(nodes, &own, &dict, &mut work);
  let (entries, roots, predicted) = materialize_dependent(
    nodes,
    &own,
    &dict,
    &costs,
    &order,
    dag.roots(),
    &mut work,
  )?;
  meter.work(work)?;
  let model = predicted.plus_u64(tag0_len(k)).exact().ok_or_else(overflow)?;
  meter.output(model)?;
  let mut check_meter = Meter::new(meter.limits());
  let (check, entry_ids) =
    SharingDag::build_full(&roots, Some(&entries), &mut check_meter)?;
  if check != *dag {
    return Err(internal("materialized encoding changes the expanded AST"));
  }
  if entry_ids
    .iter()
    .map(|x| x.unwrap_or(TermId::MAX))
    .ne(order.iter().copied())
  {
    return Err(internal(
      "materialized entries do not expand to the stored terms",
    ));
  }
  let mut measured = tag0_len(k);
  for e in entries.iter().chain(&roots) {
    measured =
      expr_len(e).and_then(|l| measured.checked_add(l)).ok_or_else(overflow)?;
  }
  let base_len = all_costs(nodes, &own, &super::dict::NoWidths, &mut work);
  let mut unshared = Len::new(tag0_len(0));
  for &r in dag.roots() {
    unshared = unshared.plus(base_len[ix(r)]);
  }
  let mut sorted = stored.to_vec();
  sorted.sort_unstable();
  Ok(UniformSharingResult {
    roots,
    sharing: entries,
    table_terms: order,
    model_len: model,
    variable_len: measured,
    unshared_len: unshared.exact(),
    stored: sorted,
    certain_stored: Vec::new(),
    certain_excluded: Vec::new(),
    uncertain: Vec::new(),
    low_degree: Vec::new(),
    components: Vec::new(),
    states_visited: 0,
    lower_bracket: false,
    stats: meter.stats.clone(),
  })
}

/// Exact uniform-width sharing of ordered, fully expanded roots.
pub fn optimize_sharing_uniform(
  w: u64,
  roots: &[Arc<Expr>],
  limits: &ExactSharingLimits,
) -> Result<UniformSharingResult, SharingError> {
  let mut meter = Meter::new(limits);
  let dag = SharingDag::build(roots, None, &mut meter)?;
  optimize_uniform(w, &dag, &mut meter)
}

/// [`optimize_sharing_uniform`] on an already built DAG.
pub fn optimize_dag_uniform(
  w: u64,
  dag: &SharingDag,
  limits: &ExactSharingLimits,
) -> Result<UniformSharingResult, SharingError> {
  optimize_uniform(w, dag, &mut Meter::new(limits))
}

/// Expand `c`'s table and re-share it with the uniform-width optimum.
pub fn normalize_constant_sharing_uniform(
  w: u64,
  c: &Constant,
  limits: &ExactSharingLimits,
) -> Result<(Constant, UniformSharingResult), SharingError> {
  let mut meter = Meter::new(limits);
  let roots = constant_info_root_exprs(&c.info);
  let dag = SharingDag::build(&roots, Some(&c.sharing), &mut meter)?;
  let fixed = constant_fixed_len(c).ok_or_else(overflow)?;
  let result = optimize_uniform(w, &dag, &mut meter)?;
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
    return Err(internal("uniform output length differs from its accounting"));
  }
  Ok((out, result))
}

#[cfg(test)]
mod count_bracket_tests {
  use super::{tag0_bracket_start, tag0_len, tag0_step_bound};
  use crate::tag::TagN;

  fn counts() -> Vec<u64> {
    let mut v = vec![0u64, 1, 2, 255, 256, u64::MAX - 1, u64::MAX];
    for e in [
      TagN::end1(0),
      TagN::end2(0),
      TagN::end3(0),
      TagN::end4(0),
      TagN::end5(0),
    ] {
      v.extend([e - 1, e, e + 1]);
    }
    v
  }

  /// Same checks as the Lean `widthTests` for `tag0BracketStart` and
  /// `tag0StepBound`.
  #[test]
  fn bracket_start_and_step_bound() {
    for k in counts() {
      let s = tag0_bracket_start(k);
      assert_eq!(tag0_len(s), tag0_len(k), "bracket start of {k}");
      assert!(s == 0 || tag0_len(s - 1) < tag0_len(k), "least start of {k}");
      if k > 0 {
        assert!(tag0_len(k) - tag0_len(k - 1) <= tag0_step_bound(k), "{k}");
      }
    }
    assert_eq!(tag0_step_bound(82048), 1);
    assert_eq!(tag0_step_bound(TagN::end5(0) - 1), 1);
    assert_eq!(tag0_step_bound(TagN::end5(0)), 4);
  }
}
