//! Exact minimum sharing under a uniform Share width.
//!
//! This is a byte-for-byte port of the Lean `Ix/Sharing/Exact/Uniform.lean`;
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
//! The component search is the reclassifying branch and bound of the Lean
//! implementation. At each node it (1) recomputes the bounds and visible
//! counts over the component's area with the members decided "not stored"
//! removed from `M`, and forces
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
//! The plain subset enumeration is kept as a test oracle
//! (`ExactSharingLimits::uniform_subset_search`); it is not on the compiler
//! path, and the Lean optimality theorems assume it is off.
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

use std::cell::RefCell;
use std::rc::Rc;
use std::sync::Arc;

use rustc_hash::FxHashMap;

use super::cost::{Len, exprs_len_with, tag0_len, tag4_len};
use super::dag::{Node, SharingDag, TermId, ix};
use super::dict::{
  DependentPlan, Evaluation, PlanShares, ReadEdges, UniformIndex, all_costs,
  build_dependent, decide_dependent,
};
use super::prof::{self, Phase};
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
pub(crate) enum UniformClass {
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

/// Bytes a non-telescope node writes itself, excluding its children, from
/// its `Node::own_len` `own`.
fn own_bytes(node: &Node, own: Len) -> Result<u128, SharingError> {
  match node.family() {
    Some(_) => Ok(0),
    None => own.exact().map(u).ok_or_else(overflow),
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
  /// Distinct parents of each term, ascending:
  /// `parents[parent_start[t]..parent_start[t + 1]]`.
  parent_start: Vec<usize>,
  parents: Vec<TermId>,
  /// Per entry of `parents`: the edges from that parent to the term, and
  /// how many of them are head edges (not continuing the parent's
  /// telescope).
  parent_edges: Vec<(u64, u64)>,
}

impl Facts {
  /// The distinct parents of `t`, ascending.
  #[inline]
  pub(crate) fn parents(&self, t: TermId) -> &[TermId] {
    &self.parents[self.parent_start[ix(t)]..self.parent_start[ix(t) + 1]]
  }

  /// The distinct parents of `t`, ascending, each with its edges to `t`
  /// and its head edges to `t`.
  #[inline]
  fn parent_edges(
    &self,
    t: TermId,
  ) -> impl Iterator<Item = (TermId, u64, u64)> + '_ {
    let r = self.parent_start[ix(t)]..self.parent_start[ix(t) + 1];
    self.parents[r.clone()]
      .iter()
      .zip(&self.parent_edges[r])
      .map(|(&q, &(ma, mh))| (q, ma, mh))
  }
}

pub(crate) fn graph_facts(dag: &SharingDag) -> Facts {
  let nodes = dag.nodes();
  let n = nodes.len();
  let mut deg = vec![0u64; n];
  for &r in dag.roots() {
    deg[ix(r)] += 1;
  }
  // The distinct children of a node: a child repeated in one node (the
  // only way a parent repeats, parents being added in increasing ID) is
  // listed once.
  let distinct = |kids: &[TermId], i: usize| !kids[..i].contains(&kids[i]);
  let mut parent_start = vec![0usize; n + 1];
  for node in nodes {
    let kids = node.children();
    let kids = kids.as_slice();
    for (i, &c) in kids.iter().enumerate() {
      deg[ix(c)] += 1;
      if distinct(kids, i) {
        parent_start[ix(c) + 1] += 1;
      }
    }
  }
  for i in 0..n {
    parent_start[i + 1] += parent_start[i];
  }
  let mut fill: Vec<usize> = parent_start[..n].to_vec();
  let mut parents: Vec<TermId> = vec![0; parent_start[n]];
  let mut parent_edges: Vec<(u64, u64)> = vec![(0, 0); parent_start[n]];
  for (t, node) in nodes.iter().enumerate() {
    let kids = node.children();
    let kids = kids.as_slice();
    for (i, &c) in kids.iter().enumerate() {
      if distinct(kids, i) {
        let (mut ma, mut mh) = (0u64, 0u64);
        for (k, &d) in kids.iter().enumerate() {
          if d == c {
            ma += 1;
            if !continuation_edge(node, k, &nodes[ix(c)]) {
              mh += 1;
            }
          }
        }
        parents[fill[ix(c)]] = tid(t);
        parent_edges[fill[ix(c)]] = (ma, mh);
        fill[ix(c)] += 1;
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
  Facts { deg, occ, parent_start, parents, parent_edges }
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
  /// `Node::own_len` of every term.
  own: &'d [Len],
  w: u128,
  opaq: Vec<bool>,
  t_len: Vec<u64>,
  t_tail: Vec<TermId>,
  base: Vec<UVal>,
}

impl<'d> UPrep<'d> {
  fn new(
    nodes: &'d [Node],
    own: &'d [Len],
    w: u128,
    opaq: Vec<bool>,
  ) -> Result<Self, SharingError> {
    let (t_len, t_tail) = spine_tables(nodes, &opaq);
    let mut up = UPrep { nodes, own, w, opaq, t_len, t_tail, base: Vec::new() };
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
  #[inline]
  fn node<G: Fn(TermId) -> UVal, A: Fn(TermId) -> bool>(
    &self,
    get: &G,
    avail: &A,
    t: TermId,
  ) -> Result<(UVal, u64), SharingError> {
    let node = &self.nodes[ix(t)];
    let mut steps = 0u64;
    let mut v = UVal::default();
    if node.family().is_none() {
      let mut inl = own_bytes(node, self.own[ix(t)])?;
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

/// Lower bounds of the certain-stored test (Lean `UBounds`): `inl`, bytes
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

/// One step of the bounds (Lean `boundsStep`): `[inl, merged, head_lb,
/// cont_lb]` of `t` from its children's head/continuation bounds; `own` is
/// `Node::own_len` of every term.
#[inline]
fn bound_step<H: Fn(TermId) -> u128, C: Fn(TermId) -> u128>(
  nodes: &[Node],
  own: &[Len],
  t: TermId,
  w: u128,
  maybe: bool,
  head: &H,
  cont: &C,
) -> Result<[u128; 4], SharingError> {
  let node = &nodes[ix(t)];
  let (i, m) = if node.family().is_none() {
    let mut i = own_bytes(node, own[ix(t)])?;
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
  own: &[Len],
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
      bound_step(nodes, own, tid(t), w, mb, &|c| hl[ix(c)], &|c| cl[ix(c)])?
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

/// Lean `propagateCounts`: per term, root occurrences plus, over the edges
/// from each parent `y` (descending IDs), `weight(y, count of y)`; the second
/// array counts only head (non-continuation) edges.
fn propagate_counts<F: Fn(usize, u64) -> u64>(
  dag: &SharingDag,
  weight: &F,
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

/// The certain-stored gain bound (Lean `storedGainC`) with `d` inline
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
  // The representatives of each term, `reps[start[t]..start[t + 1]]`: each
  // term's list is final once computed and is read only by its parents
  // (larger IDs), so the lists are appended to one buffer in ID order.
  let mut reps: Vec<usize> = Vec::new();
  let mut start: Vec<usize> = Vec::with_capacity(n + 1);
  start.push(0);
  let mut rs: Vec<usize> = Vec::new();
  for t in 0..n {
    if cls[t] == UniformClass::CertainStored {
      start.push(reps.len());
      continue;
    }
    rs.clear();
    for &c in nodes[t].children().as_slice() {
      for &r in &reps[start[ix(c)]..start[ix(c) + 1]] {
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
      reps.push(t);
    } else {
      reps.extend_from_slice(&rs);
    }
    start.push(reps.len());
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

/// Members and their ancestors, not continuing above an opaque term,
/// ascending. `pos` holds `NO_POS` for every term on entry; on return it
/// holds each area term's position in the area (it serves as the visited
/// set of the walk).
fn component_area(
  up: &UPrep<'_>,
  facts: &Facts,
  members: &[TermId],
  pos: &mut [u32],
) -> Vec<TermId> {
  // Any value but `NO_POS` marks a visited term during the walk.
  const SEEN: u32 = 0;
  let mut out: Vec<TermId> = Vec::with_capacity(members.len());
  for &t in members {
    if pos[ix(t)] == NO_POS {
      pos[ix(t)] = SEEN;
      out.push(t);
    }
  }
  let mut stack: Vec<TermId> = members.to_vec();
  while let Some(t) = stack.pop() {
    if up.opaq[ix(t)] {
      continue;
    }
    for &q in facts.parents(t) {
      if pos[ix(q)] == NO_POS {
        pos[ix(q)] = SEEN;
        out.push(q);
        stack.push(q);
      }
    }
  }
  out.sort_unstable();
  for (j, &t) in out.iter().enumerate() {
    pos[ix(t)] = u32::try_from(j).unwrap_or(NO_POS);
  }
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
// Reclassifying branch and bound with splitting (Lean `SCtx`)
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

// ---------------------------------------------------------------------------
// Table-count knapsack
// ---------------------------------------------------------------------------

/// "No element": the first difference of two equal sets.
const NO_DIFF: u32 = u32::MAX;

/// The least element of the symmetric difference of two ascending sets
/// (`NO_DIFF` if they are equal): at the first position where the lists
/// differ, the smaller element is in one set only.
fn first_diff(a: &[TermId], b: &[TermId]) -> u32 {
  let (mut i, mut j) = (0, 0);
  loop {
    match (a.get(i), b.get(j)) {
      (Some(x), Some(y)) if x == y => {
        i += 1;
        j += 1;
      },
      (Some(x), Some(y)) => return (*x).min(*y),
      (Some(x), None) => return *x,
      (None, Some(y)) => return *y,
      (None, None) => return NO_DIFF,
    }
  }
}

/// One layer of [`Knapsack`]: per cell (total count) the least delta, the
/// rank of the cell's set among the layer's sets (`set_prec` order), and a
/// sparse table over the first differences of rank-adjacent sets.
struct KnapsackLayer {
  delta: Vec<Option<i128>>,
  rank: Vec<u32>,
  /// `sparse[i][r]`: the least first difference among the rank-adjacent
  /// pairs `r .. r + 2^i`.
  sparse: Vec<Vec<u32>>,
}

impl KnapsackLayer {
  /// The least element of the symmetric difference of the sets of two
  /// distinct cells. For sets in ascending `set_prec` order (lexicographic
  /// on their indicator vectors), it is the least first difference of the
  /// rank-adjacent pairs between them, as for sorted strings.
  fn first_diff(&self, a: usize, b: usize) -> u32 {
    let (ra, rb) = (self.rank[a] as usize, self.rank[b] as usize);
    let (lo, hi) = if ra < rb { (ra, rb) } else { (rb, ra) };
    let level = (hi - lo).ilog2() as usize;
    self.sparse[level][lo].min(self.sparse[level][hi - (1 << level)])
  }
}

/// The table-count knapsack of [`optimize_uniform`] for total counts
/// `<= cap`: after the components `0..j`, every cell `c` holds the least
/// `(delta, set)` under [`better`] (delta, then `set_prec`) over the choices
/// of one entry per component table with counts summing to `c`. The sets of
/// distinct choices differ (the components are disjoint), so `better` is a
/// strict total order on them, and adding the same entry of a later
/// component preserves it; each cell is therefore the least combination of
/// the cells of the previous layer with the entries of the next table.
///
/// The sets themselves are not built. Comparing `S_a + X` with `S_b + Y`
/// (`S` from earlier components, `X`, `Y` entries of the next one) needs the
/// least element of the symmetric difference: the smaller of that of `S_a,
/// S_b` (from the previous layer's ranks) and that of `X, Y`; the set
/// without it precedes. `back` keeps the entry each cell took, to rebuild
/// the chosen set.
struct Knapsack {
  last: KnapsackLayer,
  /// Per component, per cell: the count of the entry taken (`u32::MAX`
  /// where the cell is empty).
  back: Vec<Vec<u32>>,
}

impl Knapsack {
  fn run(tables: &[&CTable], cap: usize) -> Knapsack {
    let mut layer = KnapsackLayer {
      delta: vec![None; cap + 1],
      rank: vec![0; cap + 1],
      sparse: Vec::new(),
    };
    layer.delta[0] = Some(0);
    let mut back: Vec<Vec<u32>> = Vec::with_capacity(tables.len());
    for tab in tables {
      let prev = &layer;
      // Whether choice `(a, ka)` precedes `(b, kb)` (distinct choices).
      let prec = |(a, ka): (usize, usize), (b, kb): (usize, usize)| {
        let old = if a == b { NO_DIFF } else { prev.first_diff(a, b) };
        let (xa, xb) = (&tab[ka], &tab[kb]);
        let new = match (xa, xb) {
          (Some((_, xa)), Some((_, xb))) if ka != kb => first_diff(xa, xb),
          _ => NO_DIFF,
        };
        if old < new {
          prev.rank[a] < prev.rank[b]
        } else {
          xa.as_ref().is_none_or(|(_, xa)| xa.binary_search(&new).is_err())
        }
      };
      let mut delta: Vec<Option<i128>> = vec![None; cap + 1];
      let mut choice: Vec<(usize, usize)> = vec![(0, 0); cap + 1];
      let mut took: Vec<u32> = vec![u32::MAX; cap + 1];
      for c in 0..=cap {
        let mut best: Option<(i128, usize, usize)> = None;
        for (k, entry) in tab.iter().enumerate().take(c + 1) {
          let Some((dk, _)) = entry else { continue };
          let a = c - k;
          let Some(da) = prev.delta[a] else { continue };
          let d = da + dk;
          if best.is_none_or(|(bd, ba, bk)| {
            d < bd || (d == bd && prec((a, k), (ba, bk)))
          }) {
            best = Some((d, a, k));
          }
        }
        if let Some((d, a, k)) = best {
          delta[c] = Some(d);
          choice[c] = (a, k);
          took[c] = u32::try_from(k).unwrap_or(u32::MAX);
        }
      }
      // Rank the new sets and record the first differences of neighbours.
      let mut order: Vec<usize> =
        (0..=cap).filter(|&c| delta[c].is_some()).collect();
      order.sort_by(|&u, &v| {
        if u == v {
          std::cmp::Ordering::Equal
        } else if prec(choice[u], choice[v]) {
          std::cmp::Ordering::Less
        } else {
          std::cmp::Ordering::Greater
        }
      });
      let mut rank = vec![0u32; cap + 1];
      for (r, &c) in order.iter().enumerate() {
        rank[c] = u32::try_from(r).unwrap_or(u32::MAX);
      }
      let adjacent: Vec<u32> = order
        .windows(2)
        .map(|w| {
          let ((a, ka), (b, kb)) = (choice[w[0]], choice[w[1]]);
          let old = if a == b { NO_DIFF } else { prev.first_diff(a, b) };
          let new = match (&tab[ka], &tab[kb]) {
            (Some((_, xa)), Some((_, xb))) if ka != kb => first_diff(xa, xb),
            _ => NO_DIFF,
          };
          old.min(new)
        })
        .collect();
      let mut sparse = vec![adjacent];
      let mut width = 1;
      loop {
        let below = &sparse[sparse.len() - 1];
        if below.len() <= width {
          break;
        }
        let next: Vec<u32> = (0..below.len() - width)
          .map(|r| below[r].min(below[r + width]))
          .collect();
        sparse.push(next);
        width *= 2;
      }
      layer = KnapsackLayer { delta, rank, sparse };
      back.push(took);
    }
    Knapsack { last: layer, back }
  }

  /// The set of cell `c` of the last layer, ascending.
  fn set(&self, tables: &[&CTable], mut c: usize) -> Vec<TermId> {
    let mut out: Vec<TermId> = Vec::new();
    for (tab, took) in tables.iter().zip(&self.back).rev() {
      let k = usize::try_from(took[c]).unwrap_or(0);
      if let Some(Some((_, s))) = tab.get(k) {
        out.extend_from_slice(s);
      }
      c -= k;
    }
    out.sort_unstable();
    out
  }
}

/// The knapsack as a plain dynamic program over explicit sets (the
/// reference of [`Knapsack`]).
#[cfg(test)]
fn knapsack_reference(tables: &[&CTable], cap: usize) -> Vec<Option<Choice>> {
  let mut dp: Vec<Option<Choice>> = vec![None; cap + 1];
  dp[0] = Some((0, Vec::new()));
  for by_size in tables {
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
  dp
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

/// Area position of no term (`SCtx::pos`).
const NO_POS: u32 = u32::MAX;

/// Spare buffers of the component searches, reused across the calls of the
/// branch and bound and across components instead of allocated per call.
/// Buffers are lent as [`Buf`]s, which come back when dropped.
#[derive(Default)]
struct Pool {
  flags: RefCell<Vec<Vec<bool>>>,
  vals: RefCell<Vec<Vec<[u128; 4]>>>,
  vis: RefCell<Vec<Vec<(u64, u64)>>>,
  uvals: RefCell<Vec<Vec<UVal>>>,
  positions: RefCell<Vec<Vec<u32>>>,
  counts: RefCell<Vec<Vec<u64>>>,
  /// The memo of a component search, emptied after each component.
  memo: RefCell<FxHashMap<Vec<u64>, Rc<CTable>>>,
  /// Scratch of `SCtx::groups` and `SCtx::memo_walk`, which do not recurse.
  walk: RefCell<WalkScratch>,
}

#[derive(Default)]
struct WalkScratch {
  uf: Vec<usize>,
  reps: Vec<usize>,
  start: Vec<usize>,
  rs: Vec<usize>,
  slot: Vec<usize>,
  stack: Vec<TermId>,
  down: Vec<TermId>,
  entries: Vec<u64>,
}

/// A buffer lent by a [`Pool`]; it goes back to the pool when dropped.
struct Buf<'p, T> {
  v: Vec<T>,
  home: &'p RefCell<Vec<Vec<T>>>,
}

impl<'p, T: Clone> Buf<'p, T> {
  /// A buffer of `len` copies of `x`.
  fn filled(home: &'p RefCell<Vec<Vec<T>>>, len: usize, x: T) -> Self {
    let mut v = home.borrow_mut().pop().unwrap_or_default();
    v.clear();
    v.resize(len, x);
    Buf { v, home }
  }
}

impl<T> Drop for Buf<'_, T> {
  fn drop(&mut self) {
    self.home.borrow_mut().push(std::mem::take(&mut self.v));
  }
}

impl<T> std::ops::Deref for Buf<'_, T> {
  type Target = Vec<T>;
  fn deref(&self) -> &Vec<T> {
    &self.v
  }
}

impl<T> std::ops::DerefMut for Buf<'_, T> {
  fn deref_mut(&mut self) -> &mut Vec<T> {
    &mut self.v
  }
}

/// Bounds of the area under a maybe-stored predicate, over the root-level
/// bounds (Lean `SCtx.rebound`): `vals[j]` for the area term at position
/// `j`, the root-level bounds elsewhere.
struct Overlay<'b> {
  base: &'b Bounds,
  pos: &'b [u32],
  vals: Buf<'b, [u128; 4]>,
}

impl Overlay<'_> {
  fn get(&self, t: TermId) -> [u128; 4] {
    match self.pos[ix(t)] {
      NO_POS => {
        let k = ix(t);
        [
          self.base.inl[k],
          self.base.merged[k],
          self.base.head_lb[k],
          self.base.cont_lb[k],
        ]
      },
      j => self.vals[j as usize],
    }
  }

  /// `get(t)[2]`, the head bound.
  #[inline]
  fn head(&self, t: TermId) -> u128 {
    match self.pos[ix(t)] {
      NO_POS => self.base.head_lb[ix(t)],
      j => self.vals[j as usize][2],
    }
  }

  /// `get(t)[3]`, the continuation bound.
  #[inline]
  fn cont(&self, t: TermId) -> u128 {
    match self.pos[ix(t)] {
      NO_POS => self.base.cont_lb[ix(t)],
      j => self.vals[j as usize][3],
    }
  }
}

/// What a `node` call takes from its caller instead of computing it: the
/// bounds (`SCtx::rebound`) and visible counts (`SCtx::revisible`) of its
/// "not stored" set, when the caller has them for the same set (both are
/// functions of that set alone), and an evaluation of `phi` the caller made
/// (`Eval`), which the call's own `phi` takes when its availability flags
/// are the same.
struct Known<'b> {
  bounds: Option<Overlay<'b>>,
  vis: Option<Buf<'b, (u64, u64)>>,
  eval: Option<Eval<'b>>,
}

impl Known<'_> {
  fn none() -> Self {
    Known { bounds: None, vis: None, eval: None }
  }
}

/// One evaluation of `SCtx::phi`: the value of each area term, the
/// availability flags it was made for, and its work.
struct Eval<'b> {
  vals: Buf<'b, UVal>,
  avail: Buf<'b, bool>,
  work: u64,
}

/// The search of one component (Lean `SCtx`). Sets of decided members are
/// passed as sorted term lists and, inside one call, as flags over the area
/// positions (every member is in the area; a term outside the area is in
/// none of them).
struct SCtx<'a, 'd> {
  up: &'a UPrep<'d>,
  facts: &'a Facts,
  cand: &'a [bool],
  b0: &'a Bounds,
  vis0: &'a (Vec<u64>, Vec<u64>),
  spine_len: &'a [u64],
  dag_size: u64,
  members: &'a [TermId],
  /// Member index of each area position (`NO_POS` for other terms).
  member_of: Buf<'a, u32>,
  area: &'a [TermId],
  /// Area position of every term of the DAG (`NO_POS` outside the area).
  pos: &'a [u32],
  /// Root occurrences of each area term (by area position).
  root_occ: Buf<'a, u64>,
  root_mult: Vec<(TermId, u128)>,
  stored_in: Vec<TermId>,
  slack: i128,
  theta: i128,
  memo: FxHashMap<Vec<u64>, Rc<CTable>>,
  memo_hits: u64,
  /// Scratch of `phi`: the value of each area term.
  vals: Buf<'a, UVal>,
  /// The availability flags `vals` were last evaluated for, with the work
  /// of that evaluation, while `vals_valid`.
  vals_for: Buf<'a, bool>,
  vals_work: u64,
  vals_valid: bool,
  pool: &'a Pool,
}

impl<'a> SCtx<'a, '_> {
  fn at(&self, t: TermId) -> Option<usize> {
    match self.pos[ix(t)] {
      NO_POS => None,
      j => Some(j as usize),
    }
  }

  /// Flags over the area positions of the terms `ts`.
  fn flags(&self, ts: &[TermId]) -> Buf<'a, bool> {
    let mut f = Buf::filled(&self.pool.flags, self.area.len(), false);
    for &t in ts {
      if let Some(j) = self.at(t) {
        f[j] = true;
      }
    }
    f
  }

  /// The component cost with the area terms flagged in `avail` available
  /// and the entries of `stored`, and the evaluation work (Lean
  /// `SCtx.phi`). Every area term is evaluated, children first; other terms
  /// keep their root-level values.
  ///
  /// The evaluation and its work depend on `avail` alone (`stored` only
  /// selects the entries summed), so when `avail` equals the flags of the
  /// last evaluation, its values and work are taken as they are (the
  /// "stored" child of a branch evaluates the same flags as its parent).
  fn phi(
    &mut self,
    avail: &[bool],
    stored: &[TermId],
  ) -> Result<(u128, u64), SharingError> {
    let work = if self.vals_valid && self.vals_for[..] == *avail {
      self.vals_work
    } else {
      self.vals_valid = false;
      let mut work = 0u64;
      for k in 0..self.area.len() {
        let t = self.area[k];
        let (v, s) = {
          let (vals, base, pos) = (&self.vals, &self.up.base, self.pos);
          let get = |c: TermId| match pos[ix(c)] {
            NO_POS => base[ix(c)],
            j => vals[j as usize],
          };
          let av = |c: TermId| match pos[ix(c)] {
            NO_POS => false,
            j => avail[j as usize],
          };
          self.up.node(&get, &av, t)?
        };
        self.vals[k] = v;
        work = work.saturating_add(1 + s);
      }
      self.vals_for.clear();
      self.vals_for.extend_from_slice(avail);
      self.vals_work = work;
      self.vals_valid = true;
      work
    };
    let get = |c: TermId| match self.pos[ix(c)] {
      NO_POS => self.up.base[ix(c)],
      j => self.vals[j as usize],
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

  /// The last evaluation of `phi`, set aside (the next `phi` evaluates into
  /// other buffers).
  fn take_eval(&mut self) -> Option<Eval<'a>> {
    if !self.vals_valid {
      return None;
    }
    self.vals_valid = false;
    let vals = Buf::filled(&self.pool.uvals, self.area.len(), UVal::default());
    let avail = Buf::filled(&self.pool.flags, 0, false);
    Some(Eval {
      vals: std::mem::replace(&mut self.vals, vals),
      avail: std::mem::replace(&mut self.vals_for, avail),
      work: self.vals_work,
    })
  }

  /// Make `e` the last evaluation of `phi`.
  fn put_eval(&mut self, e: Eval<'a>) {
    self.vals = e.vals;
    self.vals_for = e.avail;
    self.vals_work = e.work;
    self.vals_valid = true;
  }

  fn charge(meter: &mut Meter<'_>, work: u64) -> Result<(), SharingError> {
    meter.state()?;
    meter.work(work)
  }

  /// Whether `t` may be stored: a candidate not decided "not stored".
  fn maybe(&self, out: &[bool], t: TermId) -> bool {
    self.cand[ix(t)] && self.at(t).is_none_or(|j| !out[j])
  }

  fn rebound(&self, out: &[bool]) -> Result<Overlay<'a>, SharingError> {
    let mut vals = Buf::filled(&self.pool.vals, 0, [0; 4]);
    vals.reserve(self.area.len());
    let mut ov = Overlay { base: self.b0, pos: self.pos, vals };
    for (j, &t) in self.area.iter().enumerate() {
      let v = {
        let ovr = &ov;
        bound_step(
          self.up.nodes,
          self.up.own,
          t,
          self.up.w,
          self.cand[ix(t)] && !out[j],
          &|c| ovr.head(c),
          &|c| ovr.cont(c),
        )?
      };
      ov.vals.push(v);
    }
    Ok(ov)
  }

  /// Visible counts of the area terms (by area position).
  fn revisible(&self, out: &[bool]) -> Buf<'a, (u64, u64)> {
    let mut vis = Buf::filled(&self.pool.vis, self.area.len(), (0, 0));
    for j in (0..self.area.len()).rev() {
      let r = self.root_occ[j];
      let (mut d, mut h) = (r, r);
      for (q, ma, mh) in self.facts.parent_edges(self.area[j]) {
        let wq = if self.maybe(out, q) {
          1
        } else {
          match self.pos[ix(q)] {
            NO_POS => self.vis0.0[ix(q)],
            qj => vis[qj as usize].0,
          }
          .min(VISIBLE_CAP)
        };
        d = d.saturating_add(ma.saturating_mul(wq));
        h = h.saturating_add(mh.saturating_mul(wq));
      }
      vis[j] = (d, h);
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

  /// Groups of the undecided members (Lean `SCtx.groups`); `opq` and
  /// `avail_fixed` are flags over the area positions.
  fn groups(
    &self,
    opq: &[bool],
    avail_fixed: &[bool],
    und: &[TermId],
  ) -> Vec<Vec<TermId>> {
    let und_f = self.flags(und);
    let mut ws = self.pool.walk.borrow_mut();
    let WalkScratch { uf, reps, start, rs, slot, .. } = &mut *ws;
    uf.clear();
    uf.extend(0..self.members.len());
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
    let member = |j: usize| match self.member_of[j] {
      NO_POS => 0,
      m => m as usize,
    };
    // The representatives of area position `j` are
    // `reps[start[j]..start[j + 1]]`, appended in position order: a list is
    // final once computed and is read only by parents (later positions).
    reps.clear();
    start.clear();
    start.push(0);
    for j in 0..self.area.len() {
      let y = self.area[j];
      if opq[j] {
        start.push(reps.len());
        continue;
      }
      rs.clear();
      for &c in self.up.nodes[ix(y)].children().as_slice() {
        if let Some(jc) = self.at(c) {
          for &r in &reps[start[jc]..start[jc + 1]] {
            let fr = uf_find(&uf[..], r);
            if !rs.contains(&fr) {
              rs.push(fr);
            }
          }
        }
      }
      if und_f[j] {
        let iy = member(j);
        for &r in rs.iter() {
          union(uf, iy, r);
        }
        reps.push(uf_find(&uf[..], iy));
      } else if avail_fixed[j] && rs.len() > 1 {
        let r0 = rs[0];
        for &r in rs.iter() {
          union(uf, r0, r);
        }
        reps.push(uf_find(&uf[..], r0));
      } else {
        reps.extend_from_slice(rs);
      }
      start.push(reps.len());
    }
    // One group per root, in order of first occurrence in `und`.
    slot.clear();
    slot.resize(self.members.len(), usize::MAX);
    let mut gs: Vec<Vec<TermId>> = Vec::new();
    for &t in und {
      let r = uf_find(&uf[..], self.at(t).map_or(0, member));
      if slot[r] == usize::MAX {
        slot[r] = gs.len();
        gs.push(Vec::new());
      }
      gs[slot[r]].push(t);
    }
    for g in &mut gs {
      g.sort_unstable();
    }
    gs.sort_by_key(|g| g[0]);
    gs
  }

  /// The walk of `memo_key` (Lean `SCtx.memoKey`) from group `g`: the
  /// decided members that reach it, as flags over the area positions, and,
  /// with `entries`, their key codes (unsorted). `opq`, `in_f` and `out` are
  /// flags over the area positions.
  fn memo_walk(
    &self,
    opq: &[bool],
    in_f: &[bool],
    out: &[bool],
    g: &[TermId],
    mut entries: Option<&mut Vec<u64>>,
  ) -> Buf<'a, bool> {
    let code =
      |q: TermId, j: usize| u64::from(q) * 3 + if opq[j] { 2 } else { 1 };
    let mut rel = self.flags(&[]);
    let mut seen = self.flags(g);
    let mut ws = self.pool.walk.borrow_mut();
    let WalkScratch { stack, down: down_start, .. } = &mut *ws;
    down_start.clear();
    down_start.extend_from_slice(g);
    stack.clear();
    stack.extend_from_slice(g);
    while let Some(y) = stack.pop() {
      for &q in self.facts.parents(y) {
        let Some(j) = self.at(q) else { continue };
        if seen[j] {
          continue;
        }
        seen[j] = true;
        if out[j] {
          if let Some(e) = entries.as_deref_mut() {
            e.push(u64::from(q) * 3);
          }
          rel[j] = true;
        } else if in_f[j] {
          if let Some(e) = entries.as_deref_mut() {
            e.push(code(q, j));
          }
          rel[j] = true;
          if !opq[j] {
            down_start.push(q);
          }
        }
        if !opq[j] {
          stack.push(q);
        }
      }
    }
    seen.fill(false);
    for &t in down_start.iter() {
      if let Some(j) = self.at(t) {
        seen[j] = true;
      }
    }
    // The second walk starts from `down_start`, in its order.
    std::mem::swap(stack, down_start);
    while let Some(y) = stack.pop() {
      for &c in self.up.nodes[ix(y)].children().as_slice() {
        let Some(j) = self.at(c) else { continue };
        if seen[j] {
          continue;
        }
        seen[j] = true;
        if !rel[j] {
          if out[j] {
            if let Some(e) = entries.as_deref_mut() {
              e.push(u64::from(c) * 3);
            }
            rel[j] = true;
          } else if in_f[j] {
            if let Some(e) = entries.as_deref_mut() {
              e.push(code(c, j));
            }
            rel[j] = true;
          }
        }
        if !opq[j] {
          stack.push(c);
        }
      }
    }
    rel
  }

  /// Memo key of a group and the decided members that reach it (Lean
  /// `SCtx.memoKey`). `opq`, `in_f` and `out` are flags over the area
  /// positions.
  fn memo_key(
    &self,
    opq: &[bool],
    in_f: &[bool],
    out: &[bool],
    g: &[TermId],
  ) -> Vec<u64> {
    let mut entries = std::mem::take(&mut self.pool.walk.borrow_mut().entries);
    entries.clear();
    drop(self.memo_walk(opq, in_f, out, g, Some(&mut entries)));
    entries.sort_unstable();
    let mut key: Vec<u64> = Vec::with_capacity(g.len() + 1 + entries.len());
    key.extend(g.iter().map(|&t| u64::from(t)));
    key.push(3 * self.dag_size + 3);
    key.extend_from_slice(&entries);
    self.pool.walk.borrow_mut().entries = entries;
    key
  }

  /// Exact table of a group under the decided members outside it (Lean
  /// `SCtx.solve`). `phi_in` is `phi` with the area terms of `in_all`
  /// available and the entries of `in_all`, when the caller has it.
  fn solve(
    &mut self,
    meter: &mut Meter<'_>,
    g: &[TermId],
    in_all: &[TermId],
    out_all: &[TermId],
    phi_in: Option<(u128, u64)>,
  ) -> Result<Rc<CTable>, SharingError> {
    let out = self.flags(out_all);
    let in_f = self.flags(in_all);
    let b = self.rebound(&out)?;
    let key = {
      let mut opq = self.flags(&[]);
      for (j, &t) in self.area.iter().enumerate() {
        opq[j] = self.up.opaq[ix(t)] || (in_f[j] && self.opaque_under(&b, t));
      }
      self.memo_key(&opq, &in_f, &out, g)
    };
    drop(out);
    if let Some(tb) = self.memo.get(&key) {
      let tb = Rc::clone(tb);
      self.memo_hits += 1;
      return Ok(tb);
    }
    let (phi0, work) = match phi_in {
      Some(p) => p,
      None => self.phi(&in_f, in_all)?,
    };
    drop(in_f);
    Self::charge(meter, work.saturating_add(len64(self.area.len())))?;
    // `node` decides "not stored" exactly `out_all`, whose bounds are `b`.
    let tb = self.node(
      meter,
      phi0,
      in_all,
      out_all.to_vec(),
      out_all.len(),
      Vec::new(),
      g,
      Vec::new(),
      Known { bounds: Some(b), vis: None, eval: None },
    )?;
    let tb = Rc::new(table_trim(tb, self.slack));
    self.memo.insert(key, Rc::clone(&tb));
    Ok(tb)
  }

  /// Branch-and-bound node of a group (Lean `SCtx.node`). `known` holds
  /// what the caller already computed for the "not stored" set `out_all`.
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
    known: Known<'a>,
  ) -> Result<CTable, SharingError> {
    let out = self.flags(&out_all);
    let Known { bounds, vis, eval } = known;
    if let Some(e) = eval {
      self.put_eval(e);
    }
    // Reclassify.
    let b = match bounds {
      Some(b) => b,
      None => self.rebound(&out)?,
    };
    let vis = match vis {
      Some(v) => v,
      None => self.revisible(&out),
    };
    let mut gains: Vec<(TermId, i128)> = Vec::with_capacity(und.len());
    for &t in und {
      let (d, h) =
        self.at(t).map_or((self.vis0.0[ix(t)], self.vis0.1[ix(t)]), |j| vis[j]);
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
    let mut opaque_in = self.flags(&[]);
    for &t in in_ctx
      .iter()
      .chain(&local_in)
      .chain(gains.iter().filter(|(_, g)| *g >= self.theta).map(|(t, _)| t))
    {
      if self.opaque_under(&b, t)
        && let Some(j) = self.at(t)
      {
        opaque_in[j] = true;
      }
    }
    let mut known = Known { bounds: Some(b), vis: Some(vis), eval: None };
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
    let in_f = self.flags(&in_all);
    // Lower bound: every undecided member available, its entry free.
    let mut in_und = self.flags(&und);
    for (a, &b) in in_und.iter_mut().zip(in_f.iter()) {
      *a |= b;
    }
    let (phi, work) = self.phi(&in_und, &in_all)?;
    drop(in_und);
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
    let mut opq = self.flags(&[]);
    let mut avail_fixed = self.flags(&[]);
    for (j, &t) in self.area.iter().enumerate() {
      opq[j] = self.up.opaq[ix(t)] || (in_f[j] && opaque_in[j]);
      avail_fixed[j] = in_f[j] && !opq[j];
    }
    drop(opaque_in);
    let groups = self.groups(&opq, &avail_fixed, &und);
    drop(avail_fixed);
    let route = if groups.len() > 1 {
      true
    } else if groups.len() == 1 {
      let rel = self.memo_walk(&opq, &in_f, &out, &groups[0], None);
      let related = |t: &TermId| self.at(*t).is_some_and(|j| rel[j]);
      local_in.iter().any(|t| !related(t))
        || out_all[n_out_ctx..].iter().any(|t| !related(t))
    } else {
      false
    };
    drop(opq);
    drop(out);
    if route {
      drop(known);
      let (phi_none, work) = self.phi(&in_f, &in_all)?;
      drop(in_f);
      Self::charge(meter, work)?;
      let base = to_i(phi_none)? - to_i(phi0)?;
      let mut comb: CTable = vec![Some((base, local_in.clone()))];
      // Each group's `solve` evaluates `phi` with exactly `in_all`
      // available and stored: `phi_none`, with its work.
      for grp in &groups {
        let sub =
          self.solve(meter, grp, &in_all, &out_all, Some((phi_none, work)))?;
        comb = table_trim(table_conv(&comb, &sub), self.slack);
      }
      for e in comb.into_iter().flatten() {
        table_add(&mut tb, e);
      }
      return Ok(tb);
    }
    drop(in_f);
    // Branch on the largest |gain|, "stored" first when it is positive. The
    // "stored" child decides "not stored" the same set, `out_all`, and takes
    // its bounds and visible counts; its lower bound evaluates `phi` with
    // the same availability (`t` moves from undecided to stored), so it
    // also takes this node's evaluation: directly when it runs first,
    // set aside from the other child otherwise.
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
      let tb = self.node(
        meter, phi0, in_ctx, out_all, n_out_ctx, with_t, &und2, tb, known,
      )?;
      self.node(
        meter,
        phi0,
        in_ctx,
        out_t,
        n_out_ctx,
        local_in,
        &und2,
        tb,
        Known::none(),
      )
    } else {
      known.eval = self.take_eval();
      let tb = self.node(
        meter,
        phi0,
        in_ctx,
        out_t,
        n_out_ctx,
        local_in.clone(),
        &und2,
        tb,
        Known::none(),
      )?;
      self
        .node(meter, phi0, in_ctx, out_all, n_out_ctx, with_t, &und2, tb, known)
    }
  }
}

// ---------------------------------------------------------------------------
// Order and driver
// ---------------------------------------------------------------------------

/// Bound on telescope spine lengths (Lean `teleSubaddEnd = Ixon.tagNEnd5 4`,
/// 4,311,811,080): below it the TagN Share-flag width is subadditive
/// (`tag4_len(a + b) <= tag4_len(a) + tag4_len(b)`), which the certain-excluded
/// class relies on when two telescopes merge.
pub(crate) const TELE_SUBADD_END: u64 = TagN::end5(4);

/// Whether every telescope spine length is below [`TELE_SUBADD_END`].
pub(crate) fn spines_within_bound(spine_len: &[u64]) -> bool {
  spine_len.iter().all(|&l| l < TELE_SUBADD_END)
}

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

/// The nearest stored descendants of every term of a stored set: the stored
/// terms reachable from its children through unstored terms, as positions
/// in the stored list, `succ[start[k]..start[k + 1]]` for its `k`-th term
/// (in the order a depth-first walk finds them).
///
/// A DAG path between two stored terms is a sequence of such steps, so the
/// relation decides every question about stored descendants within the
/// set: closure of an order ([`NearestStored::closed_under`]) and the
/// pinned order of a subset ([`pinned_suborder`]).
#[derive(Default)]
pub(crate) struct NearestStored {
  start: Vec<usize>,
  succ: Vec<u32>,
}

impl NearestStored {
  /// The relation of `stored` (any order, no repetition) in `dag`.
  pub(crate) fn new(dag: &SharingDag, stored: &[TermId]) -> Self {
    let nodes = dag.nodes();
    // `slot[x]`: the position of `x` in `stored` plus one (0: not stored).
    let mut slot: Vec<u32> = vec![0; nodes.len()];
    for (k, &t) in stored.iter().enumerate() {
      slot[ix(t)] = u32::try_from(k + 1).unwrap_or(u32::MAX);
    }
    // `seen[x] == k + 1`: visited from the `k`-th stored term.
    let mut seen: Vec<u32> = vec![0; nodes.len()];
    let mut start: Vec<usize> = Vec::with_capacity(stored.len() + 1);
    start.push(0);
    let mut succ: Vec<u32> = Vec::new();
    let mut stack: Vec<TermId> = Vec::new();
    for (k, &t) in stored.iter().enumerate() {
      let mark = u32::try_from(k + 1).unwrap_or(u32::MAX);
      stack.clear();
      stack.extend_from_slice(nodes[ix(t)].children().as_slice());
      while let Some(x) = stack.pop() {
        if seen[ix(x)] == mark {
          continue;
        }
        seen[ix(x)] = mark;
        match slot[ix(x)] {
          0 => stack.extend_from_slice(nodes[ix(x)].children().as_slice()),
          s => succ.push(s - 1),
        }
      }
      start.push(succ.len());
    }
    NearestStored { start, succ }
  }

  /// The nearest stored descendants of the `k`-th stored term.
  fn succ(&self, k: usize) -> &[u32] {
    &self.succ[self.start[k]..self.start[k + 1]]
  }

  /// Whether an order of the stored terms (`pos[k]`: the position of the
  /// `k`-th stored term) puts every stored term after all its stored
  /// descendants. After its nearest ones suffices: along the steps of a
  /// path to any stored descendant the positions then decrease.
  pub(crate) fn closed_under(&self, pos: &[u32]) -> bool {
    (0..pos.len())
      .all(|k| self.succ(k).iter().all(|&x| pos[x as usize] < pos[k]))
  }
}

/// The pinned order of `ids` (in-degree `deg`) given the nearest stored
/// descendants `near` among them (positions in `ids`): stored descendants
/// first; among ready terms the larger in-degree first, then the smaller ID.
/// Returns positions in `ids`.
fn heap_order(near: &NearestStored, ids: &[TermId], deg: &[u64]) -> Vec<u32> {
  let m = ids.len();
  let mut pending: Vec<usize> = (0..m).map(|k| near.succ(k).len()).collect();
  // The dependents of each term (the reverse relation), grouped by term.
  let mut dstart = vec![0usize; m + 1];
  for &x in &near.succ {
    dstart[x as usize + 1] += 1;
  }
  for i in 0..m {
    dstart[i + 1] += dstart[i];
  }
  let mut fill: Vec<usize> = dstart[..m].to_vec();
  let mut dependents: Vec<u32> = vec![0; near.succ.len()];
  for k in 0..m {
    for &x in near.succ(k) {
      dependents[fill[x as usize]] = u32::try_from(k).unwrap_or(u32::MAX);
      fill[x as usize] += 1;
    }
  }
  // The position breaks no tie: the term IDs are distinct.
  let mut heap: std::collections::BinaryHeap<(
    u64,
    std::cmp::Reverse<TermId>,
    u32,
  )> = std::collections::BinaryHeap::new();
  let entry = |k: usize| {
    (deg[ix(ids[k])], std::cmp::Reverse(ids[k]), u32::try_from(k).unwrap_or(0))
  };
  for (k, &p) in pending.iter().enumerate() {
    if p == 0 {
      heap.push(entry(k));
    }
  }
  let mut order = Vec::with_capacity(m);
  while let Some((_, _, k)) = heap.pop() {
    order.push(k);
    let k = k as usize;
    for &d in &dependents[dstart[k]..dstart[k + 1]] {
      let d = d as usize;
      pending[d] -= 1;
      if pending[d] == 0 {
        heap.push(entry(d));
      }
    }
  }
  order
}

/// Pinned table order of a stored set: stored descendants first; among
/// ready terms the larger in-degree first, then the smaller ID.
pub(crate) fn pinned_order(
  dag: &SharingDag,
  deg: &[u64],
  stored: &[TermId],
) -> Vec<TermId> {
  let near = NearestStored::new(dag, stored);
  heap_order(&near, stored, deg)
    .into_iter()
    .map(|k| stored[k as usize])
    .collect()
}

/// [`pinned_order`] of the subset `sub` (positions in `stored`, no
/// repetition) of the stored set of `near`, from `near` alone: a term of
/// `sub` is a nearest `sub`-descendant of another exactly when the walk of
/// nearest-stored steps through terms outside `sub` reaches it (a DAG path
/// between two stored terms is a sequence of such steps, and the path avoids
/// `sub` between its ends exactly when its intermediate stored terms do).
/// Returns positions in `stored`.
pub(crate) fn pinned_suborder(
  near: &NearestStored,
  stored: &[TermId],
  deg: &[u64],
  sub: &[u32],
) -> Vec<u32> {
  // `slot[k]`: the position of the `k`-th stored term in `sub` plus one.
  let mut slot: Vec<u32> = vec![0; stored.len()];
  for (i, &k) in sub.iter().enumerate() {
    slot[k as usize] = u32::try_from(i + 1).unwrap_or(u32::MAX);
  }
  let mut seen: Vec<u32> = vec![0; stored.len()];
  let mut start: Vec<usize> = Vec::with_capacity(sub.len() + 1);
  start.push(0);
  let mut succ: Vec<u32> = Vec::new();
  let mut stack: Vec<u32> = Vec::new();
  for (i, &k) in sub.iter().enumerate() {
    let mark = u32::try_from(i + 1).unwrap_or(u32::MAX);
    stack.clear();
    stack.extend_from_slice(near.succ(k as usize));
    while let Some(x) = stack.pop() {
      if seen[x as usize] == mark {
        continue;
      }
      seen[x as usize] = mark;
      match slot[x as usize] {
        0 => stack.extend_from_slice(near.succ(x as usize)),
        s => succ.push(s - 1),
      }
    }
    start.push(succ.len());
  }
  let ids: Vec<TermId> = sub.iter().map(|&k| stored[k as usize]).collect();
  heap_order(&NearestStored { start, succ }, &ids, deg)
    .into_iter()
    .map(|i| sub[i as usize])
    .collect()
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
  let (mut result, plan) =
    optimize_uniform_with(w, dag, &DagPrep::new(dag), meter)?;
  let built = plan.build(dag, &result.table_terms, meter.limits())?;
  result.roots = built.roots;
  result.sharing = built.entries;
  result.variable_len = built.measured;
  Ok(result)
}

/// The tables of one DAG that do not depend on the uniform width, computed
/// once and shared by the candidates of the tiered construction. Each is
/// exactly what `optimize_uniform` and `tiered_at` computed for themselves.
pub(crate) struct DagPrep {
  /// `Node::own_len` of every term.
  pub(crate) own: Vec<Len>,
  /// `C_0` (`all_costs` with no dictionary), with each term's work.
  pub(crate) base: Evaluation,
  /// The parent edges and what each parent reads (phase 3).
  pub(crate) edges: ReadEdges,
  pub(crate) facts: Facts,
  /// Spine lengths with no stop terms.
  spine_len: Vec<u64>,
  /// Unshared sizes of the uniform model (the empty evaluation; it does not
  /// read the width), or its overflow error.
  size: Result<Vec<u128>, SharingError>,
  /// Terms with in-degree >= 2 and unshared length >= 2 (`TieredStats::
  /// candidate_count`).
  pub(crate) candidate_count: u64,
}

impl DagPrep {
  pub(crate) fn new(dag: &SharingDag) -> Self {
    let nodes = dag.nodes();
    let n = nodes.len();
    let own: Vec<Len> = nodes.iter().map(Node::own_len).collect();
    let base = Evaluation::new(nodes, &own, &super::dict::NoWidths);
    let edges = ReadEdges::new(nodes);
    let facts = graph_facts(dag);
    let (spine_len, _) = spine_tables(nodes, &vec![false; n]);
    // With no opaque and no available term, `UPrep::node` reads the width
    // nowhere (no cut is available and every cost is the inline bound), so
    // any width gives these sizes.
    let size = UPrep::new(nodes, &own, 1, vec![false; n])
      .map(|empty| empty.base.iter().map(|v| v.cost).collect());
    let candidate_count = len64(
      (0..n)
        .filter(|&t| facts.deg[t] >= 2 && base.costs[t] >= Len::new(2))
        .count(),
    );
    DagPrep { own, base, edges, facts, spine_len, size, candidate_count }
  }
}

/// [`optimize_uniform`] (`w >= 1`) with the width-independent tables of
/// `prep`, up to the decisions: the result has empty `roots` and `sharing`
/// and `variable_len` 0, and the [`UniformPlan`] builds the expressions
/// ([`UniformPlan::build`], which [`optimize_uniform`] does) or describes
/// them ([`UniformPlan::shares`], the dry run of phase 1 of the tiered
/// construction).
pub(crate) fn optimize_uniform_with(
  w: u64,
  dag: &SharingDag,
  prep: &DagPrep,
  meter: &mut Meter<'_>,
) -> Result<(UniformSharingResult, UniformPlan), SharingError> {
  if w == 0 {
    return Err(SharingError::FormatBound(FormatBound::UniformWidth { w }));
  }
  let wu = u(w);
  let nodes = dag.nodes();
  let n = nodes.len();
  let p = prof::scope(Phase::Classify);
  let facts = &prep.facts;
  // Fail closed on a telescope spine of `TELE_SUBADD_END` or more steps,
  // before the search (Lean's `optimizeUniformExpanded`).
  let spine_len = &prep.spine_len;
  if !spines_within_bound(spine_len) {
    return Err(SharingError::FormatBound(FormatBound::TelescopeSpine {
      bound: TELE_SUBADD_END,
    }));
  }
  // Unshared sizes C_0 (no stop terms, nothing available).
  let size: &[u128] = prep.size.as_ref().map_err(Clone::clone)?;
  // Classes: certain-excluded, low degree, and the gain test on visible
  // counts with threshold theta.
  let mut ce: Vec<bool> = Vec::with_capacity(n);
  let mut cand: Vec<bool> = Vec::with_capacity(n);
  for ((&o, &s), &d) in facts.occ.iter().zip(size).zip(&facts.deg) {
    let x = certainly_excluded(o, s, wu);
    ce.push(x);
    cand.push(!x && d >= 2);
  }
  let own = &prep.own;
  let bounds = uniform_bounds(nodes, own, wu, &cand)?;
  let vis0 = visible_counts(dag, &cand);
  // theta = 1 + tag0_step_bound(#candidates) always holds (one more entry
  // grows the table count by at most that many bytes; 2 below 4311826560
  // candidates); 1 when every minimum lies in one count bracket.
  let n_cand = len64(cand.iter().filter(|&&c| c).count());
  let theta_max = i128::from(tag0_step_bound(n_cand)) + 1;
  // The gain bound of every candidate (the terms the gain test reads),
  // computed once for both thresholds, in increasing ID (the first overflow
  // is the error).
  let mut gain: Vec<i128> = vec![0; n];
  let mut n_cs_max = 0usize;
  for t in 0..n {
    if cand[t] {
      gain[t] = stored_gain(
        &nodes[t],
        vis0.0[t],
        vis0.1[t],
        spine_len[t],
        bounds.inl[t],
        bounds.merged[t],
        wu,
      )?;
      n_cs_max += usize::from(gain[t] >= theta_max);
    }
  }
  let n_cs_max = len64(n_cs_max);
  let theta: i128 =
    if tag0_len(n_cand) == tag0_len(n_cs_max) { 1 } else { theta_max };
  // The classes, and the terms of each class in increasing ID.
  let mut cls: Vec<UniformClass> = Vec::with_capacity(n);
  let (mut cs, mut ce_terms, mut unc, mut low) =
    (Vec::new(), Vec::new(), Vec::new(), Vec::new());
  let mut opaq = vec![false; n];
  for t in 0..n {
    let c = if ce[t] {
      ce_terms.push(tid(t));
      UniformClass::CertainExcluded
    } else if facts.deg[t] < 2 {
      low.push(tid(t));
      UniformClass::LowDegree
    } else if gain[t] >= theta {
      cs.push(tid(t));
      opaq[t] = true;
      UniformClass::CertainStored
    } else {
      unc.push(tid(t));
      UniformClass::Uncertain
    };
    cls.push(c);
  }
  drop(gain);
  // The candidate count is a statistic here (Lean `Stats.candidates`), not
  // a limit: `max_candidates` bounds only the width-state search (`search`),
  // and Lean's uniform optimizer has no such limit.
  meter.stats.candidates = len64(cs.len() + unc.len());
  let up = UPrep::new(nodes, own, wu, opaq)?;
  let comps = uncertain_components(dag, &cls);
  let k_cs = u64::try_from(cs.len()).unwrap_or(u64::MAX);
  let k_unc = u64::try_from(unc.len()).unwrap_or(u64::MAX);
  // Largest table-count difference between two candidate-only sets that
  // contain the certain-stored terms.
  let slack = i128::from(tag0_len(k_cs.saturating_add(k_unc)))
    - i128::from(tag0_len(k_cs));
  // Search each component (independent searches; see `Parallelism`).
  let search_area = |members: &[TermId],
                     area: &[TermId],
                     meter: &mut Meter<'_>,
                     pos: &[u32],
                     pool: &Pool|
   -> Result<(Choice, CTable), SharingError> {
    // Root occurrences in the area, by increasing root.
    let mut in_area: Vec<TermId> =
      dag.roots().iter().copied().filter(|&r| pos[ix(r)] != NO_POS).collect();
    in_area.sort_unstable();
    let mut root_mult: Vec<(TermId, u128)> = Vec::new();
    for r in in_area {
      match root_mult.last_mut() {
        Some((q, m)) if *q == r => *m += 1,
        _ => root_mult.push((r, 1)),
      }
    }
    let stored_in: Vec<TermId> =
      area.iter().copied().filter(|&t| up.opaq[ix(t)]).collect();
    if meter.limits().uniform_subset_search {
      // The reference: plain subset enumeration.
      let mut cx = CompCtx {
        up: &up,
        members: members.to_vec(),
        area: area.to_vec(),
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
    let mut member_of = Buf::filled(&pool.positions, area.len(), NO_POS);
    for (m, &t) in members.iter().enumerate() {
      if let Some(j) =
        usize::try_from(pos[ix(t)]).ok().filter(|&j| j < area.len())
      {
        member_of[j] = u32::try_from(m).unwrap_or(NO_POS);
      }
    }
    let mut root_occ = Buf::filled(&pool.counts, area.len(), 0);
    for (j, y) in area.iter().enumerate() {
      root_occ[j] = root_mult
        .iter()
        .find(|(r, _)| r == y)
        .map_or(0, |(_, m)| u64::try_from(*m).unwrap_or(u64::MAX));
    }
    let mut cx = SCtx {
      up: &up,
      facts,
      cand: &cand,
      b0: &bounds,
      vis0: &vis0,
      spine_len,
      dag_size: len64(n),
      members,
      member_of,
      area,
      pos,
      root_occ,
      root_mult,
      stored_in,
      slack,
      theta,
      memo: pool.memo.take(),
      memo_hits: 0,
      vals: Buf::filled(&pool.uvals, area.len(), UVal::default()),
      vals_for: Buf::filled(&pool.flags, 0, false),
      vals_work: 0,
      vals_valid: false,
      pool,
    };
    let tb = cx.solve(meter, members, &[], &[], None);
    // The memo holds the other references of the table; it goes back to
    // the pool empty.
    let mut memo = std::mem::take(&mut cx.memo);
    drop(cx);
    memo.clear();
    pool.memo.replace(memo);
    let tb = Rc::unwrap_or_clone(tb?);
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
  // `pos` maps every term to its position in the component's area
  // (`NO_POS` outside it); it is set for the area of each component and
  // cleared afterwards, so one buffer serves every component.
  let search_one = |members: &Vec<TermId>,
                    meter: &mut Meter<'_>,
                    pos: &mut [u32],
                    pool: &Pool|
   -> Result<(Choice, CTable), SharingError> {
    let area = component_area(&up, facts, members, pos);
    let res = search_area(members, &area, meter, pos, pool);
    for &t in &area {
      pos[ix(t)] = NO_POS;
    }
    res
  };
  drop(p);
  let p = prof::scope(Phase::Search);
  let budget = meter.parallel.components;
  let mut results: Vec<(Choice, CTable)> = Vec::with_capacity(comps.len());
  if budget <= 1 {
    let mut pos = vec![NO_POS; n];
    let pool = Pool::default();
    for members in &comps {
      results.push(search_one(members, meter, &mut pos, &pool)?);
    }
  } else {
    // Each component on its own meter; the counts are added in component
    // order afterwards (`Meter::absorb`), then the results are used in the
    // same order as sequentially.
    let limits = meter.limits();
    let outs = super::par::map_ranges(comps.len(), budget, |r| {
      let mut pos = vec![NO_POS; n];
      let pool = Pool::default();
      r.map(|j| {
        let mut m = Meter::new(limits);
        let res = search_one(&comps[j], &mut m, &mut pos, &pool);
        (res, m.stats)
      })
      .collect()
    });
    for (res, stats) in outs {
      meter.absorb(&stats)?;
      results.push(res?);
    }
  }
  drop(p);
  let p = prof::scope(Phase::Knapsack);
  let states_visited = meter.stats.states_created;
  // Combine: per-component optima, unless a lower count bracket is shorter.
  // The components are disjoint, so the union of their sets is their
  // concatenation, sorted once.
  let mut chosen_x: Vec<TermId> = Vec::new();
  let mut chosen_delta: i128 = 0;
  for ((d, s), _) in &results {
    chosen_x.extend_from_slice(s);
    chosen_delta += d;
  }
  chosen_x.sort_unstable();
  let len_u64 = |v: usize| u64::try_from(v).unwrap_or(u64::MAX);
  let k0 = k_cs.saturating_add(len_u64(chosen_x.len()));
  let start = tag0_bracket_start(k0);
  let mut lower_bracket = false;
  if start > k_cs {
    let cap = usize::try_from(start - 1 - k_cs).map_err(|_e| overflow())?;
    let cells = (results.len() + 1).saturating_mul(cap + 1);
    if u64::try_from(cells).unwrap_or(u64::MAX)
      > meter.limits().max_knapsack_cells
    {
      return Err(SharingError::ResourceExhausted(super::ResourceExhausted {
        resource: super::Resource::KnapsackCells,
        limit: meter.limits().max_knapsack_cells,
      }));
    }
    let tables: Vec<&CTable> = results.iter().map(|(_, t)| t).collect();
    let ks = Knapsack::run(&tables, cap);
    // The per-component optimum is replaced by the least cell under
    // (length, set_prec) when that cell precedes it: the least of the
    // optimum and every cell, as a scan of the cells in count order with
    // `set_prec` on ties keeps. The cells' ranks are their `set_prec` order.
    let l0 =
      chosen_delta + i128::from(tag0_len(k_cs + len_u64(chosen_x.len())));
    let mut best: Option<(i128, u32, usize, i128)> = None;
    for c in 0..=cap {
      let Some(d) = ks.last.delta[c] else { continue };
      let l = d + i128::from(tag0_len(k_cs + len_u64(c)));
      let r = ks.last.rank[c];
      if best.is_none_or(|(bl, br, _, _)| l < bl || (l == bl && r < br)) {
        best = Some((l, r, c, d));
      }
    }
    if let Some((l, _, c, d)) = best {
      let s = ks.set(&tables, c);
      if l < l0 || (l == l0 && set_prec(&s, &chosen_x)) {
        chosen_x = s;
        chosen_delta = d;
        lower_bracket = true;
      }
    }
  }
  drop(p);
  let p = prof::scope(Phase::UniformMaterialize);
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
  let nearest = NearestStored::new(dag, &stored);
  let order: Vec<TermId> = heap_order(&nearest, &stored, &facts.deg)
    .into_iter()
    .map(|k| stored[k as usize])
    .collect();
  if order.len() != stored.len() {
    return Err(internal("pinned order dropped a stored term"));
  }
  let mut index: Vec<Option<u64>> = vec![None; n];
  for (pos, &t) in order.iter().enumerate() {
    index[ix(t)] = Some(len_u64(pos));
  }
  let dict = UniformIndex { index, width: w };
  let own = &prep.own;
  let mut work = 0u64;
  let costs = all_costs(nodes, own, &dict, &mut work);
  let plan = decide_dependent(
    nodes,
    own,
    &dict,
    &costs,
    &order,
    dag.roots(),
    &mut work,
  )?;
  meter.work(work)?;
  let predicted = plan.predicted.plus_u64(tag0_len(k));
  if predicted != Len::new(model) {
    return Err(internal(format!(
      "uniform model length {model} differs from the full evaluation {predicted:?}"
    )));
  }
  let mut unshared = Len::new(tag0_len(0));
  for &r in dag.roots() {
    unshared = unshared.plus(prep.base.costs[ix(r)]);
  }
  let result = UniformSharingResult {
    roots: Vec::new(),
    sharing: Vec::new(),
    table_terms: order,
    model_len: model,
    variable_len: 0,
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
  };
  drop(p);
  Ok((result, UniformPlan { dict, plan, model, k, nearest }))
}

/// The decisions of one uniform-width optimum ([`optimize_uniform_with`]):
/// the table indices of the stored terms and the materialization choice of
/// every entry top and needed term. The expressions are either built and
/// checked ([`UniformPlan::build`]) or only described
/// ([`UniformPlan::shares`]); both read the same decisions.
pub(crate) struct UniformPlan {
  dict: UniformIndex,
  plan: DependentPlan,
  /// The uniform-model variable length.
  model: u64,
  /// The table length.
  k: u64,
  /// The nearest stored descendants of the stored set
  /// (`UniformSharingResult::stored`, ascending), which phase 2 reuses.
  pub(crate) nearest: NearestStored,
}

/// The phase-1 expressions of a [`UniformPlan`], checked by re-expansion.
pub(crate) struct UniformExprs {
  pub(crate) entries: Vec<Arc<Expr>>,
  pub(crate) roots: Vec<Arc<Expr>>,
  /// Real variable length (Shares at their TagN width, as `put_expr`
  /// writes them).
  pub(crate) measured: u64,
  /// Pointer-distinct expression nodes, as the re-expansion check counted
  /// them (`None` when the check without interning reported a mismatch and
  /// the interning build accepted the encoding, which it never should).
  pub(crate) visited: Option<u64>,
}

impl UniformPlan {
  /// What the expressions contain, from the decisions alone (the phase-1
  /// dry run of the tiered construction): [`PlanShares`], and the real
  /// variable length, which is the model with every Share priced at its
  /// TagN width instead of `w`, Share by Share. Charges `max_input_nodes`
  /// with the expression nodes the build allocates, which are the input
  /// nodes the re-expansion check of the built expressions charges.
  pub(crate) fn shares(
    &self,
    dag: &SharingDag,
    table: &[TermId],
    limits: &ExactSharingLimits,
  ) -> Result<(PlanShares, u64), SharingError> {
    let _p = prof::scope(Phase::UniformCheck);
    let position =
      |t: TermId| self.dict.index[ix(t)].and_then(|i| usize::try_from(i).ok());
    let shares =
      self.plan.shares(dag.nodes(), table, dag.roots(), &position)?;
    dag.check_input_nodes(shares.nodes, limits)?;
    let mut real = i128::from(self.model);
    for (i, &r) in shares.refs.iter().enumerate() {
      let delta = i128::from(tag4_len(len64(i))) - i128::from(self.dict.width);
      real = real
        .checked_add(i128::from(r).checked_mul(delta).ok_or_else(overflow)?)
        .ok_or_else(overflow)?;
    }
    let real = u64::try_from(real)
      .ok()
      .filter(|&l| l < u64::MAX)
      .ok_or_else(overflow)?;
    Ok((shares, real))
  }

  /// Build the table `table` and the roots, check them by re-expansion
  /// (charging `max_input_nodes` with their nodes) and measure their real
  /// length.
  pub(crate) fn build(
    &self,
    dag: &SharingDag,
    table: &[TermId],
    limits: &ExactSharingLimits,
  ) -> Result<UniformExprs, SharingError> {
    let p = prof::scope(Phase::UniformMaterialize);
    let (entries, roots) =
      build_dependent(dag.nodes(), &self.dict, &self.plan, table, dag.roots())?;
    drop(p);
    let _p = prof::scope(Phase::UniformCheck);
    // The re-expansion check, then the real length (Shares at their TagN
    // width, `expr_len`); both in one walk when the check passes.
    let (visited, measured) =
      match dag.check_and_measure(table, &entries, &roots, &tag4_len) {
        Some((visited, len)) => {
          dag.check_input_nodes(visited, limits)?;
          (Some(visited), len)
        },
        None => {
          dag.check_reexpansion(
            table,
            &entries,
            &roots,
            limits,
            "materialized encoding changes the expanded AST",
            "materialized entries do not expand to the stored terms",
          )?;
          let len =
            exprs_len_with(self.k, entries.iter().chain(&roots), &tag4_len)
              .ok_or_else(overflow)?;
          (None, len)
        },
      };
    Ok(UniformExprs { entries, roots, measured, visited })
  }
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

#[cfg(test)]
#[allow(clippy::cast_possible_truncation, clippy::needless_range_loop)]
mod knapsack_tests {
  use super::{CTable, Knapsack, TermId, knapsack_reference, set_prec};

  struct Rng(u64);

  impl Rng {
    fn below(&mut self, n: u64) -> u64 {
      self.0 ^= self.0 << 13;
      self.0 ^= self.0 >> 7;
      self.0 ^= self.0 << 17;
      self.0 % n.max(1)
    }
  }

  /// The rank-based knapsack returns the reference's least `(delta, set)`
  /// in every cell, and its ranks order the cells' sets by `set_prec`.
  #[test]
  fn knapsack_matches_explicit_sets() {
    let mut rng = Rng(0x9E37_79B9_7F4A_7C15);
    let mut cells_checked = 0usize;
    for case in 0..400 {
      // Disjoint components over a shuffled domain of term IDs.
      let mut domain: Vec<TermId> = (0..300).collect();
      for i in (1..domain.len()).rev() {
        let j = rng.below(i as u64 + 1) as usize;
        domain.swap(i, j);
      }
      let comps = rng.below(30) as usize;
      let mut next = 0usize;
      let mut tables: Vec<CTable> = Vec::new();
      for _ in 0..comps {
        let size = 1 + rng.below(6) as usize;
        let mut members: Vec<TermId> = domain[next..next + size].to_vec();
        next += size;
        members.sort_unstable();
        let mut tb: CTable = Vec::new();
        for k in 0..=size {
          if rng.below(10) < 7 || k == 0 {
            // A random `k`-subset; small deltas make ties common.
            let mut pool = members.clone();
            let mut set = Vec::new();
            for _ in 0..k {
              let i = rng.below(pool.len() as u64) as usize;
              set.push(pool.swap_remove(i));
            }
            set.sort_unstable();
            let d = i128::from(rng.below(4) as u8) - 1;
            tb.push(Some((d, set)));
          } else {
            tb.push(None);
          }
        }
        tables.push(tb);
      }
      let total: usize = tables.iter().map(|t| t.len() - 1).sum();
      let cap = rng.below(total as u64 + 4) as usize;
      let refs: Vec<&CTable> = tables.iter().collect();
      let want = knapsack_reference(&refs, cap);
      let got = Knapsack::run(&refs, cap);
      let mut some: Vec<usize> = Vec::new();
      for c in 0..=cap {
        assert_eq!(
          got.last.delta[c],
          want[c].as_ref().map(|x| x.0),
          "case {case} cell {c}"
        );
        if let Some((_, s)) = &want[c] {
          assert_eq!(&got.set(&refs, c), s, "case {case} cell {c}");
          some.push(c);
          cells_checked += 1;
        }
      }
      for &a in &some {
        for &b in &some {
          if a != b {
            let (sa, sb) =
              (&want[a].as_ref().unwrap().1, &want[b].as_ref().unwrap().1);
            assert_eq!(
              got.last.rank[a] < got.last.rank[b],
              set_prec(sa, sb),
              "case {case} cells {a} {b}"
            );
          }
        }
      }
    }
    assert!(cells_checked > 2000);
  }
}
