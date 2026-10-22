//! Canonical family sharing under a uniform Share width.
//!
//! Production uses the fixed K16 family in `family`. The old unbounded
//! uniform optimizer and its controls live in `reference`, available only
//! to unit tests or the explicit test-FFI reference feature.
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
//! * The production result minimizes over the fixed initial component
//!   families, with certain-stored entries held fixed. The reference oracle
//!   minimizes over all tables whose entries have in-degree >= 2.
//!   In-degree-1 terms are left out by an exchange that never
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
//! Production enumerates every subset up to sixteen initial members and
//! otherwise keeps every count of the setPrec-least greedy chain. The old
//! reference component search is the reclassifying branch and bound of Lean
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

use std::sync::Arc;

use rustc_hash::{FxHashMap, FxHashSet};

use super::cost::{Len, exprs_len_with, tag0_len, tag4_len};
use super::dag::{Node, SharingDag, TermId, ix};
use super::dict::{
  DependentPlan, Evaluation, PlanShares, ReadEdges, UniformIndex, all_costs,
  build_dependent, decide_dependent,
};
use super::prof::{self, Phase};
use super::{
  ExactSharingLimits, ExactSharingStats, FormatBound, Meter, SharingError,
};
#[cfg(any(test, feature = "sharing-reference"))]
use super::{
  constant_fixed_len, constant_info_root_exprs, rebuild_constant_info,
};
#[cfg(any(test, feature = "sharing-reference"))]
use crate::constant::Constant;
use crate::expr::Expr;
use crate::tag::TagN;

mod family;
pub(crate) use family::optimize_family_with;

#[cfg(any(test, feature = "sharing-reference"))]
mod reference;
#[cfg(any(test, feature = "sharing-reference"))]
pub(crate) use reference::optimize_uniform_with;

#[cfg(test)]
pub(crate) mod experimental;

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
  /// Test-only view of retained per-count optima, including canonical ties.
  #[cfg(test)]
  pub(crate) component_tables: Vec<CTable>,
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

// This cap is used ONLY for empty costs consumed by initial classification.
// It covers 2*w for every public u64 width, not merely tiered widths 1..=3.
// Proofs: IxSharingVerify.UniformCappedSize. General UPrep/phi/gains retain
// their existing arithmetic; a capped value must never enter those paths.
const EMPTY_SIZE_CAP: u128 = (1u128 << 65) - 2;

#[cfg(test)]
mod capped_size_tests;

fn empty_cap_add(a: u128, b: u128) -> u128 {
  // Both operands become <=2^65-2, so this addition cannot overflow u128.
  (a.min(EMPTY_SIZE_CAP) + b.min(EMPTY_SIZE_CAP)).min(EMPTY_SIZE_CAP)
}

/// Exact own-payload cost, capped independently of Len's u64 sentinel.
/// In particular, all Ref/Rec universe arguments contribute their bytes.
fn empty_own_size(node: &Node) -> Result<u128, SharingError> {
  Ok(match node {
    Node::Sort(n) | Node::Var(n) | Node::Str(n) | Node::Nat(n) => {
      u(tag4_len(*n))
    },
    Node::Ref(n, us) | Node::Rec(n, us) => {
      let count = u64::try_from(us.len()).map_err(|_e| overflow())?;
      us.iter().fold(
        empty_cap_add(u(tag4_len(count)), u(tag0_len(*n))),
        |size, level| empty_cap_add(size, u(tag0_len(*level))),
      )
    },
    Node::Prj(t, f, _) => empty_cap_add(u(tag4_len(*f)), u(tag0_len(*t))),
    Node::Let(c, ..) => empty_cap_add(u(tag4_len(c.flags())), 1),
    Node::App(..) | Node::Lam(..) | Node::All(..) => 0,
  })
}

/// min(C_0, EMPTY_SIZE_CAP) in child-before-parent order. Empty evaluation
/// has no opaque/available terms and no cut or subtraction. Its only
/// recurrences are nonnegative sums of payloads, sides and natural tails;
/// distributing min(cap, _) over those sums is exact.
fn empty_sizes_capped(
  nodes: &[Node],
  spine_len: &[u64],
  spine_tail: &[TermId],
) -> Result<Vec<u128>, SharingError> {
  let mut cost = vec![0; nodes.len()];
  let mut sides = vec![0; nodes.len()];
  for (t, node) in nodes.iter().enumerate() {
    if node.family().is_none() {
      cost[t] = node
        .children()
        .as_slice()
        .iter()
        .fold(empty_own_size(node)?, |size, child| {
          empty_cap_add(size, cost[ix(*child)])
        });
    } else {
      let next = spine_next(node);
      let continued = nodes[ix(next)].family() == node.family();
      sides[t] = empty_cap_add(
        empty_cap_add(side_extra(node), cost[ix(side_child(node))]),
        if continued { sides[ix(next)] } else { 0 },
      );
      cost[t] = empty_cap_add(
        empty_cap_add(u(tag4_len(spine_len[t])), sides[t]),
        cost[ix(spine_tail[t])],
      );
    }
  }
  Ok(cost)
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
  /// Distinct parents of each term.
  pub(crate) parents: Vec<Vec<TermId>>,
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

/// `(occ-1)*size < occ*w`, with Nat subtraction, including occ=0/1 and
/// w=0. For size>w and occ>=1 this is occ*(size-w)<size, equivalently
/// occ <= (size-1)/(size-w). No product can overflow. A saturated occurrence
/// count is sound here: the quotient is strictly below size<=EMPTY_SIZE_CAP
/// (and in fact below u128::MAX for any representable size>w).
fn certainly_excluded(occ: u128, size: u128, w: u128) -> bool {
  if occ == 0 || w == 0 {
    return false;
  }
  if size <= w {
    return true;
  }
  occ <= (size - 1) / (size - w)
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

/// Lean `propagateCounts`: per term, root occurrences plus, over the edges
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
  #[cfg(any(test, feature = "sharing-reference"))]
  members: Vec<TermId>,
  area: Vec<TermId>,
  root_mult: Vec<(TermId, u128)>,
  stored_in: Vec<TermId>,
  #[cfg(any(test, feature = "sharing-reference"))]
  phi0: u128,
  #[cfg(any(test, feature = "sharing-reference"))]
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
}

// ---------------------------------------------------------------------------
// Reclassifying branch and bound with splitting (Lean `SCtx`)
// ---------------------------------------------------------------------------

/// Best `(delta, set)` per chosen count (index = set size).
type CTable = Vec<Option<Choice>>;

#[cfg(any(test, feature = "sharing-reference"))]
fn table_best(tb: &CTable) -> Option<i128> {
  tb.iter().flatten().map(|(d, _)| *d).min()
}

#[cfg(test)]
fn table_add(tb: &mut CTable, e: Choice) {
  let k = e.1.len();
  if tb.len() <= k {
    tb.resize(k + 1, None);
  }
  if better(e.0, &e.1, tb[k].as_ref()) {
    tb[k] = Some(e);
  }
}

#[cfg(test)]
fn table_trim(tb: CTable, slack: i128) -> CTable {
  match table_best(&tb) {
    None => tb,
    Some(b) => {
      tb.into_iter().map(|o| o.filter(|(d, _)| *d <= b + slack)).collect()
    },
  }
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
  // Nearest stored descendants of each stored term (`seen[x] == k + 1`:
  // visited from the `k`-th stored term).
  let mut pending: Vec<usize> = Vec::with_capacity(stored.len());
  let mut dependents: FxHashMap<TermId, Vec<TermId>> = FxHashMap::default();
  let mut seen: Vec<usize> = vec![0; nodes.len()];
  let mut stack: Vec<TermId> = Vec::new();
  for (k, &t) in stored.iter().enumerate() {
    stack.clear();
    stack.extend_from_slice(nodes[ix(t)].children().as_slice());
    let mut deps = 0usize;
    while let Some(x) = stack.pop() {
      if seen[ix(x)] == k + 1 {
        continue;
      }
      seen[ix(x)] = k + 1;
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
#[cfg(any(test, feature = "sharing-reference"))]
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
  /// Empty sizes capped at EMPTY_SIZE_CAP, ONLY for certain-excluded tests.
  /// Errors concern unencodable own-payload counts, not large unfolded costs.
  size: Result<Vec<u128>, SharingError>,
}

impl DagPrep {
  pub(crate) fn new(dag: &SharingDag) -> Self {
    let nodes = dag.nodes();
    let n = nodes.len();
    let own: Vec<Len> = nodes.iter().map(Node::own_len).collect();
    let base = Evaluation::new(nodes, &own, &super::dict::NoWidths);
    let edges = ReadEdges::new(nodes);
    let facts = graph_facts(dag);
    let (spine_len, spine_tail) = spine_tables(nodes, &vec![false; n]);
    let size = empty_sizes_capped(nodes, &spine_len, &spine_tail);
    DagPrep { own, base, edges, facts, spine_len, size }
  }
}

/// Initial classification shared by the exact path and offline experiments.
struct Initial<'d> {
  up: UPrep<'d>,
  #[cfg(any(test, feature = "sharing-reference"))]
  cand: Vec<bool>,
  #[cfg(any(test, feature = "sharing-reference"))]
  bounds: Bounds,
  #[cfg(any(test, feature = "sharing-reference"))]
  vis0: (Vec<u64>, Vec<u64>),
  #[cfg(any(test, feature = "sharing-reference"))]
  theta: i128,
  cs: Vec<TermId>,
  ce_terms: Vec<TermId>,
  unc: Vec<TermId>,
  low: Vec<TermId>,
  comps: Vec<Vec<TermId>>,
  slack: i128,
}

/// The initial canonical classification, before any recursive reclassification.
fn initial<'d>(
  w: u64,
  dag: &'d SharingDag,
  prep: &DagPrep,
  meter: &mut Meter<'_>,
) -> Result<Initial<'d>, SharingError> {
  if w == 0 {
    return Err(SharingError::FormatBound(FormatBound::UniformWidth { w }));
  }
  let wu = u(w);
  let nodes = dag.nodes();
  let n = nodes.len();
  let facts = &prep.facts;
  // Fail closed on a telescope spine of `TELE_SUBADD_END` or more steps,
  // before the search (Lean's `optimizeUniformExpanded`).
  let spine_len = &prep.spine_len;
  if !spines_within_bound(spine_len) {
    return Err(SharingError::FormatBound(FormatBound::TelescopeSpine {
      bound: TELE_SUBADD_END,
    }));
  }
  // Predicate-sufficient min(C_0, cap); never reused as a general model cost.
  let size: &[u128] = prep.size.as_ref().map_err(Clone::clone)?;
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
  // The candidate count is a statistic here (Lean `Stats.candidates`), not
  // a limit: `max_candidates` bounds only the width-state search (`search`),
  // and Lean's uniform optimizer has no such limit.
  meter.stats.candidates = len64(cs.len() + unc.len());
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
  Ok(Initial {
    up,
    #[cfg(any(test, feature = "sharing-reference"))]
    cand,
    #[cfg(any(test, feature = "sharing-reference"))]
    bounds,
    #[cfg(any(test, feature = "sharing-reference"))]
    vis0,
    #[cfg(any(test, feature = "sharing-reference"))]
    theta,
    cs,
    ce_terms,
    unc,
    low,
    comps,
    slack,
  })
}

fn combine_uniform(
  w: u64,
  dag: &SharingDag,
  prep: &DagPrep,
  meter: &mut Meter<'_>,
  stage: Initial<'_>,
  results: Vec<(Choice, CTable)>,
) -> Result<(UniformSharingResult, UniformPlan), SharingError> {
  let Initial { up, cs, ce_terms, unc, low, comps, .. } = stage;
  let nodes = dag.nodes();
  let n = nodes.len();
  let facts = &prep.facts;
  let k_cs = len64(cs.len());
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
  let order = pinned_order(dag, &facts.deg, &stored);
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
    #[cfg(test)]
    component_tables: results.into_iter().map(|(_, table)| table).collect(),
  };
  #[cfg(not(test))]
  drop(results);
  drop(p);
  Ok((result, UniformPlan { dict, plan, model, k }))
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
#[cfg(any(test, feature = "sharing-reference"))]
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
#[cfg(any(test, feature = "sharing-reference"))]
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
