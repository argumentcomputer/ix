//! Exact minimum sharing under a uniform Share width.
//!
//! This is a byte-for-byte port of W1's `Ix/Sharing/Exact/Uniform.lean`;
//! the rules below are pinned by that implementation.
//!
//! Cost model: every `Share` costs exactly `w >= 1` bytes regardless of its
//! index; the table count is an exact Tag0; telescopes and every other byte
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
//!   occurrences; `head_deg(t)`: in-edges at head positions (roots are
//!   heads; the other edges continue a telescope: an App as the function of
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
//!   bound `g >= 2`, with lower bounds computed bottom-up pricing every
//!   candidate child at `min(w, .)`, every other child at its inline bound
//!   and a header of at least 1 byte:
//!   non-telescope `g = (deg-1)*inl - deg*w`; telescope with `head_deg >= 1`
//!   `g = (deg-1)*b + (head_deg-1) - deg*w`; telescope with `head_deg = 0`
//!   `g = (deg-1)*b - tag4(spine length) - deg*w`.
//! * UNCERTAIN: the other candidates; LOW-DEGREE: the other terms.
//!
//! Certain-stored terms cost exactly `w` wherever they occur (`g >= 2`
//! forces their merged payload bound `>= w`), so costs above them are
//! evaluated with them as `w`-byte leaves that end telescopes.
//!
//! # Search
//!
//! Uncertain terms joined by a DAG path avoiding certain-stored terms form
//! a component; costs are sums of per-component functions. Each component is
//! searched by depth-first branch and bound over its members in ID order,
//! "not stored" first, with the lower bound "every undecided member
//! available, its entry free"; complete choices within `slack =
//! tag0(|certain-stored| + |uncertain|) - 1` of the best are kept, the best
//! per chosen-set size. The table-count prefix is the only coupling: when
//! the combined choice reaches a Tag0 bracket of 128 or more entries, a
//! knapsack over components checks the lower brackets.
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

use rustc_hash::FxHashSet;

use super::cost::{Len, expr_len, tag0_len, tag4_len};
use super::dag::{Node, SharingDag, TermId, ix};
use super::dict::{UniformIndex, all_costs, materialize_dependent};
use super::{
  ExactSharingLimits, ExactSharingStats, FormatBound, Meter, SharingError,
  constant_fixed_len, constant_info_root_exprs, rebuild_constant_info,
};
use crate::constant::Constant;
use crate::expr::Expr;

fn internal(msg: impl Into<String>) -> SharingError {
  SharingError::Internal(msg.into())
}

fn overflow() -> SharingError {
  SharingError::FormatBound(FormatBound::LengthOverflow)
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
  /// Whether the table-count knapsack chose a lower Tag0 bracket.
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
  head_deg: Vec<u64>,
  occ: Vec<u128>,
  parents: Vec<Vec<TermId>>,
}

pub(crate) fn graph_facts(dag: &SharingDag) -> Facts {
  let nodes = dag.nodes();
  let n = nodes.len();
  let mut deg = vec![0u64; n];
  let mut head_deg = vec![0u64; n];
  let mut parents: Vec<Vec<TermId>> = vec![Vec::new(); n];
  for &r in dag.roots() {
    deg[ix(r)] += 1;
    head_deg[ix(r)] += 1;
  }
  for (t, node) in nodes.iter().enumerate() {
    let kids = node.children();
    for (i, &c) in kids.as_slice().iter().enumerate() {
      deg[ix(c)] += 1;
      if !continuation_edge(node, i, &nodes[ix(c)]) {
        head_deg[ix(c)] += 1;
      }
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
  Facts { deg, head_deg, occ, parents }
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

struct Bounds {
  inl: Vec<u128>,
  merged: Vec<u128>,
}

fn uniform_bounds(
  nodes: &[Node],
  w: u128,
  maybe: &[bool],
) -> Result<Bounds, SharingError> {
  let n = nodes.len();
  let mut inl = vec![0u128; n];
  let mut merged = vec![0u128; n];
  let mut head_lb = vec![0u128; n];
  let mut cont_lb = vec![0u128; n];
  for (t, node) in nodes.iter().enumerate() {
    let (i, m) = if node.family().is_none() {
      let mut i = own_bytes(node)?;
      for &c in node.children().as_slice() {
        i = i.saturating_add(head_lb[ix(c)]);
      }
      (i, i)
    } else {
      let nxt = spine_next(node);
      let rest = if nodes[ix(nxt)].family() == node.family() {
        cont_lb[ix(nxt)]
      } else {
        head_lb[ix(nxt)]
      };
      let m = side_extra(node)
        .saturating_add(head_lb[ix(side_child(node))])
        .saturating_add(rest);
      (m.saturating_add(1), m)
    };
    if i == u128::MAX {
      return Err(overflow());
    }
    inl[t] = i;
    merged[t] = m;
    head_lb[t] = if maybe[t] { w.min(i) } else { i };
    cont_lb[t] = if maybe[t] { w.min(m) } else { m };
  }
  Ok(Bounds { inl, merged })
}

fn to_i(x: u128) -> Result<i128, SharingError> {
  i128::try_from(x).map_err(|_e| overflow())
}

fn stored_gain(
  node: &Node,
  deg: u64,
  head_deg: u64,
  spine_len: u64,
  b: &Bounds,
  t: usize,
  w: u128,
) -> Result<i128, SharingError> {
  let d = i128::from(deg);
  let w = to_i(w)?;
  let g = if node.family().is_none() {
    (d - 1).checked_mul(to_i(b.inl[t])?).and_then(|x| x.checked_sub(d * w))
  } else if head_deg >= 1 {
    (d - 1)
      .checked_mul(to_i(b.merged[t])?)
      .and_then(|x| x.checked_add(i128::from(head_deg) - 1))
      .and_then(|x| x.checked_sub(d * w))
  } else {
    (d - 1)
      .checked_mul(to_i(b.merged[t])?)
      .and_then(|x| x.checked_sub(i128::from(tag4_len(spine_len))))
      .and_then(|x| x.checked_sub(d * w))
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
// Order and driver
// ---------------------------------------------------------------------------

/// First count with the same Tag0 width as `k`.
fn tag0_bracket_start(k: u64) -> u64 {
  if k < 128 {
    0
  } else if k < 256 {
    128
  } else {
    1u64 << (8 * (super::cost::byte_count(k) - 1))
  }
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
  let mut dependents: rustc_hash::FxHashMap<TermId, Vec<TermId>> =
    rustc_hash::FxHashMap::default();
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
  let pos: rustc_hash::FxHashMap<TermId, usize> =
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
  // Classes.
  let ce: Vec<bool> =
    (0..n).map(|t| certainly_excluded(facts.occ[t], size[t], wu)).collect();
  let cand: Vec<bool> = (0..n).map(|t| !ce[t] && facts.deg[t] >= 2).collect();
  let bounds = uniform_bounds(nodes, wu, &cand)?;
  let mut cls = Vec::with_capacity(n);
  for t in 0..n {
    cls.push(if ce[t] {
      UniformClass::CertainExcluded
    } else if facts.deg[t] < 2 {
      UniformClass::LowDegree
    } else if stored_gain(
      &nodes[t],
      facts.deg[t],
      facts.head_deg[t],
      spine_len[t],
      &bounds,
      t,
      wu,
    )? >= 2
    {
      UniformClass::CertainStored
    } else {
      UniformClass::Uncertain
    });
  }
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
  let slack = i128::from(tag0_len(k_cs.saturating_add(k_unc))) - 1;
  // Search each component.
  let mut results: Vec<(Choice, Vec<Option<Choice>>)> = Vec::new();
  for members in &comps {
    let area = component_area(&up, &facts, members);
    let area_set: FxHashSet<TermId> = area.iter().copied().collect();
    let mut mult: std::collections::BTreeMap<TermId, u128> =
      std::collections::BTreeMap::new();
    for &r in dag.roots() {
      if area_set.contains(&r) {
        *mult.entry(r).or_default() += 1;
      }
    }
    let stored_in: Vec<TermId> =
      area.iter().copied().filter(|&t| up.opaq[ix(t)]).collect();
    let mut cx = CompCtx {
      up: &up,
      members: members.clone(),
      area,
      root_mult: mult.into_iter().collect(),
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
    results.push(cx.search(meter)?);
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
