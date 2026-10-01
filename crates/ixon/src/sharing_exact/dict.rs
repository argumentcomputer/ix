//! The fixed-dictionary optimizer `C_M` (§5) and byte-least materialization.
//!
//! For a dictionary `M` (available terms and their Share widths), `C_M(t)`
//! is the minimum length of a standalone expression expanding to `t`. The
//! options at `t` are a Share of `t` (if available) and its inline
//! constructor. For App, Lam and All the inline constructor is a telescope
//! over the maximal same-family spine `t = t_0, t_1, ..., t_l` (App follows
//! the function, Lam/All the body; `t_l` is the first node of another
//! constructor). A telescope of `j` spine nodes costs its TagN header for
//! `j`, every side child's standalone cost (App arguments; Lam/All contract
//! byte plus binder type), and its head: for `j < l` the head `t_j` continues
//! the family, so the canonical writer would merge any inline form of it
//! back into the telescope and the only legal head is a Share of `t_j`; for
//! `j = l` the head is the natural tail at its standalone cost. Every
//! canonical telescope boundary is one of these cases, so the recurrence is
//! complete; it is sound because each case is realized by a concrete
//! expression that the canonical writer emits with exactly that header.
//!
//! Children are standalone expressions and their lengths add, so the
//! recurrence runs bottom-up in term-ID order (children have smaller IDs).

use std::cmp::Ordering;
use std::sync::Arc;

use rustc_hash::FxHashMap;

use super::SharingError;
use super::cost::{Len, share_width, tag4_bytes_cmp, tag4_len};
use super::dag::{Node, SharingDag, TermId, ix};
use crate::expr::Expr;

/// Share widths available to one evaluation.
pub(crate) trait Widths {
  fn width(&self, t: TermId) -> Option<u64>;
}

/// A dictionary with actual table indices, needed to materialize Shares.
pub(crate) trait Indices: Widths {
  fn index(&self, t: TermId) -> Option<u64>;
}

/// The empty dictionary.
pub(crate) struct NoWidths;

impl Widths for NoWidths {
  fn width(&self, _t: TermId) -> Option<u64> {
    None
  }
}

/// A fixed dictionary: available terms and their actual table indices.
/// Indices need not be consecutive, which lets tests force any width.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct FixedDictionary {
  index: FxHashMap<TermId, u64>,
}

impl FixedDictionary {
  pub fn new() -> Self {
    Self::default()
  }

  /// Make `t` available as `Share(index)`; returns a previous index.
  pub fn insert(&mut self, t: TermId, index: u64) -> Option<u64> {
    self.index.insert(t, index)
  }

  pub fn index_of(&self, t: TermId) -> Option<u64> {
    self.index.get(&t).copied()
  }

  pub fn len(&self) -> usize {
    self.index.len()
  }

  pub fn is_empty(&self) -> bool {
    self.index.is_empty()
  }
}

impl Widths for FixedDictionary {
  fn width(&self, t: TermId) -> Option<u64> {
    self.index.get(&t).map(|&i| share_width(i))
  }
}

impl Indices for FixedDictionary {
  fn index(&self, t: TermId) -> Option<u64> {
    self.index_of(t)
  }
}

/// A dense prefix dictionary for table sequences (indices `< 2^32`).
pub(crate) struct DenseIndex {
  index: Vec<u64>,
}

impl DenseIndex {
  const NONE: u64 = u64::MAX;

  pub(crate) fn new(n: usize) -> Self {
    DenseIndex { index: vec![Self::NONE; n] }
  }

  pub(crate) fn set(&mut self, t: TermId, i: u64) {
    self.index[ix(t)] = i;
  }
}

impl Widths for DenseIndex {
  fn width(&self, t: TermId) -> Option<u64> {
    self.index(t).map(share_width)
  }
}

impl Indices for DenseIndex {
  fn index(&self, t: TermId) -> Option<u64> {
    let i = self.index[ix(t)];
    (i != Self::NONE).then_some(i)
  }
}

/// The representation chosen for one standalone occurrence.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Choice {
  /// A Share of this term's table entry.
  Share,
  /// The node's own constructor with standalone children (leaf, Prj, Let).
  Inline,
  /// A telescope of `j >= 1` spine nodes (see the module docs).
  Telescope(u64),
}

/// Scan the telescope options of an App/Lam/All node `t`.
///
/// Returns the least inline length found and its prefix length `j`. With
/// `ties` unset the scan may stop once no remaining option can be strictly
/// below `min(best, share)`; with `ties` set it stops only once none can
/// reach that value, and among equal lengths it keeps the `j` whose TagN
/// header bytes are least. Remaining options are bounded below by
/// `header(j) + s + 2`: headers never shrink, a further spine node adds a
/// side cost of at least one byte, and every head costs at least one byte.
#[allow(clippy::too_many_arguments)]
fn scan_telescope<W: Widths, C: Fn(TermId) -> Len>(
  nodes: &[Node],
  own: &[Len],
  t: TermId,
  widths: &W,
  cost: &C,
  ties: bool,
  share: Len,
  work: &mut u64,
) -> (Len, u64) {
  let family = nodes[ix(t)].family();
  let mut best = Len::OVERFLOW;
  let mut best_j: u64 = 0;
  let mut cur = t;
  let mut j: u64 = 0;
  let mut s = Len::ZERO;
  loop {
    *work = work.saturating_add(1);
    let (side, next) = match &nodes[ix(cur)] {
      Node::App(f, a) => (cost(*a), *f),
      Node::Lam(_, ty, b) | Node::All(_, _, ty, b) => {
        (own[ix(cur)].plus(cost(*ty)), *b)
      },
      _ => break,
    };
    s = s.plus(side);
    j = j.saturating_add(1);
    let header = Len::new(tag4_len(j));
    let continues = nodes[ix(next)].family() == family;
    let head = if continues {
      widths.width(next).map(Len::new)
    } else {
      Some(cost(next))
    };
    if let Some(h) = head {
      let len = header.plus(s).plus(h);
      if len < best
        || (ties && len == best && tag4_bytes_cmp(j, best_j) == Ordering::Less)
      {
        best = len;
        best_j = j;
      }
    }
    if !continues {
      break;
    }
    let lower = header.plus(s).plus_u64(2);
    let cap = best.min(share);
    if (ties && lower > cap) || (!ties && lower >= cap) {
      break;
    }
    cur = next;
  }
  (best, best_j)
}

/// `C_M(t)` given the minimum standalone lengths `cost` of every smaller
/// term. With `ties`, also the pinned byte-least choice among options of
/// that length: any inline form precedes a Share (expression flags
/// `0x0..=0xA` are below the Share flag `0xB`), and telescopes of one node
/// are ordered by their TagN header bytes, which differ for distinct `j`.
/// Once the head is fixed the remaining segments have fixed lengths, so
/// their least bytes are chosen independently by the same rule.
pub(crate) fn eval_node<W: Widths, C: Fn(TermId) -> Len>(
  nodes: &[Node],
  own: &[Len],
  t: TermId,
  widths: &W,
  cost: &C,
  ties: bool,
  work: &mut u64,
) -> (Len, Choice) {
  *work = work.saturating_add(1);
  let share = widths.width(t).map_or(Len::OVERFLOW, Len::new);
  let o = own[ix(t)];
  let (inline, choice) = match &nodes[ix(t)] {
    Node::Sort(_)
    | Node::Var(_)
    | Node::Ref(..)
    | Node::Rec(..)
    | Node::Str(_)
    | Node::Nat(_) => (o, Choice::Inline),
    Node::Prj(_, _, v) => (o.plus(cost(*v)), Choice::Inline),
    Node::Let(_, a, b, c) => {
      (o.plus(cost(*a)).plus(cost(*b)).plus(cost(*c)), Choice::Inline)
    },
    Node::App(..) | Node::Lam(..) | Node::All(..) => {
      let (len, j) =
        scan_telescope(nodes, own, t, widths, cost, ties, share, work);
      (len, Choice::Telescope(j))
    },
  };
  if share < inline { (share, Choice::Share) } else { (inline, choice) }
}

/// `C_M` for every term, bottom-up.
pub(crate) fn all_costs<W: Widths>(
  nodes: &[Node],
  own: &[Len],
  widths: &W,
  work: &mut u64,
) -> Vec<Len> {
  let mut costs: Vec<Len> = Vec::with_capacity(nodes.len());
  for t in 0..nodes.len() {
    let t = TermId::try_from(t).unwrap_or(TermId::MAX);
    let c = eval_node(nodes, own, t, widths, &|x| costs[ix(x)], false, work).0;
    costs.push(c);
  }
  costs
}

/// `C_M` of every term under a dictionary that grows one term at a time
/// ([`IncrementalCosts::add`]), with the work count of a full [`all_costs`]
/// evaluation of the current dictionary ([`IncrementalCosts::work`]).
///
/// Only terms whose evaluation can read a changed value are evaluated again.
/// [`eval_node`] at `t` reads `width(t)`; for a non-telescope node the costs
/// of its children; for an App/Lam/All node, along its spine `t = s_0, s_1,
/// ...` ([`scan_telescope`], which may stop earlier, so this is a superset),
/// the cost of every side child, the width of every spine successor of the
/// same family and the cost of the first successor of another family. So
/// after `width(t)` changes, `t` is evaluated again, and so is every parent
/// `p` of an evaluated term `x` such that `p` reads the cost of `x` and it
/// changed, or `x` continues the spine of `p` and either `x = t` or `x` is
/// spine-dirty (a value read along the spine of `x` changed). Terms are
/// evaluated in increasing ID, so children come first. Every other term reads
/// the same values as in the previous evaluation, so its cost and its work
/// are unchanged; the work count is the sum of the per-term work, which is
/// what [`all_costs`] counts.
pub(crate) struct IncrementalCosts<'a> {
  nodes: &'a [Node],
  own: &'a [Len],
  parents: &'a [Vec<TermId>],
  costs: Vec<Len>,
  term_work: Vec<u64>,
  total: u128,
  /// Stamps of the current step: cost changed, spine-dirty, queued.
  changed: Vec<u32>,
  spine_dirty: Vec<u32>,
  queued: Vec<u32>,
  epoch: u32,
  heap: std::collections::BinaryHeap<std::cmp::Reverse<TermId>>,
}

impl<'a> IncrementalCosts<'a> {
  /// A full evaluation of `widths` (as [`all_costs`]). `parents[t]` are the
  /// distinct parents of `t`.
  pub(crate) fn new<W: Widths>(
    nodes: &'a [Node],
    own: &'a [Len],
    parents: &'a [Vec<TermId>],
    widths: &W,
  ) -> Self {
    let n = nodes.len();
    let mut costs: Vec<Len> = Vec::with_capacity(n);
    let mut term_work: Vec<u64> = Vec::with_capacity(n);
    let mut total: u128 = 0;
    for t in 0..n {
      let t = TermId::try_from(t).unwrap_or(TermId::MAX);
      let mut w = 0u64;
      let c =
        eval_node(nodes, own, t, widths, &|x| costs[ix(x)], false, &mut w).0;
      costs.push(c);
      term_work.push(w);
      total += u128::from(w);
    }
    IncrementalCosts {
      nodes,
      own,
      parents,
      costs,
      term_work,
      total,
      changed: vec![0; n],
      spine_dirty: vec![0; n],
      queued: vec![0; n],
      epoch: 0,
      heap: std::collections::BinaryHeap::new(),
    }
  }

  /// `C_M` of every term under the current dictionary.
  pub(crate) fn costs(&self) -> &[Len] {
    &self.costs
  }

  /// The work [`all_costs`] counts for the current dictionary (saturating).
  pub(crate) fn work(&self) -> u64 {
    u64::try_from(self.total).unwrap_or(u64::MAX)
  }

  /// `widths` is the previous dictionary with `t`'s width changed (`t` was
  /// added); update every cost.
  pub(crate) fn add<W: Widths>(&mut self, t: TermId, widths: &W) {
    if self.epoch == u32::MAX {
      self.changed.fill(0);
      self.spine_dirty.fill(0);
      self.queued.fill(0);
      self.epoch = 0;
    }
    self.epoch += 1;
    let ep = self.epoch;
    let nodes = self.nodes;
    self.queued[ix(t)] = ep;
    self.heap.push(std::cmp::Reverse(t));
    while let Some(std::cmp::Reverse(x)) = self.heap.pop() {
      let xi = ix(x);
      let mut w = 0u64;
      let c = {
        let costs = &self.costs;
        eval_node(nodes, self.own, x, widths, &|y| costs[ix(y)], false, &mut w)
          .0
      };
      self.total = self.total - u128::from(self.term_work[xi]) + u128::from(w);
      self.term_work[xi] = w;
      if c != self.costs[xi] {
        self.costs[xi] = c;
        self.changed[xi] = ep;
      }
      let changed = |y: TermId| self.changed[ix(y)] == ep;
      // Whether a value read along the spine of `y` (side costs, widths of
      // continuing successors, the cost of the natural tail) changed.
      let spine_inputs = |y: TermId, side: TermId, next: TermId| {
        changed(side)
          || if nodes[ix(next)].family() == nodes[ix(y)].family() {
            next == t || self.spine_dirty[ix(next)] == ep
          } else {
            changed(next)
          }
      };
      if let Some((side, next)) = spine_parts(&nodes[xi])
        && spine_inputs(x, side, next)
      {
        self.spine_dirty[xi] = ep;
      }
      let x_changed = changed(x);
      let x_spine = x == t || self.spine_dirty[xi] == ep;
      let parents = self.parents;
      for &p in &parents[xi] {
        let pi = ix(p);
        if self.queued[pi] == ep {
          continue;
        }
        let reads = match spine_parts(&nodes[pi]) {
          Some((side, next)) => {
            (side == x && x_changed)
              || (next == x
                && if nodes[xi].family() == nodes[pi].family() {
                  x_spine
                } else {
                  x_changed
                })
          },
          None => x_changed,
        };
        if reads {
          self.queued[pi] = ep;
          self.heap.push(std::cmp::Reverse(p));
        }
      }
    }
  }
}

/// Side child and spine successor of an App/Lam/All node.
fn spine_parts(node: &Node) -> Option<(TermId, TermId)> {
  match node {
    Node::App(f, a) => Some((*a, *f)),
    Node::Lam(_, ty, b) | Node::All(_, _, ty, b) => Some((*ty, *b)),
    _ => None,
  }
}

fn internal(msg: &str) -> SharingError {
  SharingError::Internal(msg.to_string())
}

/// The spine successor of a telescope node.
fn spine_next(node: &Node) -> Option<TermId> {
  match node {
    Node::App(f, _) => Some(*f),
    Node::Lam(_, _, b) | Node::All(_, _, _, b) => Some(*b),
    _ => None,
  }
}

/// Materialize the byte-least minimum-length standalone expression of each
/// target under a fixed dictionary, given `costs = C_M` for every term.
pub(crate) fn materialize<D: Indices>(
  nodes: &[Node],
  own: &[Len],
  dict: &D,
  costs: &[Len],
  targets: &[TermId],
  work: &mut u64,
) -> Result<Vec<Arc<Expr>>, SharingError> {
  let Some(&top) = targets.iter().max() else {
    return Ok(Vec::new());
  };
  let top = ix(top);
  let mut choice: Vec<Option<Choice>> = vec![None; top + 1];
  let mut needed = vec![false; top + 1];
  for &t in targets {
    needed[ix(t)] = true;
  }
  // Top-down: decide every needed standalone occurrence. Needed children
  // have smaller IDs, so one descending sweep suffices.
  for t in (0..=top).rev() {
    if !needed[t] {
      continue;
    }
    let tid = TermId::try_from(t).map_err(|_e| internal("term id"))?;
    let (_, ch) =
      eval_node(nodes, own, tid, dict, &|x| costs[ix(x)], true, work);
    choice[t] = Some(ch);
    match ch {
      Choice::Share => {},
      Choice::Inline => {
        for &c in nodes[t].children().as_slice() {
          needed[ix(c)] = true;
        }
      },
      Choice::Telescope(j) => {
        if j == 0 {
          return Err(internal("telescope choice without an option"));
        }
        let mut cur = tid;
        for _ in 0..j {
          *work = work.saturating_add(1);
          let node = &nodes[ix(cur)];
          match node {
            Node::App(_, a) => needed[ix(*a)] = true,
            Node::Lam(_, ty, _) | Node::All(_, _, ty, _) => {
              needed[ix(*ty)] = true;
            },
            _ => return Err(internal("telescope walked off its spine")),
          }
          cur = spine_next(node).ok_or_else(|| internal("spine"))?;
        }
        if nodes[ix(cur)].family() != nodes[t].family() {
          needed[ix(cur)] = true;
        }
      },
    }
  }
  // Bottom-up: build each needed standalone representation once.
  let mut rep: Vec<Option<Arc<Expr>>> = vec![None; top + 1];
  let get = |rep: &Vec<Option<Arc<Expr>>>, c: TermId| {
    rep.get(ix(c)).cloned().flatten().ok_or_else(|| internal("missing child"))
  };
  for t in 0..=top {
    let Some(ch) = choice[t] else { continue };
    let tid = TermId::try_from(t).map_err(|_e| internal("term id"))?;
    let node = &nodes[t];
    let e = match ch {
      Choice::Share => {
        Expr::Share(dict.index(tid).ok_or_else(|| internal("share index"))?)
      },
      Choice::Inline => {
        let mut kids: Vec<Arc<Expr>> = Vec::new();
        for &c in node.children().as_slice() {
          kids.push(get(&rep, c)?);
        }
        let slot = |c: TermId| {
          let pos = node.children().as_slice().iter().position(|&x| x == c);
          kids[pos.unwrap_or(0)].clone()
        };
        node.to_expr(slot)
      },
      Choice::Telescope(j) => {
        let mut spine = Vec::new();
        let mut cur = tid;
        for _ in 0..j {
          spine.push(cur);
          cur = spine_next(&nodes[ix(cur)]).ok_or_else(|| internal("spine"))?;
        }
        let mut e = if nodes[ix(cur)].family() == node.family() {
          Arc::new(Expr::Share(
            dict.index(cur).ok_or_else(|| internal("cut index"))?,
          ))
        } else {
          get(&rep, cur)?
        };
        for &s in spine.iter().rev() {
          e = Arc::new(match &nodes[ix(s)] {
            Node::App(_, a) => Expr::App(e, get(&rep, *a)?),
            Node::Lam(c, ty, _) => Expr::Lam(*c, get(&rep, *ty)?, e),
            Node::All(c, v, ty, _) => Expr::All(*c, *v, get(&rep, *ty)?, e),
            _ => return Err(internal("telescope rebuild")),
          });
        }
        rep[t] = Some(e);
        continue;
      },
    };
    rep[t] = Some(Arc::new(e));
  }
  targets.iter().map(|&t| get(&rep, t)).collect()
}

/// [`materialize`] with scratch space reused across calls on one DAG: the
/// same choices, expressions and work, but the time of a call is linear in
/// the terms it writes, not in the largest target's ID.
///
/// The needed terms are decided in decreasing ID (a max-heap; a needed term
/// is only ever marked by a larger one, so every term is decided once, after
/// all its users, exactly as the descending sweep of [`materialize`]), then
/// built in increasing ID.
pub(crate) struct Materializer {
  /// `stamp[t] == epoch`: `t` is needed in the current call.
  stamp: Vec<u32>,
  epoch: u32,
  choice: Vec<Choice>,
  rep: Vec<Option<Arc<Expr>>>,
  heap: std::collections::BinaryHeap<TermId>,
  /// Needed terms in decision (decreasing) order.
  decided: Vec<TermId>,
}

impl Materializer {
  pub(crate) fn new(n: usize) -> Self {
    Materializer {
      stamp: vec![0; n],
      epoch: 0,
      choice: vec![Choice::Share; n],
      rep: vec![None; n],
      heap: std::collections::BinaryHeap::new(),
      decided: Vec::new(),
    }
  }

  fn need(&mut self, t: TermId) {
    let i = ix(t);
    if self.stamp[i] != self.epoch {
      self.stamp[i] = self.epoch;
      self.heap.push(t);
    }
  }

  /// [`materialize`]`(nodes, own, dict, costs, targets, work)`.
  pub(crate) fn run<D: Indices>(
    &mut self,
    nodes: &[Node],
    own: &[Len],
    dict: &D,
    costs: &[Len],
    targets: &[TermId],
    work: &mut u64,
  ) -> Result<Vec<Arc<Expr>>, SharingError> {
    if self.epoch == u32::MAX {
      self.stamp.fill(0);
      self.epoch = 0;
    }
    self.epoch += 1;
    self.heap.clear();
    self.decided.clear();
    for &t in targets {
      self.need(t);
    }
    // Top-down: decide every needed standalone occurrence.
    while let Some(tid) = self.heap.pop() {
      let t = ix(tid);
      let (_, ch) =
        eval_node(nodes, own, tid, dict, &|x| costs[ix(x)], true, work);
      self.choice[t] = ch;
      self.decided.push(tid);
      match ch {
        Choice::Share => {},
        Choice::Inline => {
          for &c in nodes[t].children().as_slice() {
            self.need(c);
          }
        },
        Choice::Telescope(j) => {
          if j == 0 {
            return Err(internal("telescope choice without an option"));
          }
          let mut cur = tid;
          for _ in 0..j {
            *work = work.saturating_add(1);
            let node = &nodes[ix(cur)];
            match node {
              Node::App(_, a) => self.need(*a),
              Node::Lam(_, ty, _) | Node::All(_, _, ty, _) => self.need(*ty),
              _ => return Err(internal("telescope walked off its spine")),
            }
            cur = spine_next(node).ok_or_else(|| internal("spine"))?;
          }
          if nodes[ix(cur)].family() != nodes[t].family() {
            self.need(cur);
          }
        },
      }
    }
    // Bottom-up: build each needed standalone representation once.
    let get = |rep: &[Option<Arc<Expr>>], c: TermId| {
      rep.get(ix(c)).cloned().flatten().ok_or_else(|| internal("missing child"))
    };
    for k in (0..self.decided.len()).rev() {
      let tid = self.decided[k];
      let t = ix(tid);
      let node = &nodes[t];
      let rep = &self.rep;
      let e = match self.choice[t] {
        Choice::Share => Arc::new(Expr::Share(
          dict.index(tid).ok_or_else(|| internal("share index"))?,
        )),
        Choice::Inline => {
          let mut kids: Vec<Arc<Expr>> = Vec::new();
          for &c in node.children().as_slice() {
            kids.push(get(rep, c)?);
          }
          let slot = |c: TermId| {
            let pos = node.children().as_slice().iter().position(|&x| x == c);
            kids[pos.unwrap_or(0)].clone()
          };
          Arc::new(node.to_expr(slot))
        },
        Choice::Telescope(j) => {
          let mut spine = Vec::new();
          let mut cur = tid;
          for _ in 0..j {
            spine.push(cur);
            cur =
              spine_next(&nodes[ix(cur)]).ok_or_else(|| internal("spine"))?;
          }
          let mut e = if nodes[ix(cur)].family() == node.family() {
            Arc::new(Expr::Share(
              dict.index(cur).ok_or_else(|| internal("cut index"))?,
            ))
          } else {
            get(rep, cur)?
          };
          for &s in spine.iter().rev() {
            e = Arc::new(match &nodes[ix(s)] {
              Node::App(_, a) => Expr::App(e, get(rep, *a)?),
              Node::Lam(c, ty, _) => Expr::Lam(*c, get(rep, *ty)?, e),
              Node::All(c, v, ty, _) => Expr::All(*c, *v, get(rep, *ty)?, e),
              _ => return Err(internal("telescope rebuild")),
            });
          }
          e
        },
      };
      self.rep[t] = Some(e);
    }
    let out: Result<Vec<Arc<Expr>>, SharingError> =
      targets.iter().map(|&t| get(&self.rep, t)).collect();
    for &t in &self.decided {
      self.rep[ix(t)] = None;
    }
    out
  }
}

/// `C_M(t)` for a fixed dictionary (§5).
pub fn dictionary_cost(
  dag: &SharingDag,
  dict: &FixedDictionary,
  t: TermId,
) -> Len {
  let own: Vec<Len> = dag.nodes().iter().map(Node::own_len).collect();
  let mut work = 0;
  let costs = all_costs(dag.nodes(), &own, dict, &mut work);
  costs.get(ix(t)).copied().unwrap_or(Len::OVERFLOW)
}

/// The byte-least minimum-length standalone expression of each target under
/// a fixed dictionary; Shares use the dictionary's actual indices.
pub fn materialize_with_dictionary(
  dag: &SharingDag,
  dict: &FixedDictionary,
  targets: &[TermId],
) -> Result<Vec<Arc<Expr>>, SharingError> {
  if targets.iter().any(|&t| ix(t) >= dag.len()) {
    return Err(internal("target out of range"));
  }
  let own: Vec<Len> = dag.nodes().iter().map(Node::own_len).collect();
  let mut work = 0;
  let costs = all_costs(dag.nodes(), &own, dict, &mut work);
  materialize(dag.nodes(), &own, dict, &costs, targets, &mut work)
}

/// A dictionary with one term's own Share hidden: the top of that term's
/// table entry, which may not reference itself.
pub(crate) struct Hide<'a, D> {
  pub(crate) inner: &'a D,
  pub(crate) hidden: TermId,
}

impl<D: Widths> Widths for Hide<'_, D> {
  fn width(&self, t: TermId) -> Option<u64> {
    if t == self.hidden { None } else { self.inner.width(t) }
  }
}

impl<D: Indices> Indices for Hide<'_, D> {
  fn index(&self, t: TermId) -> Option<u64> {
    if t == self.hidden { None } else { self.inner.index(t) }
  }
}

/// Real table indices with every Share priced at one uniform width.
pub(crate) struct UniformIndex {
  pub(crate) index: Vec<Option<u64>>,
  pub(crate) width: u64,
}

impl Widths for UniformIndex {
  fn width(&self, t: TermId) -> Option<u64> {
    self.index[ix(t)].map(|_| self.width)
  }
}

impl Indices for UniformIndex {
  fn index(&self, t: TermId) -> Option<u64> {
    self.index[ix(t)]
  }
}

/// Materialize a table given in dependency order (every stored descendant
/// of an entry precedes it) and the roots, from one evaluation `costs` of the
/// whole dictionary `dict`. In such an order each entry can use every stored
/// term that can occur inside it and no other, so the full dictionary prices
/// and builds it exactly. Entry tops take their best non-Share choice; every
/// nested occurrence takes its standalone choice. Returns entries, roots and
/// the predicted cost `sum inline(entry) + sum C(root)` (without the count).
pub(crate) fn materialize_dependent<D: Indices>(
  nodes: &[Node],
  own: &[Len],
  dict: &D,
  costs: &[Len],
  table: &[TermId],
  roots: &[TermId],
  work: &mut u64,
) -> Result<(Vec<Arc<Expr>>, Vec<Arc<Expr>>, Len), SharingError> {
  let n = nodes.len();
  let mut predicted = Len::ZERO;
  let mut entry_choice: Vec<Choice> = Vec::with_capacity(table.len());
  let mut needed = vec![false; n];
  let mark_children =
    |t: TermId, ch: Choice, needed: &mut Vec<bool>, work: &mut u64| match ch {
      Choice::Share => Ok(()),
      Choice::Inline => {
        for &c in nodes[ix(t)].children().as_slice() {
          needed[ix(c)] = true;
        }
        Ok(())
      },
      Choice::Telescope(j) => {
        if j == 0 {
          return Err(internal("telescope choice without an option"));
        }
        let mut cur = t;
        for _ in 0..j {
          *work = work.saturating_add(1);
          let node = &nodes[ix(cur)];
          match node {
            Node::App(_, a) => needed[ix(*a)] = true,
            Node::Lam(_, ty, _) | Node::All(_, _, ty, _) => {
              needed[ix(*ty)] = true
            },
            _ => return Err(internal("telescope walked off its spine")),
          }
          cur = spine_next(node).ok_or_else(|| internal("spine"))?;
        }
        if nodes[ix(cur)].family() != nodes[ix(t)].family() {
          needed[ix(cur)] = true;
        }
        Ok(())
      },
    };
  for &t in table {
    let hide = Hide { inner: dict, hidden: t };
    let (c, ch) =
      eval_node(nodes, own, t, &hide, &|x| costs[ix(x)], true, work);
    if ch == Choice::Share {
      return Err(internal("entry top chose a Share"));
    }
    predicted = predicted.plus(c);
    mark_children(t, ch, &mut needed, work)?;
    entry_choice.push(ch);
  }
  for &r in roots {
    needed[ix(r)] = true;
    predicted = predicted.plus(costs[ix(r)]);
  }
  let mut choice: Vec<Option<Choice>> = vec![None; n];
  for t in (0..n).rev() {
    if !needed[t] {
      continue;
    }
    let tid = TermId::try_from(t).map_err(|_e| internal("term id"))?;
    let (c, ch) =
      eval_node(nodes, own, tid, dict, &|x| costs[ix(x)], true, work);
    if c != costs[t] {
      return Err(internal("standalone choice differs from C_M"));
    }
    choice[t] = Some(ch);
    mark_children(tid, ch, &mut needed, work)?;
  }
  let mut rep: Vec<Option<Arc<Expr>>> = vec![None; n];
  let get = |rep: &Vec<Option<Arc<Expr>>>, c: TermId| {
    rep.get(ix(c)).cloned().flatten().ok_or_else(|| internal("missing child"))
  };
  let build = |t: TermId,
               ch: Choice,
               rep: &Vec<Option<Arc<Expr>>>|
   -> Result<Arc<Expr>, SharingError> {
    let node = &nodes[ix(t)];
    Ok(match ch {
      Choice::Share => Arc::new(Expr::Share(
        dict.index(t).ok_or_else(|| internal("share index"))?,
      )),
      Choice::Inline => {
        let mut kids: Vec<Arc<Expr>> = Vec::new();
        for &c in node.children().as_slice() {
          kids.push(get(rep, c)?);
        }
        let slot = |c: TermId| {
          let pos = node.children().as_slice().iter().position(|&x| x == c);
          kids[pos.unwrap_or(0)].clone()
        };
        Arc::new(node.to_expr(slot))
      },
      Choice::Telescope(j) => {
        let mut spine = Vec::new();
        let mut cur = t;
        for _ in 0..j {
          spine.push(cur);
          cur = spine_next(&nodes[ix(cur)]).ok_or_else(|| internal("spine"))?;
        }
        let mut e = if nodes[ix(cur)].family() == node.family() {
          Arc::new(Expr::Share(
            dict.index(cur).ok_or_else(|| internal("cut index"))?,
          ))
        } else {
          get(rep, cur)?
        };
        for &s in spine.iter().rev() {
          e = Arc::new(match &nodes[ix(s)] {
            Node::App(_, a) => Expr::App(e, get(rep, *a)?),
            Node::Lam(c, ty, _) => Expr::Lam(*c, get(rep, *ty)?, e),
            Node::All(c, v, ty, _) => Expr::All(*c, *v, get(rep, *ty)?, e),
            _ => return Err(internal("telescope rebuild")),
          });
        }
        e
      },
    })
  };
  for t in 0..n {
    if let Some(ch) = choice[t] {
      let tid = TermId::try_from(t).map_err(|_e| internal("term id"))?;
      let e = build(tid, ch, &rep)?;
      rep[t] = Some(e);
    }
  }
  let mut entries = Vec::with_capacity(table.len());
  for (&t, &ch) in table.iter().zip(&entry_choice) {
    entries.push(build(t, ch, &rep)?);
  }
  let roots_out =
    roots.iter().map(|&r| get(&rep, r)).collect::<Result<_, _>>()?;
  Ok((entries, roots_out, predicted))
}
