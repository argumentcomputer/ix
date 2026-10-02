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
  edges: &'a ReadEdges,
  eval: Evaluation,
  /// Stamps of the current step: cost changed, spine-dirty.
  changed: Vec<u32>,
  spine_dirty: Vec<u32>,
  epoch: u32,
  /// The terms queued for evaluation in the current step, as a bit set.
  queued: Vec<u64>,
}

/// One evaluation of a dictionary ([`all_costs`]) with the work of every
/// term.
#[derive(Clone)]
pub(crate) struct Evaluation {
  pub(crate) costs: Vec<Len>,
  term_work: Vec<u64>,
  total: u128,
}

impl Evaluation {
  /// [`all_costs`] of `widths`, keeping each term's work.
  pub(crate) fn new<W: Widths>(
    nodes: &[Node],
    own: &[Len],
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
    Evaluation { costs, term_work, total }
  }

  /// The work [`all_costs`] counts (it saturates; the per-term counts are
  /// small).
  pub(crate) fn work(&self) -> u64 {
    u64::try_from(self.total).unwrap_or(u64::MAX)
  }
}

/// The parent edges of a DAG grouped by child (`edges[start[x]..start[x +
/// 1]]` are the distinct parents of `x`), each tagged with what the parent's
/// evaluation reads of `x`: [`READS_COST`] and/or [`READS_SPINE`].
pub(crate) struct ReadEdges {
  start: Vec<usize>,
  edges: Vec<(TermId, u8)>,
}

/// The parent reads the cost of the child (a non-telescope child, a side
/// child, or a spine successor of another family).
const READS_COST: u8 = 1;
/// The child continues the parent's spine: the parent reads its width and
/// the values along its spine.
const READS_SPINE: u8 = 2;

impl ReadEdges {
  pub(crate) fn new(nodes: &[Node]) -> Self {
    let n = nodes.len();
    let reads = |p: &Node| -> [(TermId, u8); 3] {
      match spine_parts(p) {
        Some((side, next)) => {
          let next_reads = if nodes[ix(next)].family() == p.family() {
            READS_SPINE
          } else {
            READS_COST
          };
          if side == next {
            [(side, READS_COST | next_reads), (0, 0), (0, 0)]
          } else {
            [(side, READS_COST), (next, next_reads), (0, 0)]
          }
        },
        None => {
          let mut out = [(0, 0); 3];
          for (slot, &c) in p.children().as_slice().iter().enumerate() {
            match out[..slot].iter().position(|&(d, f)| f != 0 && d == c) {
              Some(_) => {},
              None => out[slot] = (c, READS_COST),
            }
          }
          out
        },
      }
    };
    // Offsets are `usize`: there are up to three edges per node, more than
    // `u32` holds for the largest DAGs the limits admit.
    let mut start = vec![0usize; n + 1];
    for node in nodes {
      for (c, f) in reads(node) {
        if f != 0 {
          start[ix(c) + 1] += 1;
        }
      }
    }
    for i in 0..n {
      start[i + 1] += start[i];
    }
    let mut fill: Vec<usize> = start[..n].to_vec();
    let mut edges: Vec<(TermId, u8)> = vec![(0, 0); start[n]];
    for (p, node) in nodes.iter().enumerate() {
      let p = TermId::try_from(p).unwrap_or(TermId::MAX);
      for (c, f) in reads(node) {
        if f != 0 {
          edges[fill[ix(c)]] = (p, f);
          fill[ix(c)] += 1;
        }
      }
    }
    ReadEdges { start, edges }
  }

  fn of(&self, x: usize) -> &[(TermId, u8)] {
    &self.edges[self.start[x]..self.start[x + 1]]
  }
}

impl<'a> IncrementalCosts<'a> {
  /// Continue from the evaluation `eval` of the current dictionary.
  pub(crate) fn new(
    nodes: &'a [Node],
    own: &'a [Len],
    edges: &'a ReadEdges,
    eval: Evaluation,
  ) -> Self {
    let n = nodes.len();
    IncrementalCosts {
      nodes,
      own,
      edges,
      eval,
      changed: vec![0; n],
      spine_dirty: vec![0; n],
      epoch: 0,
      queued: vec![0; n.div_ceil(64)],
    }
  }

  /// `C_M` of every term under the current dictionary.
  pub(crate) fn costs(&self) -> &[Len] {
    &self.eval.costs
  }

  /// The work [`all_costs`] counts for the current dictionary (saturating).
  pub(crate) fn work(&self) -> u64 {
    self.eval.work()
  }

  /// `widths` is the previous dictionary with `t`'s width changed (`t` was
  /// added); update every cost.
  pub(crate) fn add<W: Widths>(&mut self, t: TermId, widths: &W) {
    if self.epoch == u32::MAX {
      self.changed.fill(0);
      self.spine_dirty.fill(0);
      self.epoch = 0;
    }
    self.epoch += 1;
    let ep = self.epoch;
    let nodes = self.nodes;
    // Queued terms are only ever larger than the term being evaluated, so
    // one forward sweep over the bit set evaluates them in increasing ID.
    let mut last = ix(t);
    self.queued[last / 64] |= 1 << (last % 64);
    let mut word = last / 64;
    while word <= last / 64 {
      let bits = self.queued[word];
      if bits == 0 {
        word += 1;
        continue;
      }
      let bit = bits.trailing_zeros() as usize;
      self.queued[word] &= !(1u64 << bit);
      let xi = word * 64 + bit;
      let x = TermId::try_from(xi).unwrap_or(TermId::MAX);
      let mut w = 0u64;
      let c = {
        let costs = &self.eval.costs;
        eval_node(nodes, self.own, x, widths, &|y| costs[ix(y)], false, &mut w)
          .0
      };
      let ev = &mut self.eval;
      ev.total = ev.total - u128::from(ev.term_work[xi]) + u128::from(w);
      ev.term_work[xi] = w;
      if c != ev.costs[xi] {
        ev.costs[xi] = c;
        self.changed[xi] = ep;
      }
      let changed = |y: TermId| self.changed[ix(y)] == ep;
      // Whether a value read along the spine of `x` (side costs, widths of
      // continuing successors, the cost of the natural tail) changed.
      if let Some((side, next)) = spine_parts(&nodes[xi])
        && (changed(side)
          || if nodes[ix(next)].family() == nodes[xi].family() {
            next == t || self.spine_dirty[ix(next)] == ep
          } else {
            changed(next)
          })
      {
        self.spine_dirty[xi] = ep;
      }
      let x_changed = changed(x);
      let x_spine = x == t || self.spine_dirty[xi] == ep;
      if !x_changed && !x_spine {
        continue;
      }
      for &(p, f) in self.edges.of(xi) {
        if (f & READS_COST != 0 && x_changed)
          || (f & READS_SPINE != 0 && x_spine)
        {
          let pi = ix(p);
          self.queued[pi / 64] |= 1 << (pi % 64);
          last = last.max(pi);
        }
      }
    }
  }
}

/// The phase-3 evaluation of a growing dictionary that evaluates a term only
/// when its cost or its work is needed, with the work count of a full
/// [`all_costs`] evaluation of the current dictionary at every step.
///
/// **Work.** [`eval_node`] counts 1 for a term plus, for an App/Lam/All term
/// `t`, one per telescope option [`scan_telescope`] visits. When no term of
/// `t`'s spine (`t` and its same-family successors) is available, the scan
/// cannot stop before the natural end: no head is found before it and `t`
/// has no Share, so the bound it compares with, `min(best, share)`, stays
/// [`Len::OVERFLOW`], which no unsaturated length reaches. Its work is then
/// `1 + spine length` whatever the costs, and a non-telescope term's work is
/// always 1. Only the telescope terms with an available term on their spine
/// (`spined`; the set only grows) can have cost-dependent work; they are
/// evaluated again at every step where one of their inputs may have
/// changed. Every other term's last recorded work is its current work, so
/// the sum of the recorded work is the full evaluation's count. Saturation
/// is excluded up front ([`LazyCosts::applies`]): every cost of the empty
/// dictionary is below `2^62`, costs only decrease as terms become
/// available, and every partial length of a scan is at most the term's cost
/// of the empty dictionary plus a header and 2.
///
/// **Costs.** When a term becomes available, it and all its ancestors are
/// marked stale (the stale set is closed upward), and a stale term is
/// evaluated again only when it is needed: before a materialization, every
/// stale descendant of the targets (children first, so its inputs are
/// current), and every stale spined term at each step. Evaluating a term
/// from current inputs gives what a full evaluation gives.
pub(crate) struct LazyCosts<'a> {
  nodes: &'a [Node],
  own: &'a [Len],
  edges: &'a ReadEdges,
  eval: Evaluation,
  stale: Vec<bool>,
  spined: Vec<bool>,
  /// Scratch of `ensure`: visited marks of the current call.
  mark: Vec<u32>,
  epoch: u32,
  stack: Vec<TermId>,
  order: Vec<(TermId, bool)>,
}

impl<'a> LazyCosts<'a> {
  /// Whether the work argument applies: every cost of the empty dictionary
  /// (`base`) is below `2^62`.
  pub(crate) fn applies(base: &Evaluation) -> bool {
    base.costs.iter().all(|c| c.raw() < 1 << 62)
  }

  /// Continue from `eval`, the full evaluation of `widths`.
  pub(crate) fn new<W: Widths>(
    nodes: &'a [Node],
    own: &'a [Len],
    edges: &'a ReadEdges,
    eval: Evaluation,
    widths: &W,
  ) -> Self {
    let n = nodes.len();
    // `reach[t]`: `t` or a same-family successor on its spine is available.
    let mut reach = vec![false; n];
    let mut spined = vec![false; n];
    for t in 0..n {
      let tid = TermId::try_from(t).unwrap_or(TermId::MAX);
      let avail = widths.width(tid).is_some();
      if let Some((_, next)) = spine_parts(&nodes[t]) {
        let same = nodes[ix(next)].family() == nodes[t].family();
        reach[t] = avail || (same && reach[ix(next)]);
        spined[t] = reach[t];
      } else {
        reach[t] = avail;
      }
    }
    LazyCosts {
      nodes,
      own,
      edges,
      eval,
      stale: vec![false; n],
      spined,
      mark: vec![0; n],
      epoch: 0,
      stack: Vec::new(),
      order: Vec::new(),
    }
  }

  /// `C_M` of every term that is not stale; [`LazyCosts::prepare`] makes the
  /// descendants of targets current.
  pub(crate) fn costs(&self) -> &[Len] {
    &self.eval.costs
  }

  /// The work [`all_costs`] counts for the current dictionary (saturating).
  pub(crate) fn work(&self) -> u64 {
    self.eval.work()
  }

  /// Make the costs of `targets` and of all their descendants current.
  pub(crate) fn prepare<W: Widths>(&mut self, targets: &[TermId], widths: &W) {
    for &t in targets {
      self.ensure(t, widths);
    }
  }

  /// `widths` is the previous dictionary with `t` added.
  pub(crate) fn add<W: Widths>(&mut self, t: TermId, widths: &W) {
    let nodes = self.nodes;
    // `t` and every ancestor become stale.
    let mut due: Vec<TermId> = Vec::new();
    self.stack.clear();
    if !self.stale[ix(t)] {
      self.stale[ix(t)] = true;
      self.stack.push(t);
    }
    while let Some(x) = self.stack.pop() {
      if self.spined[ix(x)] {
        due.push(x);
      }
      for &(p, _) in self.edges.of(ix(x)) {
        if !self.stale[ix(p)] {
          self.stale[ix(p)] = true;
          self.stack.push(p);
        }
      }
    }
    // `t` and the terms whose spine reaches it are spined from now on. The
    // spined set is closed under spine predecessors, so the walk stops at a
    // term that already is.
    self.stack.clear();
    if spine_parts(&nodes[ix(t)]).is_some() && !self.spined[ix(t)] {
      self.spined[ix(t)] = true;
      self.stack.push(t);
    }
    while let Some(x) = self.stack.pop() {
      due.push(x);
      for &(p, f) in self.edges.of(ix(x)) {
        if f & READS_SPINE != 0 && !self.spined[ix(p)] {
          self.spined[ix(p)] = true;
          self.stack.push(p);
        }
      }
    }
    for x in due {
      self.ensure(x, widths);
    }
  }

  /// Evaluate the stale terms among `x` and its descendants, children
  /// first. The stale set is closed upward, so they are reached through
  /// stale terms only.
  fn ensure<W: Widths>(&mut self, x: TermId, widths: &W) {
    if !self.stale[ix(x)] {
      return;
    }
    if self.epoch == u32::MAX {
      self.mark.fill(0);
      self.epoch = 0;
    }
    self.epoch += 1;
    let ep = self.epoch;
    let nodes = self.nodes;
    // Post-order over the stale region: a term is evaluated after all its
    // stale descendants (which its evaluation may read). A term popped again
    // after its first visit is done: it cannot be its own descendant.
    let mut post: Vec<(TermId, bool)> = std::mem::take(&mut self.order);
    post.clear();
    post.push((x, false));
    while let Some((y, expanded)) = post.pop() {
      let yi = ix(y);
      if !expanded {
        if self.mark[yi] == ep {
          continue;
        }
        self.mark[yi] = ep;
        post.push((y, true));
        for &c in nodes[yi].children().as_slice() {
          if self.stale[ix(c)] && self.mark[ix(c)] != ep {
            post.push((c, false));
          }
        }
        continue;
      }
      let mut w = 0u64;
      let c = {
        let costs = &self.eval.costs;
        eval_node(nodes, self.own, y, widths, &|z| costs[ix(z)], false, &mut w)
          .0
      };
      let ev = &mut self.eval;
      ev.total = ev.total - u128::from(ev.term_work[yi]) + u128::from(w);
      ev.term_work[yi] = w;
      ev.costs[yi] = c;
      self.stale[yi] = false;
    }
    self.order = post;
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

/// Visit the terms whose standalone representations choice `ch` at `t`
/// needs: the children of an inline node; for a telescope of `j` spine
/// nodes, the side child of each spine node (one unit of `work` per spine
/// node), then the node after the spine unless the telescope stops at a
/// Share of it (a cut). Returns whether the choice is a telescope with a
/// cut.
fn for_each_needed(
  nodes: &[Node],
  t: TermId,
  ch: Choice,
  work: &mut u64,
  mut need: impl FnMut(TermId),
) -> Result<bool, SharingError> {
  match ch {
    Choice::Share => Ok(false),
    Choice::Inline => {
      for &c in nodes[ix(t)].children().as_slice() {
        need(c);
      }
      Ok(false)
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
          Node::App(_, a) => need(*a),
          Node::Lam(_, ty, _) | Node::All(_, _, ty, _) => need(*ty),
          _ => return Err(internal("telescope walked off its spine")),
        }
        cur = spine_next(node).ok_or_else(|| internal("spine"))?;
      }
      let cut = nodes[ix(cur)].family() == nodes[ix(t)].family();
      if !cut {
        need(cur);
      }
      Ok(cut)
    },
  }
}

/// The spine nodes of a telescope choice of `j` nodes at `t`, the node
/// after them, and whether the telescope stops at a Share of it (a cut).
fn telescope_parts(
  nodes: &[Node],
  t: TermId,
  j: u64,
) -> Result<(Vec<TermId>, TermId, bool), SharingError> {
  let mut spine = Vec::new();
  let mut cur = t;
  for _ in 0..j {
    spine.push(cur);
    cur = spine_next(&nodes[ix(cur)]).ok_or_else(|| internal("spine"))?;
  }
  let cut = nodes[ix(cur)].family() == nodes[ix(t)].family();
  Ok((spine, cur, cut))
}

/// The standalone representation of `c` built earlier, from `rep`.
fn built(
  rep: &[Option<Arc<Expr>>],
  c: TermId,
) -> Result<Arc<Expr>, SharingError> {
  rep.get(ix(c)).cloned().flatten().ok_or_else(|| internal("missing child"))
}

/// The expression of `t` written with choice `ch` under `dict`, the
/// standalone representations of the terms it needs read from `rep`.
fn build_choice<D: Indices>(
  nodes: &[Node],
  dict: &D,
  t: TermId,
  ch: Choice,
  rep: &[Option<Arc<Expr>>],
) -> Result<Arc<Expr>, SharingError> {
  let node = &nodes[ix(t)];
  Ok(match ch {
    Choice::Share => Arc::new(Expr::Share(
      dict.index(t).ok_or_else(|| internal("share index"))?,
    )),
    Choice::Inline => {
      let mut kids: Vec<Arc<Expr>> = Vec::new();
      for &c in node.children().as_slice() {
        kids.push(built(rep, c)?);
      }
      let slot = |c: TermId| {
        let pos = node.children().as_slice().iter().position(|&x| x == c);
        kids[pos.unwrap_or(0)].clone()
      };
      Arc::new(node.to_expr(slot))
    },
    Choice::Telescope(j) => {
      let (spine, cur, cut) = telescope_parts(nodes, t, j)?;
      let mut e = if cut {
        Arc::new(Expr::Share(
          dict.index(cur).ok_or_else(|| internal("cut index"))?,
        ))
      } else {
        built(rep, cur)?
      };
      for &s in spine.iter().rev() {
        e = Arc::new(match &nodes[ix(s)] {
          Node::App(_, a) => Expr::App(e, built(rep, *a)?),
          Node::Lam(c, ty, _) => Expr::Lam(*c, built(rep, *ty)?, e),
          Node::All(c, v, ty, _) => Expr::All(*c, *v, built(rep, *ty)?, e),
          _ => return Err(internal("telescope rebuild")),
        });
      }
      e
    },
  })
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
    for_each_needed(nodes, tid, ch, work, |c| needed[ix(c)] = true)?;
  }
  // Bottom-up: build each needed standalone representation once.
  let mut rep: Vec<Option<Arc<Expr>>> = vec![None; top + 1];
  for t in 0..=top {
    let Some(ch) = choice[t] else { continue };
    let tid = TermId::try_from(t).map_err(|_e| internal("term id"))?;
    rep[t] = Some(build_choice(nodes, dict, tid, ch, &rep)?);
  }
  targets.iter().map(|&t| built(&rep, t)).collect()
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
  rep: Vec<Option<Arc<Expr>>>,
  heap: std::collections::BinaryHeap<TermId>,
}

impl Materializer {
  pub(crate) fn new(n: usize) -> Self {
    Materializer {
      stamp: vec![0; n],
      epoch: 0,
      rep: vec![None; n],
      heap: std::collections::BinaryHeap::new(),
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
  #[cfg(test)]
  pub(crate) fn run<D: Indices>(
    &mut self,
    nodes: &[Node],
    own: &[Len],
    dict: &D,
    costs: &[Len],
    targets: &[TermId],
    work: &mut u64,
  ) -> Result<Vec<Arc<Expr>>, SharingError> {
    let plan = self.decide(nodes, own, dict, costs, targets, work)?;
    self.build(nodes, dict, &plan)
  }

  /// The decisions of [`Materializer::run`] (with all its work) without
  /// building the expressions: the needed terms with their choices, and the
  /// number of expression nodes [`Materializer::build`] allocates for them.
  pub(crate) fn decide<D: Indices>(
    &mut self,
    nodes: &[Node],
    own: &[Len],
    dict: &D,
    costs: &[Len],
    targets: &[TermId],
    work: &mut u64,
  ) -> Result<Plan, SharingError> {
    if self.epoch == u32::MAX {
      self.stamp.fill(0);
      self.epoch = 0;
    }
    self.epoch += 1;
    self.heap.clear();
    for &t in targets {
      self.need(t);
    }
    let mut plan =
      Plan { decided: Vec::new(), targets: targets.to_vec(), nodes: 0 };
    // Top-down: decide every needed standalone occurrence.
    while let Some(tid) = self.heap.pop() {
      let (_, ch) =
        eval_node(nodes, own, tid, dict, &|x| costs[ix(x)], true, work);
      plan.decided.push((tid, ch));
      plan.nodes = plan.nodes.saturating_add(match ch {
        Choice::Share | Choice::Inline => 1,
        Choice::Telescope(j) => j,
      });
      if for_each_needed(nodes, tid, ch, work, |c| self.need(c))? {
        // The cut: a Share of the spine node where the telescope stops.
        plan.nodes = plan.nodes.saturating_add(1);
      }
    }
    Ok(plan)
  }

  /// Build the expressions of `plan` (from [`Materializer::decide`] under a
  /// dictionary with the same indices as `dict` for the terms it shares).
  pub(crate) fn build<D: Indices>(
    &mut self,
    nodes: &[Node],
    dict: &D,
    plan: &Plan,
  ) -> Result<Vec<Arc<Expr>>, SharingError> {
    // Bottom-up: build each needed standalone representation once.
    for &(tid, ch) in plan.decided.iter().rev() {
      let e = build_choice(nodes, dict, tid, ch, &self.rep)?;
      self.rep[ix(tid)] = Some(e);
    }
    let out: Result<Vec<Arc<Expr>>, SharingError> =
      plan.targets.iter().map(|&t| built(&self.rep, t)).collect();
    for &(t, _) in &plan.decided {
      self.rep[ix(t)] = None;
    }
    out
  }
}

/// The decisions of one materialization ([`Materializer::decide`]): the
/// needed terms in decision (decreasing) order with their choices, the
/// targets, and the number of expression nodes the build allocates (one
/// per Share or inline node, one per spine node of a telescope and one for
/// a telescope's cut Share).
#[derive(Debug, PartialEq, Eq)]
pub(crate) struct Plan {
  decided: Vec<(TermId, Choice)>,
  targets: Vec<TermId>,
  pub(crate) nodes: u64,
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
pub(crate) fn decide_dependent<D: Indices>(
  nodes: &[Node],
  own: &[Len],
  dict: &D,
  costs: &[Len],
  table: &[TermId],
  roots: &[TermId],
  work: &mut u64,
) -> Result<DependentPlan, SharingError> {
  let n = nodes.len();
  let mut predicted = Len::ZERO;
  let mut entry_choice: Vec<Choice> = Vec::with_capacity(table.len());
  let mut needed = vec![false; n];
  let mark_children =
    |t: TermId, ch: Choice, needed: &mut Vec<bool>, work: &mut u64| {
      for_each_needed(nodes, t, ch, work, |c| needed[ix(c)] = true).map(|_| ())
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
  Ok(DependentPlan { entry_choice, choice, predicted })
}

/// The decisions of [`materialize_dependent`]: each entry's top choice,
/// the standalone choice of every needed term, and the predicted length.
pub(crate) struct DependentPlan {
  entry_choice: Vec<Choice>,
  choice: Vec<Option<Choice>>,
  pub(crate) predicted: Len,
}

/// What the expressions of a [`DependentPlan`] contain, computed without
/// building them: per table position the number of Shares of that entry in
/// all the expression trees (entries and roots, with multiplicity, as a walk
/// of each tree counts them), per entry the entries its expression shares
/// in pre-order of first occurrence, and the number of expression nodes the
/// build allocates (all pointer-distinct).
#[derive(Clone, Debug)]
pub(crate) struct PlanShares {
  pub(crate) refs: Vec<u64>,
  pub(crate) deps: Vec<Vec<TermId>>,
  pub(crate) nodes: u64,
}

/// One item of the pre-order walk of [`DependentPlan::shares`].
#[derive(Clone, Copy)]
enum WalkItem {
  /// The standalone representation of a term (shared by its occurrences).
  Rep(TermId),
  /// A Share of a term.
  Shr(TermId),
}

impl DependentPlan {
  /// The children of the expression of `t` written with choice `ch`, in
  /// expression order (`Expr` children, left to right).
  fn items(
    nodes: &[Node],
    t: TermId,
    ch: Choice,
    out: &mut Vec<WalkItem>,
  ) -> Result<u64, SharingError> {
    out.clear();
    match ch {
      Choice::Share => {
        out.push(WalkItem::Shr(t));
        Ok(1)
      },
      Choice::Inline => {
        for &c in nodes[ix(t)].children().as_slice() {
          out.push(WalkItem::Rep(c));
        }
        Ok(1)
      },
      Choice::Telescope(j) => {
        let (spine, cur, cut) = telescope_parts(nodes, t, j)?;
        let head = if cut { WalkItem::Shr(cur) } else { WalkItem::Rep(cur) };
        // App: `App(App(head, a_{j-1}) .., a_0)`, so the head, then the
        // arguments from the deepest spine node up. Lam/All:
        // `Lam(ty_0, Lam(ty_1, .. head))`, so the binder types from the top,
        // then the head.
        if matches!(nodes[ix(t)], Node::App(..)) {
          out.push(head);
          for &s in spine.iter().rev() {
            if let Node::App(_, a) = nodes[ix(s)] {
              out.push(WalkItem::Rep(a));
            }
          }
        } else {
          for &s in &spine {
            match nodes[ix(s)] {
              Node::Lam(_, ty, _) | Node::All(_, _, ty, _) => {
                out.push(WalkItem::Rep(ty));
              },
              _ => return Err(internal("telescope walked off its spine")),
            }
          }
          out.push(head);
        }
        Ok(j + u64::from(cut))
      },
    }
  }

  /// See [`PlanShares`]; `pos[t]` is the table position of a stored term.
  pub(crate) fn shares(
    &self,
    nodes: &[Node],
    table: &[TermId],
    roots: &[TermId],
    pos: &dyn Fn(TermId) -> Option<usize>,
  ) -> Result<PlanShares, SharingError> {
    let n = nodes.len();
    let mut refs = vec![0u64; table.len()];
    let add_ref = |refs: &mut Vec<u64>, x: TermId, m: u64| {
      if let Some(r) = pos(x).and_then(|i| refs.get_mut(i)) {
        *r = r.saturating_add(m);
      }
    };
    let mut items: Vec<WalkItem> = Vec::new();
    // Occurrence counts of the standalone representations in all trees.
    let mut mult = vec![0u64; n];
    let mut count = 0u64;
    for &r in roots {
      mult[ix(r)] = mult[ix(r)].saturating_add(1);
    }
    for (&t, &ch) in table.iter().zip(&self.entry_choice) {
      count = count.saturating_add(Self::items(nodes, t, ch, &mut items)?);
      for &it in &items {
        match it {
          WalkItem::Rep(c) => mult[ix(c)] = mult[ix(c)].saturating_add(1),
          WalkItem::Shr(x) => add_ref(&mut refs, x, 1),
        }
      }
    }
    for t in (0..n).rev() {
      let Some(ch) = self.choice[t] else { continue };
      let tid = TermId::try_from(t).map_err(|_e| internal("term id"))?;
      count = count.saturating_add(Self::items(nodes, tid, ch, &mut items)?);
      let m = mult[t];
      if m == 0 {
        continue;
      }
      for &it in &items {
        match it {
          WalkItem::Rep(c) => mult[ix(c)] = mult[ix(c)].saturating_add(m),
          WalkItem::Shr(x) => add_ref(&mut refs, x, m),
        }
      }
    }
    // Per entry, the shared entries in pre-order of first occurrence. A
    // representation met again contributes nothing new, so each is walked
    // once per entry.
    let mut deps = Vec::with_capacity(table.len());
    let mut seen_rep = vec![0usize; n];
    let mut seen_dep = vec![0usize; n];
    let mut stack: Vec<WalkItem> = Vec::new();
    for (e, (&t, &ch)) in table.iter().zip(&self.entry_choice).enumerate() {
      let ep = e + 1;
      let mut ds: Vec<TermId> = Vec::new();
      Self::items(nodes, t, ch, &mut items)?;
      stack.clear();
      stack.extend(items.iter().rev());
      while let Some(it) = stack.pop() {
        match it {
          WalkItem::Shr(x) => {
            if seen_dep[ix(x)] != ep {
              seen_dep[ix(x)] = ep;
              ds.push(x);
            }
          },
          WalkItem::Rep(c) => {
            if seen_rep[ix(c)] == ep {
              continue;
            }
            seen_rep[ix(c)] = ep;
            let cch =
              self.choice[ix(c)].ok_or_else(|| internal("missing choice"))?;
            Self::items(nodes, c, cch, &mut items)?;
            stack.extend(items.iter().rev());
          },
        }
      }
      deps.push(ds);
    }
    Ok(PlanShares { refs, deps, nodes: count })
  }
}

/// The expressions of the decisions of [`decide_dependent`] for the same
/// `table` and `roots`: entries and roots.
pub(crate) fn build_dependent<D: Indices>(
  nodes: &[Node],
  dict: &D,
  plan: &DependentPlan,
  table: &[TermId],
  roots: &[TermId],
) -> Result<(Vec<Arc<Expr>>, Vec<Arc<Expr>>), SharingError> {
  let n = nodes.len();
  let DependentPlan { entry_choice, choice, .. } = plan;
  let mut rep: Vec<Option<Arc<Expr>>> = vec![None; n];
  for t in 0..n {
    if let Some(ch) = choice[t] {
      let tid = TermId::try_from(t).map_err(|_e| internal("term id"))?;
      rep[t] = Some(build_choice(nodes, dict, tid, ch, &rep)?);
    }
  }
  let mut entries = Vec::with_capacity(table.len());
  for (&t, &ch) in table.iter().zip(entry_choice) {
    entries.push(build_choice(nodes, dict, t, ch, &rep)?);
  }
  let roots_out =
    roots.iter().map(|&r| built(&rep, r)).collect::<Result<_, _>>()?;
  Ok((entries, roots_out))
}
