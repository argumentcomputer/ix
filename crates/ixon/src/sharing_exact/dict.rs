//! The fixed-dictionary optimizer `C_M` (§5) and byte-least materialization.
//!
//! For a dictionary `M` (available terms and their Share widths), `C_M(t)`
//! is the minimum length of a standalone expression expanding to `t`. The
//! options at `t` are a Share of `t` (if available) and its inline
//! constructor. For App, Lam and All the inline constructor is a telescope
//! over the maximal same-family spine `t = t_0, t_1, ..., t_l` (App follows
//! the function, Lam/All the body; `t_l` is the first node of another
//! constructor). A telescope of `j` spine nodes costs its Tag4 header for
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
/// reach that value, and among equal lengths it keeps the `j` whose Tag4
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
/// are ordered by their Tag4 header bytes, which differ for distinct `j`.
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
