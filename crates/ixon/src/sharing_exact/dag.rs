//! Hash-consed structural DAG of the expanded roots and its §3.2 term IDs.
//!
//! Interning uses a hash map keyed by the complete structural [`Node`]; the
//! hash only accelerates lookup and equality is decided by `Eq` on every
//! constructor, scalar, contract and child, so hash collisions cannot merge
//! distinct terms. Share leaves of an input table resolve to the interned ID
//! of the referenced entry, which expands the table without materializing its
//! occurrence tree.

use std::sync::Arc;

use rustc_hash::{FxHashMap, FxHashSet};

use super::cost::{Len, tag0_len, tag4_len};
use super::{
  FormatBound, MalformedSharing, Meter, ShareLocation, SharingError,
};
use crate::contract::{
  BinderContract, LetContract, ValueContract, pack_all_contract,
};
use crate::expr::Expr;

/// Structural term ID: position in the §3.2 order.
pub type TermId = u32;

pub(crate) fn ix(t: TermId) -> usize {
  usize::try_from(t).unwrap_or(usize::MAX)
}

/// One distinct expanded subterm; children are term IDs.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Node {
  Sort(u64),
  Var(u64),
  Ref(u64, Vec<u64>),
  Rec(u64, Vec<u64>),
  Prj(u64, u64, TermId),
  Str(u64),
  Nat(u64),
  App(TermId, TermId),
  Lam(BinderContract, TermId, TermId),
  All(BinderContract, ValueContract, TermId, TermId),
  Let(LetContract, TermId, TermId, TermId),
}

/// Ordered children of a node (at most three).
#[derive(Clone, Copy, Debug)]
pub struct Children {
  ids: [TermId; 3],
  len: u8,
}

impl Children {
  pub fn as_slice(&self) -> &[TermId] {
    &self.ids[..usize::from(self.len)]
  }
}

/// Telescope family of App, Lam and All nodes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Family {
  App,
  Lam,
  All,
}

/// §3.2 sort key: constructor tag, scalar payload, ordered child IDs. The
/// derived order compares fields in that order, integers numerically and
/// vectors lexicographically with a proper prefix first.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct NodeKey {
  pub tag: u8,
  pub scalars: Vec<u64>,
  pub children: Vec<TermId>,
}

fn u64_len(n: usize) -> u64 {
  u64::try_from(n).unwrap_or(u64::MAX)
}

impl Node {
  /// Constructor tag (the TagN expression flag).
  pub fn tag(&self) -> u8 {
    match self {
      Node::Sort(_) => Expr::FLAG_SORT,
      Node::Var(_) => Expr::FLAG_VAR,
      Node::Ref(..) => Expr::FLAG_REF,
      Node::Rec(..) => Expr::FLAG_REC,
      Node::Prj(..) => Expr::FLAG_PRJ,
      Node::Str(_) => Expr::FLAG_STR,
      Node::Nat(_) => Expr::FLAG_NAT,
      Node::App(..) => Expr::FLAG_APP,
      Node::Lam(..) => Expr::FLAG_LAM,
      Node::All(..) => Expr::FLAG_ALL,
      Node::Let(..) => Expr::FLAG_LET,
    }
  }

  /// The §3.2 scalar payload vector.
  pub fn scalars(&self) -> Vec<u64> {
    match self {
      Node::Sort(n) | Node::Var(n) | Node::Str(n) | Node::Nat(n) => vec![*n],
      Node::Ref(n, us) | Node::Rec(n, us) => {
        let mut v = Vec::with_capacity(us.len() + 2);
        v.push(*n);
        v.push(u64_len(us.len()));
        v.extend_from_slice(us);
        v
      },
      Node::Prj(t, f, _) => vec![*t, *f],
      Node::App(..) => vec![],
      Node::Lam(c, ..) => vec![u64::from(c.to_bits())],
      Node::All(c, v, ..) => vec![u64::from(pack_all_contract(*c, *v))],
      Node::Let(c, ..) => vec![c.flags(), u64::from(c.binder.to_bits())],
    }
  }

  pub fn children(&self) -> Children {
    let (ids, len) = match self {
      Node::Sort(_)
      | Node::Var(_)
      | Node::Ref(..)
      | Node::Rec(..)
      | Node::Str(_)
      | Node::Nat(_) => ([0; 3], 0),
      Node::Prj(_, _, v) => ([*v, 0, 0], 1),
      Node::App(a, b) | Node::Lam(_, a, b) | Node::All(_, _, a, b) => {
        ([*a, *b, 0], 2)
      },
      Node::Let(_, a, b, c) => ([*a, *b, *c], 3),
    };
    Children { ids, len }
  }

  pub(crate) fn family(&self) -> Option<Family> {
    match self {
      Node::App(..) => Some(Family::App),
      Node::Lam(..) => Some(Family::Lam),
      Node::All(..) => Some(Family::All),
      _ => None,
    }
  }

  /// Bytes this node contributes besides its children and, for App/Lam/All,
  /// besides the per-telescope TagN header: the whole encoding of a leaf,
  /// Prj/Let headers, and the contract byte of each Lam/All binder.
  pub(crate) fn own_len(&self) -> Len {
    match self {
      Node::Sort(n) | Node::Var(n) | Node::Str(n) | Node::Nat(n) => {
        Len::new(tag4_len(*n))
      },
      Node::Ref(n, us) | Node::Rec(n, us) => {
        let mut len =
          Len::new(tag4_len(u64_len(us.len()))).plus_u64(tag0_len(*n));
        for u in us {
          len = len.plus_u64(tag0_len(*u));
        }
        len
      },
      Node::Prj(t, f, _) => Len::new(tag4_len(*f)).plus_u64(tag0_len(*t)),
      Node::App(..) => Len::ZERO,
      Node::Lam(..) | Node::All(..) => Len::new(1),
      Node::Let(c, ..) => Len::new(tag4_len(c.flags())).plus_u64(1),
    }
  }

  fn map_children(&self, f: impl Fn(TermId) -> TermId) -> Node {
    match self {
      Node::Sort(_)
      | Node::Var(_)
      | Node::Ref(..)
      | Node::Rec(..)
      | Node::Str(_)
      | Node::Nat(_) => self.clone(),
      Node::Prj(t, i, v) => Node::Prj(*t, *i, f(*v)),
      Node::App(a, b) => Node::App(f(*a), f(*b)),
      Node::Lam(c, a, b) => Node::Lam(*c, f(*a), f(*b)),
      Node::All(c, v, a, b) => Node::All(*c, *v, f(*a), f(*b)),
      Node::Let(c, a, b, d) => Node::Let(*c, f(*a), f(*b), f(*d)),
    }
  }

  /// Rebuild an expression node with the given child expressions.
  pub fn to_expr(&self, child: impl Fn(TermId) -> Arc<Expr>) -> Expr {
    match self {
      Node::Sort(n) => Expr::Sort(*n),
      Node::Var(n) => Expr::Var(*n),
      Node::Ref(n, us) => Expr::Ref(*n, us.clone()),
      Node::Rec(n, us) => Expr::Rec(*n, us.clone()),
      Node::Prj(t, i, v) => Expr::Prj(*t, *i, child(*v)),
      Node::Str(n) => Expr::Str(*n),
      Node::Nat(n) => Expr::Nat(*n),
      Node::App(a, b) => Expr::App(child(*a), child(*b)),
      Node::Lam(c, a, b) => Expr::Lam(*c, child(*a), child(*b)),
      Node::All(c, v, a, b) => Expr::All(*c, *v, child(*a), child(*b)),
      Node::Let(c, a, b, d) => Expr::Let(*c, child(*a), child(*b), child(*d)),
    }
  }

  pub(crate) fn from_leaf(e: &Expr) -> Option<Node> {
    Some(match e {
      Expr::Sort(n) => Node::Sort(*n),
      Expr::Var(n) => Node::Var(*n),
      Expr::Ref(n, us) => Node::Ref(*n, us.clone()),
      Expr::Rec(n, us) => Node::Rec(*n, us.clone()),
      Expr::Str(n) => Node::Str(*n),
      Expr::Nat(n) => Node::Nat(*n),
      _ => return None,
    })
  }
}

/// The distinct expanded subterms of ordered roots, indexed by §3.2 term ID.
///
/// IDs are assigned by increasing height, then by [`NodeKey`]; every child
/// therefore has a smaller ID than its parent. Only subterms reachable from
/// the roots are present, so unreachable entries of an input table cannot
/// influence IDs.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SharingDag {
  nodes: Vec<Node>,
  heights: Vec<u32>,
  roots: Vec<TermId>,
}

/// How Share leaves are resolved while interning one expression.
#[derive(Clone, Copy)]
enum ShareCtx<'a> {
  /// Input must be fully expanded; `root` names the root for errors.
  Forbidden { root: u64 },
  /// Table expansion: `resolved` are the IDs of the entries this location
  /// may reference (a prefix of `table`).
  Table {
    table: &'a [Arc<Expr>],
    resolved: &'a [TermId],
    location: ShareLocation,
  },
}

struct Builder<'m, 'l> {
  nodes: Vec<Node>,
  heights: Vec<u32>,
  index: FxHashMap<Node, TermId>,
  meter: &'m mut Meter<'l>,
}

impl Builder<'_, '_> {
  fn intern(&mut self, node: Node) -> Result<TermId, SharingError> {
    if let Some(&id) = self.index.get(&node) {
      return Ok(id);
    }
    let mut height: u32 = 0;
    for &c in node.children().as_slice() {
      let h = self.heights[ix(c)].checked_add(1).ok_or_else(|| {
        SharingError::FormatBound(FormatBound::TermIdSpace {
          nodes: u64_len(self.nodes.len()),
        })
      })?;
      height = height.max(h);
    }
    self.meter.height(u64::from(height))?;
    let count = u64_len(self.nodes.len()) + 1;
    self.meter.distinct_nodes(count)?;
    let id = TermId::try_from(self.nodes.len())
      .ok()
      .filter(|id| *id != TermId::MAX)
      .ok_or(SharingError::FormatBound(FormatBound::TermIdSpace {
        nodes: count,
      }))?;
    self.nodes.push(node.clone());
    self.heights.push(height);
    self.index.insert(node, id);
    Ok(id)
  }

  fn resolve_share(
    &mut self,
    index: u64,
    ctx: ShareCtx<'_>,
  ) -> Result<TermId, SharingError> {
    match ctx {
      ShareCtx::Forbidden { root } => {
        Err(SharingError::Malformed(MalformedSharing::UnresolvedShare {
          root,
          index,
        }))
      },
      ShareCtx::Table { table, resolved, location } => {
        if let Some(&id) =
          usize::try_from(index).ok().and_then(|i| resolved.get(i))
        {
          return Ok(id);
        }
        let table_len = u64_len(table.len());
        match location {
          ShareLocation::Entry(entry) if index < table_len => {
            Err(classify_nonbackward(table, entry, index, self.meter))
          },
          _ => {
            Err(SharingError::Malformed(MalformedSharing::ShareOutOfRange {
              location,
              index,
              table_len,
            }))
          },
        }
      },
    }
  }

  /// Intern one expression tree, iteratively and memoized by pointer.
  ///
  /// The pointer memo is shared across the entries and roots of one build.
  /// They are processed in order of increasing reference bound, so a
  /// pointer validated under a smaller bound stays valid under a larger one.
  fn intern_expr(
    &mut self,
    root: &Arc<Expr>,
    memo: &mut FxHashMap<*const Expr, TermId>,
    ctx: ShareCtx<'_>,
  ) -> Result<TermId, SharingError> {
    let mut stack: Vec<(&Expr, bool)> = vec![(root.as_ref(), false)];
    while let Some((e, ready)) = stack.pop() {
      let key = std::ptr::from_ref(e);
      if memo.contains_key(&key) {
        continue;
      }
      if !ready {
        self.meter.input_node()?;
        if let Expr::Share(i) = e {
          let id = self.resolve_share(*i, ctx)?;
          memo.insert(key, id);
          continue;
        }
        if let Some(leaf) = Node::from_leaf(e) {
          let id = self.intern(leaf)?;
          memo.insert(key, id);
          continue;
        }
        stack.push((e, true));
        for c in e.children() {
          if !memo.contains_key(&Arc::as_ptr(c)) {
            stack.push((c.as_ref(), false));
          }
        }
        continue;
      }
      let id = |c: &Arc<Expr>| memo[&Arc::as_ptr(c)];
      let node = match e {
        Expr::Prj(t, f, v) => Node::Prj(*t, *f, id(v)),
        Expr::App(a, b) => Node::App(id(a), id(b)),
        Expr::Lam(c, a, b) => Node::Lam(*c, id(a), id(b)),
        Expr::All(c, v, a, b) => Node::All(*c, *v, id(a), id(b)),
        Expr::Let(c, a, b, d) => Node::Let(*c, id(a), id(b), id(d)),
        _ => {
          return Err(SharingError::Internal(
            "leaf reached the compound interning path".into(),
          ));
        },
      };
      let id = self.intern(node)?;
      memo.insert(key, id);
    }
    memo.get(&Arc::as_ptr(root)).copied().ok_or_else(|| {
      SharingError::Internal("interned root missing from memo".into())
    })
  }

  /// Keep the subterms reachable from `roots` and renumber them by §3.2.
  fn finalize(
    self,
    roots: &[TermId],
  ) -> Result<(SharingDag, Vec<TermId>), SharingError> {
    let n = self.nodes.len();
    let mut reach = vec![false; n];
    for &r in roots {
      reach[ix(r)] = true;
    }
    // Children were interned before their parents, so they have smaller
    // provisional IDs and a descending sweep propagates reachability.
    for p in (0..n).rev() {
      if reach[p] {
        for &c in self.nodes[p].children().as_slice() {
          reach[ix(c)] = true;
        }
      }
    }
    let max_h =
      (0..n).filter(|&p| reach[p]).map(|p| self.heights[p]).max().unwrap_or(0);
    let mut buckets: Vec<Vec<usize>> =
      vec![Vec::new(); usize::try_from(max_h).unwrap_or(0) + 1];
    for p in (0..n).filter(|&p| reach[p]) {
      buckets[usize::try_from(self.heights[p]).unwrap_or(0)].push(p);
    }
    let mut new_id = vec![TermId::MAX; n];
    let mut nodes = Vec::new();
    let mut heights = Vec::new();
    let mut next: TermId = 0;
    for (h, bucket) in buckets.into_iter().enumerate() {
      let mut keyed: Vec<(NodeKey, usize)> = bucket
        .into_iter()
        .map(|p| {
          let node = &self.nodes[p];
          let key = NodeKey {
            tag: node.tag(),
            scalars: node.scalars(),
            children: node
              .children()
              .as_slice()
              .iter()
              .map(|&c| new_id[ix(c)])
              .collect(),
          };
          (key, p)
        })
        .collect();
      keyed.sort();
      for w in keyed.windows(2) {
        if w[0].0 == w[1].0 {
          return Err(SharingError::Internal(
            "two interned nodes share one structural key".into(),
          ));
        }
      }
      let h = u32::try_from(h)
        .map_err(|_e| SharingError::Internal("height exceeds u32".into()))?;
      for (_, p) in keyed {
        new_id[p] = next;
        next = next.checked_add(1).ok_or(SharingError::FormatBound(
          FormatBound::TermIdSpace { nodes: u64_len(n) },
        ))?;
        nodes.push(self.nodes[p].map_children(|c| new_id[ix(c)]));
        heights.push(h);
      }
    }
    let roots = roots.iter().map(|&r| new_id[ix(r)]).collect();
    let dag = SharingDag { nodes, heights, roots };
    Ok((dag, new_id))
  }
}

/// Classify a reference from `entry` to `index`, with
/// `entry <= index < table.len()`: a cycle if `index` can reach `entry`
/// through Share edges, otherwise a forward reference.
fn classify_nonbackward(
  table: &[Arc<Expr>],
  entry: u64,
  index: u64,
  meter: &mut Meter<'_>,
) -> SharingError {
  let forward =
    SharingError::Malformed(MalformedSharing::ForwardShare { entry, index });
  let cyclic =
    SharingError::Malformed(MalformedSharing::CyclicShare { entry, index });
  if index == entry {
    return cyclic;
  }
  let mut visited: FxHashSet<u64> = FxHashSet::default();
  let mut todo = vec![index];
  while let Some(j) = todo.pop() {
    if !visited.insert(j) {
      continue;
    }
    let Some(e) = usize::try_from(j).ok().and_then(|j| table.get(j)) else {
      continue;
    };
    let mut seen: FxHashSet<*const Expr> = FxHashSet::default();
    let mut stack: Vec<&Expr> = vec![e.as_ref()];
    while let Some(x) = stack.pop() {
      if !seen.insert(std::ptr::from_ref(x)) {
        continue;
      }
      if let Err(err) = meter.input_node() {
        return err;
      }
      if let Expr::Share(k) = x {
        if *k == entry {
          return cyclic;
        }
        todo.push(*k);
      }
      stack.extend(x.children().into_iter().map(|c| c.as_ref()));
    }
  }
  forward
}

impl SharingDag {
  /// Build from roots; with `table`, Share leaves are expanded against it
  /// under the backward-reference rule, otherwise they are rejected.
  pub(crate) fn build(
    roots: &[Arc<Expr>],
    table: Option<&[Arc<Expr>]>,
    meter: &mut Meter<'_>,
  ) -> Result<SharingDag, SharingError> {
    Self::build_full(roots, table, meter).map(|(dag, _)| dag)
  }

  /// [`SharingDag::build`], also returning the term ID each table entry
  /// expands to (`None` for an entry no root reaches).
  pub(crate) fn build_full(
    roots: &[Arc<Expr>],
    table: Option<&[Arc<Expr>]>,
    meter: &mut Meter<'_>,
  ) -> Result<(SharingDag, Vec<Option<TermId>>), SharingError> {
    let mut b = Builder {
      nodes: Vec::new(),
      heights: Vec::new(),
      index: FxHashMap::default(),
      meter,
    };
    let mut memo: FxHashMap<*const Expr, TermId> = FxHashMap::default();
    let mut root_ids = Vec::with_capacity(roots.len());
    let mut entry_ids: Vec<TermId> = Vec::new();
    match table {
      None => {
        for (i, r) in roots.iter().enumerate() {
          let ctx = ShareCtx::Forbidden { root: u64_len(i) };
          root_ids.push(b.intern_expr(r, &mut memo, ctx)?);
        }
      },
      Some(table) => {
        let mut resolved: Vec<TermId> = Vec::with_capacity(table.len());
        for (j, e) in table.iter().enumerate() {
          let ctx = ShareCtx::Table {
            table,
            resolved: &resolved,
            location: ShareLocation::Entry(u64_len(j)),
          };
          let id = b.intern_expr(e, &mut memo, ctx)?;
          resolved.push(id);
          entry_ids.push(id);
        }
        for (i, r) in roots.iter().enumerate() {
          let ctx = ShareCtx::Table {
            table,
            resolved: &resolved,
            location: ShareLocation::Root(u64_len(i)),
          };
          root_ids.push(b.intern_expr(r, &mut memo, ctx)?);
        }
      },
    }
    let (dag, new_id) = b.finalize(&root_ids)?;
    let entries = entry_ids
      .iter()
      .map(|&p| Some(new_id[ix(p)]).filter(|&id| id != TermId::MAX))
      .collect();
    Ok((dag, entries))
  }

  /// Build from fully expanded roots; any Share leaf is an error.
  pub fn from_expanded_roots(
    roots: &[Arc<Expr>],
    limits: &super::ExactSharingLimits,
  ) -> Result<SharingDag, SharingError> {
    Self::build(roots, None, &mut Meter::new(limits))
  }

  /// Build by expanding `roots` against `table` (entry `i` may reference
  /// only entries `< i`; roots may reference any entry).
  pub fn from_shared(
    roots: &[Arc<Expr>],
    table: &[Arc<Expr>],
    limits: &super::ExactSharingLimits,
  ) -> Result<SharingDag, SharingError> {
    Self::build(roots, Some(table), &mut Meter::new(limits))
  }

  /// Expand a Constant's ordered roots against its own sharing table.
  pub fn from_constant(
    c: &crate::constant::Constant,
    limits: &super::ExactSharingLimits,
  ) -> Result<SharingDag, SharingError> {
    let roots = super::constant_info_root_exprs(&c.info);
    Self::build(&roots, Some(&c.sharing), &mut Meter::new(limits))
  }

  /// Nodes indexed by term ID.
  pub fn nodes(&self) -> &[Node] {
    &self.nodes
  }

  pub fn node(&self, t: TermId) -> &Node {
    &self.nodes[ix(t)]
  }

  /// Heights indexed by term ID (leaves are 0).
  pub fn heights(&self) -> &[u32] {
    &self.heights
  }

  /// Term IDs of the ordered roots.
  pub fn roots(&self) -> &[TermId] {
    &self.roots
  }

  /// Number of distinct subterms `N`.
  pub fn len(&self) -> usize {
    self.nodes.len()
  }

  pub fn is_empty(&self) -> bool {
    self.nodes.is_empty()
  }

  /// The §3.2 key of `t`.
  pub fn key(&self, t: TermId) -> NodeKey {
    let node = self.node(t);
    NodeKey {
      tag: node.tag(),
      scalars: node.scalars(),
      children: node.children().as_slice().to_vec(),
    }
  }

  /// Every term as an expanded expression, indexed by term ID. Built bottom
  /// up with one `Arc` per distinct term.
  pub fn term_exprs(&self) -> Vec<Arc<Expr>> {
    let mut out: Vec<Arc<Expr>> = Vec::with_capacity(self.nodes.len());
    for node in &self.nodes {
      let e = node.to_expr(|c| out[ix(c)].clone());
      out.push(Arc::new(e));
    }
    out
  }

  /// The expanded roots, in order.
  pub fn root_exprs(&self) -> Vec<Arc<Expr>> {
    let terms = self.term_exprs();
    self.roots.iter().map(|&r| terms[ix(r)].clone()).collect()
  }
}
