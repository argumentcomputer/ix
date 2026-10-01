//! Experiment hooks, not constructions of the plan: maximal structural
//! sharing (MSS) on the structural DAG, and an inspector for any encoding of
//! a DAG. They exist to compare the tiered construction with MSS.
//!
//! MSS stores every candidate (compact in-degree at least 2, unshared length
//! at least 2), orders the table by the Kahn priority order of compact
//! in-degree (repeatedly the available entry, every stored term its body
//! references already placed, with the largest in-degree; ties by the
//! smaller structural ID, or the blake3 hash), and replaces every occurrence of a stored term by a
//! Share, in roots and in other entries.

use std::collections::BTreeSet;
use std::sync::Arc;

use rustc_hash::FxHashMap;

use super::cost::Len;
use super::dag::{Node, SharingDag, TermId, ix};
use super::dict::all_costs;
use super::uniform::graph_facts;
use super::{
  ExactSharingLimits, Meter, SharingError, constant_info_root_exprs,
  rebuild_constant_info,
};
use crate::constant::Constant;
use crate::expr::Expr;

fn internal(msg: &str) -> SharingError {
  SharingError::Internal(msg.to_string())
}

/// An MSS encoding of a DAG.
#[derive(Clone, Debug)]
pub struct MssEncoding {
  /// Stored terms in table order.
  pub table_terms: Vec<TermId>,
  pub sharing: Vec<Arc<Expr>>,
  pub roots: Vec<Arc<Expr>>,
  /// Compact in-degree of every term of the DAG (edges with multiplicity
  /// plus root occurrences).
  pub deg: Vec<u64>,
}

/// How MSS breaks ties between available entries of equal in-degree.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MssTies {
  /// The smaller structural ID.
  StructuralId,
  /// The smaller blake3 hash bytes of the production heuristic's hash
  /// (`sharing::analyze_block`), as in W3's `mssBuild`.
  Blake3,
}

/// MSS of a DAG.
pub fn mss_dag(
  dag: &SharingDag,
  ties: MssTies,
) -> Result<MssEncoding, SharingError> {
  let nodes = dag.nodes();
  let n = nodes.len();
  let own: Vec<Len> = nodes.iter().map(Node::own_len).collect();
  let mut work = 0u64;
  let base = all_costs(nodes, &own, &super::dict::NoWidths, &mut work);
  let facts = graph_facts(dag);
  let stored: Vec<bool> =
    (0..n).map(|t| facts.deg[t] >= 2 && base[t] >= Len::new(2)).collect();
  // Dependencies: the stored terms reachable from a stored term's children
  // through unstored terms (the Shares of its MSS body).
  let mut deps: Vec<Vec<TermId>> = vec![Vec::new(); n];
  let mut stamp = vec![usize::MAX; n];
  for t in 0..n {
    if !stored[t] {
      continue;
    }
    let mut stack: Vec<TermId> = nodes[t].children().as_slice().to_vec();
    while let Some(c) = stack.pop() {
      let c = ix(c);
      if stamp[c] == t {
        continue;
      }
      stamp[c] = t;
      if stored[c] {
        deps[t].push(TermId::try_from(c).map_err(|_e| internal("id"))?);
      } else {
        stack.extend_from_slice(nodes[c].children().as_slice());
      }
    }
  }
  // Kahn priority order by in-degree, ties by the smaller ID.
  let mut pend = vec![0usize; n];
  let mut users: Vec<Vec<usize>> = vec![Vec::new(); n];
  for t in 0..n {
    if stored[t] {
      pend[t] = deps[t].len();
      for &d in &deps[t] {
        users[ix(d)].push(t);
      }
    }
  }
  let tie: Vec<[u8; 32]> = match ties {
    MssTies::StructuralId => (0..n)
      .map(|t| {
        let mut b = [0u8; 32];
        b[24..].copy_from_slice(&(t as u64).to_be_bytes());
        b
      })
      .collect(),
    MssTies::Blake3 => {
      let exprs = dag.term_exprs();
      let (_, ptr_to_hash, _) = crate::sharing::analyze_block(&exprs, false);
      exprs
        .iter()
        .map(|e| {
          ptr_to_hash
            .get(&std::ptr::from_ref(e.as_ref()))
            .map(|h| *h.as_bytes())
            .ok_or_else(|| internal("unhashed term"))
        })
        .collect::<Result<_, _>>()?
    },
  };
  let key = |t: usize| (std::cmp::Reverse(facts.deg[t]), tie[t], t);
  let mut ready: BTreeSet<(std::cmp::Reverse<u64>, [u8; 32], usize)> =
    (0..n).filter(|&t| stored[t] && pend[t] == 0).map(key).collect();
  let mut order: Vec<usize> = Vec::new();
  while let Some((_, _, t)) = ready.pop_first() {
    order.push(t);
    for &u in &users[t] {
      pend[u] -= 1;
      if pend[u] == 0 {
        ready.insert(key(u));
      }
    }
  }
  if order.len() != stored.iter().filter(|&&s| s).count() {
    return Err(internal("MSS order is incomplete"));
  }
  let mut index = vec![None; n];
  for (i, &t) in order.iter().enumerate() {
    index[t] = Some(i as u64);
  }
  // Shared form of every term (children have smaller IDs).
  let mut shared: Vec<Arc<Expr>> = Vec::with_capacity(n);
  let mut body: Vec<Option<Arc<Expr>>> = vec![None; n];
  for t in 0..n {
    let e = Arc::new(nodes[t].to_expr(|c| shared[ix(c)].clone()));
    if let Some(i) = index[t] {
      body[t] = Some(e);
      shared.push(Expr::share(i));
    } else {
      shared.push(e);
    }
  }
  let sharing: Vec<Arc<Expr>> = order
    .iter()
    .map(|&t| body[t].clone().ok_or_else(|| internal("missing body")))
    .collect::<Result<_, _>>()?;
  let roots: Vec<Arc<Expr>> =
    dag.roots().iter().map(|&r| shared[ix(r)].clone()).collect();
  let table_terms = order
    .iter()
    .map(|&t| TermId::try_from(t).map_err(|_e| internal("id")))
    .collect::<Result<_, _>>()?;
  Ok(MssEncoding { table_terms, sharing, roots, deg: facts.deg })
}

/// MSS of a constant (its table expanded first). Returns the constant, the
/// encoding and the DAG; the encoding is checked to expand to the same DAG.
pub fn mss_constant(
  c: &Constant,
  limits: &ExactSharingLimits,
  ties: MssTies,
) -> Result<(Constant, MssEncoding, SharingDag), SharingError> {
  let mut meter = Meter::new(limits);
  let roots = constant_info_root_exprs(&c.info);
  let dag = SharingDag::build(&roots, Some(&c.sharing), &mut meter)?;
  let enc = mss_dag(&dag, ties)?;
  let mut check_meter = Meter::new(limits);
  let (check, ids) =
    SharingDag::build_full(&enc.roots, Some(&enc.sharing), &mut check_meter)?;
  if check != dag
    || ids
      .iter()
      .map(|x| x.unwrap_or(TermId::MAX))
      .ne(enc.table_terms.iter().copied())
  {
    return Err(internal("MSS encoding does not expand to the input"));
  }
  let info = rebuild_constant_info(&c.info, &enc.roots)?;
  let out = Constant {
    info,
    sharing: enc.sharing.clone(),
    refs: c.refs.clone(),
    univs: c.univs.clone(),
  };
  Ok((out, enc, dag))
}

/// What an encoding of a DAG writes, position by position.
#[derive(Clone, Debug, Default)]
pub struct EncodingInfo {
  /// `Share(i)` occurrences per table index.
  pub share_refs: Vec<u64>,
  /// Positions (outside the entry tops) that write a stored term inline.
  pub inlined: u64,
  /// The same, per stored term.
  pub inlined_by_term: FxHashMap<TermId, u64>,
  /// For every entry and root, the term ID of each written position in
  /// pre-order with Shares as `(true, term)`, inline nodes as
  /// `(false, term)`: a form independent of the table order.
  pub entry_forms: Vec<Vec<(bool, TermId)>>,
  pub root_forms: Vec<Vec<(bool, TermId)>>,
}

/// Inspect an encoding (`table_terms[i]` is the term of entry `i`) of `dag`.
pub fn inspect_encoding(
  dag: &SharingDag,
  table_terms: &[TermId],
  sharing: &[Arc<Expr>],
  roots: &[Arc<Expr>],
) -> Result<EncodingInfo, SharingError> {
  let nodes = dag.nodes();
  let lookup: FxHashMap<&Node, TermId> = nodes
    .iter()
    .enumerate()
    .map(|(t, node)| TermId::try_from(t).map(|id| (node, id)))
    .collect::<Result<_, _>>()
    .map_err(|_e| internal("id"))?;
  let stored: rustc_hash::FxHashSet<TermId> =
    table_terms.iter().copied().collect();
  let mut info = EncodingInfo {
    share_refs: vec![0; table_terms.len()],
    ..EncodingInfo::default()
  };
  let mut memo: FxHashMap<*const Expr, TermId> = FxHashMap::default();
  // Term of an expression (memoized by pointer; post-order, iterative).
  let term_of = |root: &Arc<Expr>,
                 memo: &mut FxHashMap<*const Expr, TermId>|
   -> Result<TermId, SharingError> {
    let mut stack: Vec<(&Expr, bool)> = vec![(root.as_ref(), false)];
    while let Some((e, ready)) = stack.pop() {
      let key = std::ptr::from_ref(e);
      if memo.contains_key(&key) {
        continue;
      }
      if let Expr::Share(i) = e {
        let t = usize::try_from(*i)
          .ok()
          .and_then(|i| table_terms.get(i))
          .copied()
          .ok_or_else(|| internal("share index out of range"))?;
        memo.insert(key, t);
        continue;
      }
      if let Some(leaf) = Node::from_leaf(e) {
        let t = *lookup.get(&leaf).ok_or_else(|| internal("unknown leaf"))?;
        memo.insert(key, t);
        continue;
      }
      if !ready {
        stack.push((e, true));
        for c in e.children() {
          stack.push((c.as_ref(), false));
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
        _ => return Err(internal("unexpected leaf")),
      };
      let t = *lookup.get(&node).ok_or_else(|| internal("unknown node"))?;
      memo.insert(key, t);
    }
    memo.get(&Arc::as_ptr(root)).copied().ok_or_else(|| internal("missing"))
  };
  // Walk every position of every entry and root.
  let mut walk = |e: &Arc<Expr>,
                  top_is_entry: bool,
                  info: &mut EncodingInfo|
   -> Result<Vec<(bool, TermId)>, SharingError> {
    term_of(e, &mut memo)?;
    let mut form = Vec::new();
    let mut stack: Vec<(&Arc<Expr>, bool)> = vec![(e, true)];
    while let Some((x, top)) = stack.pop() {
      let t = memo[&Arc::as_ptr(x)];
      if let Expr::Share(i) = x.as_ref() {
        form.push((true, t));
        if let Some(r) =
          usize::try_from(*i).ok().and_then(|i| info.share_refs.get_mut(i))
        {
          *r += 1;
        }
        continue;
      }
      form.push((false, t));
      if stored.contains(&t) && !(top && top_is_entry) {
        info.inlined += 1;
        *info.inlined_by_term.entry(t).or_default() += 1;
      }
      for c in x.children().iter().rev() {
        stack.push((c, false));
      }
    }
    Ok(form)
  };
  for e in sharing {
    let f = walk(e, true, &mut info)?;
    info.entry_forms.push(f);
  }
  for r in roots {
    let f = walk(r, false, &mut info)?;
    info.root_forms.push(f);
  }
  Ok(info)
}
