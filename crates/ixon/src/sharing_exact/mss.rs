//! Maximal structural sharing (MSS), a reference encoding for the tests; it
//! is not on the compiler path. The tests use it as a valid Share-bearing
//! input that the exact constructions must normalize from and never exceed.
//!
//! MSS stores every candidate (compact in-degree at least 2, unshared length
//! at least 2), orders the table by the Kahn priority order of compact
//! in-degree (repeatedly the available entry, every stored term its body
//! references already placed, with the largest in-degree; ties by the
//! smaller structural ID), and replaces every occurrence of a stored term by
//! a Share, in roots and in other entries.

use std::collections::BTreeSet;
use std::sync::Arc;

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
struct MssEncoding {
  /// Stored terms in table order.
  table_terms: Vec<TermId>,
  sharing: Vec<Arc<Expr>>,
  roots: Vec<Arc<Expr>>,
}

/// MSS of a DAG.
fn mss_dag(dag: &SharingDag) -> Result<MssEncoding, SharingError> {
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
  let key = |t: usize| (std::cmp::Reverse(facts.deg[t]), t);
  let mut ready: BTreeSet<(std::cmp::Reverse<u64>, usize)> =
    (0..n).filter(|&t| stored[t] && pend[t] == 0).map(key).collect();
  let mut order: Vec<usize> = Vec::new();
  while let Some((_, t)) = ready.pop_first() {
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
  Ok(MssEncoding { table_terms, sharing, roots })
}

/// MSS of a constant (its table expanded first), checked to expand to the
/// same DAG.
pub(crate) fn mss_constant(
  c: &Constant,
  limits: &ExactSharingLimits,
) -> Result<Constant, SharingError> {
  let mut meter = Meter::new(limits);
  let roots = constant_info_root_exprs(&c.info);
  let dag = SharingDag::build(&roots, Some(&c.sharing), &mut meter)?;
  let enc = mss_dag(&dag)?;
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
  Ok(Constant {
    info,
    sharing: enc.sharing,
    refs: c.refs.clone(),
    univs: c.univs.clone(),
  })
}
