//! A deliberately simple exact reference search for tiny inputs (§6.3).
//!
//! It shares no search code with the optimizer: IDs are recomputed from
//! expression values, every ordered sequence of distinct expanded subterms is
//! tried as the table (not only R1/R2 candidates), every table entry and
//! root enumerates every per-occurrence choice between its inline constructor
//! and a Share of an equal earlier entry, and lengths and bytes come from the
//! real serializer. Candidates are compared by the full key `(L, Q, bytes)`.
//!
//! For one table sequence the entries and roots are separate byte segments of
//! the Constant: a minimum-length Constant has every segment at its minimum
//! length, so segment positions are fixed and the byte-least Constant takes
//! the byte-least minimum segment everywhere. [`oracle_full_product`] checks
//! this separability by enumerating complete Constants.

use std::collections::HashMap;
use std::sync::Arc;

use super::roots::{constant_info_root_exprs, rebuild_constant_info};
use crate::constant::Constant;
use crate::contract::pack_all_contract;
use crate::expr::Expr;
use crate::serialize::put_expr;

fn collect(e: &Arc<Expr>, heights: &mut HashMap<Expr, u32>) -> u32 {
  if let Some(&h) = heights.get(e.as_ref()) {
    return h;
  }
  assert!(!matches!(e.as_ref(), Expr::Share(_)), "oracle input has Share");
  let h = e.children().into_iter().map(|c| collect(c, heights) + 1).max();
  let h = h.unwrap_or(0);
  heights.insert(e.as_ref().clone(), h);
  h
}

fn key(e: &Expr, ids: &HashMap<Expr, u32>) -> (u8, Vec<u64>, Vec<u32>) {
  let id = |c: &Arc<Expr>| ids[c.as_ref()];
  match e {
    Expr::Sort(u) => (0, vec![*u], vec![]),
    Expr::Var(i) => (1, vec![*i], vec![]),
    Expr::Ref(r, us) | Expr::Rec(r, us) => {
      let tag = if matches!(e, Expr::Ref(..)) { 2 } else { 3 };
      let mut s = vec![*r, us.len() as u64];
      s.extend(us.iter().copied());
      (tag, s, vec![])
    },
    Expr::Prj(t, f, v) => (4, vec![*t, *f], vec![id(v)]),
    Expr::Str(r) => (5, vec![*r], vec![]),
    Expr::Nat(r) => (6, vec![*r], vec![]),
    Expr::App(f, a) => (7, vec![], vec![id(f), id(a)]),
    Expr::Lam(c, ty, b) => {
      (8, vec![u64::from(c.to_bits())], vec![id(ty), id(b)])
    },
    Expr::All(c, v, ty, b) => {
      (9, vec![u64::from(pack_all_contract(*c, *v))], vec![id(ty), id(b)])
    },
    Expr::Let(c, ty, v, b) => (
      10,
      vec![c.flags(), u64::from(c.binder.to_bits())],
      vec![id(ty), id(v), id(b)],
    ),
    Expr::Share(_) => panic!("oracle input has Share"),
  }
}

/// Independent §3.2 IDs of the distinct subterms of `roots`, and the terms
/// in ID order.
pub(crate) fn oracle_ids(
  roots: &[Arc<Expr>],
) -> (HashMap<Expr, u32>, Vec<Arc<Expr>>) {
  let mut heights: HashMap<Expr, u32> = HashMap::new();
  for r in roots {
    collect(r, &mut heights);
  }
  let max_h = heights.values().copied().max().unwrap_or(0);
  let mut ids: HashMap<Expr, u32> = HashMap::new();
  let mut terms: Vec<Arc<Expr>> = Vec::new();
  for h in 0..=max_h {
    let mut level: Vec<(u8, Vec<u64>, Vec<u32>, Expr)> = heights
      .iter()
      .filter(|(_, hh)| **hh == h)
      .map(|(e, _)| {
        let (t, s, c) = key(e, &ids);
        (t, s, c, e.clone())
      })
      .collect();
    level.sort_by(|a, b| (&a.0, &a.1, &a.2).cmp(&(&b.0, &b.1, &b.2)));
    for (_, _, _, e) in level {
      let id = u32::try_from(terms.len()).unwrap();
      ids.insert(e.clone(), id);
      terms.push(Arc::new(e));
    }
  }
  (ids, terms)
}

/// Every representation of `e` using the available `(expanded, index)`
/// entries: at each occurrence, the inline constructor or a Share of an
/// equal entry.
pub(crate) fn variants(
  e: &Arc<Expr>,
  avail: &[(Arc<Expr>, u64)],
) -> Vec<Arc<Expr>> {
  let mut out: Vec<Arc<Expr>> = avail
    .iter()
    .filter(|(x, _)| x == e)
    .map(|(_, i)| Expr::share(*i))
    .collect();
  let kids = e.children();
  if kids.is_empty() {
    out.push(e.clone());
    return out;
  }
  let mut combos: Vec<Vec<Arc<Expr>>> = vec![vec![]];
  for c in kids {
    let vs = variants(c, avail);
    let mut next = Vec::with_capacity(combos.len() * vs.len());
    for prefix in &combos {
      for v in &vs {
        let mut row = prefix.clone();
        row.push(v.clone());
        next.push(row);
      }
    }
    assert!(next.len() <= 2_000_000, "oracle variant explosion");
    combos = next;
  }
  out.extend(combos.iter().map(|cs| Arc::new(e.with_children(cs).unwrap())));
  out
}

pub(crate) fn bytes_of(e: &Expr) -> Vec<u8> {
  let mut b = Vec::new();
  put_expr(e, &mut b);
  b
}

/// The byte-least minimum-length variant and every variant's bytes.
fn best_variant(e: &Arc<Expr>, avail: &[(Arc<Expr>, u64)]) -> Arc<Expr> {
  variants(e, avail)
    .into_iter()
    .map(|v| (bytes_of(&v), v))
    .min_by(|a, b| (a.0.len(), &a.0).cmp(&(b.0.len(), &b.0)))
    .unwrap()
    .1
}

/// Result of the exhaustive search.
#[derive(Debug)]
pub(crate) struct OracleResult {
  pub len: u64,
  pub q: Vec<u32>,
  pub bytes: Vec<u8>,
  pub constant: Constant,
  /// Every table sequence (as oracle IDs) that attains the minimum length.
  pub minimal_sequences: Vec<Vec<u32>>,
  pub sequences: u64,
}

fn constant_bytes(c: &Constant) -> Vec<u8> {
  let mut b = Vec::new();
  c.put(&mut b);
  b
}

fn for_each_sequence(n: usize, f: &mut impl FnMut(&[usize])) {
  fn go(n: usize, order: &mut Vec<usize>, f: &mut impl FnMut(&[usize])) {
    f(order);
    for i in 0..n {
      if !order.contains(&i) {
        order.push(i);
        go(n, order, f);
        order.pop();
      }
    }
  }
  go(n, &mut Vec::new(), f);
}

fn available(terms: &[Arc<Expr>], order: &[usize]) -> Vec<(Arc<Expr>, u64)> {
  order.iter().enumerate().map(|(i, &t)| (terms[t].clone(), i as u64)).collect()
}

/// Exhaustive minimum of the full key over all tables and occurrence
/// choices. `template` supplies every non-sharing field; its roots must be
/// fully expanded and its table is ignored.
pub(crate) fn oracle_optimum(template: &Constant) -> OracleResult {
  let roots = constant_info_root_exprs(&template.info);
  let (_, terms) = oracle_ids(&roots);
  let mut best: Option<(u64, Vec<u32>, Vec<u8>, Constant)> = None;
  let mut min_len = u64::MAX;
  let mut minimal: Vec<Vec<u32>> = Vec::new();
  let mut sequences = 0u64;
  for_each_sequence(terms.len(), &mut |order| {
    sequences += 1;
    let mut table = Vec::with_capacity(order.len());
    for i in 0..order.len() {
      let avail = available(&terms, &order[..i]);
      table.push(best_variant(&terms[order[i]], &avail));
    }
    let avail = available(&terms, order);
    let reps: Vec<Arc<Expr>> =
      roots.iter().map(|r| best_variant(r, &avail)).collect();
    let info = rebuild_constant_info(&template.info, &reps).unwrap();
    let c = Constant {
      info,
      sharing: table,
      refs: template.refs.clone(),
      univs: template.univs.clone(),
    };
    let bytes = constant_bytes(&c);
    let len = bytes.len() as u64;
    let q: Vec<u32> =
      order.iter().map(|&i| u32::try_from(i).unwrap()).collect();
    if len < min_len {
      min_len = len;
      minimal.clear();
    }
    if len == min_len {
      minimal.push(q.clone());
    }
    let better = match &best {
      None => true,
      Some((bl, bq, bb, _)) => (len, &q, &bytes) < (*bl, bq, bb),
    };
    if better {
      best = Some((len, q, bytes, c));
    }
  });
  let (len, q, bytes, constant) = best.unwrap();
  minimal.sort();
  OracleResult {
    len,
    q,
    bytes,
    constant,
    minimal_sequences: minimal,
    sequences,
  }
}

/// The minimum key over the complete Cartesian product of every entry's and
/// root's variants, for every table sequence. Returns `None` if some
/// sequence has more than `cap` complete Constants.
pub(crate) fn oracle_full_product(
  template: &Constant,
  cap: usize,
) -> Option<(u64, Vec<u32>, Vec<u8>, u64)> {
  let roots = constant_info_root_exprs(&template.info);
  let (_, terms) = oracle_ids(&roots);
  let mut best: Option<(u64, Vec<u32>, Vec<u8>)> = None;
  let mut complete = 0u64;
  let mut too_big = false;
  for_each_sequence(terms.len(), &mut |order| {
    if too_big {
      return;
    }
    let mut components: Vec<Vec<Arc<Expr>>> = Vec::new();
    for i in 0..order.len() {
      components
        .push(variants(&terms[order[i]], &available(&terms, &order[..i])));
    }
    let k = components.len();
    let avail = available(&terms, order);
    for r in &roots {
      components.push(variants(r, &avail));
    }
    let total: usize = components.iter().map(Vec::len).product();
    if total > cap {
      too_big = true;
      return;
    }
    let q: Vec<u32> =
      order.iter().map(|&i| u32::try_from(i).unwrap()).collect();
    let mut pick = vec![0usize; components.len()];
    loop {
      let table: Vec<Arc<Expr>> =
        (0..k).map(|i| components[i][pick[i]].clone()).collect();
      let reps: Vec<Arc<Expr>> =
        (k..components.len()).map(|i| components[i][pick[i]].clone()).collect();
      let info = rebuild_constant_info(&template.info, &reps).unwrap();
      let c = Constant {
        info,
        sharing: table,
        refs: template.refs.clone(),
        univs: template.univs.clone(),
      };
      let bytes = constant_bytes(&c);
      complete += 1;
      let len = bytes.len() as u64;
      let better = match &best {
        None => true,
        Some((bl, bq, bb)) => (len, &q, &bytes) < (*bl, bq, bb),
      };
      if better {
        best = Some((len, q.clone(), bytes));
      }
      // Odometer increment.
      let mut d = 0;
      loop {
        if d == pick.len() {
          return;
        }
        pick[d] += 1;
        if pick[d] < components[d].len() {
          break;
        }
        pick[d] = 0;
        d += 1;
      }
    }
  });
  if too_big {
    return None;
  }
  best.map(|(l, q, b)| (l, q, b, complete))
}

/// Number of representations [`variants`] would enumerate (saturating).
pub(crate) fn variant_count(e: &Arc<Expr>, avail: &[(Arc<Expr>, u64)]) -> u128 {
  let shares = avail.iter().filter(|(x, _)| x == e).count() as u128;
  let kids = e.children();
  if kids.is_empty() {
    return shares + 1;
  }
  kids
    .into_iter()
    .map(|c| variant_count(c, avail))
    .fold(1u128, u128::saturating_mul)
    .saturating_add(shares)
}
