//! Universe level operations: reduction, instantiation, and comparison.
//!
//! Ported from `Ix.Kernel.Level` (Lean). Implements the complete comparison
//! algorithm from Géran's canonical form paper, with heuristic fast path.

use std::collections::BTreeMap;

use crate::ix::env::Name;

use super::types::{KLevel, KLevelData, MetaMode};

// ============================================================================
// Reduction
// ============================================================================

/// Reduce `max a b` assuming `a` and `b` are already reduced.
pub fn reduce_max<M: MetaMode>(a: &KLevel<M>, b: &KLevel<M>) -> KLevel<M> {
  match (a.data(), b.data()) {
    (KLevelData::Zero, _) => b.clone(),
    (_, KLevelData::Zero) => a.clone(),
    (KLevelData::Succ(a_inner), KLevelData::Succ(b_inner)) => {
      KLevel::succ(reduce_max(a_inner, b_inner))
    }
    (KLevelData::Param(idx_a, _), KLevelData::Param(idx_b, _))
      if idx_a == idx_b =>
    {
      a.clone()
    }
    _ => KLevel::max(a.clone(), b.clone()),
  }
}

/// Reduce `imax a b` assuming `a` and `b` are already reduced.
pub fn reduce_imax<M: MetaMode>(a: &KLevel<M>, b: &KLevel<M>) -> KLevel<M> {
  match b.data() {
    KLevelData::Zero => KLevel::zero(),
    KLevelData::Succ(_) => reduce_max(a, b),
    _ => match a.data() {
      KLevelData::Zero => b.clone(),
      KLevelData::Succ(inner) if matches!(inner.data(), KLevelData::Zero) => {
        // imax(1, b) = b
        b.clone()
      }
      KLevelData::Param(idx_a, _) => match b.data() {
        KLevelData::Param(idx_b, _) if idx_a == idx_b => a.clone(),
        _ => KLevel::imax(a.clone(), b.clone()),
      },
      _ => KLevel::imax(a.clone(), b.clone()),
    },
  }
}

/// Reduce a level to normal form.
pub fn reduce<M: MetaMode>(l: &KLevel<M>) -> KLevel<M> {
  match l.data() {
    KLevelData::Zero | KLevelData::Param(..) => l.clone(),
    KLevelData::Succ(inner) => KLevel::succ(reduce(inner)),
    KLevelData::Max(a, b) => reduce_max(&reduce(a), &reduce(b)),
    KLevelData::IMax(a, b) => reduce_imax(&reduce(a), &reduce(b)),
  }
}

// ============================================================================
// Instantiation
// ============================================================================

/// Instantiate a single variable by index and reduce.
/// Assumes `subst` is already reduced.
pub fn inst_reduce<M: MetaMode>(
  u: &KLevel<M>,
  idx: usize,
  subst: &KLevel<M>,
) -> KLevel<M> {
  match u.data() {
    KLevelData::Zero => u.clone(),
    KLevelData::Succ(inner) => {
      KLevel::succ(inst_reduce(inner, idx, subst))
    }
    KLevelData::Max(a, b) => {
      reduce_max(
        &inst_reduce(a, idx, subst),
        &inst_reduce(b, idx, subst),
      )
    }
    KLevelData::IMax(a, b) => {
      reduce_imax(
        &inst_reduce(a, idx, subst),
        &inst_reduce(b, idx, subst),
      )
    }
    KLevelData::Param(i, _) => {
      if *i == idx {
        subst.clone()
      } else {
        u.clone()
      }
    }
  }
}

/// Instantiate multiple variables at once and reduce.
/// `.param idx` is replaced by `substs[idx]` if in range,
/// otherwise shifted by `substs.len()`.
pub fn inst_bulk_reduce<M: MetaMode>(substs: &[KLevel<M>], l: &KLevel<M>) -> KLevel<M> {
  match l.data() {
    KLevelData::Zero => l.clone(),
    KLevelData::Succ(inner) => {
      KLevel::succ(inst_bulk_reduce(substs, inner))
    }
    KLevelData::Max(a, b) => {
      reduce_max(
        &inst_bulk_reduce(substs, a),
        &inst_bulk_reduce(substs, b),
      )
    }
    KLevelData::IMax(a, b) => {
      reduce_imax(
        &inst_bulk_reduce(substs, a),
        &inst_bulk_reduce(substs, b),
      )
    }
    KLevelData::Param(idx, name) => {
      if *idx < substs.len() {
        substs[*idx].clone()
      } else {
        KLevel::param(idx - substs.len(), name.clone())
      }
    }
  }
}

// ============================================================================
// Heuristic comparison (C++ style)
// ============================================================================

/// Heuristic comparison: `a <= b + diff`. Sound but incomplete on nested imax.
/// Assumes `a` and `b` are already reduced.
fn leq_heuristic<M: MetaMode>(a: &KLevel<M>, b: &KLevel<M>, diff: i64) -> bool {
  // Fast case: a is zero and diff >= 0
  if diff >= 0 && matches!(a.data(), KLevelData::Zero) {
    return true;
  }

  match (a.data(), b.data()) {
    (KLevelData::Zero, KLevelData::Zero) => diff >= 0,

    // Succ cases
    (KLevelData::Succ(a_inner), _) => {
      leq_heuristic(a_inner, b, diff - 1)
    }
    (_, KLevelData::Succ(b_inner)) => {
      leq_heuristic(a, b_inner, diff + 1)
    }

    (KLevelData::Param(..), KLevelData::Zero) => false,
    (KLevelData::Zero, KLevelData::Param(..)) => diff >= 0,
    (KLevelData::Param(x, _), KLevelData::Param(y, _)) => {
      x == y && diff >= 0
    }

    // IMax left cases
    (KLevelData::IMax(_, b_inner), _)
      if matches!(b_inner.data(), KLevelData::Param(..)) =>
    {
      if let KLevelData::Param(idx, _) = b_inner.data() {
        let idx = *idx;
        leq_heuristic(
          &KLevel::zero(),
          &inst_reduce(b, idx, &KLevel::zero()),
          diff,
        ) && {
          let s = KLevel::succ(KLevel::param(idx, M::Field::<Name>::default()));
          leq_heuristic(
            &inst_reduce(a, idx, &s),
            &inst_reduce(b, idx, &s),
            diff,
          )
        }
      } else {
        false
      }
    }
    (KLevelData::IMax(c, inner), _)
      if matches!(inner.data(), KLevelData::Max(..)) =>
    {
      if let KLevelData::Max(e, f) = inner.data() {
        let new_max = reduce_max(
          &reduce_imax(c, e),
          &reduce_imax(c, f),
        );
        leq_heuristic(&new_max, b, diff)
      } else {
        false
      }
    }
    (KLevelData::IMax(c, inner), _)
      if matches!(inner.data(), KLevelData::IMax(..)) =>
    {
      if let KLevelData::IMax(e, f) = inner.data() {
        let new_max =
          reduce_max(&reduce_imax(c, f), &KLevel::imax(e.clone(), f.clone()));
        leq_heuristic(&new_max, b, diff)
      } else {
        false
      }
    }

    // IMax right cases
    (_, KLevelData::IMax(_, b_inner))
      if matches!(b_inner.data(), KLevelData::Param(..)) =>
    {
      if let KLevelData::Param(idx, _) = b_inner.data() {
        let idx = *idx;
        leq_heuristic(
          &inst_reduce(a, idx, &KLevel::zero()),
          &KLevel::zero(),
          diff,
        ) && {
          let s = KLevel::succ(KLevel::param(idx, M::Field::<Name>::default()));
          leq_heuristic(
            &inst_reduce(a, idx, &s),
            &inst_reduce(b, idx, &s),
            diff,
          )
        }
      } else {
        false
      }
    }
    (_, KLevelData::IMax(c, inner))
      if matches!(inner.data(), KLevelData::Max(..)) =>
    {
      if let KLevelData::Max(e, f) = inner.data() {
        let new_max = reduce_max(
          &reduce_imax(c, e),
          &reduce_imax(c, f),
        );
        leq_heuristic(a, &new_max, diff)
      } else {
        false
      }
    }
    (_, KLevelData::IMax(c, inner))
      if matches!(inner.data(), KLevelData::IMax(..)) =>
    {
      if let KLevelData::IMax(e, f) = inner.data() {
        let new_max =
          reduce_max(&reduce_imax(c, f), &KLevel::imax(e.clone(), f.clone()));
        leq_heuristic(a, &new_max, diff)
      } else {
        false
      }
    }

    // Max cases
    (KLevelData::Max(c, d), _) => {
      leq_heuristic(c, b, diff) && leq_heuristic(d, b, diff)
    }
    (_, KLevelData::Max(c, d)) => {
      leq_heuristic(a, c, diff) || leq_heuristic(a, d, diff)
    }

    _ => false,
  }
}

/// Heuristic semantic equality of levels.
fn equal_level_heuristic<M: MetaMode>(a: &KLevel<M>, b: &KLevel<M>) -> bool {
  leq_heuristic(a, b, 0) && leq_heuristic(b, a, 0)
}

// ============================================================================
// Complete canonical-form normalization
// ============================================================================

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct VarNode {
  idx: usize,
  offset: usize,
}

#[derive(Debug, Clone, Default)]
struct Node {
  constant: usize,
  var: Vec<VarNode>,
}

impl Node {
  fn add_var(&mut self, idx: usize, k: usize) {
    match self.var.binary_search_by_key(&idx, |v| v.idx) {
      Ok(pos) => self.var[pos].offset = self.var[pos].offset.max(k),
      Err(pos) => self.var.insert(pos, VarNode { idx, offset: k }),
    }
  }
}

type NormLevel = BTreeMap<Vec<usize>, Node>;

fn norm_add_var(
  s: &mut NormLevel,
  idx: usize,
  k: usize,
  path: &[usize],
) {
  s.entry(path.to_vec())
    .or_default()
    .add_var(idx, k);
}

fn norm_add_node(
  s: &mut NormLevel,
  idx: usize,
  path: &[usize],
) {
  s.entry(path.to_vec())
    .or_default()
    .add_var(idx, 0);
}

fn norm_add_const(s: &mut NormLevel, k: usize, path: &[usize]) {
  if k == 0 || (k == 1 && !path.is_empty()) {
    return;
  }
  let node = s.entry(path.to_vec()).or_default();
  node.constant = node.constant.max(k);
}

/// Insert `a` into a sorted slice, returning `Some(new_vec)` if not already
/// present, `None` if duplicate.
fn ordered_insert(a: usize, list: &[usize]) -> Option<Vec<usize>> {
  match list.binary_search(&a) {
    Ok(_) => None, // already present
    Err(pos) => {
      let mut result = list.to_vec();
      result.insert(pos, a);
      Some(result)
    }
  }
}

fn normalize_aux<M: MetaMode>(
  l: &KLevel<M>,
  path: &[usize],
  k: usize,
  acc: &mut NormLevel,
) {
  match l.data() {
    KLevelData::Zero => {
      norm_add_const(acc, k, path);
    }
    KLevelData::Succ(inner) => {
      normalize_aux(inner, path, k + 1, acc);
    }
    KLevelData::Max(a, b) => {
      normalize_aux(a, path, k, acc);
      normalize_aux(b, path, k, acc);
    }
    KLevelData::IMax(_, b) if matches!(b.data(), KLevelData::Zero) => {
      norm_add_const(acc, k, path);
    }
    KLevelData::IMax(u, b) if matches!(b.data(), KLevelData::Succ(..)) => {
      if let KLevelData::Succ(v) = b.data() {
        normalize_aux(u, path, k, acc);
        normalize_aux(v, path, k + 1, acc);
      }
    }
    KLevelData::IMax(u, b) if matches!(b.data(), KLevelData::Max(..)) => {
      if let KLevelData::Max(v, w) = b.data() {
        let imax_uv = KLevel::imax(u.clone(), v.clone());
        let imax_uw = KLevel::imax(u.clone(), w.clone());
        normalize_aux(&imax_uv, path, k, acc);
        normalize_aux(&imax_uw, path, k, acc);
      }
    }
    KLevelData::IMax(u, b) if matches!(b.data(), KLevelData::IMax(..)) => {
      if let KLevelData::IMax(v, w) = b.data() {
        let imax_uw = KLevel::imax(u.clone(), w.clone());
        let imax_vw = KLevel::imax(v.clone(), w.clone());
        normalize_aux(&imax_uw, path, k, acc);
        normalize_aux(&imax_vw, path, k, acc);
      }
    }
    KLevelData::IMax(u, b) if matches!(b.data(), KLevelData::Param(..)) => {
      if let KLevelData::Param(idx, _) = b.data() {
        let idx = *idx;
        if let Some(new_path) = ordered_insert(idx, path) {
          norm_add_node(acc, idx, &new_path);
          normalize_aux(u, &new_path, k, acc);
        } else {
          normalize_aux(u, path, k, acc);
        }
      }
    }
    KLevelData::Param(idx, _) => {
      let idx = *idx;
      if let Some(new_path) = ordered_insert(idx, path) {
        norm_add_const(acc, k, path);
        norm_add_node(acc, idx, &new_path);
        if k != 0 {
          norm_add_var(acc, idx, k, &new_path);
        }
      } else if k != 0 {
        norm_add_var(acc, idx, k, path);
      }
    }
    _ => {
      // IMax with non-matching patterns — shouldn't happen after reduction
      norm_add_const(acc, k, path);
    }
  }
}

fn subsume_vars(xs: &[VarNode], ys: &[VarNode]) -> Vec<VarNode> {
  let mut result = Vec::new();
  let mut xi = 0;
  let mut yi = 0;
  while xi < xs.len() {
    if yi >= ys.len() {
      result.extend_from_slice(&xs[xi..]);
      break;
    }
    match xs[xi].idx.cmp(&ys[yi].idx) {
      std::cmp::Ordering::Less => {
        result.push(xs[xi].clone());
        xi += 1;
      }
      std::cmp::Ordering::Equal => {
        if xs[xi].offset > ys[yi].offset {
          result.push(xs[xi].clone());
        }
        xi += 1;
        yi += 1;
      }
      std::cmp::Ordering::Greater => {
        yi += 1;
      }
    }
  }
  result
}

fn is_subset(xs: &[usize], ys: &[usize]) -> bool {
  let mut yi = 0;
  for &x in xs {
    while yi < ys.len() && ys[yi] < x {
      yi += 1;
    }
    if yi >= ys.len() || ys[yi] != x {
      return false;
    }
    yi += 1;
  }
  true
}

fn subsumption(acc: &mut NormLevel) {
  let keys: Vec<_> = acc.keys().cloned().collect();
  let snapshot: Vec<_> = acc.iter().map(|(k, v)| (k.clone(), v.clone())).collect();

  for (p1, n1) in acc.iter_mut() {
    for (p2, n2) in &snapshot {
      if !is_subset(p2, p1) {
        continue;
      }
      let same = p1.len() == p2.len();

      // Subsume constant
      if n1.constant != 0 {
        let max_var_offset =
          n1.var.iter().map(|v| v.offset).max().unwrap_or(0);
        let keep_const = (same || n1.constant > n2.constant)
          && (n2.var.is_empty()
            || n1.constant > max_var_offset + 1);
        if !keep_const {
          n1.constant = 0;
        }
      }

      // Subsume variables
      if !same && !n2.var.is_empty() {
        n1.var = subsume_vars(&n1.var, &n2.var);
      }
    }
  }

  // Remove empty nodes
  let _ = keys; // suppress unused warning
}

fn normalize_level<M: MetaMode>(l: &KLevel<M>) -> NormLevel {
  let mut acc = NormLevel::new();
  acc.insert(Vec::new(), Node::default());
  normalize_aux(l, &[], 0, &mut acc);
  subsumption(&mut acc);
  acc
}

fn le_vars(xs: &[VarNode], ys: &[VarNode]) -> bool {
  let mut yi = 0;
  for x in xs {
    loop {
      if yi >= ys.len() {
        return false;
      }
      match x.idx.cmp(&ys[yi].idx) {
        std::cmp::Ordering::Less => return false,
        std::cmp::Ordering::Equal => {
          if x.offset > ys[yi].offset {
            return false;
          }
          yi += 1;
          break;
        }
        std::cmp::Ordering::Greater => {
          yi += 1;
        }
      }
    }
  }
  true
}

fn norm_level_le(l1: &NormLevel, l2: &NormLevel) -> bool {
  for (p1, n1) in l1 {
    if n1.constant == 0 && n1.var.is_empty() {
      continue;
    }
    let mut found = false;
    for (p2, n2) in l2 {
      if (!n2.var.is_empty() || n1.var.is_empty())
        && is_subset(p2, p1)
        && (n1.constant <= n2.constant
          || n2.var.iter().any(|v| n1.constant <= v.offset + 1))
        && le_vars(&n1.var, &n2.var)
      {
        found = true;
        break;
      }
    }
    if !found {
      return false;
    }
  }
  true
}

fn norm_level_eq(l1: &NormLevel, l2: &NormLevel) -> bool {
  if l1.len() != l2.len() {
    return false;
  }
  for (k, v1) in l1 {
    match l2.get(k) {
      Some(v2) => {
        if v1.constant != v2.constant
          || v1.var.len() != v2.var.len()
          || v1.var.iter().zip(v2.var.iter()).any(|(a, b)| a != b)
        {
          return false;
        }
      }
      None => return false,
    }
  }
  true
}

// ============================================================================
// Public comparison API
// ============================================================================

/// Check if `a <= b + diff`. Assumes `a` and `b` are already reduced.
/// Uses heuristic as fast path, with complete normalization as fallback for
/// `diff = 0`.
pub fn leq<M: MetaMode>(a: &KLevel<M>, b: &KLevel<M>, diff: i64) -> bool {
  leq_heuristic(a, b, diff)
    || (diff == 0
      && norm_level_le(&normalize_level(a), &normalize_level(b)))
}

/// Semantic equality of levels. Assumes `a` and `b` are already reduced.
pub fn equal_level<M: MetaMode>(a: &KLevel<M>, b: &KLevel<M>) -> bool {
  equal_level_heuristic(a, b) || {
    let na = normalize_level(a);
    let nb = normalize_level(b);
    norm_level_eq(&na, &nb)
  }
}

/// Check if a level is definitionally zero. Assumes reduced.
pub fn is_zero<M: MetaMode>(l: &KLevel<M>) -> bool {
  matches!(l.data(), KLevelData::Zero)
}

/// Check if a level could possibly be zero (not guaranteed >= 1).
pub fn could_be_zero<M: MetaMode>(l: &KLevel<M>) -> bool {
  let s = reduce(l);
  could_be_zero_core(&s)
}

fn could_be_zero_core<M: MetaMode>(l: &KLevel<M>) -> bool {
  match l.data() {
    KLevelData::Zero => true,
    KLevelData::Succ(_) => false,
    KLevelData::Param(..) => true,
    KLevelData::Max(a, b) => {
      could_be_zero_core(a) && could_be_zero_core(b)
    }
    KLevelData::IMax(_, b) => could_be_zero_core(b),
  }
}

/// Check if a level is non-zero (guaranteed >= 1 for all param assignments).
pub fn is_nonzero<M: MetaMode>(l: &KLevel<M>) -> bool {
  !could_be_zero(l)
}

#[cfg(test)]
mod tests {
  use super::*;
  use super::super::types::Meta;

  fn anon() -> Name {
    Name::anon()
  }

  #[test]
  fn test_reduce_basic() {
    let zero = KLevel::<Meta>::zero();
    let one = KLevel::<Meta>::succ(zero.clone());
    let two = KLevel::<Meta>::succ(one.clone());

    assert!(is_zero::<Meta>(&reduce::<Meta>(&zero)));
    assert_eq!(reduce::<Meta>(&KLevel::max(zero.clone(), one.clone())), one);
    assert_eq!(
      reduce::<Meta>(&KLevel::max(one.clone(), two.clone())),
      two
    );
  }

  #[test]
  fn test_imax_reduce() {
    let zero = KLevel::<Meta>::zero();
    let one = KLevel::<Meta>::succ(zero.clone());

    // imax(a, 0) = 0
    assert!(is_zero::<Meta>(&reduce::<Meta>(&KLevel::imax(one.clone(), zero.clone()))));

    // imax(0, succ b) = max(0, succ b) = succ b
    assert_eq!(
      reduce::<Meta>(&KLevel::imax(zero.clone(), one.clone())),
      one
    );
  }

  #[test]
  fn test_leq_basic() {
    let zero = KLevel::<Meta>::zero();
    let one = KLevel::<Meta>::succ(zero.clone());
    let two = KLevel::<Meta>::succ(one.clone());

    assert!(leq::<Meta>(&zero, &one, 0));
    assert!(leq::<Meta>(&one, &two, 0));
    assert!(leq::<Meta>(&zero, &two, 0));
    assert!(!leq::<Meta>(&two, &one, 0));
    assert!(!leq::<Meta>(&one, &zero, 0));
  }

  #[test]
  fn test_equal_level() {
    let zero = KLevel::<Meta>::zero();
    let p0 = KLevel::<Meta>::param(0, anon());
    let p1 = KLevel::<Meta>::param(1, anon());

    assert!(equal_level::<Meta>(&zero, &zero));
    assert!(equal_level::<Meta>(&p0, &p0));
    assert!(!equal_level::<Meta>(&p0, &p1));

    // max(p0, p0) = p0
    let max_pp = reduce::<Meta>(&KLevel::max(p0.clone(), p0.clone()));
    assert!(equal_level::<Meta>(&max_pp, &p0));
  }

  #[test]
  fn test_inst_bulk_reduce() {
    let zero = KLevel::<Meta>::zero();
    let one = KLevel::<Meta>::succ(zero.clone());
    let p0 = KLevel::<Meta>::param(0, anon());

    // Substitute p0 -> one
    let result = inst_bulk_reduce::<Meta>(&[one.clone()], &p0);
    assert!(equal_level::<Meta>(&result, &one));

    // Substitute in max(p0, zero)
    let max_expr = KLevel::<Meta>::max(p0.clone(), zero.clone());
    let result = inst_bulk_reduce::<Meta>(&[one.clone()], &max_expr);
    assert!(equal_level::<Meta>(&reduce::<Meta>(&result), &one));
  }
}
