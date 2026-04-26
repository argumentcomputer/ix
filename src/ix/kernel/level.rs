//! Universe levels with optional metadata and Géran's canonical-form comparison.
//!
//! `KUniv<M>` is an Arc-wrapped universe level. Each variant carries a blake3
//! Merkle hash (`Addr`) for content addressing. `Param` additionally carries
//! `M::MField<Name>` — the parameter name in Meta mode, erased to `()` in
//! Anon mode.
//!
//! # Relationship to Lean4Lean
//!
//! `normalize_level` is a line-by-line port of Lean4Lean's `Level.Normalize`
//! (see `refs/lean4lean/Lean4Lean/Level.lean`), based on Yoan Géran's paper
//! "A Canonical Form for Universe Levels in Impredicative Type Theory"
//! (<https://lmf.cnrs.fr/downloads/Perso/long.pdf>). The Rust `NormLevel` is
//! a `BTreeMap<Vec<u64>, Node>` indexed by sorted param-index paths — the
//! Rust analogue of Lean4Lean's `Std.TreeMap (List Name) Node`, with `u64`
//! param indices replacing `Name` since our anon-mode params are positional.
//!
//! Point of divergence: `norm_level_le` is intentionally stronger than
//! Lean4Lean's `NormLevel.le`. Lean4Lean's variant looks for a *single*
//! `p2 ⊆ p1` entry in `l2` that dominates both the constant and the variable
//! contributions of `n_p1`; ours splits that into independent per-ingredient
//! searches (`covers_const` and `covers_var`). See the detailed doc on
//! `norm_level_le` for the concrete witness that motivated the change.
//!
//! This is a soundness-preserving completeness strengthening, not a
//! disagreement with the canonical-form theory: Lean4Lean's
//! `NormLevel.subsumption_eval` is `sorry` in
//! `refs/lean4lean/Lean4Lean/Verify/Level.lean:545`, and there is no
//! `geq'_wf` / `NormLevel.le_wf` theorem anywhere in the Verify tree, so the
//! "complete for level algebra" claim in Lean4Lean's `divergences.md` is
//! aspirational for `geq'` specifically. `univ_eq` (via `norm_level_eq`)
//! matches Lean4Lean's `isEquiv'` bit-for-bit, since that direction *is*
//! proven sound (`isEquiv'_wf`, `Verify/Level.lean:578`) and the witness
//! that exposed `NormLevel.le`'s gap is not an equality case.

use std::collections::BTreeMap;
use std::fmt;
use std::sync::Arc;

use crate::ix::env::{Name, UIMAX, UMAX, UPARAM, USUCC, UZERO};

use super::env::Addr;
use super::mode::{KernelMode, MetaDisplay, MetaHash};

/// Universe level. Thin Arc wrapper — cheap to clone, O(1) identity
/// via `Arc::ptr_eq`.
#[derive(Clone, Debug)]
pub struct KUniv<M: KernelMode>(Arc<UnivData<M>>);

/// Universe level data. Each variant carries its Merkle hash (`Addr`).
#[derive(Clone, Debug)]
pub enum UnivData<M: KernelMode> {
  Zero(Addr),
  Succ(KUniv<M>, Addr),
  Max(KUniv<M>, KUniv<M>, Addr),
  IMax(KUniv<M>, KUniv<M>, Addr),
  Param(u64, M::MField<Name>, Addr),
}

impl<M: KernelMode> KUniv<M> {
  /// Wrap raw data into a `KUniv`.
  pub fn new(data: UnivData<M>) -> Self {
    KUniv(Arc::new(data))
  }

  pub fn data(&self) -> &UnivData<M> {
    &self.0
  }

  pub fn addr(&self) -> &Addr {
    match self.data() {
      UnivData::Zero(h)
      | UnivData::Succ(_, h)
      | UnivData::Max(_, _, h)
      | UnivData::IMax(_, _, h)
      | UnivData::Param(_, _, h) => h,
    }
  }

  pub fn ptr_eq(&self, other: &KUniv<M>) -> bool {
    Arc::ptr_eq(&self.0, &other.0)
  }

  /// Structural equality by Merkle hash (pointer-first fast path).
  pub fn hash_eq(&self, other: &KUniv<M>) -> bool {
    self.ptr_eq(other) || self.addr() == other.addr()
  }

  /// True if this level is definitionally zero (Prop).
  pub fn is_zero(&self) -> bool {
    matches!(self.data(), UnivData::Zero(_))
  }

  /// True if this level is an explicit numeral: `Succ^n(Zero)` for some n ≥ 0.
  pub fn is_explicit(&self) -> bool {
    match self.data() {
      UnivData::Zero(_) => true,
      UnivData::Succ(inner, _) => inner.is_explicit(),
      _ => false,
    }
  }

  /// True if this level is `Succ^n(base)` with n > 0. Such a level is never
  /// zero under any parameter assignment.
  pub fn is_never_zero(&self) -> bool {
    match self.data() {
      UnivData::Succ(..) => true,
      UnivData::Max(a, b, _) => a.is_never_zero() || b.is_never_zero(),
      UnivData::IMax(_, b, _) => b.is_never_zero(),
      _ => false,
    }
  }

  /// Peel the outermost constant offset: returns `(base, n)` where
  /// `self = Succ^n(base)` and `base` is not `Succ`.
  pub fn offset(&self) -> (&KUniv<M>, u64) {
    let mut u = self;
    let mut n = 0u64;
    loop {
      match u.data() {
        UnivData::Succ(inner, _) => {
          u = inner;
          n += 1;
        },
        _ => return (u, n),
      }
    }
  }
}

impl<M: KernelMode> KUniv<M> {
  pub fn zero() -> Self {
    KUniv::new(UnivData::Zero(Arc::new(blake3::hash(&[UZERO]))))
  }

  pub fn succ(inner: KUniv<M>) -> Self {
    let mut hasher = blake3::Hasher::new();
    hasher.update(&[USUCC]);
    hasher.update(inner.addr().as_bytes());
    KUniv::new(UnivData::Succ(inner, Arc::new(hasher.finalize())))
  }

  /// Construct `max(a, b)` with Lean-style simplifications:
  ///
  /// - `max(k₁, k₂) = max(k₁, k₂)` when both are explicit numerals
  /// - `max(a, a) = a`
  /// - `max(0, a) = a`, `max(a, 0) = a`
  /// - `max(a, max(a, b)) = max(a, b)` (absorption)
  /// - `max(max(a, b), b) = max(a, b)` (absorption)
  /// - `max(succ^n(base), succ^m(base)) = succ^max(n,m)(base)` (same-base offset)
  ///
  /// Matches Lean's `mk_max` in `kernel/level.cpp:81-103`.
  pub fn max(a: KUniv<M>, b: KUniv<M>) -> Self {
    // Both explicit numerals (Succ^n(Zero)): take the larger.
    if a.is_explicit() && b.is_explicit() {
      let (_, na) = a.offset();
      let (_, nb) = b.offset();
      return if na >= nb { a } else { b };
    }
    // Structural equality.
    if a == b {
      return a;
    }
    // Zero absorption.
    if a.is_zero() {
      return b;
    }
    if b.is_zero() {
      return a;
    }
    // max(a, max(a, b')) = max(a, b'), max(a, max(b', a)) = max(b', a)
    if let UnivData::Max(bl, br, _) = b.data()
      && (*bl == a || *br == a) {
        return b;
      }
    // max(max(a', b), b) = max(a', b), max(max(b, a'), b) = max(b, a')
    if let UnivData::Max(al, ar, _) = a.data()
      && (*al == b || *ar == b) {
        return a;
      }
    // Same base, different offsets: succ^n(x) vs succ^m(x) → take the larger.
    let (base_a, off_a) = a.offset();
    let (base_b, off_b) = b.offset();
    if base_a == base_b {
      return if off_a >= off_b { a } else { b };
    }
    // No simplification — construct the raw Max node.
    Self::max_raw(a, b)
  }

  /// Raw `Max` constructor without simplification. Used by `max()` after
  /// all simplification opportunities are exhausted.
  fn max_raw(a: KUniv<M>, b: KUniv<M>) -> Self {
    let mut hasher = blake3::Hasher::new();
    hasher.update(&[UMAX]);
    hasher.update(a.addr().as_bytes());
    hasher.update(b.addr().as_bytes());
    KUniv::new(UnivData::Max(a, b, Arc::new(hasher.finalize())))
  }

  /// Construct `imax(a, b)` with Lean-style simplifications:
  ///
  /// - `imax(a, b) = max(a, b)` when `b` is never zero
  /// - `imax(a, 0) = 0`
  /// - `imax(0, b) = b`, `imax(1, b) = b`
  /// - `imax(a, a) = a`
  ///
  /// Matches Lean's `mk_imax` in `kernel/level.cpp:112-120`.
  pub fn imax(a: KUniv<M>, b: KUniv<M>) -> Self {
    if b.is_never_zero() {
      return Self::max(a, b);
    }
    if b.is_zero() {
      return b; // imax(a, 0) = 0
    }
    if a.is_zero() {
      return b; // imax(0, b) = b
    }
    // imax(1, b) = b  (Lean: is_one check)
    if let UnivData::Succ(inner, _) = a.data()
      && inner.is_zero() {
        return b;
      }
    if a == b {
      return a; // imax(a, a) = a
    }
    // No simplification — construct raw IMax node.
    let mut hasher = blake3::Hasher::new();
    hasher.update(&[UIMAX]);
    hasher.update(a.addr().as_bytes());
    hasher.update(b.addr().as_bytes());
    KUniv::new(UnivData::IMax(a, b, Arc::new(hasher.finalize())))
  }

  pub fn param(idx: u64, name: M::MField<Name>) -> Self {
    let mut hasher = blake3::Hasher::new();
    hasher.update(&[UPARAM]);
    hasher.update(&idx.to_le_bytes());
    name.meta_hash(&mut hasher);
    KUniv::new(UnivData::Param(idx, name, Arc::new(hasher.finalize())))
  }
}

// Structural equality by Merkle hash.
impl<M: KernelMode> PartialEq for KUniv<M> {
  fn eq(&self, other: &Self) -> bool {
    self.hash_eq(other)
  }
}

impl<M: KernelMode> Eq for KUniv<M> {}

/// Meta mode: shows names when available, positional index as fallback.
/// Anon mode: shows positional parameter indices.
impl<M: KernelMode> fmt::Display for KUniv<M> {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    fmt_univ(self, f)
  }
}

fn fmt_univ<M: KernelMode>(
  u: &KUniv<M>,
  f: &mut fmt::Formatter<'_>,
) -> fmt::Result {
  match u.data() {
    UnivData::Zero(_) => write!(f, "0"),
    UnivData::Succ(_, _) => {
      let (base, n) = u.offset();
      if base.is_zero() {
        write!(f, "{n}")
      } else {
        fmt_univ(base, f)?;
        write!(f, "+{n}")
      }
    },
    UnivData::Max(a, b, _) => {
      write!(f, "max(")?;
      fmt_univ(a, f)?;
      write!(f, ", ")?;
      fmt_univ(b, f)?;
      write!(f, ")")
    },
    UnivData::IMax(a, b, _) => {
      write!(f, "imax(")?;
      fmt_univ(a, f)?;
      write!(f, ", ")?;
      fmt_univ(b, f)?;
      write!(f, ")")
    },
    UnivData::Param(idx, name, _) => {
      if name.has_meta() {
        name.meta_fmt(f)
      } else {
        write!(f, "u{idx}")
      }
    },
  }
}

// Géran's canonical-form normalization and comparison
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct VarNode {
  idx: u64,
  offset: u64,
}

#[derive(Debug, Clone, Default)]
struct Node {
  constant: u64,
  var: Vec<VarNode>,
}

impl Node {
  fn add_var(&mut self, idx: u64, k: u64) {
    match self.var.binary_search_by_key(&idx, |v| v.idx) {
      Ok(pos) => self.var[pos].offset = self.var[pos].offset.max(k),
      Err(pos) => self.var.insert(pos, VarNode { idx, offset: k }),
    }
  }
}

/// Canonical form: a map from imax-paths (sorted param indices representing
/// the conditioning chain) to nodes tracking constant offsets and variable
/// contributions.
type NormLevel = BTreeMap<Vec<u64>, Node>;

fn norm_add_var(s: &mut NormLevel, idx: u64, k: u64, path: &[u64]) {
  s.entry(path.to_vec()).or_default().add_var(idx, k);
}

/// Insert `(idx, k)` into the var list at `path`, taking the max of offsets
/// when `idx` is already present. Mirrors Lean4Lean's
/// `NormLevel.addNode v k path'` (`refs/lean4lean/Lean4Lean/Level.lean:92`);
/// `k` must be the current succ-accumulator from `normalize_aux`.
///
/// An earlier port of this function dropped `k` and always inserted
/// `(idx, 0)`, which silently mis-normalized `Succ^n(imax(u, Param v))`
/// shapes for `n > 0`. Keep the `k` parameter.
fn norm_add_node(s: &mut NormLevel, idx: u64, k: u64, path: &[u64]) {
  s.entry(path.to_vec()).or_default().add_var(idx, k);
}

fn norm_add_const(s: &mut NormLevel, k: u64, path: &[u64]) {
  if k == 0 || (k == 1 && !path.is_empty()) {
    return;
  }
  let node = s.entry(path.to_vec()).or_default();
  node.constant = node.constant.max(k);
}

/// Insert into a sorted list, returning `None` if already present.
fn ordered_insert(a: u64, list: &[u64]) -> Option<Vec<u64>> {
  match list.binary_search(&a) {
    Ok(_) => None,
    Err(pos) => {
      let mut result = list.to_vec();
      result.insert(pos, a);
      Some(result)
    },
  }
}

/// Recursively flatten a level into canonical form, accumulating into `acc`.
/// `path` tracks the imax-conditioning chain, `k` is the accumulated succ offset.
fn normalize_aux<M: KernelMode>(
  l: &KUniv<M>,
  path: &[u64],
  k: u64,
  acc: &mut NormLevel,
) {
  match l.data() {
    UnivData::Zero(_) => {
      norm_add_const(acc, k, path);
    },
    UnivData::Succ(inner, _) => {
      normalize_aux(inner, path, k + 1, acc);
    },
    UnivData::Max(a, b, _) => {
      normalize_aux(a, path, k, acc);
      normalize_aux(b, path, k, acc);
    },
    UnivData::IMax(_, b, _) if b.is_zero() => {
      norm_add_const(acc, k, path);
    },
    UnivData::IMax(u, b, _) if matches!(b.data(), UnivData::Succ(..)) => {
      if let UnivData::Succ(v, _) = b.data() {
        normalize_aux(u, path, k, acc);
        normalize_aux(v, path, k + 1, acc);
      }
    },
    UnivData::IMax(u, b, _) if matches!(b.data(), UnivData::Max(..)) => {
      if let UnivData::Max(v, w, _) = b.data() {
        normalize_imax_max(u, v, w, path, k, acc);
      }
    },
    UnivData::IMax(u, b, _) if matches!(b.data(), UnivData::IMax(..)) => {
      if let UnivData::IMax(v, w, _) = b.data() {
        normalize_imax_imax(u, v, w, path, k, acc);
      }
    },
    UnivData::IMax(u, b, _) if matches!(b.data(), UnivData::Param(..)) => {
      if let UnivData::Param(idx, _, _) = b.data() {
        let idx = *idx;
        if let Some(new_path) = ordered_insert(idx, path) {
          // When param(idx) = 0, imax(u, 0) = 0, contributing k from outer succs.
          norm_add_const(acc, k, path);
          norm_add_node(acc, idx, k, &new_path);
          normalize_aux(u, &new_path, k, acc);
        } else {
          // Param(idx) is already in path (so we're in an `imax(u, v)` where
          // v = Param(idx) and idx is fixed > 0 by the enclosing chain).
          // The outer k Succ's still contribute when idx > 0, which it is
          // along this path. Matches Lean4Lean's `acc.addVar v k path`.
          if k != 0 {
            norm_add_var(acc, idx, k, path);
          }
          normalize_aux(u, path, k, acc);
        }
      }
    },
    UnivData::Param(idx, _, _) => {
      let idx = *idx;
      if let Some(new_path) = ordered_insert(idx, path) {
        norm_add_const(acc, k, path);
        norm_add_node(acc, idx, k, &new_path);
      } else if k != 0 {
        norm_add_var(acc, idx, k, path);
      }
    },
    // All UnivData variants are covered above. If this is reached,
    // it indicates a bug (e.g., a new variant was added without updating this match).
    #[allow(unreachable_patterns)]
    _ => unreachable!("normalize_aux: all UnivData variants should be covered"),
  }
}

/// Handle `imax(u, max(v, w))` = `max(imax(u, v), imax(u, w))`.
fn normalize_imax_max<M: KernelMode>(
  u: &KUniv<M>,
  v: &KUniv<M>,
  w: &KUniv<M>,
  path: &[u64],
  k: u64,
  acc: &mut NormLevel,
) {
  normalize_imax_dispatch(u, v, path, k, acc);
  normalize_imax_dispatch(u, w, path, k, acc);
}

/// Handle `imax(u, imax(v, w))` = `max(imax(u, w), imax(v, w))`.
fn normalize_imax_imax<M: KernelMode>(
  u: &KUniv<M>,
  v: &KUniv<M>,
  w: &KUniv<M>,
  path: &[u64],
  k: u64,
  acc: &mut NormLevel,
) {
  normalize_imax_dispatch(u, w, path, k, acc);
  normalize_imax_dispatch(v, w, path, k, acc);
}

/// Dispatch `imax(a, b)` normalization based on `b`'s shape.
fn normalize_imax_dispatch<M: KernelMode>(
  a: &KUniv<M>,
  b: &KUniv<M>,
  path: &[u64],
  k: u64,
  acc: &mut NormLevel,
) {
  if b.is_zero() {
    norm_add_const(acc, k, path);
  } else if let UnivData::Succ(v, _) = b.data() {
    normalize_aux(a, path, k, acc);
    normalize_aux(v, path, k + 1, acc);
  } else if let UnivData::Max(v, w, _) = b.data() {
    normalize_imax_max(a, v, w, path, k, acc);
  } else if let UnivData::IMax(v, w, _) = b.data() {
    normalize_imax_imax(a, v, w, path, k, acc);
  } else if let UnivData::Param(idx, _, _) = b.data() {
    let idx = *idx;
    if let Some(new_path) = ordered_insert(idx, path) {
      // When param(idx) = 0, imax(a, 0) = 0, contributing k from outer succs.
      norm_add_const(acc, k, path);
      norm_add_node(acc, idx, k, &new_path);
      normalize_aux(a, &new_path, k, acc);
    } else {
      // idx is already in path; outer k Succ's still contribute.
      // Matches Lean4Lean's `acc.addVar v k path`.
      if k != 0 {
        norm_add_var(acc, idx, k, path);
      }
      normalize_aux(a, path, k, acc);
    }
  } else {
    // All UnivData variants for `b` are covered above.
    unreachable!(
      "normalize_imax_dispatch: all UnivData variants for b should be covered"
    );
  }
}

// Subsumption (Phase 2)
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
      },
      std::cmp::Ordering::Equal => {
        if xs[xi].offset > ys[yi].offset {
          result.push(xs[xi].clone());
        }
        xi += 1;
        yi += 1;
      },
      std::cmp::Ordering::Greater => {
        yi += 1;
      },
    }
  }
  result
}

fn is_subset(xs: &[u64], ys: &[u64]) -> bool {
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
  let snapshot: Vec<_> =
    acc.iter().map(|(k, v)| (k.clone(), v.clone())).collect();

  for (p1, n1) in acc.iter_mut() {
    for (p2, n2) in &snapshot {
      if !is_subset(p2, p1) {
        continue;
      }
      let same = p1.len() == p2.len();

      if n1.constant != 0 {
        let max_var_offset = n1.var.iter().map(|v| v.offset).max().unwrap_or(0);
        let keep_const = (same || n1.constant > n2.constant)
          && (n2.var.is_empty() || n1.constant > max_var_offset + 1);
        if !keep_const {
          n1.constant = 0;
        }
      }

      if !same && !n2.var.is_empty() {
        n1.var = subsume_vars(&n1.var, &n2.var);
      }
    }
  }
}

// Comparison

/// Check whether some entry `(p2, n2)` in `l2` with `p2 ⊆ p1` provides a
/// contribution that dominates `n1.const` along every assignment satisfying
/// `p1`'s activation. A `p2` entry contributes `n_p2.const` unconditionally
/// (in that branch), and each `v ∈ n_p2.var` contributes at least `v.offset + 1`
/// because `v.idx ∈ p2 ⊆ p1` guarantees `u_v ≥ 1`.
fn covers_const(l2: &NormLevel, p1: &[u64], c: u64) -> bool {
  l2.iter().any(|(p2, n2)| {
    is_subset(p2, p1)
      && (c <= n2.constant || n2.var.iter().any(|v| c <= v.offset + 1))
  })
}

/// Check whether some entry `(p2, n2)` in `l2` with `p2 ⊆ p1` contains a
/// variable node that dominates `(w, off)`: i.e., some `v ∈ n_p2.var` with
/// `v.idx == w && v.offset >= off`. Because `v.idx` is always in `p2`, the
/// matching p2 automatically has `w ∈ p2 ⊆ p1`, keeping the branch analysis
/// consistent.
fn covers_var(l2: &NormLevel, p1: &[u64], w: u64, off: u64) -> bool {
  l2.iter().any(|(p2, n2)| {
    is_subset(p2, p1) && n2.var.iter().any(|v| v.idx == w && v.offset >= off)
  })
}

/// Semantic `l1 ≤ l2` on canonical forms. For each `(p1, n1)` in `l1`, the
/// contribution `max(n1.const, u_w + v.off for v ∈ n1.var)` in the branch
/// where `p1`'s params are all positive must be dominated by the max of
/// contributions from `{(p2, n_p2) : p2 ⊆ p1}` in the same branch.
///
/// # Divergence from Lean4Lean
///
/// Lean4Lean's `NormLevel.le` (`refs/lean4lean/Lean4Lean/Level.lean:164`)
/// looks for a *single* `p2` covering both `n1.const` and `n1.var`
/// simultaneously — sound, but incomplete. Concrete witness (see
/// `prop_univ_max_is_geq_both_components_imax_witness`):
///
/// ```text
/// a = Succ^3(0)
/// b = imax(imax(a, Param 0), Param 1)
/// m = max(a, b)
/// ```
///
/// After normalization + subsumption:
///
/// ```text
/// normalize(m): [] → const=3, [1] → var=[(1,0)], [0,1] → var=[(0,0)]
/// normalize(b): [] → const=0, [1] → var=[(1,0)], [0,1] → {const=3, var=[(0,0)]}
/// ```
///
/// Checking `b ≤ m` at `p1 = [0,1]` needs both `const=3` and `var=[(0,0)]`.
/// `m[[]]` covers the const (no var); `m[[0,1]]` covers the var (const was
/// zeroed out by subsumption against `m[[]]`). No single `p2 ⊆ [0,1]` in
/// `m` has both, so Lean4Lean's `le` reports `m ≱ b` even though `m ≥ b`
/// holds for every parameter assignment.
///
/// The version here splits the check into `covers_const` and `covers_var`,
/// each searching `l2` independently. This is sound:
///
/// - For `n1.const = C`, if some `p2 ⊆ p1` has `n_p2.const ≥ C`, then along
///   any `ρ` with `p1` active, `p2` is active too, so `l2`'s total already
///   includes `n_p2.const ≥ C`. Same argument for the fallback clause
///   `v.offset + 1 ≥ C` with `v ∈ n_p2.var`, because every `v` inserted
///   during `normalize_aux` has `v.idx ∈ p2` (so `u_v ≥ 1` in an active
///   branch).
/// - For each `(w, off) ∈ n1.var`, if some `p2 ⊆ p1` has `(w, off') ∈
///   n_p2.var` with `off' ≥ off`, then `l2`'s contribution along active
///   `p1` is at least `u_w + off' ≥ u_w + off`.
///
/// This matches what Lean4Lean's paper-level theory expects but its
/// implementation doesn't cover (cf. the `sorry` on
/// `NormLevel.subsumption_eval` in `Verify/Level.lean:545`, and the absence
/// of any `geq'_wf`).
fn norm_level_le(l1: &NormLevel, l2: &NormLevel) -> bool {
  for (p1, n1) in l1 {
    if n1.constant == 0 && n1.var.is_empty() {
      continue;
    }
    if n1.constant != 0 && !covers_const(l2, p1, n1.constant) {
      return false;
    }
    for v in &n1.var {
      if !covers_var(l2, p1, v.idx, v.offset) {
        return false;
      }
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
      },
      None => return false,
    }
  }
  true
}

/// Normalize a universe level to Géran's canonical form.
fn normalize_level<M: KernelMode>(l: &KUniv<M>) -> NormLevel {
  let mut acc = NormLevel::new();
  acc.insert(Vec::new(), Node::default());
  normalize_aux(l, &[], 0, &mut acc);
  subsumption(&mut acc);
  acc
}

/// Semantic universe equality: `u ≡ v` for all parameter assignments.
pub fn univ_eq<M: KernelMode>(u: &KUniv<M>, v: &KUniv<M>) -> bool {
  u.hash_eq(v) || norm_level_eq(&normalize_level(u), &normalize_level(v))
}

/// Check `u ≥ v` for all parameter assignments.
pub fn univ_geq<M: KernelMode>(u: &KUniv<M>, v: &KUniv<M>) -> bool {
  u.hash_eq(v)
    || v.is_zero()
    || norm_level_le(&normalize_level(v), &normalize_level(u))
}

#[cfg(test)]
mod tests {
  use super::super::mode::{Anon, Meta};
  use super::*;
  use crate::ix::env::Name;

  type MU = KUniv<Meta>;
  type AU = KUniv<Anon>;

  fn mk_name(s: &str) -> Name {
    let mut name = Name::anon();
    for part in s.split('.') {
      name = Name::str(name, part.to_string());
    }
    name
  }

  // ---- Constructors & hashing ----

  #[test]
  fn zero_hash_deterministic() {
    assert_eq!(MU::zero().addr(), MU::zero().addr());
    assert_eq!(AU::zero().addr(), AU::zero().addr());
  }

  #[test]
  fn zero_and_succ_differ() {
    let z = MU::zero();
    let s = MU::succ(z.clone());
    assert_ne!(z.addr(), s.addr());
  }

  #[test]
  fn succ_hash_depends_on_child() {
    let s1 = MU::succ(MU::zero());
    let s2 = MU::succ(MU::succ(MU::zero()));
    assert_ne!(s1.addr(), s2.addr());
  }

  #[test]
  fn max_hash_depends_on_order() {
    let p0 = AU::param(0, ());
    let p1 = AU::param(1, ());
    let m1 = AU::max(p0.clone(), p1.clone());
    let m2 = AU::max(p1, p0);
    assert_ne!(m1.addr(), m2.addr());
  }

  #[test]
  fn max_vs_imax_differ() {
    let p0 = AU::param(0, ());
    let p1 = AU::param(1, ());
    let m = AU::max(p0.clone(), p1.clone());
    let im = AU::imax(p0, p1);
    assert_ne!(m.addr(), im.addr());
  }

  #[test]
  fn param_index_differs() {
    let p0 = AU::param(0, ());
    let p1 = AU::param(1, ());
    assert_ne!(p0.addr(), p1.addr());
  }

  // ---- Meta mode: names affect hash ----

  #[test]
  fn meta_param_name_affects_hash() {
    let a = MU::param(0, mk_name("u"));
    let b = MU::param(0, mk_name("v"));
    assert_ne!(a.addr(), b.addr());
  }

  #[test]
  fn meta_param_same_name_same_hash() {
    let a = MU::param(0, mk_name("u"));
    let b = MU::param(0, mk_name("u"));
    assert_eq!(a.addr(), b.addr());
  }

  // ---- Anon mode: names erased ----

  #[test]
  fn anon_param_same_index_same_hash() {
    let a = AU::param(0, ());
    let b = AU::param(0, ());
    assert_eq!(a.addr(), b.addr());
  }

  // ---- Anon vs Meta structural hash differs (meta contributes name bytes) ----

  #[test]
  fn anon_vs_meta_named_param_differ() {
    let anon = AU::param(0, ());
    let meta = MU::param(0, mk_name("u"));
    assert_ne!(anon.addr(), meta.addr());
  }

  #[test]
  fn anon_vs_meta_anon_param_same() {
    // Meta with anonymous name: UPARAM ++ idx ++ anon_name_hash_bytes
    // Anon: UPARAM ++ idx (no name bytes)
    // These differ because Meta still writes the anon name hash.
    let anon = AU::param(0, ());
    let meta = MU::param(0, Name::anon());
    assert_ne!(anon.addr(), meta.addr());
  }

  // ---- PartialEq ----

  #[test]
  fn eq_by_hash() {
    let a = MU::succ(MU::zero());
    let b = MU::succ(MU::zero());
    assert_eq!(a, b);
    assert_ne!(a, MU::zero());
  }

  // ---- is_zero / is_never_zero / offset ----

  #[test]
  fn is_zero_checks() {
    assert!(AU::zero().is_zero());
    assert!(!AU::succ(AU::zero()).is_zero());
    assert!(!AU::param(0, ()).is_zero());
  }

  #[test]
  fn is_never_zero_checks() {
    let z = AU::zero();
    let s1 = AU::succ(z.clone());
    let p = AU::param(0, ());
    assert!(!z.is_never_zero());
    assert!(s1.is_never_zero());
    assert!(!p.is_never_zero());
    // max(succ(0), p) is never zero
    assert!(AU::max(s1.clone(), p.clone()).is_never_zero());
    // imax(p, succ(0)) is never zero
    assert!(AU::imax(p, s1).is_never_zero());
  }

  #[test]
  fn offset_peeling() {
    let z = MU::zero();
    let s1 = MU::succ(z.clone());
    let s3 = MU::succ(MU::succ(MU::succ(MU::param(0, mk_name("u")))));
    assert_eq!(z.offset().1, 0);
    assert_eq!(s1.offset().1, 1);
    assert!(s1.offset().0.is_zero());
    assert_eq!(s3.offset().1, 3);
    assert!(matches!(s3.offset().0.data(), UnivData::Param(0, _, _)));
  }

  // ---- Display ----

  #[test]
  fn display_zero() {
    assert_eq!(format!("{}", MU::zero()), "0");
    assert_eq!(format!("{}", AU::zero()), "0");
  }

  #[test]
  fn display_succ_chain() {
    let s2 = MU::succ(MU::succ(MU::zero()));
    assert_eq!(format!("{s2}"), "2");
  }

  #[test]
  fn display_succ_offset() {
    let p = MU::param(0, mk_name("u"));
    let sp = MU::succ(MU::succ(p));
    assert_eq!(format!("{sp}"), "u+2");
  }

  #[test]
  fn display_anon_param() {
    assert_eq!(format!("{}", AU::param(0, ())), "u0");
    assert_eq!(format!("{}", AU::param(3, ())), "u3");
  }

  #[test]
  fn display_meta_named_param() {
    assert_eq!(format!("{}", MU::param(0, mk_name("v"))), "v");
    assert_eq!(format!("{}", MU::param(1, mk_name("w"))), "w");
  }

  #[test]
  fn display_meta_anonymous_param() {
    assert_eq!(format!("{}", MU::param(0, Name::anon())), "u0");
  }

  #[test]
  fn display_max() {
    let m = AU::max(AU::param(0, ()), AU::param(1, ()));
    assert_eq!(format!("{m}"), "max(u0, u1)");
  }

  #[test]
  fn display_imax() {
    // imax(u0, 1) simplifies to max(u0, 1) since 1 is never zero.
    let im = AU::imax(AU::param(0, ()), AU::succ(AU::zero()));
    assert_eq!(format!("{im}"), "max(u0, 1)");
    // imax with a potentially-zero rhs stays as imax.
    let im2 = AU::imax(AU::param(0, ()), AU::param(1, ()));
    assert_eq!(format!("{im2}"), "imax(u0, u1)");
  }

  #[test]
  fn display_meta_max_with_names() {
    let m = MU::max(MU::param(0, mk_name("u")), MU::param(1, mk_name("v")));
    assert_eq!(format!("{m}"), "max(u, v)");
  }

  // ---- Géran comparison ----

  #[test]
  fn univ_eq_basic() {
    let z = AU::zero();
    let s1 = AU::succ(z.clone());
    let p = AU::param(0, ());
    assert!(univ_eq(&z, &z));
    assert!(univ_eq(&s1, &s1));
    assert!(!univ_eq(&z, &s1));
    assert!(!univ_eq(&s1, &p));
  }

  #[test]
  fn univ_eq_max_commutative() {
    let p0 = AU::param(0, ());
    let p1 = AU::param(1, ());
    let m1 = AU::max(p0.clone(), p1.clone());
    let m2 = AU::max(p1, p0);
    assert!(univ_eq(&m1, &m2));
  }

  #[test]
  fn univ_eq_max_idempotent() {
    let p = AU::param(0, ());
    let m = AU::max(p.clone(), p.clone());
    assert!(univ_eq(&m, &p));
  }

  #[test]
  fn univ_eq_max_zero() {
    let z = AU::zero();
    let p = AU::param(0, ());
    let m = AU::max(p.clone(), z);
    assert!(univ_eq(&m, &p));
  }

  #[test]
  fn univ_eq_imax_zero() {
    let z = AU::zero();
    let p = AU::param(0, ());
    let im = AU::imax(p, z.clone());
    assert!(univ_eq(&im, &z));
  }

  #[test]
  fn univ_eq_imax_succ() {
    let s1 = AU::succ(AU::zero());
    let p = AU::param(0, ());
    // imax(p, succ(0)) = max(p, succ(0))
    let im = AU::imax(p.clone(), s1.clone());
    let m = AU::max(p, s1);
    assert!(univ_eq(&im, &m));
  }

  #[test]
  fn univ_eq_imax_distribute() {
    let p0 = AU::param(0, ());
    let p1 = AU::param(1, ());
    let p2 = AU::param(2, ());
    // imax(p0, max(p1, p2)) = max(imax(p0, p1), imax(p0, p2))
    let m = AU::max(p1.clone(), p2.clone());
    let lhs = AU::imax(p0.clone(), m);
    let im1 = AU::imax(p0.clone(), p1);
    let im2 = AU::imax(p0, p2);
    let rhs = AU::max(im1, im2);
    assert!(univ_eq(&lhs, &rhs));
  }

  #[test]
  fn univ_geq_basic() {
    let z = AU::zero();
    let s1 = AU::succ(z.clone());
    let s2 = AU::succ(s1.clone());
    let p = AU::param(0, ());
    assert!(univ_geq(&z, &z));
    assert!(univ_geq(&s1, &z));
    assert!(univ_geq(&p, &z));
    assert!(univ_geq(&s2, &s1));
    assert!(!univ_geq(&s1, &s2));
  }

  #[test]
  fn univ_geq_param() {
    let p = AU::param(0, ());
    let sp = AU::succ(p.clone());
    assert!(univ_geq(&sp, &p));
    assert!(!univ_geq(&p, &sp));
  }

  // ---- Meta mode Géran (names don't affect semantic equality) ----

  #[test]
  fn meta_univ_eq_ignores_names() {
    // Same structure, different names — semantically equal
    let a = MU::param(0, mk_name("u"));
    let b = MU::param(0, mk_name("v"));
    // Hash differs (names contribute), but Géran comparison sees same index
    assert_ne!(a.addr(), b.addr());
    assert!(univ_eq(&a, &b));
  }

  // =========================================================================
  // Property-style tests for universe-level algebra invariants.
  //
  // Use a deterministic seeded generator (xorshift) to produce randomized
  // `KUniv<Anon>` values of bounded depth and check algebraic laws:
  // reflexivity, symmetry of equality, transitivity of geq, and interaction
  // between geq and eq.
  // =========================================================================

  struct UPrng(u64);
  impl UPrng {
    fn new(seed: u64) -> Self {
      UPrng(seed.wrapping_mul(0x9E37_79B9_7F4A_7C15) ^ 0xDEAD_BEEF_CAFE_BABE)
    }
    fn next_u64(&mut self) -> u64 {
      let mut x = self.0;
      x ^= x << 13;
      x ^= x >> 7;
      x ^= x << 17;
      self.0 = x;
      x
    }
    fn next_u32(&mut self, bound: u32) -> u32 {
      // Truncating to u32 is intentional for the test RNG.
      #[allow(clippy::cast_possible_truncation)]
      let lo = self.next_u64() as u32;
      lo % bound.max(1)
    }
  }

  /// Generate a bounded-depth `KUniv<Anon>`. Parameter indices are drawn
  /// from `0..=max_param` so multiple universes in the same test can share
  /// parameters — important for geq transitivity tests.
  fn gen_univ(rng: &mut UPrng, depth: u32, max_param: u64) -> AU {
    if depth == 0 {
      return match rng.next_u32(3) {
        0 => AU::zero(),
        1 => AU::param(rng.next_u64() % (max_param + 1), ()),
        _ => AU::succ(AU::zero()),
      };
    }
    match rng.next_u32(5) {
      0 => AU::zero(),
      1 => AU::param(rng.next_u64() % (max_param + 1), ()),
      2 => AU::succ(gen_univ(rng, depth - 1, max_param)),
      3 => AU::max(
        gen_univ(rng, depth - 1, max_param),
        gen_univ(rng, depth - 1, max_param),
      ),
      _ => AU::imax(
        gen_univ(rng, depth - 1, max_param),
        gen_univ(rng, depth - 1, max_param),
      ),
    }
  }

  #[test]
  fn prop_univ_eq_reflexive() {
    let mut rng = UPrng::new(0x1234);
    for _ in 0..200 {
      let u = gen_univ(&mut rng, 4, 3);
      assert!(univ_eq(&u, &u), "reflexivity failed for {u:?}");
    }
  }

  #[test]
  fn prop_univ_eq_symmetric() {
    let mut rng = UPrng::new(0xABCD);
    for _ in 0..200 {
      let a = gen_univ(&mut rng, 3, 2);
      let b = gen_univ(&mut rng, 3, 2);
      assert_eq!(
        univ_eq(&a, &b),
        univ_eq(&b, &a),
        "symmetry failed for {a:?} vs {b:?}"
      );
    }
  }

  #[test]
  fn prop_univ_geq_reflexive() {
    let mut rng = UPrng::new(0x5678);
    for _ in 0..200 {
      let u = gen_univ(&mut rng, 4, 3);
      assert!(univ_geq(&u, &u), "geq reflexivity failed for {u:?}");
    }
  }

  #[test]
  fn prop_univ_eq_implies_geq_both_ways() {
    let mut rng = UPrng::new(0xF00D);
    for _ in 0..200 {
      let a = gen_univ(&mut rng, 3, 2);
      let b = gen_univ(&mut rng, 3, 2);
      if univ_eq(&a, &b) {
        assert!(
          univ_geq(&a, &b),
          "eq implies geq failed (a>=b) for {a:?} == {b:?}"
        );
        assert!(
          univ_geq(&b, &a),
          "eq implies geq failed (b>=a) for {a:?} == {b:?}"
        );
      }
    }
  }

  #[test]
  fn prop_univ_succ_is_geq_base() {
    let mut rng = UPrng::new(0xBA_D0);
    for _ in 0..200 {
      let u = gen_univ(&mut rng, 3, 2);
      let su = AU::succ(u.clone());
      assert!(univ_geq(&su, &u), "succ u must be >= u for {u:?}");
      // And the reverse is (usually) false; guard for Zero-valued u (only
      // case where succ u vs u... no, actually succ u > u always in
      // Géran's semantics, so strict one-way geq should always hold).
      assert!(!univ_geq(&u, &su), "u must NOT be >= succ u for {u:?}");
    }
  }

  /// Generate a universe that uses only Zero / Succ / Max / Param — no IMax.
  /// Property-tested `univ_geq` reliably holds `max(a, b) >= {a, b}` on
  /// this subset; see `prop_univ_max_is_geq_both_components_imax_known_limit`
  /// for the IMax case that surfaced a gap in Géran's comparison during
  /// the initial sweep.
  fn gen_univ_no_imax(rng: &mut UPrng, depth: u32, max_param: u64) -> AU {
    if depth == 0 {
      return match rng.next_u32(3) {
        0 => AU::zero(),
        1 => AU::param(rng.next_u64() % (max_param + 1), ()),
        _ => AU::succ(AU::zero()),
      };
    }
    match rng.next_u32(4) {
      0 => AU::zero(),
      1 => AU::param(rng.next_u64() % (max_param + 1), ()),
      2 => AU::succ(gen_univ_no_imax(rng, depth - 1, max_param)),
      _ => AU::max(
        gen_univ_no_imax(rng, depth - 1, max_param),
        gen_univ_no_imax(rng, depth - 1, max_param),
      ),
    }
  }

  #[test]
  fn prop_univ_max_is_geq_both_components() {
    let mut rng = UPrng::new(0xBEEF);
    for _ in 0..200 {
      let a = gen_univ_no_imax(&mut rng, 3, 2);
      let b = gen_univ_no_imax(&mut rng, 3, 2);
      let m = AU::max(a.clone(), b.clone());
      assert!(univ_geq(&m, &a), "max(a,b) >= a failed for a={a:?} b={b:?}");
      assert!(univ_geq(&m, &b), "max(a,b) >= b failed for a={a:?} b={b:?}");
    }
  }

  /// Full property: `max(a, b) ≥ {a, b}` also holds when imax is allowed
  /// anywhere in the operands. Previously this failed — see the witness
  /// regression test below.
  #[test]
  fn prop_univ_max_is_geq_both_components_with_imax() {
    let mut rng = UPrng::new(0xCAFE);
    for _ in 0..400 {
      let a = gen_univ(&mut rng, 3, 2);
      let b = gen_univ(&mut rng, 3, 2);
      let m = AU::max(a.clone(), b.clone());
      assert!(univ_geq(&m, &a), "max(a,b) >= a failed for a={a:?} b={b:?}");
      assert!(univ_geq(&m, &b), "max(a,b) >= b failed for a={a:?} b={b:?}");
    }
  }

  /// Regression test for a property failure surfaced by property testing
  /// with a full `gen_univ` that included IMax nodes.
  ///
  /// Witness: `univ_geq(max(a, b), b)` with `b = imax(imax(Succ^3(0),
  /// Param(0)), Param(1))` and `a = Succ^3(0)`. Semantically the property
  /// holds for every parameter assignment.
  ///
  /// The original Lean4Lean `NormLevel.le` was incomplete: it searched for
  /// a single `p2 ⊆ p1` in `l2` covering both the constant and variable
  /// ingredients of `n_p1`. Here `m`'s canonical form splits its `const=3`
  /// at `[]` from its `var=[(0,0)]` at `[0,1]`, while `b`'s `[0,1]` carries
  /// both. Our `norm_level_le` now checks each ingredient of `n_p1`
  /// independently so different `p2`s may cover different parts.
  #[test]
  fn prop_univ_max_is_geq_both_components_imax_witness() {
    let a = AU::succ(AU::succ(AU::succ(AU::zero())));
    // b = imax(imax(Succ^3(0), Param(0)), Param(1))
    let b = AU::imax(AU::imax(a.clone(), AU::param(0, ())), AU::param(1, ()));
    let m = AU::max(a.clone(), b.clone());
    assert!(
      univ_geq(&m, &b),
      "max(a,b) >= b with imax-heavy b — Géran gap regression"
    );
  }
}
