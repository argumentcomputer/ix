//! Kernel-side canonical-block validation.
//!
//! Mirrors the compile-side `sort_consts` machinery
//! (`src/ix/compile.rs:2727`) so the kernel can independently verify that
//! stored mutual blocks ship in canonical (alpha-collapsed, structurally
//! sorted) order. Two operating modes:
//!
//! 1. [`validate_canonical_block_single_pass`] — for the stored primary
//!    block. Treats the input as the alleged canonical partition (each
//!    member at its own class index) and checks adjacent pairs are strictly
//!    strong `Less`. Fails on `Greater` (wrong order) or `Equal`
//!    (uncollapsed alpha-equivalence). If a pair is only weak `Less`, the
//!    singleton partition has not proved canonicity, so validation falls back
//!    to full iterative refinement and requires the result to be the same
//!    ordered list of singleton classes.
//!
//! 2. [`sort_kconsts`] / [`sort_kconsts_with_seed_key`] — for rediscovered
//!    auxiliary inductives. Runs the iterative partition refinement (sort →
//!    group → re-sort under updated `KMutCtx`) until fixpoint. Returns
//!    canonical equivalence classes.
//!
//! Both share the same comparator — [`compare_kconst`] / [`compare_kexpr`]
//! / [`compare_kuniv`] — keyed on a [`KMutCtx`] that maps block-local
//! constant addresses to their class indices. References resolved through
//! the ctx are compared *positionally* (block-local), references that miss
//! the ctx fall back to address-order (external).
//!
//! # Faithful replication of compile-side
//!
//! The comparator field order, alpha-blindness through binders, and the
//! fallback-to-address rule for external refs all match
//! `src/ix/compile.rs`. Any divergence becomes a kernel correctness bug,
//! observable as a `kernel-check-const` test failure.
//!
//! See `docs/ix_canonicity.md` §4.4 for the soundness argument.

use std::cmp::Ordering;

use rustc_hash::FxHashMap;

use crate::ix::address::Address;

use super::constant::{KConst, RecRule};
use super::error::TcError;
use super::expr::{ExprData, KExpr};
use super::id::KId;
use super::level::{KUniv, UnivData};
use super::mode::KernelMode;

pub use crate::ix::strong_ordering::SOrd;

// ===========================================================================
// KMutCtx — block-local address → class-index map
// ===========================================================================

/// Maps a constant's content address to its position in the canonical
/// partition.
///
/// Built from a slice of `&KConst<M>`s the same way `MutConst::ctx`
/// (`src/ix/mutual.rs:177`) builds it from `MutConst`s: each member's
/// address gets its class index `j` (where `j` is the position in the
/// outer slice), and constructor addresses get offset indices following
/// the per-class ctor contributions.
///
/// Used by [`compare_kexpr`] to resolve `Const` and `Prj` references
/// block-locally instead of by raw address.
#[derive(Default, Debug, Clone)]
pub struct KMutCtx {
  pub map: FxHashMap<Address, usize>,
}

/// Extract a member's constructor `KId`s for `KMutCtx` construction.
/// Returns an empty slice for non-`Indc` kinds.
fn cnst_ctors<M: KernelMode>(c: &KConst<M>) -> Vec<KId<M>> {
  match c {
    KConst::Indc { ctors, .. } => ctors.clone(),
    _ => Vec::new(),
  }
}

impl KMutCtx {
  pub fn get(&self, a: &Address) -> Option<usize> {
    self.map.get(a).copied()
  }

  /// Build from `(KId, &KConst)` pairs, treating each as its own class.
  /// This is the single-pass primary-validation case.
  pub fn from_id_pairs<M: KernelMode>(pairs: &[(KId<M>, &KConst<M>)]) -> Self {
    let classes: Vec<Vec<(KId<M>, &KConst<M>)>> =
      pairs.iter().map(|p| vec![p.clone()]).collect();
    Self::from_id_classes::<M>(&classes)
  }

  /// Build from grouped equivalence classes carrying `(KId, &KConst)`
  /// pairs. Mirrors `MutConst::ctx` (`src/ix/mutual.rs:177-192`):
  ///
  /// - All members of class `j` get index `j`.
  /// - Ctor offsets start at `classes.len()` and advance by `max_ctors`
  ///   per class so ctor addresses across classes don't collide.
  pub fn from_id_classes<M: KernelMode>(
    classes: &[Vec<(KId<M>, &KConst<M>)>],
  ) -> Self {
    let mut map: FxHashMap<Address, usize> = FxHashMap::default();
    let mut i = classes.len();
    for (j, class) in classes.iter().enumerate() {
      let mut max_ctors = 0usize;
      for (id, cnst) in class {
        map.insert(id.addr.clone(), j);
        let ctor_ids = cnst_ctors::<M>(cnst);
        max_ctors = max_ctors.max(ctor_ids.len());
        for (cidx, cid) in ctor_ids.iter().enumerate() {
          map.insert(cid.addr.clone(), i + cidx);
        }
      }
      i += max_ctors;
    }
    KMutCtx { map }
  }
}

// ===========================================================================
// Comparators
// ===========================================================================

/// Compare two universe levels structurally. Anon-mode KUniv has no
/// `Param`-by-name resolution: the param index *is* its identity.
///
/// Mirrors `compare_level` (`src/ix/compile.rs:2179`); simpler because
/// there are no metavariables and `Param(idx)` carries the index directly.
pub fn compare_kuniv<M: KernelMode>(x: &KUniv<M>, y: &KUniv<M>) -> SOrd {
  // The Max and IMax arms intentionally use the same body — variant order
  // is encoded by the surrounding wildcard arms (Max < IMax), so collapsing
  // the recursive arms into one would obscure that structure.
  #[allow(clippy::match_same_arms)]
  match (x.data(), y.data()) {
    (UnivData::Zero(_), UnivData::Zero(_)) => SOrd::eq(true),
    (UnivData::Zero(_), _) => SOrd::lt(true),
    (_, UnivData::Zero(_)) => SOrd::gt(true),
    (UnivData::Succ(x, _), UnivData::Succ(y, _)) => compare_kuniv(x, y),
    (UnivData::Succ(_, _), _) => SOrd::lt(true),
    (_, UnivData::Succ(_, _)) => SOrd::gt(true),
    (UnivData::Max(xl, xr, _), UnivData::Max(yl, yr, _)) => {
      compare_kuniv(xl, yl).compare(compare_kuniv(xr, yr))
    },
    (UnivData::Max(_, _, _), _) => SOrd::lt(true),
    (_, UnivData::Max(_, _, _)) => SOrd::gt(true),
    (UnivData::IMax(xl, xr, _), UnivData::IMax(yl, yr, _)) => {
      compare_kuniv(xl, yl).compare(compare_kuniv(xr, yr))
    },
    (UnivData::IMax(_, _, _), _) => SOrd::lt(true),
    (_, UnivData::IMax(_, _, _)) => SOrd::gt(true),
    (UnivData::Param(xi, _, _), UnivData::Param(yi, _, _)) => SOrd::cmp(xi, yi),
  }
}

/// Compare two kernel expressions structurally for canonical ordering.
/// Alpha-blind through binders (`Lam`, `All`, `Let` ignore names) and uses
/// `ctx` to resolve block-local constant references.
///
/// Mirrors `compare_expr` (`src/ix/compile.rs:2258`). Differences:
/// - No `Mvar`/`Fvar`/`Mdata` cases (the kernel form has none).
/// - `Const` lookup uses `ctx.get(&id.addr)`; misses fall back to
///   `SOrd::cmp(&x.addr, &y.addr)` (the kernel analogue of
///   `compare_external_refs`, which directly compares compiled addresses).
pub fn compare_kexpr<M: KernelMode>(
  x: &KExpr<M>,
  y: &KExpr<M>,
  ctx: &KMutCtx,
) -> SOrd {
  // Cheap pointer / hash equality short-circuit. Equal-by-content kernel
  // expressions trivially produce SOrd::eq(true).
  if x.hash_eq(y) {
    return SOrd::eq(true);
  }
  // The App/Lam/All arms intentionally use the same recursive body — variant
  // ordering is preserved by the surrounding wildcard arms, so collapsing
  // them would obscure the structural total order.
  #[allow(clippy::match_same_arms)]
  match (x.data(), y.data()) {
    (ExprData::Var(xi, _, _), ExprData::Var(yi, _, _)) => SOrd::cmp(xi, yi),
    (ExprData::Var(..), _) => SOrd::lt(true),
    (_, ExprData::Var(..)) => SOrd::gt(true),

    (ExprData::Sort(xu, _), ExprData::Sort(yu, _)) => compare_kuniv(xu, yu),
    (ExprData::Sort(..), _) => SOrd::lt(true),
    (_, ExprData::Sort(..)) => SOrd::gt(true),

    (ExprData::Const(xid, xls, _), ExprData::Const(yid, yls, _)) => {
      let us = SOrd::try_zip::<_, (), _>(
        |a, b| Ok::<_, ()>(compare_kuniv(a, b)),
        xls,
        yls,
      )
      .expect("compare_kuniv is infallible");
      if us.ordering != Ordering::Equal {
        us
      } else if xid.addr == yid.addr {
        SOrd::eq(true)
      } else {
        match (ctx.get(&xid.addr), ctx.get(&yid.addr)) {
          (Some(nx), Some(ny)) => SOrd::weak_cmp(&nx, &ny),
          (Some(_), None) => SOrd::lt(true),
          (None, Some(_)) => SOrd::gt(true),
          (None, None) => SOrd::cmp(&xid.addr, &yid.addr),
        }
      }
    },
    (ExprData::Const(..), _) => SOrd::lt(true),
    (_, ExprData::Const(..)) => SOrd::gt(true),

    (ExprData::App(xl, xr, _), ExprData::App(yl, yr, _)) => {
      compare_kexpr(xl, yl, ctx).compare(compare_kexpr(xr, yr, ctx))
    },
    (ExprData::App(..), _) => SOrd::lt(true),
    (_, ExprData::App(..)) => SOrd::gt(true),

    (ExprData::Lam(_, _, xt, xb, _), ExprData::Lam(_, _, yt, yb, _)) => {
      compare_kexpr(xt, yt, ctx).compare(compare_kexpr(xb, yb, ctx))
    },
    (ExprData::Lam(..), _) => SOrd::lt(true),
    (_, ExprData::Lam(..)) => SOrd::gt(true),

    (ExprData::All(_, _, xt, xb, _), ExprData::All(_, _, yt, yb, _)) => {
      compare_kexpr(xt, yt, ctx).compare(compare_kexpr(xb, yb, ctx))
    },
    (ExprData::All(..), _) => SOrd::lt(true),
    (_, ExprData::All(..)) => SOrd::gt(true),

    (
      ExprData::Let(_, xt, xv, xb, _, _),
      ExprData::Let(_, yt, yv, yb, _, _),
    ) => SOrd::try_zip::<_, (), _>(
      |a, b| Ok::<_, ()>(compare_kexpr(a, b, ctx)),
      &[xt, xv, xb],
      &[yt, yv, yb],
    )
    .expect("compare_kexpr is infallible"),
    (ExprData::Let(..), _) => SOrd::lt(true),
    (_, ExprData::Let(..)) => SOrd::gt(true),

    (ExprData::Nat(xv, _, _), ExprData::Nat(yv, _, _)) => SOrd::cmp(xv, yv),
    (ExprData::Nat(..), _) => SOrd::lt(true),
    (_, ExprData::Nat(..)) => SOrd::gt(true),

    (ExprData::Str(xv, _, _), ExprData::Str(yv, _, _)) => SOrd::cmp(xv, yv),
    (ExprData::Str(..), _) => SOrd::lt(true),
    (_, ExprData::Str(..)) => SOrd::gt(true),

    (ExprData::Prj(xid, xi, xb, _), ExprData::Prj(yid, yi, yb, _)) => {
      // Type ref: ctx-aware (block-local) then ctx-miss falls back to
      // address compare. Mirror compile-side `compare_expr(Proj)`.
      let tn = match (ctx.get(&xid.addr), ctx.get(&yid.addr)) {
        (Some(nx), Some(ny)) => SOrd::weak_cmp(&nx, &ny),
        (Some(_), None) => SOrd::lt(true),
        (None, Some(_)) => SOrd::gt(true),
        (None, None) => SOrd::cmp(&xid.addr, &yid.addr),
      };
      tn.compare(SOrd::cmp(xi, yi)).compare(compare_kexpr(xb, yb, ctx))
    },
  }
}

/// Compare two recursor rules: `(fields, rhs)`. Mirrors
/// `compare_recr_rule` (`src/ix/compile.rs:2526`).
pub fn compare_krec_rule<M: KernelMode>(
  x: &RecRule<M>,
  y: &RecRule<M>,
  ctx: &KMutCtx,
) -> SOrd {
  SOrd::cmp(&x.fields, &y.fields).compare(compare_kexpr(&x.rhs, &y.rhs, ctx))
}

/// Compare two `KConst::Indc` payloads. Mirrors `compare_indc`
/// (`src/ix/compile.rs:2472`).
///
/// Field order:
/// `(is_rec, is_unsafe, lvls, params, indices, |ctors|, ty, ctors[*])`.
///
/// `is_rec` and `is_unsafe` participate so alpha-collapse can't merge
/// inductives whose derived flags differ.
fn compare_kindc<M: KernelMode>(
  x_lvls: u64,
  x_params: u64,
  x_indices: u64,
  x_is_rec: bool,
  x_is_unsafe: bool,
  x_ty: &KExpr<M>,
  x_ctors: &[KId<M>],
  y_lvls: u64,
  y_params: u64,
  y_indices: u64,
  y_is_rec: bool,
  y_is_unsafe: bool,
  y_ty: &KExpr<M>,
  y_ctors: &[KId<M>],
  ctx: &KMutCtx,
  resolve_ctor: &dyn Fn(&KId<M>) -> Option<KConst<M>>,
) -> SOrd {
  SOrd::cmp(&x_is_rec, &y_is_rec)
    .compare(SOrd::cmp(&x_is_unsafe, &y_is_unsafe))
    .compare(SOrd::cmp(&x_lvls, &y_lvls))
    .compare(SOrd::cmp(&x_params, &y_params))
    .compare(SOrd::cmp(&x_indices, &y_indices))
    .compare(SOrd::cmp(&x_ctors.len(), &y_ctors.len()))
    .compare(compare_kexpr(x_ty, y_ty, ctx))
    .compare(
      SOrd::try_zip::<_, (), _>(
        |a, b| {
          let xc = resolve_ctor(a);
          let yc = resolve_ctor(b);
          Ok::<_, ()>(match (xc, yc) {
            (Some(xc), Some(yc)) => compare_kctor(&xc, &yc, ctx),
            // If either ctor is missing from env, fall back to address.
            // This shouldn't happen for valid blocks but keeps the
            // comparator total.
            (None, _) | (_, None) => SOrd::cmp(&a.addr, &b.addr),
          })
        },
        x_ctors,
        y_ctors,
      )
      .expect("compare_kctor is infallible"),
    )
}

/// Compare two `KConst::Ctor` payloads.
/// Mirrors `compare_ctor_inner` (`src/ix/compile.rs:2412`):
/// `(lvls, cidx, params, fields, ty)`.
fn compare_kctor<M: KernelMode>(
  x: &KConst<M>,
  y: &KConst<M>,
  ctx: &KMutCtx,
) -> SOrd {
  match (x, y) {
    (
      KConst::Ctor {
        lvls: xl, cidx: xc, params: xp, fields: xf, ty: xt, ..
      },
      KConst::Ctor {
        lvls: yl, cidx: yc, params: yp, fields: yf, ty: yt, ..
      },
    ) => SOrd::cmp(xl, yl)
      .compare(SOrd::cmp(xc, yc))
      .compare(SOrd::cmp(xp, yp))
      .compare(SOrd::cmp(xf, yf))
      .compare(compare_kexpr(xt, yt, ctx)),
    _ => SOrd::cmp(&kconst_kind_ord(x), &kconst_kind_ord(y)),
  }
}

/// Compare two `KConst::Recr` payloads. Mirrors `compare_recr`
/// (`src/ix/compile.rs:2540`):
/// `(lvls, params, indices, motives, minors, k, ty, rules[*])`.
#[allow(clippy::too_many_arguments)]
fn compare_krecr<M: KernelMode>(
  x_lvls: u64,
  x_params: u64,
  x_indices: u64,
  x_motives: u64,
  x_minors: u64,
  x_k: bool,
  x_ty: &KExpr<M>,
  x_rules: &[RecRule<M>],
  y_lvls: u64,
  y_params: u64,
  y_indices: u64,
  y_motives: u64,
  y_minors: u64,
  y_k: bool,
  y_ty: &KExpr<M>,
  y_rules: &[RecRule<M>],
  ctx: &KMutCtx,
) -> SOrd {
  SOrd::cmp(&x_lvls, &y_lvls)
    .compare(SOrd::cmp(&x_params, &y_params))
    .compare(SOrd::cmp(&x_indices, &y_indices))
    .compare(SOrd::cmp(&x_motives, &y_motives))
    .compare(SOrd::cmp(&x_minors, &y_minors))
    .compare(SOrd::cmp(&x_k, &y_k))
    .compare(compare_kexpr(x_ty, y_ty, ctx))
    .compare(
      SOrd::try_zip::<_, (), _>(
        |a, b| Ok::<_, ()>(compare_krec_rule(a, b, ctx)),
        x_rules,
        y_rules,
      )
      .expect("compare_krec_rule is infallible"),
    )
}

/// Compare two `KConst::Defn` payloads. Mirrors `compare_defn`
/// (`src/ix/compile.rs:2373`):
/// `(kind, lvls, ty, val)`.
///
/// Note: `safety` and `hints` are intentionally NOT compared — matches
/// the compile-side comparator field-for-field. Compile-side decides
/// alpha-collapse on the canonical IXON form, which doesn't include
/// hints (and treats safety as a separate sidecar in practice).
fn compare_kdefn<M: KernelMode>(
  x_kind: crate::ix::ixon::constant::DefKind,
  x_lvls: u64,
  x_ty: &KExpr<M>,
  x_val: &KExpr<M>,
  y_kind: crate::ix::ixon::constant::DefKind,
  y_lvls: u64,
  y_ty: &KExpr<M>,
  y_val: &KExpr<M>,
  ctx: &KMutCtx,
) -> SOrd {
  SOrd::cmp(&x_kind, &y_kind)
    .compare(SOrd::cmp(&x_lvls, &y_lvls))
    .compare(compare_kexpr(x_ty, y_ty, ctx))
    .compare(compare_kexpr(x_val, y_val, ctx))
}

/// A stable kind ordinal for cross-kind `KConst` comparison. Matches the
/// compile-side `mut_const_kind` (`src/ix/compile.rs:2590`) tagging:
/// Defn=0, Indc=1, Recr=2; Axio/Quot/Ctor are not block-eligible but
/// receive distinct slots for total comparator behavior.
fn kconst_kind_ord<M: KernelMode>(c: &KConst<M>) -> u8 {
  match c {
    KConst::Defn { .. } => 0,
    KConst::Indc { .. } => 1,
    KConst::Recr { .. } => 2,
    KConst::Ctor { .. } => 3,
    KConst::Axio { .. } => 4,
    KConst::Quot { .. } => 5,
  }
}

/// Compare two block-eligible `KConst`s with full structural ordering.
/// Different kinds order by `kconst_kind_ord`; same-kind dispatch goes to
/// the kind-specific comparator.
///
/// `resolve_ctor` is invoked for each Indc-vs-Indc comparison to fetch
/// the concrete `KConst::Ctor` referenced by a ctor `KId`. The kernel
/// caller threads a closure that consults `KEnv::get`.
pub fn compare_kconst<M: KernelMode>(
  x: &KConst<M>,
  y: &KConst<M>,
  ctx: &KMutCtx,
  resolve_ctor: &dyn Fn(&KId<M>) -> Option<KConst<M>>,
) -> SOrd {
  match (x, y) {
    (
      KConst::Defn { kind: xk, lvls: xl, ty: xt, val: xv, .. },
      KConst::Defn { kind: yk, lvls: yl, ty: yt, val: yv, .. },
    ) => compare_kdefn::<M>(*xk, *xl, xt, xv, *yk, *yl, yt, yv, ctx),
    (
      KConst::Indc {
        lvls: xl,
        params: xp,
        indices: xi,
        is_rec: xr,
        is_unsafe: xu,
        ty: xt,
        ctors: xc,
        ..
      },
      KConst::Indc {
        lvls: yl,
        params: yp,
        indices: yi,
        is_rec: yr,
        is_unsafe: yu,
        ty: yt,
        ctors: yc,
        ..
      },
    ) => compare_kindc::<M>(
      *xl,
      *xp,
      *xi,
      *xr,
      *xu,
      xt,
      xc,
      *yl,
      *yp,
      *yi,
      *yr,
      *yu,
      yt,
      yc,
      ctx,
      resolve_ctor,
    ),
    (
      KConst::Recr {
        lvls: xl,
        params: xp,
        indices: xi,
        motives: xm,
        minors: xn,
        k: xk,
        ty: xt,
        rules: xr,
        ..
      },
      KConst::Recr {
        lvls: yl,
        params: yp,
        indices: yi,
        motives: ym,
        minors: yn,
        k: yk,
        ty: yt,
        rules: yr,
        ..
      },
    ) => compare_krecr::<M>(
      *xl, *xp, *xi, *xm, *xn, *xk, xt, xr, *yl, *yp, *yi, *ym, *yn, *yk, yt,
      yr, ctx,
    ),
    _ => SOrd::cmp(&kconst_kind_ord(x), &kconst_kind_ord(y)),
  }
}

// ===========================================================================
// Sort_consts port (iterative partition refinement)
// ===========================================================================

/// Merge two sorted slices of `(KId, &KConst)` pairs. Mirrors `merge`
/// (`src/ix/compile.rs:2671`).
fn merge<'a, M: KernelMode>(
  left: Vec<(KId<M>, &'a KConst<M>)>,
  right: Vec<(KId<M>, &'a KConst<M>)>,
  ctx: &KMutCtx,
  resolve_ctor: &dyn Fn(&KId<M>) -> Option<KConst<M>>,
) -> Vec<(KId<M>, &'a KConst<M>)> {
  let mut result = Vec::with_capacity(left.len() + right.len());
  let mut left_iter = left.into_iter();
  let mut right_iter = right.into_iter();
  let mut left_item = left_iter.next();
  let mut right_item = right_iter.next();

  while let (Some(l), Some(r)) = (&left_item, &right_item) {
    let cmp = compare_kconst(l.1, r.1, ctx, resolve_ctor).ordering;
    if cmp == Ordering::Greater {
      result.push(right_item.take().unwrap());
      right_item = right_iter.next();
    } else {
      result.push(left_item.take().unwrap());
      left_item = left_iter.next();
    }
  }
  if let Some(l) = left_item {
    result.push(l);
    result.extend(left_iter);
  }
  if let Some(r) = right_item {
    result.push(r);
    result.extend(right_iter);
  }
  result
}

/// Merge-sort a class of `(KId, &KConst)` pairs by structural comparison.
/// Mirrors `sort_by_compare` (`src/ix/compile.rs:2708`).
fn sort_by_compare<'a, M: KernelMode>(
  items: &[(KId<M>, &'a KConst<M>)],
  ctx: &KMutCtx,
  resolve_ctor: &dyn Fn(&KId<M>) -> Option<KConst<M>>,
) -> Vec<(KId<M>, &'a KConst<M>)> {
  if items.len() <= 1 {
    return items.to_vec();
  }
  let mid = items.len() / 2;
  let (left, right) = items.split_at(mid);
  let left = sort_by_compare::<M>(left, ctx, resolve_ctor);
  let right = sort_by_compare::<M>(right, ctx, resolve_ctor);
  merge::<M>(left, right, ctx, resolve_ctor)
}

/// Group consecutive equal elements in a sorted slice. Mirrors `group_by`
/// (`src/ix/compile.rs:2644`) — the consecutive-equal grouping is sound
/// because the input is already sorted by the same comparator.
fn group_consecutive<'a, M: KernelMode>(
  items: Vec<(KId<M>, &'a KConst<M>)>,
  ctx: &KMutCtx,
  resolve_ctor: &dyn Fn(&KId<M>) -> Option<KConst<M>>,
) -> Vec<Vec<(KId<M>, &'a KConst<M>)>> {
  let mut groups: Vec<Vec<(KId<M>, &'a KConst<M>)>> = Vec::new();
  let mut current: Vec<(KId<M>, &'a KConst<M>)> = Vec::new();
  for item in items {
    if let Some(last) = current.last() {
      let eq = compare_kconst(last.1, item.1, ctx, resolve_ctor).ordering
        == Ordering::Equal;
      if eq {
        current.push(item);
      } else {
        groups.push(std::mem::replace(&mut current, vec![item]));
      }
    } else {
      current.push(item);
    }
  }
  if !current.is_empty() {
    groups.push(current);
  }
  groups
}

/// Sort kernel constants into canonical equivalence classes.
///
/// Iterative refinement (mirroring `sort_consts`,
/// `src/ix/compile.rs:2727`):
///
/// 1. Seed with all members in a single class.
/// 2. Build `KMutCtx` from the current partition.
/// 3. Sort each multi-element class structurally; group adjacent equals.
/// 4. Tiebreak each class by `id.addr` (kernel analogue of compile-side's
///    `class.sort_by_key(|x| x.name())`).
/// 5. Repeat until the partition stabilizes.
///
/// Returns equivalence classes in canonical order. Within-class element
/// order is by ascending `id.addr` and is observationally invisible (all
/// members in a class compile to byte-identical canonical forms — they
/// share an `Address`).
pub fn sort_kconsts<'a, M: KernelMode>(
  members: &[(KId<M>, &'a KConst<M>)],
  resolve_ctor: &dyn Fn(&KId<M>) -> Option<KConst<M>>,
) -> Vec<Vec<(KId<M>, &'a KConst<M>)>> {
  sort_kconsts_with_seed_key::<M>(
    members,
    resolve_ctor,
    &|id: &KId<M>, _c: &KConst<M>| id.addr.clone(),
  )
}

/// Sort kernel constants using the same partition-refinement algorithm as
/// [`sort_kconsts`], but let callers provide the deterministic seed/tiebreak
/// key. Compile-side `sort_consts` seeds and stabilizes each class by
/// `MutConst.name()`; kernel aux reconstruction uses this hook to feed the
/// hash of the compiler's synthetic aux name instead of the transient content
/// address used for the synthetic `KId`.
pub fn sort_kconsts_with_seed_key<'a, M: KernelMode>(
  members: &[(KId<M>, &'a KConst<M>)],
  resolve_ctor: &dyn Fn(&KId<M>) -> Option<KConst<M>>,
  seed_key: &dyn Fn(&KId<M>, &KConst<M>) -> Address,
) -> Vec<Vec<(KId<M>, &'a KConst<M>)>> {
  if members.is_empty() {
    return Vec::new();
  }

  // Seed with a single class, ordered by the caller's compile-side analogue.
  let mut seed: Vec<(KId<M>, &'a KConst<M>)> = members.to_vec();
  seed.sort_by(|a, b| {
    seed_key(&a.0, a.1)
      .cmp(&seed_key(&b.0, b.1))
      .then_with(|| a.0.addr.cmp(&b.0.addr))
  });
  let mut classes: Vec<Vec<(KId<M>, &'a KConst<M>)>> = vec![seed];

  loop {
    let ctx = KMutCtx::from_id_classes::<M>(&classes);
    let mut new_classes: Vec<Vec<(KId<M>, &'a KConst<M>)>> = Vec::new();
    for class in classes.iter() {
      match class.len() {
        0 => unreachable!("sort_kconsts: empty class"),
        1 => new_classes.push(class.clone()),
        _ => {
          let sorted = sort_by_compare::<M>(class, &ctx, resolve_ctor);
          let groups = group_consecutive::<M>(sorted, &ctx, resolve_ctor);
          new_classes.extend(groups);
        },
      }
    }
    // No within-class re-sort by seed_key. Items in a class are either
    // alpha-equivalent (and any rep is fine) or weak-Equal pending future
    // refinement (and their order is whatever `sort_by_compare` gave —
    // stable on previous-iter order). Re-sorting by seed_key here would
    // turn that "tentatively equal" relationship into a name-derived
    // tiebreak that propagates through subsequent iterations as if it
    // were a structural fact, producing different canonical orders for
    // identical content depending on Meta/Anon mode and discovery
    // numbering. See `docs/ix_canonicity.md` and the rationale below.
    if classes_eq(&classes, &new_classes) {
      return new_classes;
    }
    classes = new_classes;
  }
}

fn classes_eq<M: KernelMode>(
  a: &[Vec<(KId<M>, &KConst<M>)>],
  b: &[Vec<(KId<M>, &KConst<M>)>],
) -> bool {
  if a.len() != b.len() {
    return false;
  }
  for (ca, cb) in a.iter().zip(b.iter()) {
    if ca.len() != cb.len() {
      return false;
    }
    for (xa, xb) in ca.iter().zip(cb.iter()) {
      if xa.0.addr != xb.0.addr {
        return false;
      }
    }
  }
  true
}

fn default_seed_key<M: KernelMode>(id: &KId<M>) -> Address {
  M::meta_name(&id.name).map_or_else(
    || id.addr.clone(),
    |name| Address::from_blake3_hash(*name.get_hash()),
  )
}

fn validate_by_full_refinement<M: KernelMode>(
  block_addr: &Address,
  members: &[(KId<M>, &KConst<M>)],
  resolve_ctor: &dyn Fn(&KId<M>) -> Option<KConst<M>>,
) -> Result<(), TcError<M>> {
  let classes =
    sort_kconsts_with_seed_key::<M>(members, resolve_ctor, &|id, _| {
      default_seed_key::<M>(id)
    });

  if classes.len() != members.len() {
    let pos = classes.iter().position(|class| class.len() > 1).unwrap_or(0);
    return Err(TcError::NonCanonicalBlock {
      block: block_addr.clone(),
      pos,
      ordering: Ordering::Equal,
    });
  }

  for (i, (class, member)) in classes.iter().zip(members.iter()).enumerate() {
    if class.len() != 1 || class[0].0.addr != member.0.addr {
      return Err(TcError::NonCanonicalBlock {
        block: block_addr.clone(),
        pos: i,
        ordering: Ordering::Greater,
      });
    }
  }

  Ok(())
}

// ===========================================================================
// Single-pass primary block validation
// ===========================================================================

/// Validate that a stored primary block ships in canonical (sort_consts)
/// order.
///
/// Walks adjacent pairs under the singleton partition and requires strong
/// strict `Less`. Two immediate failure modes:
///
/// - `Greater` — the stored order disagrees with sort_consts.
/// - `Equal` — two distinct stored entries are alpha-equivalent. The
///   compiler should have collapsed them to one canonical Ixon constant;
///   shipping two separate addresses for the same alpha-equivalence class
///   is a canonicity violation.
///
/// A weak `Less` means the singleton partition itself supplied the
/// distinguishing order for a block-local recursive reference. That is not
/// proof of canonicity, so validation falls back to the full iterative
/// `sort_kconsts` refinement and accepts only if refinement returns the same
/// ordered list of singleton classes.
///
/// Returns `Ok(())` only if every adjacent pair is strongly `Less`, or if the
/// fallback refinement proves the stored singleton order is already canonical.
///
/// `resolve_ctor` is the env lookup the comparator needs to recurse
/// through Indc ctors. The kernel caller passes a closure over `KEnv::get`.
pub fn validate_canonical_block_single_pass<M: KernelMode>(
  block_addr: &Address,
  members: &[(KId<M>, &KConst<M>)],
  resolve_ctor: &dyn Fn(&KId<M>) -> Option<KConst<M>>,
) -> Result<(), TcError<M>> {
  if members.len() < 2 {
    return Ok(());
  }
  let ctx = KMutCtx::from_id_pairs::<M>(members);
  for (i, w) in members.windows(2).enumerate() {
    let so = compare_kconst(w[0].1, w[1].1, &ctx, resolve_ctor);
    match so.ordering {
      Ordering::Less if so.strong => {},
      Ordering::Less => {
        return validate_by_full_refinement(block_addr, members, resolve_ctor);
      },
      Ordering::Equal => {
        return Err(TcError::NonCanonicalBlock {
          block: block_addr.clone(),
          pos: i,
          ordering: Ordering::Equal,
        });
      },
      Ordering::Greater => {
        return Err(TcError::NonCanonicalBlock {
          block: block_addr.clone(),
          pos: i,
          ordering: Ordering::Greater,
        });
      },
    }
  }
  Ok(())
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::ix::address::Address;
  use crate::ix::env::{BinderInfo, Name};
  use crate::ix::env::{DefinitionSafety, ReducibilityHints};
  use crate::ix::ixon::constant::DefKind;

  use super::super::expr::KExpr;
  use super::super::level::KUniv;
  use super::super::mode::Anon;

  type AE = KExpr<Anon>;
  type AU = KUniv<Anon>;

  fn mk_addr(s: &str) -> Address {
    Address::hash(s.as_bytes())
  }

  fn mk_order_addr(byte: u8) -> Address {
    Address::from_slice(&[byte; 32]).unwrap()
  }

  fn mk_id(s: &str) -> KId<Anon> {
    KId::new(mk_addr(s), ())
  }

  fn sort0() -> AE {
    KExpr::sort(KUniv::zero())
  }

  fn nat() -> AE {
    AE::cnst(mk_id("Nat"), Box::new([]))
  }

  fn mk_indc(
    addr: &str,
    params: u64,
    indices: u64,
    ctors: Vec<KId<Anon>>,
    ty: AE,
  ) -> (KId<Anon>, KConst<Anon>) {
    let id = mk_id(addr);
    let c = KConst::Indc {
      name: (),
      level_params: (),
      lvls: 0,
      params,
      indices,
      is_rec: false,
      is_refl: false,
      is_unsafe: false,
      nested: 0,
      block: KId::new(mk_addr("blk"), ()),
      member_idx: 0,
      ty,
      ctors,
      lean_all: (),
    };
    (id, c)
  }

  fn mk_ctor(_addr: &str, fields: u64, params: u64, ty: AE) -> KConst<Anon> {
    KConst::Ctor {
      name: (),
      level_params: (),
      is_unsafe: false,
      lvls: 0,
      induct: KId::new(mk_addr("anon-ind"), ()),
      cidx: 0,
      params,
      fields,
      ty,
    }
  }

  fn no_ctors() -> Box<dyn Fn(&KId<Anon>) -> Option<KConst<Anon>>> {
    Box::new(|_| None)
  }

  // ---- compare_kuniv ----

  #[test]
  fn compare_kuniv_zero_eq_zero() {
    let z = AU::zero();
    let z2 = AU::zero();
    assert_eq!(compare_kuniv(&z, &z2).ordering, Ordering::Equal);
  }

  #[test]
  fn compare_kuniv_zero_lt_succ() {
    let z = AU::zero();
    let s = AU::succ(AU::zero());
    assert_eq!(compare_kuniv(&z, &s).ordering, Ordering::Less);
    assert_eq!(compare_kuniv(&s, &z).ordering, Ordering::Greater);
  }

  #[test]
  fn compare_kuniv_param_by_index() {
    assert_eq!(
      compare_kuniv(&AU::param(0, ()), &AU::param(1, ())).ordering,
      Ordering::Less
    );
    assert_eq!(
      compare_kuniv(&AU::param(2, ()), &AU::param(2, ())).ordering,
      Ordering::Equal
    );
  }

  // ---- compare_kexpr ----

  #[test]
  fn compare_kexpr_alpha_blind() {
    // Lambdas with different binder names but same structure compare Equal.
    let ctx = KMutCtx::default();
    // In Anon mode names are erased, so this is trivially the case;
    // the test still asserts the structural-only comparator
    let l1 = AE::lam((), (), sort0(), AE::var(0, ()));
    let l2 = AE::lam((), (), sort0(), AE::var(0, ()));
    assert_eq!(compare_kexpr(&l1, &l2, &ctx).ordering, Ordering::Equal);
  }

  #[test]
  fn compare_kexpr_var_ordering() {
    let ctx = KMutCtx::default();
    let v0 = AE::var(0, ());
    let v1 = AE::var(1, ());
    assert_eq!(compare_kexpr(&v0, &v1, &ctx).ordering, Ordering::Less);
    assert_eq!(compare_kexpr(&v1, &v0, &ctx).ordering, Ordering::Greater);
  }

  #[test]
  fn compare_kexpr_const_external_by_addr() {
    let ctx = KMutCtx::default();
    // Two distinct Const refs neither in the ctx → fall back to address.
    let a = AE::cnst(mk_id("Foo"), Box::new([]));
    let b = AE::cnst(mk_id("Bar"), Box::new([]));
    let so = compare_kexpr(&a, &b, &ctx);
    let direct = mk_addr("Foo").cmp(&mk_addr("Bar"));
    assert_eq!(so.ordering, direct);
    assert!(so.strong);
  }

  #[test]
  fn compare_kexpr_const_block_local() {
    // Build a ctx with two block-local addresses at distinct class indices.
    let mut ctx = KMutCtx::default();
    ctx.map.insert(mk_addr("A"), 0);
    ctx.map.insert(mk_addr("B"), 1);
    let ca = AE::cnst(mk_id("A"), Box::new([]));
    let cb = AE::cnst(mk_id("B"), Box::new([]));
    let so = compare_kexpr(&ca, &cb, &ctx);
    assert_eq!(so.ordering, Ordering::Less);
    assert!(!so.strong); // weak: name-resolved (block-local)
  }

  #[test]
  fn compare_kexpr_const_block_local_vs_external() {
    // A block-local Const compares Less than an external Const (matches
    // compile-side: `Some(_), None` → Less).
    let mut ctx = KMutCtx::default();
    ctx.map.insert(mk_addr("Local"), 0);
    let local = AE::cnst(mk_id("Local"), Box::new([]));
    let external = AE::cnst(mk_id("External"), Box::new([]));
    assert_eq!(compare_kexpr(&local, &external, &ctx).ordering, Ordering::Less);
  }

  // ---- compare_kindc / compare_kconst Indc-Indc ----

  #[test]
  fn compare_kindc_alpha_collapse() {
    // Two Indcs with structurally-identical ctors and types compare Equal.
    let ctor_id = mk_id("ctor1");
    let ctor1 = mk_ctor("ctor1", 0, 0, sort0());
    let ctor_id_2 = mk_id("ctor2");
    let ctor2 = mk_ctor("ctor2", 0, 0, sort0());
    let (_, ind_a) = mk_indc("A", 0, 0, vec![ctor_id.clone()], sort0());
    let (_, ind_b) = mk_indc("B", 0, 0, vec![ctor_id_2.clone()], sort0());

    let resolve = move |id: &KId<Anon>| -> Option<KConst<Anon>> {
      if id.addr == mk_addr("ctor1") {
        Some(ctor1.clone())
      } else if id.addr == mk_addr("ctor2") {
        Some(ctor2.clone())
      } else {
        None
      }
    };
    let ctx = KMutCtx::default();
    let so = compare_kconst(&ind_a, &ind_b, &ctx, &resolve);
    assert_eq!(so.ordering, Ordering::Equal);
  }

  #[test]
  fn compare_kindc_orders_by_params() {
    let resolve = move |_: &KId<Anon>| -> Option<KConst<Anon>> { None };
    let ctx = KMutCtx::default();
    let (_, a) = mk_indc("A", 1, 0, vec![], sort0()); // 1 param
    let (_, b) = mk_indc("B", 2, 0, vec![], sort0()); // 2 params
    assert_eq!(compare_kconst(&a, &b, &ctx, &resolve).ordering, Ordering::Less);
  }

  // ---- sort_kconsts ----

  #[test]
  fn sort_kconsts_canonical_three_indcs() {
    // Three Indcs with distinct params (1, 2, 3). sort_kconsts orders them
    // ascending by params (the first discriminating field after the bools
    // and lvls).
    let resolve = move |_: &KId<Anon>| -> Option<KConst<Anon>> { None };
    let (id_a, ind_a) = mk_indc("A", 3, 0, vec![], sort0());
    let (id_b, ind_b) = mk_indc("B", 1, 0, vec![], sort0());
    let (id_c, ind_c) = mk_indc("C", 2, 0, vec![], sort0());

    // Pass in arbitrary order
    let members = vec![(id_a, &ind_a), (id_b, &ind_b), (id_c, &ind_c)];
    let classes = sort_kconsts::<Anon>(&members, &resolve);
    let order: Vec<u64> = classes
      .iter()
      .map(|cls| match cls[0].1 {
        KConst::Indc { params, .. } => *params,
        _ => unreachable!(),
      })
      .collect();
    assert_eq!(order, vec![1, 2, 3]);
  }

  #[test]
  fn sort_kconsts_alpha_collapses_into_one_class() {
    // Two structurally-identical Indcs collapse into a single class.
    let resolve = move |_: &KId<Anon>| -> Option<KConst<Anon>> { None };
    let (id_a, ind_a) = mk_indc("A", 1, 0, vec![], sort0());
    let (id_b, ind_b) = mk_indc("B", 1, 0, vec![], sort0());
    let members = vec![(id_a, &ind_a), (id_b, &ind_b)];
    let classes = sort_kconsts::<Anon>(&members, &resolve);
    assert_eq!(classes.len(), 1);
    assert_eq!(classes[0].len(), 2);
  }

  #[test]
  fn sort_kconsts_seed_key_orders_equal_class_representative() {
    // Aux sorting mirrors compile-side `sort_consts`: when structural
    // refinement collapses two members, the representative is chosen by the
    // compiler-shaped seed key, not by the transient synthetic address.
    let resolve = move |_: &KId<Anon>| -> Option<KConst<Anon>> { None };
    let (id_a, ind_a) = mk_indc("A", 1, 0, vec![], sort0());
    let (id_b, ind_b) = mk_indc("B", 1, 0, vec![], sort0());
    let id_a_addr = id_a.addr.clone();
    let id_b_addr = id_b.addr.clone();
    let members = vec![(id_a, &ind_a), (id_b, &ind_b)];

    let classes =
      sort_kconsts_with_seed_key::<Anon>(&members, &resolve, &|id, _| {
        if id.addr == id_b_addr {
          mk_order_addr(0)
        } else if id.addr == id_a_addr {
          mk_order_addr(1)
        } else {
          id.addr.clone()
        }
      });
    assert_eq!(classes.len(), 1);
    assert_eq!(classes[0].len(), 2);
    assert_eq!(classes[0][0].0.addr, id_b_addr);
  }

  // ---- validate_canonical_block_single_pass ----

  #[test]
  fn validate_single_pass_accepts_canonical_order() {
    // Three Indcs with distinct params in ascending canonical order — Ok.
    let resolve = move |_: &KId<Anon>| -> Option<KConst<Anon>> { None };
    let (id_a, ind_a) = mk_indc("A", 1, 0, vec![], sort0());
    let (id_b, ind_b) = mk_indc("B", 2, 0, vec![], sort0());
    let (id_c, ind_c) = mk_indc("C", 3, 0, vec![], sort0());
    let members = vec![(id_a, &ind_a), (id_b, &ind_b), (id_c, &ind_c)];
    let res: Result<(), TcError<Anon>> =
      validate_canonical_block_single_pass(&mk_addr("blk"), &members, &resolve);
    assert!(res.is_ok());
  }

  #[test]
  fn validate_single_pass_rejects_swap() {
    // Wrong order — Greater at the first adjacent pair.
    let resolve = move |_: &KId<Anon>| -> Option<KConst<Anon>> { None };
    let (id_a, ind_a) = mk_indc("A", 2, 0, vec![], sort0());
    let (id_b, ind_b) = mk_indc("B", 1, 0, vec![], sort0()); // wrong: 1 < 2
    let members = vec![(id_a, &ind_a), (id_b, &ind_b)];
    let res: Result<(), TcError<Anon>> =
      validate_canonical_block_single_pass(&mk_addr("blk"), &members, &resolve);
    match res {
      Err(TcError::NonCanonicalBlock { ordering, pos, .. }) => {
        assert_eq!(ordering, Ordering::Greater);
        assert_eq!(pos, 0);
      },
      _ => panic!("expected NonCanonicalBlock(Greater) at pos 0, got {res:?}"),
    }
  }

  #[test]
  fn validate_single_pass_rejects_uncollapsed_alpha() {
    // Two structurally-identical Indcs adjacent — Equal, must reject.
    let resolve = move |_: &KId<Anon>| -> Option<KConst<Anon>> { None };
    let (id_a, ind_a) = mk_indc("A", 1, 0, vec![], sort0());
    let (id_b, ind_b) = mk_indc("B", 1, 0, vec![], sort0());
    let members = vec![(id_a, &ind_a), (id_b, &ind_b)];
    let res: Result<(), TcError<Anon>> =
      validate_canonical_block_single_pass(&mk_addr("blk"), &members, &resolve);
    match res {
      Err(TcError::NonCanonicalBlock { ordering, pos, .. }) => {
        assert_eq!(ordering, Ordering::Equal);
        assert_eq!(pos, 0);
      },
      _ => panic!("expected NonCanonicalBlock(Equal) at pos 0, got {res:?}"),
    }
  }

  #[test]
  fn validate_single_pass_rejects_recursive_alpha_pair_via_refinement() {
    // The singleton partition makes each self-reference look ordered:
    //
    //   A.ctor : A -> A
    //   B.ctor : B -> B
    //
    // compares as weak-Less because the provisional ctx maps A ↦ 0 and
    // B ↦ 1. That weak order is not a canonicity proof; full refinement
    // starts with A and B in the same class, sees both self-references as
    // equal, and must reject the uncollapsed alpha pair.
    let id_a = mk_id("A");
    let id_b = mk_id("B");
    let ctor_a_id = mk_id("A.mk");
    let ctor_b_id = mk_id("B.mk");

    let self_a = AE::cnst(id_a.clone(), Box::new([]));
    let self_b = AE::cnst(id_b.clone(), Box::new([]));
    let ctor_a = mk_ctor("A.mk", 1, 0, AE::all((), (), self_a.clone(), self_a));
    let ctor_b = mk_ctor("B.mk", 1, 0, AE::all((), (), self_b.clone(), self_b));
    let (_, ind_a) = mk_indc("A", 0, 0, vec![ctor_a_id.clone()], sort0());
    let (_, ind_b) = mk_indc("B", 0, 0, vec![ctor_b_id.clone()], sort0());
    let resolve = move |id: &KId<Anon>| -> Option<KConst<Anon>> {
      if id.addr == ctor_a_id.addr {
        Some(ctor_a.clone())
      } else if id.addr == ctor_b_id.addr {
        Some(ctor_b.clone())
      } else {
        None
      }
    };

    let members = vec![(id_a, &ind_a), (id_b, &ind_b)];
    let singleton_ctx = KMutCtx::from_id_pairs::<Anon>(&members);
    let singleton_cmp =
      compare_kconst(&ind_a, &ind_b, &singleton_ctx, &resolve);
    assert_eq!(singleton_cmp.ordering, Ordering::Less);
    assert!(!singleton_cmp.strong);

    let res: Result<(), TcError<Anon>> =
      validate_canonical_block_single_pass(&mk_addr("blk"), &members, &resolve);
    match res {
      Err(TcError::NonCanonicalBlock { ordering, pos, .. }) => {
        assert_eq!(ordering, Ordering::Equal);
        assert_eq!(pos, 0);
      },
      _ => panic!(
        "expected refinement to reject recursive alpha pair, got {res:?}"
      ),
    }
  }

  // ---- KMutCtx ----

  #[test]
  fn kmutctx_from_id_pairs_assigns_class_per_member() {
    let (id_a, c_a) = mk_indc("A", 0, 0, vec![], sort0());
    let (id_b, c_b) = mk_indc("B", 0, 0, vec![], sort0());
    let pairs = vec![(id_a.clone(), &c_a), (id_b.clone(), &c_b)];
    let ctx = KMutCtx::from_id_pairs::<Anon>(&pairs);
    assert_eq!(ctx.get(&id_a.addr), Some(0));
    assert_eq!(ctx.get(&id_b.addr), Some(1));
  }

  #[test]
  fn kmutctx_ctors_get_offset_indices() {
    let ctor_id = mk_id("c1");
    let (id_a, c_a) = mk_indc("A", 0, 0, vec![ctor_id.clone()], sort0());
    let pairs = vec![(id_a.clone(), &c_a)];
    let ctx = KMutCtx::from_id_pairs::<Anon>(&pairs);
    assert_eq!(ctx.get(&id_a.addr), Some(0));
    // 1 class → ctor offsets start at 1
    assert_eq!(ctx.get(&ctor_id.addr), Some(1));
  }

  // Silence the dead-code warnings on imports kept for future use:
  #[test]
  fn _imports_smoke() {
    let _ = sort0();
    let _ = nat();
    let _ = no_ctors();
    let _ = ReducibilityHints::Opaque;
    let _ = DefinitionSafety::Safe;
    let _ = DefKind::Definition;
    let _ = BinderInfo::Default;
    let _ = Name::anon();
  }
}
