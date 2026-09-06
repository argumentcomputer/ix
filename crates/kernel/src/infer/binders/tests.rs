//! Differential tests against the former one-binder-at-a-time inference.

use super::*;
use crate::env::{InternTable, KEnv};
use crate::expr::FVarId;
use crate::mode::{Anon, Meta};
use crate::profile::{OpCounts, take_op_counts};
use ix_common::address::Address;
use ix_common::env::{BinderInfo, DataValue, Name};

fn name<M: KernelMode>(s: &str) -> M::MField<Name> {
  M::meta_field(Name::str(Name::anon(), s.to_owned()))
}

fn var<M: KernelMode>(i: u64) -> KExpr<M> {
  KExpr::var(i, name::<M>("source-variable"))
}

fn sort<M: KernelMode>(n: u64) -> KExpr<M> {
  let mut u = KUniv::zero();
  for _ in 0..n {
    u = KUniv::succ(u);
  }
  KExpr::sort(u)
}

fn lam<M: KernelMode>(ty: KExpr<M>, body: KExpr<M>) -> KExpr<M> {
  KExpr::lam(name::<M>("lambda"), M::meta_field(BinderInfo::Implicit), ty, body)
}

fn all<M: KernelMode>(ty: KExpr<M>, body: KExpr<M>) -> KExpr<M> {
  KExpr::all(
    name::<M>("forall"),
    M::meta_field(BinderInfo::InstImplicit),
    ty,
    body,
  )
}

fn app<M: KernelMode>(f: KExpr<M>, a: KExpr<M>) -> KExpr<M> {
  KExpr::app_mdata(
    f,
    a,
    M::meta_field(vec![vec![(
      Name::str(Name::anon(), "tag".to_owned()),
      DataValue::OfString("binder differential".to_owned()),
    )]]),
  )
}

// A test-only copy of the former Lam/All branches, including cache behavior,
// dependent domain validation, one-at-a-time opening/closing, and scope
// restoration. Non-binder operations use the normal checker. This is an
// oracle for telescope handling, not a second implementation of the kernel.
fn reference<M: KernelMode>(
  tc: &mut TypeChecker<'_, M>,
  e: &KExpr<M>,
) -> Result<KExpr<M>, TcError<M>> {
  let key = tc.infer_key(e);
  if let Some(ty) = tc.env.infer_cache.get(&key) {
    return Ok(ty.clone());
  }
  if tc.infer_only
    && let Some(ty) = tc.env.infer_only_cache.get(&key)
  {
    return Ok(ty.clone());
  }
  let result = match e.data() {
    ExprData::Lam(name, bi, ty, body, _) => {
      if !tc.infer_only {
        let domain_ty = reference(tc, ty)?;
        tc.ensure_sort(&domain_ty)?;
      }
      tc.with_lctx_scope(|tc| {
        let id = tc.fresh_fvar_id();
        let fv = tc.intern(KExpr::fvar(id, name.clone()));
        tc.lctx.push(
          id,
          LocalDecl::CDecl {
            name: name.clone(),
            bi: bi.clone(),
            ty: ty.clone(),
          },
        );
        let opened = instantiate_rev(&mut tc.env.intern, body, &[fv]);
        let body_ty = reference(tc, &opened)?;
        let body_ty = cheap_beta_reduce(&mut tc.env.intern, &body_ty);
        let closed = abstract_fvars(&mut tc.env.intern, &body_ty, &[id]);
        Ok(tc.intern(KExpr::all(
          M::meta_field(Name::anon()),
          M::meta_field(BinderInfo::Default),
          ty.clone(),
          closed,
        )))
      })?
    },
    ExprData::All(name, bi, ty, body, _) => {
      let domain_ty = reference(tc, ty)?;
      let u1 = tc.ensure_sort(&domain_ty)?;
      tc.with_lctx_scope(|tc| {
        let id = tc.fresh_fvar_id();
        let fv = tc.intern(KExpr::fvar(id, name.clone()));
        tc.lctx.push(
          id,
          LocalDecl::CDecl {
            name: name.clone(),
            bi: bi.clone(),
            ty: ty.clone(),
          },
        );
        let opened = instantiate_rev(&mut tc.env.intern, body, &[fv]);
        let body_ty = reference(tc, &opened)?;
        let u2 = tc.ensure_sort(&body_ty)?;
        Ok(tc.intern(KExpr::sort(KUniv::imax(u1, u2))))
      })?
    },
    _ => return tc.infer(e),
  };
  if tc.infer_only {
    tc.env.infer_only_cache.insert(key, result.clone());
  } else {
    tc.env.infer_cache.insert(key, result.clone());
  }
  Ok(result)
}

fn same_shape<M: KernelMode>(a: KExpr<M>, b: KExpr<M>) {
  // Check occurrence metadata BEFORE interning together: first-insert-wins
  // interning intentionally ignores names, binder info, and mdata.
  let mut pending = vec![(&a, &b)];
  let mut seen = rustc_hash::FxHashSet::default();
  while let Some((a, b)) = pending.pop() {
    if !seen.insert((*a.addr(), *b.addr())) {
      continue;
    }
    assert_eq!(a.mdata(), b.mdata(), "expression metadata differs");
    assert_eq!(a.univ_decor(), b.univ_decor(), "universe spelling differs");
    assert_eq!(a.lbr(), b.lbr());
    assert_eq!(a.count_0(), b.count_0());
    assert_eq!(a.has_fvars(), b.has_fvars());
    match (a.data(), b.data()) {
      (ExprData::Var(i, n, _), ExprData::Var(j, m, _)) => {
        assert_eq!(i, j);
        assert_eq!(n, m);
      },
      (ExprData::FVar(i, n, _), ExprData::FVar(j, m, _)) => {
        assert_eq!(i, j);
        assert_eq!(n, m);
      },
      (ExprData::App(f, x, _), ExprData::App(g, y, _)) => {
        pending.extend([(f, g), (x, y)]);
      },
      (ExprData::Lam(n, bi, t, r, _), ExprData::Lam(m, bj, u, s, _))
      | (ExprData::All(n, bi, t, r, _), ExprData::All(m, bj, u, s, _)) => {
        assert_eq!(n, m);
        assert_eq!(bi, bj);
        pending.extend([(t, u), (r, s)]);
      },
      (ExprData::Let(n, t, v, r, nd, _), ExprData::Let(m, u, w, s, md, _)) => {
        assert_eq!(n, m);
        assert_eq!(nd, md);
        pending.extend([(t, u), (v, w), (r, s)]);
      },
      (ExprData::Prj(i, f, v, _), ExprData::Prj(j, g, w, _)) => {
        assert_eq!(i, j);
        assert_eq!(f, g);
        pending.push((v, w));
      },
      (ExprData::Sort(..), ExprData::Sort(..))
      | (ExprData::Const(..), ExprData::Const(..))
      | (ExprData::Nat(..), ExprData::Nat(..))
      | (ExprData::Str(..), ExprData::Str(..)) => {},
      _ => panic!("different expression constructors"),
    }
  }
  // The common interner additionally checks semantic payloads and complete
  // universe structure/spelling (without depending on separate-env UIDs).
  let mut intern = InternTable::new();
  let a = intern.intern_expr(a);
  let b = intern.intern_expr(b);
  assert!(a.ptr_eq(&b), "different inferred shapes:\n{a:?}\n{b:?}");
}

fn differential<M: KernelMode>(e: &KExpr<M>) {
  for infer_only in [false, true] {
    let mut baseline = KEnv::new();
    let mut batched = KEnv::new();
    let mut a = TypeChecker::new(&mut baseline);
    let mut b = TypeChecker::new(&mut batched);
    a.infer_only = infer_only;
    b.infer_only = infer_only;
    let ea = a.intern(e.clone());
    let eb = b.intern(e.clone());
    let expected = reference(&mut a, &ea).unwrap();
    let actual = b.infer(&eb).unwrap();
    assert!(a.lctx.is_empty() && b.lctx.is_empty());
    assert!(!actual.has_fvars(), "batch-local FVars escaped inference");
    same_shape(actual, expected);
  }
}

fn dependent_examples<M: KernelMode>() {
  // (A : Type) (B : A -> Type) (x : A) (y : B x), with deliberately
  // nonempty binder/Var/App metadata. In particular the returned dependent
  // domains must have the same metadata normalization as sequential opening.
  let domains = [sort(1), all(var(0), sort(1)), var(1), app(var(1), var(0))];
  let mut lambda = var::<M>(0);
  let mut forall = app::<M>(var(2), var(1));
  for domain in domains.into_iter().rev() {
    lambda = lam(domain.clone(), lambda);
    forall = all(domain, forall);
  }
  differential(&lambda);
  differential(&forall);

  // A let interrupts the lambda telescope; its existing zeta/beta handling
  // must still close the inferred type without leaving a Let or local FVar.
  let body = KExpr::let_(name::<M>("z"), var::<M>(1), var(0), var(0), false);
  differential(&lam(sort(1), lam(var(0), body)));

  // A lambda's inferred body type can be a head beta redex. Full validation
  // must accept the dependent annotation and closing must still cheap-beta.
  let redex = app(lam(sort(1), var(0)), var(0));
  differential(&lam(sort(1), lam(redex, var::<M>(0))));
}

#[test]
fn batch_dependent_domains_and_metadata_match_sequential() {
  dependent_examples::<Anon>();
  dependent_examples::<Meta>();
}

fn universes<M: KernelMode>() {
  let p = KUniv::param(0, name::<M>("u"));
  let q = KUniv::param(1, name::<M>("v"));
  for domain in [sort(0), sort(1), KExpr::sort(p.clone())] {
    for inner in [sort(0), sort(2), KExpr::sort(q.clone())] {
      differential(&all::<M>(domain.clone(), all(inner, sort(0))));
    }
  }
  // (P : Prop) -> (A : Sort u) -> P lives in Prop regardless of u.
  let e = all(sort(0), all(KExpr::sort(p), var::<M>(1)));
  differential(&e);
  let mut env = KEnv::new();
  let mut tc = TypeChecker::new(&mut env);
  let ty = tc.infer(&e).unwrap();
  assert!(matches!(ty.data(), ExprData::Sort(u, _) if u.is_zero()));
}

#[test]
fn batch_forall_preserves_imax_prop_and_symbolic_universes() {
  universes::<Anon>();
  universes::<Meta>();
}

fn outer_contexts<M: KernelMode>() {
  let mut baseline = KEnv::new();
  let mut batched = KEnv::new();
  let mut a = TypeChecker::new(&mut baseline);
  let mut b = TypeChecker::new(&mut batched);
  // Preserve both kinds of enclosing local context while opening a batch.
  for tc in [&mut a, &mut b] {
    tc.push_local(sort(1));
    let id = tc.fresh_fvar_id();
    assert_eq!(id, FVarId(0));
    tc.lctx.push(
      id,
      LocalDecl::CDecl {
        name: name::<M>("outer"),
        bi: M::meta_field(BinderInfo::Default),
        ty: sort(1),
      },
    );
  }
  let legacy = lam(var(0), lam(var(1), var::<M>(0)));
  let outer = KExpr::fvar(FVarId(0), name::<M>("outer"));
  let free = lam(outer.clone(), lam(outer, var(0)));
  for e in [legacy, free] {
    let ea = a.intern(e.clone());
    let eb = b.intern(e);
    same_shape(reference(&mut a, &ea).unwrap(), b.infer(&eb).unwrap());
    assert_eq!(a.lctx.len(), 1);
    assert_eq!(b.lctx.len(), 1);
    assert_eq!(b.ctx.len(), 1);
    assert!(b.lctx.find(FVarId(0)).is_some());
  }
}

#[test]
fn batch_preserves_outer_fvars_and_legacy_context() {
  outer_contexts::<Anon>();
  outer_contexts::<Meta>();
}

fn missing<M: KernelMode>(s: &str) -> KExpr<M> {
  KExpr::cnst(KId::new(Address::hash(s.as_bytes()), name::<M>(s)), Box::new([]))
}

fn errors<M: KernelMode>() {
  // Every domain, not just the first, must be checked before the body.
  let good = [sort::<M>(1), sort(0), var(1)];
  for bad_index in 0..=good.len() {
    for forall in [false, true] {
      let mut e = missing("bad-body");
      for (i, ty) in good.iter().enumerate().rev() {
        let domain =
          if i == bad_index { missing("bad-domain") } else { ty.clone() };
        e = if forall { all(domain, e) } else { lam(domain, e) };
      }
      for infer_only in [false, true] {
        let mut baseline = KEnv::new();
        let mut batched = KEnv::new();
        let mut a = TypeChecker::new(&mut baseline);
        let mut b = TypeChecker::new(&mut batched);
        a.infer_only = infer_only;
        b.infer_only = infer_only;
        let expected = reference(&mut a, &e).unwrap_err();
        let actual = b.infer(&e).unwrap_err();
        assert_eq!(expected.to_string(), actual.to_string());
        assert!(b.lctx.is_empty());
        let key = b.infer_key(&e);
        assert!(!b.env.infer_cache.contains_key(&key));
        assert!(!b.env.infer_only_cache.contains_key(&key));
      }
    }
  }
  // A domain whose inferred type is not a sort, and an ill-scoped body.
  for e in [
    lam(sort(1), lam(var(0), lam(var(0), sort::<M>(0)))),
    all(sort(1), all(var(0), all(var(0), sort(0)))),
    lam(sort(1), lam(sort(1), var(5))),
    all(sort(1), all(sort(1), var(5))),
  ] {
    let mut baseline = KEnv::new();
    let mut batched = KEnv::new();
    let expected =
      reference(&mut TypeChecker::new(&mut baseline), &e).unwrap_err();
    let mut tc = TypeChecker::new(&mut batched);
    let actual = tc.infer(&e).unwrap_err();
    assert_eq!(expected.to_string(), actual.to_string());
    assert!(tc.lctx.is_empty());
  }
}

#[test]
fn batch_errors_preserve_validation_order_and_restore_scope() {
  errors::<Anon>();
  errors::<Meta>();
}

fn caches<M: KernelMode>() {
  let mut env = KEnv::new();
  let mut tc = TypeChecker::new(&mut env);
  let suffix = tc.intern(lam(sort(1), lam(sort(1), sort::<M>(0))));
  let suffix_ty = tc.infer(&suffix).unwrap();
  let e = tc.intern(lam(sort(1), suffix));
  let before = tc.fresh_fvar_id().0;
  let ty = tc.infer(&e).unwrap();
  let after = tc.fresh_fvar_id().0;
  assert_eq!(after - before, 2, "cached suffix was opened again");
  let expected = tc.env.intern.intern_all(
    M::meta_field(Name::anon()),
    M::meta_field(BinderInfo::Default),
    &sort(1),
    &suffix_ty,
  );
  same_shape(ty.clone(), expected);
  let before = tc.fresh_fvar_id().0;
  let entries = tc.env.infer_cache.len();
  assert!(tc.infer(&e).unwrap().ptr_eq(&ty));
  assert_eq!(tc.fresh_fvar_id().0 - before, 1);
  assert_eq!(tc.env.infer_cache.len(), entries);

  // An infer-only suffix must not be accepted as a validated full-mode
  // result. This application passes synthesis but has an invalid argument.
  let bad_app = app(lam(sort(1), var(0)), sort(1));
  let bad_suffix = tc.intern(lam(sort(1), lam(sort(1), bad_app)));
  assert!(tc.with_infer_only(|tc| tc.infer(&bad_suffix)).is_ok());
  let bad_outer = tc.intern(lam(sort(1), bad_suffix));
  assert!(matches!(tc.infer(&bad_outer), Err(TcError::AppTypeMismatch { .. })));
  assert!(tc.lctx.is_empty());
  let key = tc.infer_key(&bad_outer);
  assert!(!tc.env.infer_cache.contains_key(&key));

  // Conversely, a full result is available to infer-only callers too.
  let before = tc.fresh_fvar_id().0;
  assert!(tc.with_infer_only(|tc| tc.infer(&e)).unwrap().ptr_eq(&ty));
  assert_eq!(tc.fresh_fvar_id().0 - before, 1);
}

#[test]
fn batch_keeps_outer_and_closed_suffix_cache_hits_mode_safe() {
  caches::<Anon>();
  caches::<Meta>();
}

#[test]
fn batch_forall_reuses_closed_suffix_without_reopening() {
  let mut env = KEnv::<Meta>::new();
  let mut tc = TypeChecker::new(&mut env);
  let suffix = tc.intern(all(sort(1), all(sort(2), sort(0))));
  let suffix_ty = tc.infer(&suffix).unwrap();
  let e = tc.intern(all(sort(1), suffix));
  let before = tc.fresh_fvar_id().0;
  let ty = tc.infer(&e).unwrap();
  assert_eq!(tc.fresh_fvar_id().0 - before, 2);
  let body_level = tc.ensure_sort(&suffix_ty).unwrap();
  let domain_level = tc.ensure_sort(&sort(2)).unwrap();
  let expected = tc.intern(KExpr::sort(KUniv::imax(domain_level, body_level)));
  same_shape(ty, expected);
}

#[test]
fn batch_error_preserves_existing_local_and_does_not_recycle_ids() {
  let mut env = KEnv::<Anon>::new();
  let mut tc = TypeChecker::new(&mut env);
  let (outer_id, outer) = tc.push_fvar_decl_anon(sort(1));
  let e = lam(outer.clone(), lam(outer.clone(), missing("bad-body")));
  assert!(tc.infer(&e).is_err());
  assert_eq!(tc.lctx.len(), 1);
  assert!(tc.lctx.find(outer_id).is_some());
  assert_eq!(tc.fresh_fvar_id().0, outer_id.0 + 3);
  let ty = tc.infer(&outer).unwrap();
  same_shape(ty, sort(1));
}

// A well-typed DAG under a long telescope:
//   (A : Type) (x_0 ... x_n : A) (f : A -> A -> A) => balanced f-tree.
// Distinct leaves keep the term wide without making recursive descent deep.
fn wide_telescope<M: KernelMode>(n: u64) -> KExpr<M> {
  assert!(n.is_power_of_two());
  let mut domains = vec![sort(1)];
  domains.extend((0..n).map(var));
  domains.push(all(var(n), all(var(n + 1), var(n + 2))));
  let f = var::<M>(0);
  let mut layer: Vec<_> = (1..=n).map(var).collect();
  while layer.len() > 1 {
    layer = layer
      .as_chunks::<2>()
      .0
      .iter()
      .map(|pair| app(app(f.clone(), pair[0].clone()), pair[1].clone()))
      .collect();
  }
  let mut body = layer.pop().unwrap();
  for domain in domains.into_iter().rev() {
    body = lam(domain, body);
  }
  body
}

struct Measurement<M: KernelMode> {
  ty: KExpr<M>,
  ops: OpCounts,
  elapsed: std::time::Duration,
  entries: usize,
}

fn measure<M: KernelMode>(e: &KExpr<M>, batched: bool) -> Measurement<M> {
  let mut env = KEnv::new();
  let mut tc = TypeChecker::new(&mut env);
  let e = tc.intern(e.clone());
  take_op_counts();
  let start = std::time::Instant::now();
  let ty = if batched { tc.infer(&e) } else { reference(&mut tc, &e) }.unwrap();
  let elapsed = start.elapsed();
  Measurement {
    ty,
    ops: take_op_counts(),
    elapsed,
    entries: tc.env.infer_cache.len(),
  }
}

fn work_reduction<M: KernelMode>() {
  let e = wide_telescope::<M>(64);
  let a = measure(&e, false);
  let b = measure(&e, true);
  same_shape(a.ty, b.ty);
  assert!(
    b.ops.subst_nodes * 4 < a.ops.subst_nodes,
    "batch did not eliminate repeated opening: {} vs {} visits",
    b.ops.subst_nodes,
    a.ops.subst_nodes,
  );
  assert!(b.entries < a.entries, "intermediate suffixes were still cached");
}

#[test]
fn batch_reduces_telescope_node_visits_without_changing_type() {
  work_reduction::<Anon>();
  work_reduction::<Meta>();
}

#[test]
#[ignore = "manual paired release microbenchmark; timings are not a test gate"]
fn batch_binder_microbenchmark() {
  let e = wide_telescope::<Anon>(128);
  for round in 0..5 {
    for batched in if round % 2 == 0 { [false, true] } else { [true, false] } {
      let m = measure(&e, batched);
      eprintln!(
        "round={round} batched={batched} elapsed={:?} subst={} intern={} infer_entries={}",
        m.elapsed, m.ops.subst_nodes, m.ops.intern_nodes, m.entries,
      );
    }
  }
}
