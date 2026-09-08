//! Differential tests against sequential, one-App-at-a-time inference.

use super::*;
use crate::env::{InternTable, KEnv};
use crate::mode::{Anon, Meta};
use crate::profile::take_op_counts;
use ix_common::address::Address;
use ix_common::env::{BinderInfo, DataValue, Name};

fn name<M: KernelMode>(s: &str) -> M::MField<Name> {
  M::meta_field(Name::str(Name::anon(), s.to_owned()))
}
fn var<M: KernelMode>(i: u64) -> KExpr<M> {
  KExpr::var(i, name::<M>("variable"))
}
fn sort<M: KernelMode>(n: u64) -> KExpr<M> {
  let mut u = KUniv::zero();
  for _ in 0..n {
    u = KUniv::succ(u);
  }
  KExpr::sort(u)
}
fn all<M: KernelMode>(dom: KExpr<M>, cod: KExpr<M>) -> KExpr<M> {
  KExpr::all(name::<M>("binder"), M::meta_field(BinderInfo::Implicit), dom, cod)
}
fn app<M: KernelMode>(f: KExpr<M>, a: KExpr<M>) -> KExpr<M> {
  KExpr::app_mdata(
    f,
    a,
    M::meta_field(vec![vec![(
      Name::str(Name::anon(), "tag".to_owned()),
      DataValue::OfString("application differential".to_owned()),
    )]]),
  )
}
fn axiom<M: KernelMode>(env: &mut KEnv<M>, s: &str, ty: KExpr<M>) -> KExpr<M> {
  let id = KId::new(Address::hash(s.as_bytes()), name::<M>(s));
  env.insert(
    id.clone(),
    KConst::Axio {
      name: name::<M>(s),
      level_params: M::meta_field(vec![]),
      is_unsafe: false,
      lvls: 0,
      ty,
    },
  );
  KExpr::cnst(id, Box::new([]))
}

// Independent copy of the former recursive App rule. Other expression
// constructors use the normal checker, so this isolates the changed rule.
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
  let ExprData::App(f, a, _) = e.data() else { return tc.infer(e) };
  let f_ty = reference(tc, f)?;
  let (dom, cod) = tc.ensure_forall(&f_ty)?;
  if !tc.infer_only {
    let a_ty = reference(tc, a)?;
    let eager = tc.eager_reduce;
    tc.eager_reduce |= tc.is_eager_reduce(a);
    let eq = tc.is_def_eq(&a_ty, &dom);
    tc.eager_reduce = eager;
    if !eq? {
      return Err(TcError::AppTypeMismatch { a_ty, dom, depth: tc.ctx.len() });
    }
  }
  let ty = subst(&mut tc.env.intern, &cod, a, 0);
  if tc.infer_only {
    tc.env.infer_only_cache.insert(key, ty.clone());
  } else {
    tc.env.infer_cache.insert(key, ty.clone());
  }
  Ok(ty)
}

fn same_type<M: KernelMode>(a: KExpr<M>, b: KExpr<M>) {
  let mut pending = vec![(&a, &b)];
  let mut seen = rustc_hash::FxHashSet::default();
  while let Some((a, b)) = pending.pop() {
    if !seen.insert((*a.addr(), *b.addr())) {
      continue;
    }
    assert_eq!(a.mdata(), b.mdata());
    assert_eq!(a.univ_decor(), b.univ_decor());
    assert_eq!(a.lbr(), b.lbr());
    match (a.data(), b.data()) {
      (ExprData::App(f, x, _), ExprData::App(g, y, _)) => {
        pending.extend([(f, g), (x, y)])
      },
      (ExprData::All(n, i, d, c, _), ExprData::All(m, j, e, r, _))
      | (ExprData::Lam(n, i, d, c, _), ExprData::Lam(m, j, e, r, _)) => {
        assert_eq!(n, m);
        assert_eq!(i, j);
        pending.extend([(d, e), (c, r)]);
      },
      (ExprData::Var(i, n, _), ExprData::Var(j, m, _)) => {
        assert_eq!(i, j);
        assert_eq!(n, m);
      },
      (ExprData::Let(n, t, v, r, nd, _), ExprData::Let(m, u, w, s, md, _)) => {
        assert_eq!(n, m);
        assert_eq!(nd, md);
        pending.extend([(t, u), (v, w), (r, s)]);
      },
      (ExprData::Prj(_, _, v, _), ExprData::Prj(_, _, w, _)) => {
        pending.push((v, w))
      },
      _ => {},
    }
  }
  let mut intern = InternTable::new();
  let a = intern.intern_expr(a);
  let b = intern.intern_expr(b);
  assert!(a.ptr_eq(&b), "different inferred types: {a:?}\n{b:?}");
}

fn fixture<M: KernelMode>(env: &mut KEnv<M>) -> (KExpr<M>, Vec<KExpr<M>>) {
  let a = axiom(env, "A", sort(1));
  let b = axiom(env, "B", all(a.clone(), sort(1)));
  let x = axiom(env, "x", a.clone());
  let y = axiom(env, "y", app(b.clone(), x.clone()));
  // f : (A : Type) -> (B : A -> Type) -> (x : A) -> B x -> B x
  let ty = all(
    sort(1),
    all(
      all(var(0), sort(1)),
      all(var(1), all(app(var(1), var(0)), app(var(2), var(1)))),
    ),
  );
  (axiom(env, "f", ty), vec![a, b, x, y])
}

fn dependent<M: KernelMode>() {
  for infer_only in [false, true] {
    for count in 1..=4 {
      let mut env_a = KEnv::<M>::new();
      let mut env_b = KEnv::<M>::new();
      let (mut a, args_a) = fixture(&mut env_a);
      let (mut b, args_b) = fixture(&mut env_b);
      for i in 0..count {
        a = app(a, args_a[i].clone());
        b = app(b, args_b[i].clone());
      }
      let mut tc_a = TypeChecker::new(&mut env_a);
      let mut tc_b = TypeChecker::new(&mut env_b);
      tc_a.infer_only = infer_only;
      tc_b.infer_only = infer_only;
      same_type(reference(&mut tc_a, &a).unwrap(), tc_b.infer(&b).unwrap());
      assert!(tc_b.lctx.is_empty() && tc_b.ctx.is_empty());
    }
  }
}

#[test]
fn dependent_partial_and_full_applications() {
  dependent::<Anon>();
  dependent::<Meta>();
}

fn boundaries<M: KernelMode>() {
  for infer_only in [false, true] {
    for hidden in [false, true] {
      let mut a = KEnv::new();
      let mut b = KEnv::new();
      let mk = |env: &mut KEnv<M>| {
        // An applied type variable, or a let, exposes a new Pi only AFTER
        // substituting the first argument into the function's codomain.
        let result = if hidden {
          KExpr::let_(name::<M>("T"), sort(1), var(0), var(0), false)
        } else {
          var(0)
        };
        let f = axiom(env, "dependentFunction", all(sort(1), result));
        app(app(f, all(sort(0), sort(0))), axiom(env, "P", sort(0)))
      };
      let ea = mk(&mut a);
      let eb = mk(&mut b);
      let mut a = TypeChecker::new(&mut a);
      let mut b = TypeChecker::new(&mut b);
      a.infer_only = infer_only;
      b.infer_only = infer_only;
      same_type(reference(&mut a, &ea).unwrap(), b.infer(&eb).unwrap());
    }
  }
}

#[test]
fn flushes_pending_arguments_before_revealing_hidden_pi() {
  boundaries::<Anon>();
  boundaries::<Meta>();
}

fn open_args<M: KernelMode>() {
  for infer_only in [false, true] {
    let mut a = KEnv::new();
    let mut b = KEnv::new();
    let mk = |env: &mut KEnv<M>| {
      // f : (A : Type) -> A -> ((z : A) -> A). Return a function so the
      // open replacement A must be lifted underneath the residual binder.
      let f = axiom(
        env,
        "openFunction",
        all(sort(1), all(var(0), all(var(1), var(2)))),
      );
      app(app(f, var(1)), var(0))
    };
    let ea = mk(&mut a);
    let eb = mk(&mut b);
    let mut a = TypeChecker::new(&mut a);
    let mut b = TypeChecker::new(&mut b);
    a.infer_only = infer_only;
    b.infer_only = infer_only;
    a.push_local(sort(1));
    a.push_local(var(0));
    b.push_local(sort(1));
    b.push_local(var(0));
    same_type(reference(&mut a, &ea).unwrap(), b.infer(&eb).unwrap());
    assert_eq!(b.ctx.len(), 2);
  }
}

#[test]
fn lifts_ambient_arguments_under_residual_binders() {
  open_args::<Anon>();
  open_args::<Meta>();
}

#[test]
fn checks_every_argument_and_keeps_infer_only_cache_separate() {
  for bad_index in 0..4 {
    let mut env = KEnv::<Anon>::new();
    let (mut f, mut args) = fixture(&mut env);
    args[bad_index] = sort(4);
    for a in args {
      f = app(f, a);
    }
    let mut tc = TypeChecker::new(&mut env);
    let _ = tc.with_infer_only(|tc| tc.infer(&f));
    assert!(tc.env.infer_cache.is_empty());
    let key = tc.infer_key(&f);
    assert!(matches!(tc.infer(&f), Err(TcError::AppTypeMismatch { .. })));
    assert!(!tc.env.infer_cache.contains_key(&key));
  }
}

#[test]
fn overapplication_and_unknown_heads_are_rejected() {
  let mut env = KEnv::<Anon>::new();
  let (mut f, args) = fixture(&mut env);
  for a in args {
    f = app(f, a);
  }
  let f = app(f, sort(0));
  let mut tc = TypeChecker::new(&mut env);
  assert!(matches!(tc.infer(&f), Err(TcError::FunExpected { .. })));
  let missing =
    KExpr::cnst(KId::new(Address::hash(b"absent"), ()), Box::new([]));
  assert!(matches!(
    tc.infer(&app(app(missing, sort(0)), sort(0))),
    Err(TcError::UnknownConst(_))
  ));
}

#[test]
fn batched_heads_still_validate_universe_arity_and_scope() {
  let mut env = KEnv::<Anon>::new();
  let id = KId::new(Address::hash(b"universeFunction"), ());
  env.insert(
    id.clone(),
    KConst::Axio {
      name: (),
      level_params: (),
      is_unsafe: false,
      lvls: 1,
      ty: all(KExpr::sort(KUniv::param(0, ())), all(var(0), var(1))),
    },
  );
  let mut tc = TypeChecker::new(&mut env);
  let wrong_arity =
    app(app(KExpr::cnst(id.clone(), Box::new([])), sort(0)), sort(0));
  for infer_only in [false, true] {
    tc.infer_only = infer_only;
    assert!(matches!(
      tc.infer(&wrong_arity),
      Err(TcError::UnivParamMismatch { .. })
    ));
  }
  tc.env.insert(
    id.clone(),
    KConst::Axio {
      name: (),
      level_params: (),
      is_unsafe: false,
      lvls: 1,
      ty: all(KExpr::sort(KUniv::param(1, ())), all(var(0), var(1))),
    },
  );
  let bad_scope =
    app(app(KExpr::cnst(id, Box::new([KUniv::zero()])), sort(0)), sort(0));
  for infer_only in [false, true] {
    tc.infer_only = infer_only;
    assert!(matches!(
      tc.infer(&bad_scope),
      Err(TcError::UnivParamOutOfRange { .. })
    ));
  }
}

#[test]
fn application_cache_does_not_cross_local_let_contexts() {
  let mut env = KEnv::<Anon>::new();
  let a = axiom(&mut env, "A", sort(1));
  let b = axiom(&mut env, "B", sort(1));
  let x = axiom(&mut env, "x", a.clone());
  let f = axiom(&mut env, "id", all(sort(1), all(var(0), var(1))));
  let e = app(app(f, var(1)), var(0));
  let mut tc = TypeChecker::new(&mut env);
  tc.push_let(sort(1), a.clone());
  tc.push_let(a.clone(), x.clone());
  let key = tc.infer_key(&e);
  tc.infer(&e).unwrap();
  tc.pop_local();
  tc.pop_local();
  tc.push_let(sort(1), b);
  tc.push_let(a, x);
  assert_ne!(key, tc.infer_key(&e));
  assert!(matches!(tc.infer(&e), Err(TcError::AppTypeMismatch { .. })));
}

fn fvar_arguments<M: KernelMode>() {
  let mut env = KEnv::<M>::new();
  let f = axiom(&mut env, "id", all(sort(1), all(var(0), all(var(1), var(2)))));
  let mut tc = TypeChecker::new(&mut env);
  tc.with_lctx_scope(|tc| {
    let aid = tc.fresh_fvar_id();
    let a = tc.intern(KExpr::fvar(aid, name::<M>("A")));
    tc.lctx.push(
      aid,
      LocalDecl::CDecl {
        name: name::<M>("A"),
        bi: M::meta_field(BinderInfo::Default),
        ty: sort(1),
      },
    );
    let xid = tc.fresh_fvar_id();
    let x = tc.intern(KExpr::fvar(xid, name::<M>("x")));
    tc.lctx.push(
      xid,
      LocalDecl::CDecl {
        name: name::<M>("x"),
        bi: M::meta_field(BinderInfo::Default),
        ty: a.clone(),
      },
    );
    let e = app(app(f, a), x);
    for infer_only in [false, true] {
      tc.infer_only = infer_only;
      tc.env.clear_reduction_caches();
      let expected = reference(tc, &e)?;
      tc.env.clear_reduction_caches();
      tc.prefix_admission = Default::default();
      let root = tc.infer_key(&e);
      let ExprData::App(prefix, _, _) = e.data() else { unreachable!() };
      let key = tc.infer_key(prefix);
      for _ in 0..2 {
        tc.env.infer_cache.remove(&root);
        tc.env.infer_only_cache.remove(&root);
        tc.prefix_admission.observe(key, infer_only);
        same_type(expected.clone(), tc.infer(&e)?);
      }
      assert!(
        tc.env.infer_cache.contains_key(&key)
          || tc.env.infer_only_cache.contains_key(&key)
      );
    }
    Ok::<(), TcError<M>>(())
  })
  .unwrap();
  assert!(tc.lctx.is_empty());
}

#[test]
fn fvar_arguments_match_sequential_substitution_in_both_modes() {
  fvar_arguments::<Anon>();
  fvar_arguments::<Meta>();
}

#[test]
fn honors_cached_dependent_prefixes() {
  let mut env = KEnv::<Anon>::new();
  let (f, args) = fixture(&mut env);
  let prefix = app(app(f, args[0].clone()), args[1].clone());
  let mut tc = TypeChecker::new(&mut env);
  let ty = tc.infer(&prefix).unwrap();
  let key = tc.infer_key(&prefix);
  assert!(tc.env.infer_cache.get(&key).unwrap().ptr_eq(&ty));
  let tail = app(app(prefix, args[2].clone()), args[3].clone());
  // A valid cached prefix should be enough; no inference of the head is
  // needed. Keep the declaration environment intact, remove all other
  // synthesis results, then verify that the prefix remains reusable.
  tc.env.infer_cache.retain(|k, _| k == &key);
  let actual = tc.infer(&tail).unwrap();
  same_type(actual, app(args[1].clone(), args[2].clone()));
  assert!(tc.env.infer_cache.get(&key).unwrap().ptr_eq(&ty));
}

#[test]
fn eager_scope_is_restored_on_errors_and_success() {
  let mut env = KEnv::<Anon>::new();
  let a = axiom(&mut env, "someValue", sort(0));
  let mut tc = TypeChecker::new(&mut env);
  for saved in [false, true] {
    tc.eager_reduce = saved;
    tc.check_app_argument(&a, &a, &sort(0)).unwrap();
    assert_eq!(tc.eager_reduce, saved);
    assert!(tc.check_app_argument(&a, &a, &sort(3)).is_err());
    assert_eq!(tc.eager_reduce, saved);
    tc.rec_fuel = 0;
    assert!(tc.check_app_argument(&a, &a, &sort(5)).is_err());
    assert_eq!(tc.eager_reduce, saved);
    tc.rec_fuel = crate::tc::max_rec_fuel();
  }
}

fn long_application(env: &mut KEnv<Anon>, count: u64) -> KExpr<Anon> {
  let mut pack_ty = sort(1);
  for _ in 0..count {
    pack_ty = all(sort(1), pack_ty);
  }
  let mut ty = axiom(env, "Pack", pack_ty);
  // Every argument occurs in the result, so sequential inference revisits
  // a growingly-instantiated Pack application at every telescope step.
  for i in (0..count).rev() {
    ty = app(ty, var(i));
  }
  for _ in 0..count {
    ty = all(sort(1), ty);
  }
  let mut f = axiom(env, "longFunction", ty);
  for _ in 0..count {
    f = app(f, sort(0));
  }
  f
}

#[test]
fn long_telescope_avoids_quadratic_codomain_construction() {
  let mut a = KEnv::new();
  let mut b = KEnv::new();
  let ea = long_application(&mut a, 96);
  let eb = long_application(&mut b, 96);
  let mut a = TypeChecker::new(&mut a);
  let mut b = TypeChecker::new(&mut b);
  take_op_counts();
  let expected = reference(&mut a, &ea).unwrap();
  let old = take_op_counts();
  let actual = b.infer(&eb).unwrap();
  let new = take_op_counts();
  eprintln!("application work: sequential={old:?}, batched={new:?}");
  assert!(new.intern_nodes * 4 < old.intern_nodes);
  same_type(actual, expected);
}

fn hot_prefixes<M: KernelMode>() {
  for infer_only in [false, true] {
    let mut env = KEnv::<M>::new();
    let (f, args) = fixture(&mut env);
    let result = app(args[1].clone(), args[2].clone());
    let y2 = axiom(&mut env, "anotherY", result.clone());
    let y3 = axiom(&mut env, "thirdY", result.clone());
    let prefix =
      app(app(app(f, args[0].clone()), args[1].clone()), args[2].clone());
    let first = app(prefix.clone(), args[3].clone());
    let mut reference_env = KEnv::<M>::new();
    for (id, declaration) in env.iter() {
      reference_env.insert(id, declaration);
    }
    let mut reference_tc = TypeChecker::new(&mut reference_env);
    reference_tc.infer_only = infer_only;
    let expected = reference(&mut reference_tc, &first).unwrap();
    let expected_prefix = reference(&mut reference_tc, &prefix).unwrap();
    let mut tc = TypeChecker::new(&mut env);
    tc.infer_only = infer_only;
    let key = tc.infer_key(&prefix);
    same_type(tc.infer(&first).unwrap(), expected.clone());
    assert!(!tc.env.infer_cache.contains_key(&key));
    assert!(!tc.env.infer_only_cache.contains_key(&key));
    // The bounded filter is allowed to forget intervening collisions. Seed
    // this nomination immediately so the cache-contract test is UID-order
    // independent, including under parallel unit-test scheduling.
    tc.prefix_admission.observe(key, infer_only);
    same_type(tc.infer(&app(prefix.clone(), y2)).unwrap(), expected.clone());
    let cache =
      if infer_only { &tc.env.infer_only_cache } else { &tc.env.infer_cache };
    same_type(cache[&key].clone(), expected_prefix);
    // A third use needs no synthesis of earlier prefixes or the head.
    tc.env.infer_cache.retain(|k, _| k == &key);
    tc.env.infer_only_cache.retain(|k, _| k == &key);
    same_type(tc.infer(&app(prefix, y3)).unwrap(), expected);
    if infer_only {
      assert!(tc.env.infer_cache.is_empty());
    }
  }
}

#[test]
fn repeated_dependent_prefixes_are_published_in_the_correct_mode() {
  hot_prefixes::<Anon>();
  hot_prefixes::<Meta>();
}

fn invalid_hot_prefixes<M: KernelMode>() {
  for bad_index in 0..4 {
    let mut env = KEnv::<M>::new();
    let (mut f, mut args) = fixture(&mut env);
    args[bad_index] = sort(4);
    let mut prefixes = vec![];
    for arg in args {
      f = app(f, arg);
      prefixes.push(f.clone());
    }
    let mut tc = TypeChecker::new(&mut env);
    // Warm unchecked results/admission history first. They must never grant
    // full-mode validity, even when the same UID is seen repeatedly.
    for _ in 0..3 {
      let root = tc.infer_key(&f);
      tc.env.infer_only_cache.remove(&root);
      let _ = tc.with_infer_only(|tc| tc.infer(&f));
    }
    for _ in 0..3 {
      assert!(matches!(tc.infer(&f), Err(TcError::AppTypeMismatch { .. })));
      for invalid in &prefixes[bad_index..] {
        let key = tc.infer_key(invalid);
        assert!(!tc.env.infer_cache.contains_key(&key));
      }
    }
  }
}

#[test]
fn repeated_invalid_prefixes_and_infer_only_results_never_validate_arguments() {
  invalid_hot_prefixes::<Anon>();
  invalid_hot_prefixes::<Meta>();
}

fn warm_open_prefix<M: KernelMode>() {
  for infer_only in [false, true] {
    let mut env = KEnv::<M>::new();
    let a = axiom(&mut env, "A", sort(1));
    let b = axiom(&mut env, "B", sort(1));
    let x = axiom(&mut env, "x", a.clone());
    let f =
      axiom(&mut env, "openId", all(sort(1), all(var(0), all(var(1), var(2)))));
    let prefix = app(f, var(1));
    let e = app(prefix.clone(), var(0));
    let mut tc = TypeChecker::new(&mut env);
    tc.infer_only = infer_only;
    tc.push_let(sort(1), a.clone());
    tc.push_let(a.clone(), x.clone());
    let root = tc.infer_key(&e);
    let key_a = tc.infer_key(&prefix);
    let expected = reference(&mut tc, &e).unwrap();
    let expected_prefix = reference(&mut tc, &prefix).unwrap();
    tc.env.clear_reduction_caches();
    for _ in 0..2 {
      tc.env.infer_cache.remove(&root);
      tc.env.infer_only_cache.remove(&root);
      tc.prefix_admission.observe(key_a, infer_only);
      same_type(tc.infer(&e).unwrap(), expected.clone());
    }
    // The cached residual binder contains correctly lifted ambient Vars.
    let cache =
      if infer_only { &tc.env.infer_only_cache } else { &tc.env.infer_cache };
    same_type(cache[&key_a].clone(), expected_prefix);
    tc.pop_local();
    tc.pop_local();
    tc.push_let(sort(1), b);
    tc.push_let(a, x);
    let key_b = tc.infer_key(&prefix);
    assert_ne!(key_a, key_b);
    assert!(!tc.env.infer_cache.contains_key(&key_b));
    assert!(!tc.env.infer_only_cache.contains_key(&key_b));
    if !infer_only {
      assert!(matches!(tc.infer(&e), Err(TcError::AppTypeMismatch { .. })));
    }
  }
}

#[test]
fn warmed_dependent_prefixes_lift_ambient_vars_and_respect_let_contexts() {
  warm_open_prefix::<Anon>();
  warm_open_prefix::<Meta>();
}

#[test]
fn hot_long_telescope_materializes_at_most_one_dependent_suffix() {
  let mut env = KEnv::new();
  let e = long_application(&mut env, 96);
  let mut tc = TypeChecker::new(&mut env);
  // Warm every prefix's admission history WITHOUT precomputing types. This
  // is the adversarial case for accidentally restoring quadratic batching.
  let mut prefixes = vec![];
  let ExprData::App(p, _, _) = e.data() else { unreachable!() };
  let mut p = p;
  while let ExprData::App(f, _, _) = p.data() {
    let key = tc.infer_key(p);
    tc.prefix_admission.observe(key, false);
    prefixes.push(p);
    p = f;
  }
  let longest = tc.infer_key(prefixes[0]);
  tc.prefix_admission.observe(longest, false);
  take_op_counts();
  let expected = tc.infer(&e).unwrap();
  let work = take_op_counts();
  let published = prefixes
    .iter()
    .filter(|p| {
      let key = tc.infer_key(p);
      tc.env.infer_cache.contains_key(&key)
    })
    .count();
  assert_eq!(published, 1);
  assert!(work.intern_nodes < 2000, "suffixes must stay batched: {work:?}");
  tc.env.clear_reduction_caches();
  tc.prefix_admission = Default::default();
  same_type(tc.infer(&e).unwrap(), expected);
}

#[test]
fn reset_forgets_admission_and_full_prefixes_remain_usable_by_infer_only() {
  let mut env = KEnv::<Anon>::new();
  let (f, args) = fixture(&mut env);
  let prefix =
    app(app(app(f, args[0].clone()), args[1].clone()), args[2].clone());
  let e = app(prefix.clone(), args[3].clone());
  let mut tc = TypeChecker::new(&mut env);
  let key = tc.infer_key(&prefix);
  assert!(!tc.prefix_admission.observe(key, false));
  tc.reset();
  assert!(!tc.prefix_admission.observe(key, false));
  let expected = tc.infer(&e).unwrap();
  assert!(tc.env.infer_cache.contains_key(&key));
  let root = tc.infer_key(&e);
  tc.env.infer_cache.remove(&root);
  tc.env.infer_only_cache.clear();
  tc.env.infer_cache.retain(|k, _| k == &key);
  same_type(tc.with_infer_only(|tc| tc.infer(&e)).unwrap(), expected);
  assert!(tc.env.infer_only_cache.contains_key(&root));
  assert!(!tc.env.infer_only_cache.contains_key(&key));
  tc.env.clear_reduction_caches();
  assert!(!tc.env.infer_cache.contains_key(&key));
  assert!(!tc.env.infer_only_cache.contains_key(&key));
}

#[test]
fn warm_hidden_pi_boundaries_still_flush_pending_arguments() {
  for infer_only in [false, true] {
    let mut env = KEnv::<Anon>::new();
    let ty = all(sort(1), var(0));
    let f = axiom(&mut env, "hiddenPrefix", ty);
    let p = axiom(&mut env, "P", sort(0));
    let h = app(f, all(sort(0), all(sort(0), sort(0))));
    let e = app(app(h, p.clone()), p);
    let mut tc = TypeChecker::new(&mut env);
    tc.infer_only = infer_only;
    let expected = reference(&mut tc, &e).unwrap();
    tc.env.clear_reduction_caches();
    let root = tc.infer_key(&e);
    for _ in 0..3 {
      tc.env.infer_cache.remove(&root);
      tc.env.infer_only_cache.remove(&root);
      same_type(tc.infer(&e).unwrap(), expected.clone());
    }
  }
}

#[test]
fn hot_prefix_reuse_reduces_checked_argument_work() {
  let run = |admit: bool| {
    let mut env = KEnv::<Anon>::new();
    let application = long_application(&mut env, 32);
    let ExprData::App(prefix, _, _) = application.data() else {
      unreachable!()
    };
    let tails: Vec<_> = (0..32)
      .map(|i| {
        let arg = axiom(&mut env, &format!("tailType{i}"), sort(1));
        app(prefix.clone(), arg)
      })
      .collect();
    let mut tc = TypeChecker::new(&mut env);
    let key = tc.infer_key(prefix);
    take_op_counts();
    for tail in tails {
      if !admit {
        // A cold two-touch filter never nominates a prefix, reproducing the
        // previous batched result-cache policy without a production toggle.
        tc.prefix_admission = Default::default();
      } else {
        tc.prefix_admission.observe(key, false);
      }
      tc.infer(&tail).unwrap();
    }
    take_op_counts()
  };
  let cold = run(false);
  let hot = run(true);
  eprintln!("reused prefix work: cold={cold:?}, hot={hot:?}");
  assert!(hot.def_eq_calls * 4 < cold.def_eq_calls);
  assert!(hot.intern_nodes * 2 < cold.intern_nodes);
}
