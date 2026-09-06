use super::*;
use crate::env::KEnv;
use crate::mode::{Anon, Meta};
use ix_common::address::Address;
use ix_common::env::{BinderInfo, Name};

fn name<M: KernelMode>(s: &str) -> M::MField<Name> {
  M::meta_field(Name::str(Name::anon(), s.to_owned()))
}
fn sort<M: KernelMode>(n: u64) -> KExpr<M> {
  let mut u = KUniv::zero();
  for _ in 0..n {
    u = KUniv::succ(u);
  }
  KExpr::sort(u)
}
fn var<M: KernelMode>(i: u64) -> KExpr<M> {
  KExpr::var(i, name::<M>("var"))
}
fn all<M: KernelMode>(dom: KExpr<M>, cod: KExpr<M>) -> KExpr<M> {
  KExpr::all(name::<M>("binder"), M::meta_field(BinderInfo::Implicit), dom, cod)
}
fn axiom<M: KernelMode>(
  env: &mut KEnv<M>,
  s: &str,
  lvls: u64,
  ty: KExpr<M>,
) -> KId<M> {
  let id = KId::new(Address::hash(s.as_bytes()), name::<M>(s));
  env.insert(
    id.clone(),
    KConst::Axio {
      name: name::<M>(s),
      level_params: M::meta_field(
        (0..lvls).map(|i| Name::str(Name::anon(), format!("u{i}"))).collect(),
      ),
      is_unsafe: false,
      lvls,
      ty,
    },
  );
  id
}
fn cnst<M: KernelMode>(id: &KId<M>, us: &[KUniv<M>]) -> KExpr<M> {
  KExpr::cnst(id.clone(), us.to_vec().into_boxed_slice())
}
fn app<M: KernelMode>(f: KExpr<M>, a: KExpr<M>) -> KExpr<M> {
  KExpr::app(f, a)
}

fn propositions_and_data<M: KernelMode>() {
  let mut env = KEnv::<M>::new();
  let prop = axiom(&mut env, "P", 0, sort(0));
  let p = cnst(&prop, &[]);
  let proof1 = axiom(&mut env, "p1", 0, p.clone());
  let proof2 = axiom(&mut env, "p2", 0, p.clone());
  let data = axiom(&mut env, "A", 0, sort(1));
  let a = cnst(&data, &[]);
  let data1 = axiom(&mut env, "x1", 0, a.clone());
  let data2 = axiom(&mut env, "x2", 0, a.clone());
  let mut tc = TypeChecker::new(&mut env);
  assert!(tc.known_non_proof(&p), "a proposition is not itself a proof");
  assert!(tc.known_non_proof(&a));
  assert!(tc.known_non_proof(&cnst(&data1, &[])));
  assert!(!tc.known_non_proof(&cnst(&proof1, &[])));
  assert!(tc.is_def_eq(&cnst(&proof1, &[]), &cnst(&proof2, &[])).unwrap());
  assert!(!tc.is_def_eq(&cnst(&data1, &[]), &cnst(&data2, &[])).unwrap());
}

#[test]
fn distinguishes_propositions_proofs_and_data_in_both_modes() {
  propositions_and_data::<Anon>();
  propositions_and_data::<Meta>();
}

fn universes<M: KernelMode>() {
  let mut env = KEnv::<M>::new();
  let u = KUniv::param(0, name::<M>("u"));
  // id.{u} : (A : Sort u) -> A -> A. For u=0 it is a proof even
  // before application, because the remaining Pis are impredicative.
  let id =
    axiom(&mut env, "identity", 1, all(KExpr::sort(u), all(var(0), var(1))));
  let mut tc = TypeChecker::new(&mut env);
  for (u, expected) in [
    (KUniv::zero(), false),
    (KUniv::succ(KUniv::zero()), true),
    (KUniv::param(7, name::<M>("symbolic")), false),
    (KUniv::imax(KUniv::succ(KUniv::zero()), KUniv::zero()), false),
    (
      KUniv::max(KUniv::param(2, name::<M>("v")), KUniv::succ(KUniv::zero())),
      true,
    ),
  ] {
    let head = cnst(&id, &[u]);
    let summary = tc.summarize_declaration(&head).unwrap();
    assert_eq!(summary.arity, 2);
    assert_eq!(summary.result == ProofEligibility::NonProof, expected);
    let mut term = head;
    for _ in 0..=2 {
      assert_eq!(tc.known_non_proof(&term), expected);
      // Eligibility is independent of argument values; this does NOT assert
      // that these deliberately arbitrary arguments are well-typed.
      term = app(term, sort(0));
    }
    assert!(!tc.known_non_proof(&term), "overapplication is not summarized");
  }
  assert_eq!(tc.env.decl_summary_cache.len(), 5);
  assert!(tc.env.infer_cache.is_empty());
  assert!(tc.env.infer_only_cache.is_empty());
  assert!(tc.ctx.is_empty() && tc.lctx.is_empty());
}

#[test]
fn universe_instantiations_and_partial_applications_stay_separate() {
  universes::<Anon>();
  universes::<Meta>();
}

fn partial_proofs<M: KernelMode>() {
  let mut env = KEnv::<M>::new();
  let p_id = axiom(&mut env, "P", 0, sort(0));
  let p = cnst(&p_id, &[]);
  let h_id = axiom(&mut env, "hP", 0, p.clone());
  let h = cnst(&h_id, &[]);
  let ty =
    all(KExpr::sort(KUniv::param(0, name::<M>("u"))), all(var(0), var(1)));
  let f = axiom(&mut env, "f", 1, ty.clone());
  let g = axiom(&mut env, "g", 1, ty);
  for (u, args, non_proof) in [
    (KUniv::zero(), [p.clone(), h], false),
    (KUniv::succ(KUniv::zero()), [sort(0), p], true),
  ] {
    let mut a = cnst(&f, std::slice::from_ref(&u));
    let mut b = cnst(&g, &[u]);
    let mut tc = TypeChecker::new(&mut env);
    for applied in 0..=2 {
      tc.infer(&a).unwrap();
      tc.infer(&b).unwrap();
      assert_eq!(tc.known_non_proof(&a), non_proof);
      assert_eq!(tc.is_def_eq(&a, &b).unwrap(), !non_proof);
      if let Some(arg) = args.get(applied) {
        a = app(a, arg.clone());
        b = app(b, arg.clone());
      }
    }
  }
}

#[test]
fn impredicative_partial_applications_preserve_proof_irrelevance() {
  partial_proofs::<Anon>();
  partial_proofs::<Meta>();
}

fn families<M: KernelMode>() {
  let mut env = KEnv::<M>::new();
  let u = KUniv::param(0, name::<M>("u"));
  // F.{u} : Type -> Sort u. g.{u} : (A : Type) -> F.{u} A.
  let family = axiom(&mut env, "F", 1, all(sort(1), KExpr::sort(u.clone())));
  let result = app(cnst(&family, std::slice::from_ref(&u)), var(0));
  let g = axiom(&mut env, "g", 1, all(sort(1), result));
  // h : (A : Type) -> (B : A -> Type) -> (x : A) -> B x
  let h = axiom(
    &mut env,
    "h",
    0,
    all(sort(1), all(all(var(0), sort(1)), all(var(1), app(var(1), var(0))))),
  );
  let h = cnst(&h, &[]);
  let mut tc = TypeChecker::new(&mut env);
  assert!(!tc.known_non_proof(&cnst(&g, &[KUniv::zero()])));
  assert!(tc.known_non_proof(&cnst(&g, &[KUniv::succ(KUniv::zero())])));
  assert!(tc.known_non_proof(&h));
  // The summary does not create/open FVars or depend on the caller's local
  // context. Warm queries must remain free of type-inference/fuel work.
  tc.push_local(sort(1));
  tc.rec_fuel = 0;
  assert!(tc.known_non_proof(&h));
  assert_eq!(tc.rec_fuel, 0);
  assert_eq!(tc.ctx.len(), 1);
  assert!(tc.lctx.is_empty());
}

#[test]
fn composes_universe_substitutions_and_handles_bound_type_families() {
  families::<Anon>();
  families::<Meta>();
}

#[test]
fn unknown_shapes_fall_back_without_unfolding() {
  let mut env = KEnv::<Anon>::new();
  let hidden = KExpr::let_((), sort(1), sort(0), var(0), false);
  let f = axiom(&mut env, "hidden", 0, hidden);
  let mut deep = sort(1);
  for _ in 0..65 {
    deep = all(sort(1), deep);
  }
  let deep = axiom(&mut env, "deep", 0, deep);
  let malformed = axiom(&mut env, "loose", 0, var(0));
  let mut tc = TypeChecker::new(&mut env);
  for id in [&f, &deep, &malformed] {
    assert!(!tc.known_non_proof(&cnst(id, &[])));
  }
  assert!(!tc.known_non_proof(&app(var(0), sort(0))));
  assert!(tc.env.whnf_cache.is_empty() && tc.env.unfold_cache.is_empty());
  assert!(tc.env.infer_cache.is_empty() && tc.env.infer_only_cache.is_empty());
  assert_eq!(tc.fuel_used(), 0);
}

#[test]
fn arity_missing_dependencies_and_universe_errors_are_not_cached() {
  let mut env = KEnv::<Anon>::new();
  let id = axiom(&mut env, "poly", 1, KExpr::sort(KUniv::param(0, ())));
  let missing = KId::new(Address::hash(b"missing"), ());
  let f = axiom(&mut env, "f", 0, cnst(&missing, &[]));
  let broken = axiom(&mut env, "broken", 0, KExpr::sort(KUniv::param(1, ())));
  let mut tc = TypeChecker::new(&mut env);
  for e in
    [cnst(&id, &[]), cnst(&f, &[]), cnst(&broken, &[]), cnst(&missing, &[])]
  {
    assert!(!tc.known_non_proof(&e));
  }
  assert!(tc.env.decl_summary_cache.is_empty());
  let inserted = axiom(tc.env, "missing", 0, sort(1));
  assert_eq!(inserted, missing);
  assert!(tc.known_non_proof(&cnst(&f, &[])));
}

#[test]
fn declaration_replacement_and_all_reset_paths_invalidate_summaries() {
  let mut env = KEnv::<Anon>::new();
  let t = axiom(&mut env, "T", 0, sort(1));
  let f = axiom(&mut env, "f", 0, cnst(&t, &[]));
  let e = cnst(&f, &[]);
  assert!(TypeChecker::new(&mut env).known_non_proof(&e));
  assert_eq!(env.cache_sizes().decl_summary, 1);
  // Change a dependency, not just f itself.
  axiom(&mut env, "T", 0, sort(0));
  assert!(env.decl_summary_cache.is_empty());
  assert!(!TypeChecker::new(&mut env).known_non_proof(&e));
  for reset in 0..4 {
    let t = axiom(&mut env, "T", 0, sort(1));
    let f = axiom(&mut env, "f", 0, cnst(&t, &[]));
    assert!(TypeChecker::new(&mut env).known_non_proof(&cnst(&f, &[])));
    assert!(!env.decl_summary_cache.is_empty());
    match reset {
      0 => env.clear_reduction_caches(),
      1 => env.clear(),
      2 => env.clear_with_capacity_limit(0),
      _ => env.clear_releasing_memory(),
    }
    assert!(env.decl_summary_cache.is_empty());
  }
}

#[test]
fn bounded_level_classification_handles_imax_and_symbolic_zero() {
  use ProofEligibility::{NonProof, ProofEligible, Unknown};
  let u: KUniv<Anon> = KUniv::param(0, ());
  for (level, expected) in [
    (u.clone(), Unknown),
    (KUniv::zero(), ProofEligible),
    (KUniv::succ(u.clone()), NonProof),
    (KUniv::imax(KUniv::succ(u.clone()), u.clone()), Unknown),
    (KUniv::imax(u.clone(), KUniv::zero()), ProofEligible),
    (KUniv::max(u, KUniv::succ(KUniv::zero())), NonProof),
  ] {
    assert_eq!(classify_sort(&level, &[], &mut 256).unwrap(), Some(expected));
    assert_eq!(classify_sort(&level, &[], &mut 0).unwrap(), None);
  }
}

#[test]
fn universe_analysis_is_bounded_and_does_not_capture_actual_parameters() {
  let mut u: KUniv<Anon> = KUniv::zero();
  for _ in 0..MAX_LEVEL_VISITS + 1 {
    u = KUniv::succ(u);
  }
  let mut visits = MAX_LEVEL_VISITS;
  assert_eq!(classify_sort(&u, &[], &mut visits).unwrap(), None);
  // Substituting u0 -> u0 leaves a symbolic parameter, not a cycle.
  let p = KUniv::<Anon>::param(0, ());
  assert_eq!(
    classify_sort(&p, &[std::slice::from_ref(&p)], &mut 8).unwrap(),
    Some(ProofEligibility::Unknown)
  );
  let inner = [p.clone()];
  let outer = [KUniv::zero()];
  assert_eq!(
    classify_sort(&p, &[&inner, &outer], &mut 8).unwrap(),
    Some(ProofEligibility::ProofEligible)
  );
}
