use super::*;
use crate::{
  constant::KConst,
  env::KEnv,
  mode::{Anon, Meta},
};
use ix_common::{
  address::Address,
  env::{BinderInfo, DefinitionSafety, Name, ReducibilityHints},
};

fn id<M: KernelMode>(s: &str) -> KId<M> {
  KId::new(
    Address::hash(s.as_bytes()),
    M::meta_field(Name::str(Name::anon(), s.to_owned())),
  )
}

fn cnst<M: KernelMode>(s: &str) -> KExpr<M> {
  KExpr::cnst(id(s), Box::new([]))
}

fn arrow<M: KernelMode>(a: KExpr<M>, b: KExpr<M>) -> KExpr<M> {
  KExpr::all(
    M::meta_field(Name::anon()),
    M::meta_field(BinderInfo::Default),
    a,
    b,
  )
}

fn lam<M: KernelMode>(body: KExpr<M>) -> KExpr<M> {
  KExpr::lam(
    M::meta_field(Name::anon()),
    M::meta_field(BinderInfo::Default),
    cnst("A"),
    body,
  )
}

fn axiom<M: KernelMode>(env: &mut KEnv<M>, name: &str, ty: KExpr<M>) {
  env.insert(
    id(name),
    KConst::Axio {
      name: M::meta_field(Name::anon()),
      level_params: M::meta_field(vec![]),
      is_unsafe: false,
      lvls: 0,
      ty,
    },
  );
}

fn defn<M: KernelMode>(
  env: &mut KEnv<M>,
  name: &str,
  ty: KExpr<M>,
  val: KExpr<M>,
) {
  env.insert(
    id(name),
    KConst::Defn {
      name: M::meta_field(Name::anon()),
      level_params: M::meta_field(vec![]),
      kind: DefKind::Definition,
      safety: DefinitionSafety::Safe,
      hints: ReducibilityHints::Regular(7),
      lvls: 0,
      ty,
      val,
      lean_all: M::meta_field(vec![]),
      block: id(name),
    },
  );
}

fn setup<M: KernelMode>() -> KEnv<M> {
  let mut env = KEnv::new();
  axiom(&mut env, "A", KExpr::sort(KUniv::succ(KUniv::zero())));
  axiom(&mut env, "a", cnst("A"));
  axiom(&mut env, "b", cnst("A"));
  axiom(&mut env, "F", arrow(cnst("A"), cnst("A")));
  axiom(&mut env, "G", arrow(cnst("A"), arrow(cnst("A"), cnst("A"))));
  defn(&mut env, "alias", cnst("A"), cnst("a"));
  defn(
    &mut env,
    "id",
    arrow(cnst("A"), cnst("A")),
    lam(KExpr::var(0, M::meta_field(Name::anon()))),
  );
  defn(&mut env, "ignore", arrow(cnst("A"), cnst("A")), lam(cnst("a")));
  env
}

fn app<M: KernelMode>(
  tc: &mut TypeChecker<'_, M>,
  f: KExpr<M>,
  a: KExpr<M>,
) -> KExpr<M> {
  tc.intern(KExpr::app(f, a))
}

fn pair_key<M: KernelMode>(
  tc: &mut TypeChecker<'_, M>,
  a: &KExpr<M>,
  b: &KExpr<M>,
) -> (Addr, Addr, CtxAddr) {
  let (lo, hi) = canonical_pair(a.hash_key(), b.hash_key());
  (lo, hi, tc.def_eq_ctx_key(a, b))
}

fn chain<M: KernelMode>(
  tc: &mut TypeChecker<'_, M>,
  n: usize,
) -> (KExpr<M>, KExpr<M>) {
  let f = tc.intern(cnst("F"));
  let mut a = tc.intern(cnst("alias"));
  let mut b = tc.intern(cnst("a"));
  for _ in 0..n {
    a = app(tc, f.clone(), a);
    b = app(tc, f.clone(), b);
  }
  (a, b)
}

fn deep_chain<M: KernelMode>() {
  let mut env = setup::<M>();
  let mut tc = TypeChecker::new(&mut env);
  let (a, b) = chain(&mut tc, MAX_DEF_EQ_DEPTH as usize + 100);
  assert!(tc.is_def_eq(&a, &b).unwrap());
  assert!(
    tc.def_eq_peak < APP_CONGRUENCE_MIN_DEPTH + 20,
    "depth {}",
    tc.def_eq_peak
  );
  assert_eq!(tc.def_eq_depth, 0);
  assert!(!tc.in_app_congruence);

  // Fresh caches and the original path: same well-typed finite chain still
  // reaches the old guard. Large stack matches the real dedicated worker.
  let mut old_env = setup::<M>();
  let mut old = TypeChecker::new(&mut old_env);
  old.in_app_congruence = true;
  let (a, b) = chain(&mut old, MAX_DEF_EQ_DEPTH as usize + 100);
  assert!(matches!(old.is_def_eq(&a, &b), Err(TcError::MaxRecDepth)));
  assert_eq!(old.def_eq_depth, 0);
}

#[test]
fn long_application_chain_uses_worklist_not_def_eq_stack() {
  std::thread::Builder::new()
    .stack_size(256 * 1024 * 1024)
    .spawn(|| {
      deep_chain::<Anon>();
      deep_chain::<Meta>();
    })
    .unwrap()
    .join()
    .unwrap();
}

fn partial_success<M: KernelMode>() {
  let mut env = setup::<M>();
  let mut tc = TypeChecker::new(&mut env);
  let left_inner = app(&mut tc, cnst("F"), cnst("alias"));
  let right_inner = app(&mut tc, cnst("F"), cnst("a"));
  let left_fn = app(&mut tc, cnst("G"), left_inner);
  let right_fn = app(&mut tc, cnst("G"), right_inner);
  let a = app(&mut tc, left_fn.clone(), cnst("a"));
  let b = app(&mut tc, right_fn.clone(), cnst("b"));
  let root_key = pair_key(&mut tc, &a, &b);
  let fn_key = pair_key(&mut tc, &left_fn, &right_fn);
  assert!(!tc.app_congruence_probe(&a, &b).unwrap());
  assert_eq!(tc.env.def_eq_cache.get(&fn_key), Some(&true));
  assert!(!tc.env.def_eq_cache.contains_key(&root_key));
  assert!(!tc.equiv_manager.is_equiv(
    &EqKey::new(a.hash_key(), root_key.2, 0, 0),
    &EqKey::new(b.hash_key(), root_key.2, 0, 0),
  ));
  assert!(!tc.is_def_eq(&a, &b).unwrap());
  assert!(!tc.is_def_eq(&b, &a).unwrap());
}

#[test]
fn failed_child_never_completes_pending_parent() {
  partial_success::<Anon>();
  partial_success::<Meta>();
}

fn non_injective<M: KernelMode>() {
  let mut env = setup::<M>();
  let mut tc = TypeChecker::new(&mut env);
  tc.def_eq_depth = APP_CONGRUENCE_MIN_DEPTH;
  let a = app(&mut tc, cnst("ignore"), cnst("a"));
  let b = app(&mut tc, cnst("ignore"), cnst("b"));
  let key = pair_key(&mut tc, &a, &b);
  assert!(!tc.app_congruence_probe(&a, &b).unwrap());
  assert!(!tc.env.def_eq_cache.contains_key(&key));
  assert!(tc.is_def_eq(&a, &b).unwrap());
}

#[test]
fn unequal_arguments_of_ignoring_function_fall_back_to_reduction() {
  non_injective::<Anon>();
  non_injective::<Meta>();
}

fn diamond<M: KernelMode>() {
  let mut env = setup::<M>();
  let mut tc = TypeChecker::new(&mut env);
  let g = tc.intern(cnst("G"));
  let (mut a, mut b) = (tc.intern(cnst("alias")), tc.intern(cnst("a")));
  for _ in 0..64 {
    let af = app(&mut tc, g.clone(), a.clone());
    let bf = app(&mut tc, g.clone(), b.clone());
    a = app(&mut tc, af, a);
    b = app(&mut tc, bf, b);
  }
  tc.rec_fuel = 1_000;
  assert!(tc.app_congruence_probe(&a, &b).unwrap());
  assert!(tc.rec_fuel > 700, "completed DAG branches must not be revisited");
}

#[test]
fn shared_diamond_uses_only_completed_equalities() {
  diamond::<Anon>();
  diamond::<Meta>();
}

fn budgets<M: KernelMode>() {
  let mut env = setup::<M>();
  let mut tc = TypeChecker::new(&mut env);
  let (a, b) = chain(&mut tc, 4);
  let key = pair_key(&mut tc, &a, &b);
  tc.rec_fuel = 1;
  assert!(!tc.app_congruence_probe(&a, &b).unwrap());
  assert_eq!(tc.rec_fuel, 0);
  assert!(!tc.in_app_congruence);
  assert!(!tc.env.def_eq_cache.contains_key(&key));
  assert_eq!(tc.def_eq_depth, 0);

  tc.rec_fuel = 10_000;
  tc.def_eq_depth = MAX_DEF_EQ_DEPTH;
  assert!(!tc.app_congruence_probe(&a, &b).unwrap());
  assert_eq!(tc.def_eq_depth, MAX_DEF_EQ_DEPTH);
  assert!(tc.rec_fuel < 10_000);
  assert!(!tc.in_app_congruence);
  assert!(!tc.env.def_eq_cache.contains_key(&key));
  tc.def_eq_depth = 0;
  assert!(tc.is_def_eq(&a, &b).unwrap());

  let (a, b) =
    chain(&mut tc, usize::try_from(APP_CONGRUENCE_FUEL).unwrap() + 100);
  let key = pair_key(&mut tc, &a, &b);
  tc.rec_fuel = 20_000;
  assert!(!tc.app_congruence_probe(&a, &b).unwrap());
  assert_eq!(tc.rec_fuel, 20_000 - APP_CONGRUENCE_FUEL);
  assert!(!tc.in_app_congruence);
  assert!(!tc.env.def_eq_cache.contains_key(&key));
}

#[test]
fn budget_and_depth_misses_restore_state_without_refunds() {
  std::thread::Builder::new()
    .stack_size(256 * 1024 * 1024)
    .spawn(|| {
      budgets::<Anon>();
      budgets::<Meta>();
    })
    .unwrap()
    .join()
    .unwrap();
}

fn malformed<M: KernelMode>() {
  let mut env = setup::<M>();
  defn(
    &mut env,
    "bad",
    cnst("A"),
    KExpr::sort(KUniv::param(1, M::meta_field(Name::anon()))),
  );
  let mut tc = TypeChecker::new(&mut env);
  let a =
    app(&mut tc, cnst("F"), KExpr::cnst(id("bad"), Box::new([KUniv::zero()])));
  let b = app(&mut tc, cnst("F"), cnst("a"));
  let key = pair_key(&mut tc, &a, &b);
  let fuel = tc.rec_fuel;
  assert!(matches!(
    tc.app_congruence_probe(&a, &b),
    Err(TcError::UnivParamOutOfRange { .. })
  ));
  assert!(!tc.in_app_congruence);
  assert_eq!(tc.def_eq_depth, 0);
  assert!(tc.rec_fuel < fuel);
  assert!(!tc.env.def_eq_cache.contains_key(&key));
}

#[test]
fn non_budget_leaf_error_propagates_without_parent_cache_entry() {
  malformed::<Anon>();
  malformed::<Meta>();
}

fn contexts<M: KernelMode>() {
  let mut env = setup::<M>();
  let mut tc = TypeChecker::new(&mut env);
  let a = app(&mut tc, cnst("F"), KExpr::var(0, M::meta_field(Name::anon())));
  let b = app(&mut tc, cnst("F"), cnst("a"));
  tc.push_let(cnst("A"), cnst("a"));
  let first = pair_key(&mut tc, &a, &b);
  assert!(tc.app_congruence_probe(&a, &b).unwrap());
  assert_eq!(tc.depth(), 1);
  tc.pop_local();
  tc.push_let(cnst("A"), cnst("b"));
  let second = pair_key(&mut tc, &a, &b);
  assert_ne!(first, second);
  assert!(!tc.app_congruence_probe(&a, &b).unwrap());
  assert!(!tc.env.def_eq_cache.contains_key(&second));
  assert!(!tc.is_def_eq(&a, &b).unwrap());
  assert_eq!(tc.depth(), 1);
}

#[test]
fn completed_open_pair_is_not_reused_in_another_context() {
  contexts::<Anon>();
  contexts::<Meta>();
}

fn modes<M: KernelMode>() {
  let mut env = setup::<M>();
  let mut tc = TypeChecker::new(&mut env);
  let (a, b) = chain(&mut tc, 4);
  let key = pair_key(&mut tc, &a, &b);
  // A failed cheap attempt is not a full-mode inequality certificate.
  tc.env.def_eq_cheap_cache.insert(key, false);
  assert!(tc.app_congruence_probe(&a, &b).unwrap());
  assert_eq!(tc.env.def_eq_cache.get(&key), Some(&true));
  tc.env.clear_reduction_caches();
  tc.equiv_manager.clear();
  tc.cheap_recursion_depth = 1;
  tc.infer_only = true;
  tc.eager_reduce = true;
  assert!(tc.app_congruence_probe(&a, &b).unwrap());
  assert_eq!(tc.env.def_eq_cheap_cache.get(&key), Some(&true));
  assert_eq!(tc.env.def_eq_cache.get(&key), Some(&true));
  assert_eq!(tc.cheap_recursion_depth, 1);
  assert!(tc.infer_only && tc.eager_reduce);
  assert_eq!(tc.depth(), 0);
}

#[test]
fn mode_boundaries_and_positive_cache_promotion_are_preserved() {
  modes::<Anon>();
  modes::<Meta>();
}

fn dependent<M: KernelMode>() {
  let mut env = setup::<M>();
  axiom(
    &mut env,
    "B",
    arrow(cnst("A"), KExpr::sort(KUniv::succ(KUniv::zero()))),
  );
  let b_a = KExpr::app(cnst("B"), cnst("a"));
  axiom(&mut env, "v", b_a);
  let b_alias = KExpr::app(cnst("B"), cnst("alias"));
  defn(&mut env, "vAlias", b_alias, cnst("v"));
  axiom(
    &mut env,
    "dep",
    arrow(
      cnst("A"),
      arrow(
        KExpr::app(cnst("B"), KExpr::var(0, M::meta_field(Name::anon()))),
        cnst("A"),
      ),
    ),
  );
  let mut tc = TypeChecker::new(&mut env);
  let af = app(&mut tc, cnst("dep"), cnst("alias"));
  let bf = app(&mut tc, cnst("dep"), cnst("a"));
  let a = app(&mut tc, af, cnst("vAlias"));
  let b = app(&mut tc, bf, cnst("v"));
  tc.infer(&a).unwrap();
  tc.infer(&b).unwrap();
  assert!(tc.app_congruence_probe(&a, &b).unwrap());
  assert!(tc.is_def_eq(&a, &b).unwrap());
}

#[test]
fn dependent_spine_compares_prefix_before_later_arguments() {
  dependent::<Anon>();
  dependent::<Meta>();
}

#[test]
fn probe_does_not_nest_and_reset_clears_its_flag() {
  let mut env = setup::<Anon>();
  let mut tc = TypeChecker::new(&mut env);
  let (a, b) = chain(&mut tc, 4);
  tc.in_app_congruence = true;
  let fuel = tc.rec_fuel;
  assert!(!tc.app_congruence_probe(&a, &b).unwrap());
  assert!(tc.in_app_congruence);
  assert_eq!(tc.rec_fuel, fuel);
  tc.reset();
  assert!(!tc.in_app_congruence);
}

#[test]
fn shallow_comparisons_do_not_pay_for_speculative_work() {
  let mut env = setup::<Anon>();
  let mut tc = TypeChecker::new(&mut env);
  let (a, b) = chain(&mut tc, 4);
  tc.def_eq_depth = APP_CONGRUENCE_MIN_DEPTH - 1;
  let fuel = tc.rec_fuel;
  assert!(!tc.try_app_congruence(&a, &b).unwrap());
  assert_eq!(tc.rec_fuel, fuel);
  assert!(tc.env.def_eq_cache.is_empty());
  tc.def_eq_depth += 1;
  assert!(tc.try_app_congruence(&a, &b).unwrap());
  assert_eq!(tc.def_eq_depth, APP_CONGRUENCE_MIN_DEPTH);
}

fn below_guard_matches_original<M: KernelMode>() {
  for n in [1, 64, 128] {
    let check = |old: bool| {
      let mut env = setup::<M>();
      let mut tc = TypeChecker::new(&mut env);
      tc.in_app_congruence = old;
      let (a, b) = chain(&mut tc, n);
      assert!(tc.is_def_eq(&a, &b).unwrap());
      assert!(tc.def_eq_peak < APP_CONGRUENCE_MIN_DEPTH);
      (tc.fuel_used(), tc.def_eq_peak)
    };
    assert_eq!(check(false), check(true), "chain length {n}");
  }
}

#[test]
fn ordinary_comparisons_preserve_recursive_work_and_depth() {
  // Depth 64 was enough to activate the earlier eager variant. These
  // successful ordinary checks should do exactly the original work now.
  below_guard_matches_original::<Anon>();
  below_guard_matches_original::<Meta>();
}

#[test]
fn cached_unequal_child_only_abandons_the_probe() {
  let mut env = setup::<Anon>();
  let mut tc = TypeChecker::new(&mut env);
  let a = app(&mut tc, cnst("F"), cnst("a"));
  let b = app(&mut tc, cnst("F"), cnst("b"));
  assert!(!tc.is_def_eq(&a, &b).unwrap());
  let left = app(&mut tc, cnst("ignore"), a);
  let right = app(&mut tc, cnst("ignore"), b);
  let fuel = tc.rec_fuel;
  let key = pair_key(&mut tc, &left, &right);
  assert!(!tc.app_congruence_probe(&left, &right).unwrap());
  assert_eq!(tc.rec_fuel, fuel - 1, "the cached child must not be expanded");
  assert!(!tc.env.def_eq_cache.contains_key(&key));
  assert!(tc.is_def_eq(&left, &right).unwrap());
}

fn generated<M: KernelMode>(
  tc: &mut TypeChecker<'_, M>,
  seed: u64,
  depth: u64,
) -> KExpr<M> {
  if depth == 0 {
    return tc.intern(cnst(["a", "b", "alias"][(seed % 3) as usize]));
  }
  let child = generated(tc, seed / 3 + 1, depth - 1);
  match seed % 4 {
    0 => app(tc, cnst("F"), child),
    1 => app(tc, cnst("id"), child),
    2 => app(tc, cnst("ignore"), child),
    _ => {
      let f = app(tc, cnst("G"), child.clone());
      app(tc, f, child)
    },
  }
}

fn differential<M: KernelMode>() {
  for n in 0..96 {
    let check = |old: bool| {
      let mut env = setup::<M>();
      let mut tc = TypeChecker::new(&mut env);
      tc.in_app_congruence = old;
      // Exercise the worklist even on these small terms. Both variants
      // start at the same depth; only the old path disables the probe.
      tc.def_eq_depth = APP_CONGRUENCE_MIN_DEPTH;
      let a = generated(&mut tc, n * 17 + 3, 5);
      let b = generated(&mut tc, n * 13 + 3, 5);
      tc.is_def_eq(&a, &b).unwrap()
    };
    assert_eq!(check(false), check(true), "seed {n}");
  }
}

#[test]
fn small_well_typed_terms_match_original_recursive_conversion() {
  differential::<Anon>();
  differential::<Meta>();
}

fn universes_and_arity<M: KernelMode>() {
  let mut env = setup::<M>();
  // An unused universe parameter leaves both applications well typed, but
  // different instantiations of an irreducible axiom are not def-eq heads.
  env.insert(
    id("poly"),
    KConst::Axio {
      name: M::meta_field(Name::anon()),
      level_params: M::meta_field(vec![Name::str(
        Name::anon(),
        "u".to_owned(),
      )]),
      is_unsafe: false,
      lvls: 1,
      ty: arrow(cnst("A"), cnst("A")),
    },
  );
  let mut tc = TypeChecker::new(&mut env);
  tc.def_eq_depth = APP_CONGRUENCE_MIN_DEPTH;
  let a =
    app(&mut tc, KExpr::cnst(id("poly"), Box::new([KUniv::zero()])), cnst("a"));
  let b = app(
    &mut tc,
    KExpr::cnst(id("poly"), Box::new([KUniv::succ(KUniv::zero())])),
    cnst("a"),
  );
  tc.infer(&a).unwrap();
  tc.infer(&b).unwrap();
  assert_eq!(tc.try_same_head_spine(&a, &b).unwrap(), None);
  assert!(!tc.app_congruence_probe(&a, &b).unwrap());
  assert!(!tc.is_def_eq(&a, &b).unwrap());

  let partial = app(&mut tc, cnst("G"), cnst("a"));
  let full = app(&mut tc, partial.clone(), cnst("b"));
  tc.infer(&partial).unwrap();
  tc.infer(&full).unwrap();
  assert_eq!(tc.try_same_head_spine(&partial, &full).unwrap(), None);
}

#[test]
fn same_head_is_not_enough_without_matching_universes_and_arity() {
  universes_and_arity::<Anon>();
  universes_and_arity::<Meta>();
}
