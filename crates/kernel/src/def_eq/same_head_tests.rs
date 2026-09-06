use super::*;
use crate::{
  env::KEnv,
  mode::{Anon, Meta},
};
use ix_common::{
  address::Address,
  env::{BinderInfo, DefinitionSafety, Name, ReducibilityHints},
};

fn id<M: KernelMode>(name: &str) -> KId<M> {
  KId::new(Address::hash(name.as_bytes()), M::meta_field(Name::anon()))
}

fn cnst<M: KernelMode>(name: &str) -> KExpr<M> {
  KExpr::cnst(id(name), Box::new([]))
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
  for (name, ty) in [
    ("A", KExpr::sort(KUniv::succ(KUniv::zero()))),
    ("a", cnst("A")),
    ("b", cnst("A")),
  ] {
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
  for (name, body) in
    [("ignore", cnst("a")), ("id", KExpr::var(0, M::meta_field(Name::anon())))]
  {
    let ty = KExpr::all(
      M::meta_field(Name::anon()),
      M::meta_field(BinderInfo::Default),
      cnst("A"),
      cnst("A"),
    );
    let val = KExpr::lam(
      M::meta_field(Name::anon()),
      M::meta_field(BinderInfo::Default),
      cnst("A"),
      body,
    );
    defn(&mut env, name, ty, val);
  }
  env
}

/// A well-typed, finite alias chain with beta steps per link. Bare constant
/// aliases do not consume recursive fuel in the lazy-delta loop. Each body
/// is shallow, avoiding a deep expression/drop stack or enlarged thread stack.
fn beta_alias_chain<M: KernelMode>(
  env: &mut KEnv<M>,
  links: u64,
  betas: usize,
) -> KExpr<M> {
  let mut val = cnst("a");
  let identity = KExpr::lam(
    M::meta_field(Name::anon()),
    M::meta_field(BinderInfo::Default),
    cnst("A"),
    KExpr::var(0, M::meta_field(Name::anon())),
  );
  for i in 0..links {
    let name = format!("alias{i}");
    for _ in 0..betas {
      val = KExpr::app(identity.clone(), val);
    }
    defn(env, &name, cnst("A"), val);
    val = cnst(&name);
  }
  val
}

fn expensive<M: KernelMode>(env: &mut KEnv<M>) -> KExpr<M> {
  // Exceed the Regular allowance without reaching the separate 10k-iteration
  // lazy-delta guard or constructing a deeply nested expression body.
  beta_alias_chain(env, SAME_HEAD_SPECULATION_ATTEMPT_FUEL, 64)
}

fn assert_not_cached<M: KernelMode>(
  tc: &mut TypeChecker<'_, M>,
  a: &KExpr<M>,
  b: &KExpr<M>,
) {
  let (lo, hi) = canonical_pair(a.hash_key(), b.hash_key());
  let key = (lo, hi, tc.def_eq_ctx_key(a, b));
  assert!(!tc.env.def_eq_cache.contains_key(&key));
  assert!(!tc.env.def_eq_cheap_cache.contains_key(&key));
}

fn fallback<M: KernelMode>(head: &str, expected: bool) {
  let mut env = setup::<M>();
  let arg = expensive(&mut env);
  let head_expr = cnst(head);
  let other_arg = cnst("b");
  let a = KExpr::app(head_expr.clone(), arg.clone());
  let b = KExpr::app(head_expr.clone(), other_arg.clone());
  let mut tc = TypeChecker::new(&mut env);
  let before = tc.rec_fuel;
  assert_eq!(
    tc.try_same_head_spine_speculative(&a, &b, &id(head), true).unwrap(),
    None
  );
  assert_eq!(before - tc.rec_fuel, SAME_HEAD_REGULAR_ATTEMPT_FUEL);
  assert_eq!(tc.same_head_fuel_reserve, 0);
  assert!(!tc.same_head_backoff.should_skip(true));
  assert_not_cached(&mut tc, &a, &b);
  assert_not_cached(&mut tc, &arg, &other_arg);
  assert_eq!(tc.def_eq_depth, 0);
  assert_eq!(tc.is_def_eq(&a, &b).unwrap(), expected);
  // Confirm delta rather than only a result rescued by congruence.
  assert!(tc.env.unfold_cache.contains_key(&head_expr.hash_key()));
  assert!(tc.fuel_used() > SAME_HEAD_REGULAR_ATTEMPT_FUEL);
}

#[test]
fn expensive_regular_probe_falls_back_without_accepting_unequal_terms() {
  fallback::<Anon>("ignore", true);
  fallback::<Meta>("ignore", true);
  fallback::<Anon>("id", false);
  fallback::<Meta>("id", false);
}

fn nested<M: KernelMode>(cheap: bool) {
  let mut env = setup::<M>();
  let arg = expensive(&mut env);
  let other_arg = cnst("a");
  let inner_a = KExpr::app(cnst("id"), arg.clone());
  let inner_b = KExpr::app(cnst("id"), other_arg.clone());
  let a = KExpr::app(cnst("ignore"), inner_a.clone());
  let b = KExpr::app(cnst("ignore"), inner_b.clone());
  let mut tc = TypeChecker::new(&mut env);
  tc.cheap_recursion_depth = u32::from(cheap);
  // Simulate an enclosing probe with less than one fresh allowance.
  tc.rec_fuel = 1_000;
  crate::perf::same_head::reset();
  assert_eq!(
    tc.try_same_head_spine_speculative(&a, &b, &id("ignore"), true).unwrap(),
    None
  );
  assert_eq!(tc.rec_fuel, 0, "nested probes must not replenish fuel");
  assert_eq!(tc.same_head_fuel_reserve, 0);
  assert_not_cached(&mut tc, &a, &b);
  assert_not_cached(&mut tc, &inner_a, &inner_b);
  assert_not_cached(&mut tc, &arg, &other_arg);
  assert_eq!(tc.def_eq_depth, 0);
  if crate::perf::same_head::enabled() {
    let report = crate::perf::same_head::summary();
    assert!(report.contains("active=0 max_depth=2 "), "{report}");
    assert!(report.contains("root_fuel=1000 "), "{report}");
    assert!(report.contains("accounting_errors=0"), "{report}");
  }
  // Resuming the same environment must not observe poisoned negative caches.
  tc.rec_fuel = crate::tc::max_rec_fuel();
  tc.cheap_recursion_depth = 0;
  assert!(tc.is_def_eq(&inner_a, &inner_b).unwrap());
  assert!(tc.is_def_eq(&a, &b).unwrap());
}

#[test]
fn nested_regular_probes_share_remaining_fuel_without_cache_poisoning() {
  for cheap in [false, true] {
    nested::<Anon>(cheap);
    nested::<Meta>(cheap);
  }
}

#[test]
fn productive_regular_probe_has_more_than_the_non_regular_allowance() {
  let mut env = setup::<Anon>();
  let arg = beta_alias_chain(&mut env, 128, 64);
  let head = cnst("id");
  let a = KExpr::app(head.clone(), arg);
  let b = KExpr::app(head.clone(), cnst("a"));
  let mut tc = TypeChecker::new(&mut env);
  assert!(tc.is_def_eq(&a, &b).unwrap());
  assert!(tc.fuel_used() > SAME_HEAD_SPECULATION_ATTEMPT_FUEL);
  assert!(tc.fuel_used() < SAME_HEAD_REGULAR_ATTEMPT_FUEL);
  assert!(!tc.env.unfold_cache.contains_key(&head.hash_key()));
  assert_eq!(tc.same_head_fuel_reserve, 0);
}

#[test]
fn late_regular_probe_still_uses_successful_congruence() {
  let mut env = setup::<Anon>();
  defn(&mut env, "alias", cnst("A"), cnst("a"));
  let head = cnst("id");
  let a = KExpr::app(head.clone(), cnst("alias"));
  let b = KExpr::app(head.clone(), cnst("a"));
  let mut tc = TypeChecker::new(&mut env);
  tc.rec_fuel -= SAME_HEAD_SPECULATION_START_FUEL;
  let before = tc.rec_fuel;
  assert!(tc.is_def_eq(&a, &b).unwrap());
  assert!(before - tc.rec_fuel < SAME_HEAD_SPECULATION_ATTEMPT_FUEL);
  assert!(!tc.env.unfold_cache.contains_key(&head.hash_key()));
}

#[test]
fn regular_reservation_preserves_non_regular_startup_window() {
  for used in [0, SAME_HEAD_SPECULATION_START_FUEL] {
    let mut env = setup::<Anon>();
    defn(&mut env, "alias", cnst("A"), cnst("a"));
    let mut abbrev = env.get(&id("id")).unwrap();
    if let KConst::Defn { hints, block, .. } = &mut abbrev {
      *hints = ReducibilityHints::Abbrev;
      *block = id("abbrev");
    }
    env.insert(id("abbrev"), abbrev);
    let head = cnst("abbrev");
    let a = KExpr::app(cnst("id"), KExpr::app(head.clone(), cnst("alias")));
    let b = KExpr::app(cnst("id"), KExpr::app(head.clone(), cnst("a")));
    let mut tc = TypeChecker::new(&mut env);
    tc.rec_fuel -= used;
    assert_eq!(
      tc.try_same_head_spine_speculative(&a, &b, &id("id"), true).unwrap(),
      Some(true)
    );
    // The outer Regular allowance neither closes the early window nor
    // reopens a late one. Only the latter case must delta-unfold the Abbrev.
    assert_eq!(tc.env.unfold_cache.contains_key(&head.hash_key()), used > 0);
    assert_eq!(tc.same_head_fuel_reserve, 0);
  }
}

#[test]
fn alternate_lazy_delta_path_falls_back_after_probe_abort() {
  let mut env = setup::<Anon>();
  let arg = expensive(&mut env);
  let mut a = KExpr::app(cnst("ignore"), arg);
  let mut b = KExpr::app(cnst("ignore"), cnst("b"));
  let mut tc = TypeChecker::new(&mut env);
  assert!(matches!(
    tc.lazy_delta_reduction_step(&mut a, &mut b).unwrap(),
    LazyDeltaStep::Equal
  ));
  assert!(tc.fuel_used() >= SAME_HEAD_REGULAR_ATTEMPT_FUEL);
}

#[test]
fn resource_abort_is_unknown_but_other_errors_propagate() {
  let mut env = setup::<Anon>();
  defn(&mut env, "alias", cnst("A"), cnst("a"));
  defn(&mut env, "bad", cnst("A"), KExpr::sort(KUniv::param(1, ())));
  let a = KExpr::app(cnst("id"), cnst("alias"));
  let b = KExpr::app(cnst("id"), cnst("a"));
  let mut tc = TypeChecker::new(&mut env);
  tc.rec_fuel = 0;
  assert_eq!(
    tc.try_same_head_spine_speculative(&a, &b, &id("id"), true).unwrap(),
    None
  );
  assert!(matches!(tc.is_def_eq(&a, &b), Err(TcError::MaxRecFuel)));
  assert_not_cached(&mut tc, &a, &b);

  tc.rec_fuel = 20_000;
  tc.def_eq_depth = MAX_DEF_EQ_DEPTH;
  assert_eq!(
    tc.try_same_head_spine_speculative(&a, &b, &id("id"), true).unwrap(),
    None
  );
  assert_eq!(tc.def_eq_depth, MAX_DEF_EQ_DEPTH);
  assert_eq!(tc.same_head_fuel_reserve, 0);
  assert!(
    tc.rec_fuel < 20_000
      && tc.rec_fuel > 20_000 - SAME_HEAD_SPECULATION_ATTEMPT_FUEL
  );
  tc.def_eq_depth = 0;
  assert!(tc.is_def_eq(&a, &b).unwrap());

  let bad =
    KExpr::app(cnst("id"), KExpr::cnst(id("bad"), Box::new([KUniv::zero()])));
  tc.rec_fuel = 1_000_000;
  let before = tc.rec_fuel;
  assert!(matches!(
    tc.try_same_head_spine_speculative(&bad, &b, &id("id"), true),
    Err(TcError::UnivParamOutOfRange { .. })
  ));
  assert!(
    tc.rec_fuel < before
      && tc.rec_fuel > before - SAME_HEAD_SPECULATION_ATTEMPT_FUEL
  );
  assert_eq!(tc.def_eq_depth, 0);
  assert_eq!(tc.same_head_fuel_reserve, 0);
  assert_not_cached(&mut tc, &bad, &b);
}

fn seed_backoff<M: KernelMode>(tc: &mut TypeChecker<'_, M>) {
  tc.same_head_backoff.enter();
  tc.same_head_backoff.leave(true, true, speculation::FAILED_FUEL_TOTAL);
}

fn backoff_fallback<M: KernelMode>(head: &str, expected: bool, cheap: bool) {
  let mut env = setup::<M>();
  let a = KExpr::app(cnst(head), cnst("a"));
  let b = KExpr::app(cnst(head), cnst("b"));
  let mut tc = TypeChecker::new(&mut env);
  seed_backoff(&mut tc);
  tc.cheap_recursion_depth = u32::from(cheap);
  let before = tc.rec_fuel;
  crate::perf::same_head::reset();
  assert_eq!(
    tc.try_same_head_spine_speculative(&a, &b, &id(head), true).unwrap(),
    None
  );
  assert_eq!(tc.rec_fuel, before, "a skip does not spend or refund fuel");
  assert_eq!(tc.same_head_fuel_reserve, 0);
  assert_not_cached(&mut tc, &a, &b);
  if crate::perf::same_head::enabled() {
    let report = crate::perf::same_head::summary();
    assert!(report.contains("skipped_backoff=1"), "{report}");
    assert!(report.contains("active=0 max_depth=0"), "{report}");
  }
  tc.cheap_recursion_depth = 0;
  assert_eq!(tc.is_def_eq(&a, &b).unwrap(), expected);
}

#[test]
fn cumulative_backoff_never_publishes_equality_or_inequality() {
  for cheap in [false, true] {
    backoff_fallback::<Anon>("ignore", true, cheap);
    backoff_fallback::<Meta>("ignore", true, cheap);
    backoff_fallback::<Anon>("id", false, cheap);
    backoff_fallback::<Meta>("id", false, cheap);
  }
}

#[test]
fn cumulative_backoff_applies_to_both_lazy_delta_paths() {
  let mut env = setup::<Anon>();
  let mut a = KExpr::app(cnst("ignore"), cnst("a"));
  let mut b = KExpr::app(cnst("ignore"), cnst("b"));
  let mut tc = TypeChecker::new(&mut env);
  seed_backoff(&mut tc);
  assert!(matches!(
    tc.lazy_delta_reduction_step(&mut a, &mut b).unwrap(),
    LazyDeltaStep::Equal
  ));
  assert!(tc.fuel_used() < SAME_HEAD_SPECULATION_ATTEMPT_FUEL);
}

#[test]
fn reset_restores_productive_regular_probes_without_reusing_fvar_ids() {
  let mut env = setup::<Anon>();
  let arg = beta_alias_chain(&mut env, 128, 64);
  let a = KExpr::app(cnst("id"), arg);
  let b = KExpr::app(cnst("id"), cnst("a"));
  let mut tc = TypeChecker::new(&mut env);
  seed_backoff(&mut tc);
  assert!(tc.same_head_backoff.should_skip(true));
  let old_fvar = tc.fresh_fvar_id();
  tc.reset();
  assert_ne!(old_fvar, tc.fresh_fvar_id());
  assert!(!tc.same_head_backoff.should_skip(true));
  assert_eq!(
    tc.try_same_head_spine_speculative(&a, &b, &id("id"), true).unwrap(),
    Some(true)
  );
  assert!(tc.fuel_used() > SAME_HEAD_SPECULATION_ATTEMPT_FUEL);
  assert!(tc.fuel_used() < SAME_HEAD_REGULAR_ATTEMPT_FUEL);
}
