use super::*;
use crate::env::KEnv;
use crate::level::KUniv;
use crate::mode::{Anon, Meta};
use crate::profile::{OpCounts, take_op_counts};
use ix_common::address::Address;
use ix_common::env::{DefinitionSafety, ReducibilityHints};

fn name<M: KernelMode>(s: &str) -> M::MField<Name> {
  M::meta_field(Name::str(Name::anon(), s.to_owned()))
}

fn id<M: KernelMode>(s: &str) -> KId<M> {
  KId::new(Address::hash(s.as_bytes()), name::<M>(s))
}

fn cnst<M: KernelMode>(s: &str) -> KExpr<M> {
  KExpr::cnst(id(s), Box::new([]))
}

fn var<M: KernelMode>(i: u64) -> KExpr<M> {
  KExpr::var(i, name::<M>("original-var"))
}

fn sort<M: KernelMode>() -> KExpr<M> {
  KExpr::sort(KUniv::succ(KUniv::zero()))
}

fn binder<M: KernelMode>(
  is_lam: bool,
  ty: KExpr<M>,
  body: KExpr<M>,
) -> KExpr<M> {
  let n = name::<M>(if is_lam { "lambda" } else { "forall" });
  let bi = M::meta_field(BinderInfo::Implicit);
  if is_lam { KExpr::lam(n, bi, ty, body) } else { KExpr::all(n, bi, ty, body) }
}

fn axiom<M: KernelMode>(env: &mut KEnv<M>, s: &str, ty: KExpr<M>) {
  env.insert(
    id(s),
    KConst::Axio {
      name: name::<M>(s),
      level_params: M::meta_field(vec![]),
      is_unsafe: false,
      lvls: 0,
      ty,
    },
  );
}

fn defn<M: KernelMode>(
  env: &mut KEnv<M>,
  s: &str,
  ty: KExpr<M>,
  val: KExpr<M>,
) {
  env.insert(
    id(s),
    KConst::Defn {
      name: name::<M>(s),
      level_params: M::meta_field(vec![]),
      kind: DefKind::Definition,
      safety: DefinitionSafety::Safe,
      hints: ReducibilityHints::Regular(7),
      lvls: 0,
      ty,
      val,
      lean_all: M::meta_field(vec![]),
      block: id(s),
    },
  );
}

fn setup<M: KernelMode>() -> KEnv<M> {
  let mut env = KEnv::new();
  axiom(&mut env, "A", sort());
  axiom(&mut env, "B", sort());
  axiom(&mut env, "a", cnst("A"));
  axiom(&mut env, "b", cnst("A"));
  axiom(
    &mut env,
    "G",
    binder(false, sort(), binder(false, var(0), binder(false, var(1), var(2)))),
  );
  axiom(&mut env, "P", binder(false, sort(), binder(false, var(0), sort())));
  defn(&mut env, "Alias", sort(), cnst("A"));
  defn(&mut env, "alias", cnst("A"), cnst("a"));
  defn(
    &mut env,
    "id",
    binder(false, cnst("A"), cnst("A")),
    binder(true, cnst("A"), var(0)),
  );
  defn(
    &mut env,
    "ignore",
    binder(false, cnst("A"), cnst("A")),
    binder(true, cnst("A"), cnst("a")),
  );
  env
}

fn telescope<M: KernelMode>(
  n: usize,
  is_lam: bool,
  mut body: KExpr<M>,
) -> KExpr<M> {
  for _ in 0..n {
    body = binder(is_lam, cnst("A"), body);
  }
  body
}

fn compare<M: KernelMode>(
  a: &KExpr<M>,
  b: &KExpr<M>,
  old: bool,
) -> (bool, u64, u32, OpCounts) {
  let mut env = setup::<M>();
  let mut tc = TypeChecker::new(&mut env);
  tc.in_binder_batch = old;
  let a = tc.intern(a.clone());
  let b = tc.intern(b.clone());
  take_op_counts();
  let verdict = tc.is_def_eq(&a, &b).unwrap();
  assert!(tc.lctx.is_empty());
  assert_eq!(tc.def_eq_depth, 0);
  assert_eq!(tc.in_binder_batch, old);
  (verdict, tc.fuel_used(), tc.def_eq_peak, take_op_counts())
}

fn long_positive<M: KernelMode>(
  count: u64,
  compare_reference: bool,
  report: bool,
) {
  for is_lam in [false, true] {
    // (T : Type) (x1 : T) ... (x_{count-1} : T). Unlike closed suffixes,
    // these domains really must be traversed by repeated single opening.
    let make = |alias: bool| {
      // Every value binder is used, so each single opening must revisit
      // the terminal DAG; merely depending on T would only traverse once.
      let g = KExpr::app(cnst("G"), var(count - 1));
      let mut body = var(0);
      for i in 1..count - 1 {
        body = KExpr::app(KExpr::app(g.clone(), var(i)), body);
      }
      if !is_lam {
        body = KExpr::app(KExpr::app(cnst("P"), var(count - 1)), body);
      }
      if alias {
        let ty = if is_lam { var(count - 1) } else { sort() };
        body = KExpr::let_(name::<M>("alias"), ty, body, var(0), false);
      }
      for i in (0..count).rev() {
        let ty = if i == 0 { sort() } else { var(i - 1) };
        body = binder(is_lam, ty, body);
      }
      body
    };
    let a = make(false);
    let b = make(true);
    let mut env = setup::<M>();
    let mut tc = TypeChecker::new(&mut env);
    tc.infer(&a).unwrap();
    tc.infer(&b).unwrap();
    let new = compare::<M>(&a, &b, false);
    assert!(new.0);
    assert!(new.2 < 10, "batch peak {}", new.2);
    if !compare_reference {
      continue;
    }
    let old = compare::<M>(&a, &b, true);
    if report {
      println!(
        "mode={} lambda={is_lam} subst={}->{} intern={}->{} fuel={}->{} peak={}->{}",
        std::any::type_name::<M>(),
        old.3.subst_nodes,
        new.3.subst_nodes,
        old.3.intern_nodes,
        new.3.intern_nodes,
        old.1,
        new.1,
        old.2,
        new.2,
      );
    }
    assert!(old.0);
    assert!(u64::from(old.2) >= count);
    assert!(
      new.3.subst_nodes * 4 < old.3.subst_nodes,
      "subst {} vs {}",
      new.3.subst_nodes,
      old.3.subst_nodes
    );
  }
}

#[test]
fn long_telescope_opens_terminal_bodies_once() {
  // The deliberately recursive reference needs one native frame per
  // binder. Keep this differential/work-counter fixture within the normal
  // test stack; exercise the full deep case on the production path below.
  long_positive::<Anon>(32, true, false);
  long_positive::<Meta>(32, true, false);
}

#[test]
fn deep_batched_telescope_uses_default_stack() {
  // Do not spawn a large-stack worker or require RUST_MIN_STACK here.
  long_positive::<Anon>(128, false, false);
  long_positive::<Meta>(128, false, false);
}

#[test]
#[ignore = "manual paired work-counter report; not a wall-time benchmark"]
fn report_dependent_telescope_work() {
  long_positive::<Anon>(32, true, true);
  long_positive::<Meta>(32, true, true);
}

fn dependent<M: KernelMode>() {
  let mut env = setup::<M>();
  // idPoly : (T : Type) -> T -> T
  let id_ty = binder(false, sort(), binder(false, var(0), var(1)));
  let id_val = binder(true, sort(), binder(true, var(0), var(0)));
  defn(&mut env, "idPoly", id_ty, id_val);
  for is_lam in [false, true] {
    let make = |alias: bool| {
      // (T : Type) (x : T) (y : T) (z : T), x / T.
      let terminal = if is_lam { var(2) } else { var(3) };
      let terminal = if alias && is_lam {
        KExpr::app(KExpr::app(cnst("idPoly"), var(3)), terminal)
      } else {
        terminal
      };
      let domain_z = if alias {
        // A local type alias reduces to T; both domains are well typed.
        KExpr::let_(name::<M>("D"), sort(), var(2), var(0), false)
      } else {
        var(2)
      };
      binder(
        is_lam,
        sort(),
        binder(
          is_lam,
          var(0),
          binder(is_lam, var(1), binder(is_lam, domain_z, terminal)),
        ),
      )
    };
    let mut tc = TypeChecker::new(&mut env);
    let a = tc.intern(make(false));
    let b = tc.intern(make(true));
    tc.infer(&a).unwrap();
    tc.infer(&b).unwrap();
    assert!(tc.is_def_eq(&a, &b).unwrap());
    assert!(tc.lctx.is_empty());
    assert!(!tc.in_binder_batch);
  }
}

#[test]
fn dependent_domains_and_shared_fresh_locals_are_preserved() {
  dependent::<Anon>();
  dependent::<Meta>();
}

fn negative_cases<M: KernelMode>() {
  for n in [4, 8, 17] {
    // Same domains but unequal terminal values/types.
    for is_lam in [false, true] {
      let (a, b) =
        if is_lam { (cnst("a"), cnst("b")) } else { (cnst("A"), cnst("B")) };
      let a = telescope(n, is_lam, a);
      let b = telescope(n, is_lam, b);
      assert!(!compare::<M>(&a, &b, true).0);
      assert!(!compare::<M>(&a, &b, false).0);
    }
    let a = telescope(n, false, binder(false, cnst("A"), cnst("A")));
    let b = telescope(n, false, binder(false, cnst("B"), cnst("A")));
    assert!(!compare::<M>(&a, &b, true).0);
    assert!(!compare::<M>(&a, &b, false).0);
  }
}

#[test]
fn failed_domains_and_terminal_comparisons_match_original() {
  negative_cases::<Anon>();
  negative_cases::<Meta>();
}

fn diverging<M: KernelMode>() {
  let a = telescope(4, true, binder(true, cnst("A"), var(0)));
  let b = telescope(4, true, cnst("id"));
  assert!(compare::<M>(&a, &b, true).0);
  assert!(compare::<M>(&a, &b, false).0);
  let a = telescope(4, false, cnst("A"));
  let b = telescope(3, false, cnst("A"));
  assert!(!compare::<M>(&a, &b, true).0);
  assert!(!compare::<M>(&a, &b, false).0);
}

#[test]
fn divergent_suffix_uses_normal_conversion_including_eta() {
  diverging::<Anon>();
  diverging::<Meta>();
}

fn contexts<M: KernelMode>() {
  let mut env = setup::<M>();
  let mut tc = TypeChecker::new(&mut env);
  // The same loose outer Var means different values in different legacy
  // let contexts. Opening four binders must shift it down by exactly four.
  let a = tc.intern(telescope(4, true, var(4)));
  let b = tc.intern(telescope(4, true, cnst("a")));
  tc.push_let(cnst("A"), cnst("a"));
  let first = tc.def_eq_ctx_key(&a, &b);
  assert!(tc.is_def_eq(&a, &b).unwrap());
  assert_eq!(tc.depth(), 1);
  assert!(tc.lctx.is_empty());
  tc.pop_local();
  tc.push_let(cnst("A"), cnst("b"));
  let second = tc.def_eq_ctx_key(&a, &b);
  assert_ne!(first, second);
  assert!(!tc.is_def_eq(&a, &b).unwrap());
  assert!(tc.lctx.is_empty());
  assert_eq!(tc.depth(), 1);
}

#[test]
fn batched_results_are_scoped_to_the_original_outer_context() {
  contexts::<Anon>();
  contexts::<Meta>();
}

#[test]
fn resource_failure_restores_scope_flag_and_does_not_cache_false() {
  let mut env = setup::<Anon>();
  let mut tc = TypeChecker::new(&mut env);
  let a = tc.intern(telescope(16, true, cnst("a")));
  let b = tc.intern(telescope(16, true, cnst("alias")));
  let (lo, hi) = canonical_pair(a.hash_key(), b.hash_key());
  let key = (lo, hi, tc.def_eq_ctx_key(&a, &b));
  let before = tc.fresh_fvar_id();
  tc.rec_fuel = 2;
  assert!(matches!(tc.is_def_eq(&a, &b), Err(TcError::MaxRecFuel)));
  assert_eq!(tc.rec_fuel, 0);
  assert!(tc.lctx.is_empty());
  assert!(!tc.in_binder_batch);
  assert_eq!(tc.def_eq_depth, 0);
  assert!(!tc.env.def_eq_cache.contains_key(&key));
  let after = tc.fresh_fvar_id();
  assert_ne!(before, after);
  tc.rec_fuel = 100_000;
  assert!(tc.is_def_eq(&a, &b).unwrap());
}

#[test]
fn non_resource_errors_propagate_and_restore_scope() {
  let mut env = setup::<Anon>();
  defn(&mut env, "bad", cnst("A"), KExpr::sort(KUniv::param(1, ())));
  let mut tc = TypeChecker::new(&mut env);
  let a = tc.intern(telescope(
    4,
    true,
    KExpr::cnst(id("bad"), Box::new([KUniv::zero()])),
  ));
  let b = tc.intern(telescope(4, true, cnst("a")));
  assert!(matches!(
    tc.is_def_eq(&a, &b),
    Err(TcError::UnivParamOutOfRange { .. })
  ));
  assert!(tc.lctx.is_empty());
  assert!(!tc.in_binder_batch);
  assert_eq!(tc.def_eq_depth, 0);
}

#[test]
fn short_binders_keep_original_work_and_reset_clears_flag() {
  for n in 1..BINDER_BATCH_MIN_LENGTH {
    let a = telescope(n, true, cnst::<Anon>("a"));
    let b = telescope(n, true, cnst::<Anon>("alias"));
    let old = compare(&a, &b, true);
    let new = compare(&a, &b, false);
    assert_eq!((old.0, old.1, old.2), (new.0, new.1, new.2));
    assert_eq!(old.3.subst_nodes, new.3.subst_nodes);
    assert_eq!(old.3.intern_nodes, new.3.intern_nodes);
  }
  let mut env = setup::<Anon>();
  let mut tc = TypeChecker::new(&mut env);
  tc.in_binder_batch = true;
  tc.reset();
  assert!(!tc.in_binder_batch);
}

#[test]
fn generated_telescope_pairs_match_the_original_checker() {
  fn check<M: KernelMode>() {
    for n in 0..64 {
      let body = |k| {
        let a = cnst(["a", "b", "alias"][k % 3]);
        if k % 2 == 0 { a } else { KExpr::app(cnst("ignore"), a) }
      };
      let a = telescope(4 + n % 5, true, body(n * 7));
      let b = telescope(4 + n % 5, true, body(n * 11));
      assert_eq!(
        compare::<M>(&a, &b, true).0,
        compare::<M>(&a, &b, false).0,
        "seed {n}"
      );
    }
  }
  check::<Anon>();
  check::<Meta>();
}

#[test]
fn closed_suffix_cache_is_honored_without_reopening_it() {
  let mut env = setup::<Anon>();
  let mut tc = TypeChecker::new(&mut env);
  let left_suffix = tc.intern(telescope(12, true, cnst("a")));
  let right_suffix = tc.intern(telescope(12, true, cnst("alias")));
  assert!(tc.is_def_eq(&left_suffix, &right_suffix).unwrap());
  assert!(tc.has_closed_binder_result(&left_suffix, &right_suffix));
  let a = tc.intern(telescope(4, true, left_suffix));
  let b = tc.intern(telescope(4, true, right_suffix));
  let fuel = tc.rec_fuel;
  assert!(tc.is_def_eq(&a, &b).unwrap());
  assert!(fuel - tc.rec_fuel <= 4);
  assert!(tc.lctx.is_empty());
}

#[test]
fn cheap_negative_cache_does_not_poison_full_binder_comparison() {
  fn check<M: KernelMode>() {
    let mut env = setup::<M>();
    let mut tc = TypeChecker::new(&mut env);
    let a = tc.intern(telescope(4, true, cnst("a")));
    let b = tc.intern(telescope(4, true, cnst("alias")));
    let (lo, hi) = canonical_pair(a.hash_key(), b.hash_key());
    let key = (lo, hi, tc.def_eq_ctx_key(&a, &b));
    tc.env.def_eq_cheap_cache.insert(key, false);
    assert!(tc.is_def_eq(&a, &b).unwrap());
    assert_eq!(tc.env.def_eq_cache.get(&key), Some(&true));
    tc.env.clear_reduction_caches();
    tc.equiv_manager.clear();
    tc.cheap_recursion_depth = 1;
    tc.infer_only = true;
    tc.eager_reduce = true;
    assert!(tc.is_def_eq(&a, &b).unwrap());
    assert_eq!(tc.env.def_eq_cheap_cache.get(&key), Some(&true));
    assert_eq!(tc.env.def_eq_cache.get(&key), Some(&true));
    assert_eq!(tc.cheap_recursion_depth, 1);
    assert!(tc.infer_only && tc.eager_reduce);
    assert!(!tc.in_binder_batch);
    assert!(tc.lctx.is_empty());
  }
  check::<Anon>();
  check::<Meta>();
}

#[test]
fn local_budget_miss_falls_back_without_refunding_work() {
  let mut env = setup::<Anon>();
  let mut next = cnst("a");
  // Finite beta+delta chain: productive betas exceed the batch slice.
  // Bare aliases alone use the separate local delta-loop guard and do not
  // necessarily consume recursive fuel once their structural forms hit.
  for i in 0..3000 {
    let s = format!("step{i}");
    defn(&mut env, &s, cnst("A"), KExpr::app(cnst("id"), next));
    next = cnst(&s);
  }
  let mut tc = TypeChecker::new(&mut env);
  let a = tc.intern(telescope(4, true, next));
  let b = tc.intern(telescope(4, true, cnst("a")));
  let before = tc.fresh_fvar_id().0;
  let fuel = tc.rec_fuel;
  assert!(tc.is_def_eq(&a, &b).unwrap());
  let after = tc.fresh_fvar_id().0;
  assert!(
    after - before >= 9,
    "expected batch+fallback: new fvars={}, fuel consumed={}",
    after - before,
    fuel - tc.rec_fuel,
  );
  assert!(fuel - tc.rec_fuel > BINDER_BATCH_FUEL);
  assert!(!tc.in_binder_batch);
  assert!(tc.lctx.is_empty());
}

#[test]
fn proof_irrelevance_inside_a_telescope_remains_available() {
  fn check<M: KernelMode>(old: bool) {
    let mut env = setup::<M>();
    axiom(&mut env, "PropP", KExpr::sort(KUniv::zero()));
    axiom(&mut env, "proof1", cnst("PropP"));
    axiom(&mut env, "proof2", cnst("PropP"));
    let mut tc = TypeChecker::new(&mut env);
    tc.in_binder_batch = old;
    let a = tc.intern(telescope(8, true, cnst("proof1")));
    let b = tc.intern(telescope(8, true, cnst("proof2")));
    tc.infer(&a).unwrap();
    tc.infer(&b).unwrap();
    assert!(tc.is_def_eq(&a, &b).unwrap());
    assert!(tc.lctx.is_empty());
    assert_eq!(tc.in_binder_batch, old);
  }
  for old in [false, true] {
    check::<Anon>(old);
    check::<Meta>(old);
  }
}
