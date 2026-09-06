//! Projection-first probes may establish equality, never assume it on a miss.

use super::*;
use crate::env::KEnv;
use crate::mode::{Anon, Meta};
use ix_common::address::Address;
use ix_common::env::{BinderInfo, DefinitionSafety, Name, ReducibilityHints};

fn id<M: KernelMode>(s: &str) -> KId<M> {
  KId::new(
    Address::hash(s.as_bytes()),
    M::meta_field(Name::str(Name::anon(), s.to_owned())),
  )
}

fn cnst<M: KernelMode>(s: &str) -> KExpr<M> {
  KExpr::cnst(id(s), Box::new([]))
}

fn axiom<M: KernelMode>(env: &mut KEnv<M>, s: &str, ty: KExpr<M>) {
  env.insert(
    id(s),
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
  s: &str,
  ty: KExpr<M>,
  val: KExpr<M>,
) {
  env.insert(
    id(s),
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
      block: id(s),
    },
  );
}

/// A : Type; a b : A; Box : Type; Box.mk : A → Box.
/// `pack x` either stores x or ignores x and stores a. `neutral` is an axiom.
fn setup<M: KernelMode>(keep_arg: bool) -> KEnv<M> {
  let mut env = KEnv::new();
  let type0 = KExpr::sort(KUniv::succ(KUniv::zero()));
  axiom(&mut env, "A", type0.clone());
  axiom(&mut env, "a", cnst("A"));
  axiom(&mut env, "b", cnst("A"));
  env.insert(
    id("Box"),
    KConst::Indc {
      name: M::meta_field(Name::anon()),
      level_params: M::meta_field(vec![]),
      lvls: 0,
      params: 0,
      indices: 0,
      is_unsafe: false,
      block: id("Box"),
      member_idx: 0,
      ty: type0,
      ctors: vec![id("Box.mk")],
      lean_all: M::meta_field(vec![]),
    },
  );
  let fun_ty = KExpr::all(
    M::meta_field(Name::anon()),
    M::meta_field(BinderInfo::Default),
    cnst("A"),
    cnst("Box"),
  );
  env.insert(
    id("Box.mk"),
    KConst::Ctor {
      name: M::meta_field(Name::anon()),
      level_params: M::meta_field(vec![]),
      is_unsafe: false,
      lvls: 0,
      induct: id("Box"),
      cidx: 0,
      params: 0,
      fields: 1,
      ty: fun_ty.clone(),
    },
  );
  let field = if keep_arg {
    KExpr::var(0, M::meta_field(Name::anon()))
  } else {
    cnst("a")
  };
  let body = KExpr::lam(
    M::meta_field(Name::anon()),
    M::meta_field(BinderInfo::Default),
    cnst("A"),
    KExpr::app(cnst("Box.mk"), field),
  );
  defn(&mut env, "pack", fun_ty.clone(), body);
  axiom(&mut env, "neutral", fun_ty);
  env
}

fn proj<M: KernelMode>(head: &str, arg: KExpr<M>) -> KExpr<M> {
  KExpr::prj(id("Box"), 0, KExpr::app(cnst(head), arg))
}

fn ignored_expensive_argument<M: KernelMode>() {
  let make = || {
    let mut env = setup::<M>(false);
    let mut expensive = cnst("a");
    for i in 0..256 {
      let s = format!("expensive.{i}");
      let step = KExpr::app(
        KExpr::lam(
          M::meta_field(Name::anon()),
          M::meta_field(BinderInfo::Default),
          cnst("A"),
          KExpr::var(0, M::meta_field(Name::anon())),
        ),
        expensive,
      );
      defn(&mut env, &s, cnst("A"), step);
      expensive = cnst(&s);
    }
    (env, expensive)
  };
  let (mut env, expensive) = make();
  let mut tc = TypeChecker::new(&mut env);
  tc.rec_fuel = 128;
  assert!(
    tc.is_def_eq(&proj("pack", expensive.clone()), &proj("pack", cnst("b")))
      .unwrap()
  );
  assert!(tc.rec_fuel > 0);
  assert!(!tc.in_projection_probe);
  assert_eq!(tc.def_eq_depth, 0);
  assert_eq!(tc.depth(), 0);

  // The original whole-record-first path exhausts the SAME total budget.
  let (mut old_env, expensive) = make();
  let mut old = TypeChecker::new(&mut old_env);
  old.rec_fuel = 128;
  assert!(matches!(
    old.lazy_delta_proj_reduction(
      &id("Box"),
      0,
      &mut KExpr::app(cnst("pack"), expensive),
      &mut KExpr::app(cnst("pack"), cnst("b")),
    ),
    Err(TcError::MaxRecFuel)
  ));
}

#[test]
fn projection_probe_avoids_ignored_argument_work() {
  ignored_expensive_argument::<Anon>();
  ignored_expensive_argument::<Meta>();
}

fn unequal_fields<M: KernelMode>() {
  let mut env = setup::<M>(true);
  let mut tc = TypeChecker::new(&mut env);
  let (a, b) = (proj("pack", cnst("a")), proj("pack", cnst("b")));
  assert!(!tc.try_projected_def_eq(&a, &b).unwrap());
  assert!(!tc.is_def_eq(&a, &b).unwrap());
  assert!(!tc.is_def_eq(&b, &a).unwrap());
  assert!(!tc.in_projection_probe);
}

#[test]
fn projection_probe_rejects_unequal_fields() {
  unequal_fields::<Anon>();
  unequal_fields::<Meta>();
}

fn neutral_fallback<M: KernelMode>() {
  let mut env = setup::<M>(true);
  let beta = KExpr::app(
    KExpr::lam(
      M::meta_field(Name::anon()),
      M::meta_field(BinderInfo::Default),
      cnst("A"),
      KExpr::var(0, M::meta_field(Name::anon())),
    ),
    cnst("a"),
  );
  let (a, b) = (proj("neutral", beta), proj("neutral", cnst("a")));
  let mut tc = TypeChecker::new(&mut env);
  assert!(!tc.try_projected_def_eq(&a, &b).unwrap());
  assert!(tc.is_def_eq(&a, &b).unwrap());
}

#[test]
fn projection_probe_miss_retains_record_congruence() {
  neutral_fallback::<Anon>();
  neutral_fallback::<Meta>();
}

fn guard_restoration<M: KernelMode>() {
  let mut env = setup::<M>(true);
  let mut tc = TypeChecker::new(&mut env);
  let (a, b) = (proj("pack", cnst("a")), proj("pack", cnst("b")));
  tc.rec_fuel = 1;
  assert!(!tc.try_projected_def_eq(&a, &b).unwrap());
  assert_eq!(tc.rec_fuel, 0, "probe work must not be refunded");
  assert!(!tc.in_projection_probe);
  assert!(tc.env.def_eq_cache.is_empty());
  assert!(tc.env.def_eq_cheap_cache.is_empty());

  tc.rec_fuel = 10_000;
  tc.def_eq_depth = MAX_DEF_EQ_DEPTH;
  assert!(!tc.try_projected_def_eq(&a, &b).unwrap());
  assert_eq!(tc.def_eq_depth, MAX_DEF_EQ_DEPTH);
  assert!(tc.rec_fuel < 10_000);
  assert!(!tc.in_projection_probe);
  assert!(tc.env.def_eq_cache.is_empty());
  tc.def_eq_depth = 0;
  assert!(!tc.is_def_eq(&a, &b).unwrap());
}

#[test]
fn projection_probe_guards_do_not_cache_verdicts_or_refund_work() {
  guard_restoration::<Anon>();
  guard_restoration::<Meta>();
}

fn malformed_field<M: KernelMode>() {
  let mut env = setup::<M>(true);
  // Deliberately malformed declaration: its body references universe 1,
  // while the supplied substitution contains only universe 0.
  defn(
    &mut env,
    "bad",
    cnst("Box"),
    KExpr::sort(KUniv::param(1, M::meta_field(Name::anon()))),
  );
  let mut tc = TypeChecker::new(&mut env);
  let result = tc.try_projected_def_eq(
    &KExpr::prj(
      id("Box"),
      0,
      KExpr::cnst(id("bad"), Box::new([KUniv::zero()])),
    ),
    &proj("pack", cnst("b")),
  );
  assert!(
    matches!(result, Err(TcError::UnivParamOutOfRange { .. })),
    "{result:?}"
  );
  assert!(!tc.in_projection_probe);
  assert!(tc.rec_fuel < crate::tc::max_rec_fuel());
}

#[test]
fn projection_probe_propagates_non_budget_errors() {
  malformed_field::<Anon>();
  malformed_field::<Meta>();
}

#[test]
fn projection_probe_does_not_nest_or_reset_enclosing_state() {
  let mut env = setup::<Anon>(false);
  let mut tc = TypeChecker::new(&mut env);
  tc.in_projection_probe = true;
  let fuel = tc.rec_fuel;
  assert!(
    !tc
      .try_projected_def_eq(&proj("pack", cnst("a")), &proj("pack", cnst("b")))
      .unwrap()
  );
  assert_eq!(tc.rec_fuel, fuel);
  assert!(tc.in_projection_probe);
  tc.reset();
  assert!(!tc.in_projection_probe);
}

fn exhausted_proposition_probe<M: KernelMode>() {
  let mut env = setup::<M>(true);
  let type0 = KExpr::sort(KUniv::succ(KUniv::zero()));
  defn(
    &mut env,
    "propSort",
    type0.clone(),
    KExpr::app(
      KExpr::lam(
        M::meta_field(Name::anon()),
        M::meta_field(BinderInfo::Default),
        type0,
        KExpr::var(0, M::meta_field(Name::anon())),
      ),
      KExpr::sort(KUniv::zero()),
    ),
  );
  axiom(&mut env, "P", cnst("propSort"));
  let mut tc = TypeChecker::new(&mut env);
  tc.rec_fuel = 0;
  assert!(!tc.is_prop_type(&cnst("P")));
  assert!(tc.env.is_prop_cache.is_empty());
  tc.rec_fuel = 10_000;
  assert!(tc.is_prop_type(&cnst("P")));
}

#[test]
fn projection_probe_fuel_misses_do_not_poison_proposition_cache() {
  exhausted_proposition_probe::<Anon>();
  exhausted_proposition_probe::<Meta>();
}
