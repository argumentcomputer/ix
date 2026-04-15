//! Shared test helpers for zero kernel tests.
//!
//! Provides convenience constructors for `KExpr<Meta>`, `KUniv<Meta>`, `KId<Meta>`,
//! and `KConst<Meta>` to reduce boilerplate in hand-built test environments.

use std::sync::Arc;

use crate::ix::address::Address;
use crate::ix::env::{BinderInfo, DefinitionSafety, Name, ReducibilityHints};
use crate::ix::ixon::constant::DefKind;

use super::constant::KConst;
use super::env::KEnv;
use super::expr::KExpr;
use super::id::KId;
use super::level::KUniv;
use super::mode::Meta;
use super::tc::TypeChecker;

// ---- Type aliases ----

pub type ME = KExpr<Meta>;
pub type MU = KUniv<Meta>;
pub type MId = KId<Meta>;

// ---- Name / Address / Id ----

pub fn mk_name(s: &str) -> Name {
  let mut name = Name::anon();
  for part in s.split('.') {
    name = Name::str(name, part.to_string());
  }
  name
}

pub fn mk_addr(s: &str) -> Address {
  Address::hash(s.as_bytes())
}

pub fn mk_id(s: &str) -> MId {
  KId::new(mk_addr(s), mk_name(s))
}

// ---- Expressions ----

pub fn var(i: u64) -> ME {
  ME::var(i, mk_name("_"))
}

pub fn nvar(name: &str, i: u64) -> ME {
  ME::var(i, mk_name(name))
}

pub fn sort0() -> ME {
  ME::sort(MU::zero())
}

pub fn sort1() -> ME {
  ME::sort(MU::succ(MU::zero()))
}

pub fn sort(u: MU) -> ME {
  ME::sort(u)
}

pub fn pi(dom: ME, cod: ME) -> ME {
  ME::all(mk_name("_"), BinderInfo::Default, dom, cod)
}

pub fn npi(name: &str, dom: ME, cod: ME) -> ME {
  ME::all(mk_name(name), BinderInfo::Default, dom, cod)
}

pub fn ipi(name: &str, dom: ME, cod: ME) -> ME {
  ME::all(mk_name(name), BinderInfo::Implicit, dom, cod)
}

pub fn lam(dom: ME, body: ME) -> ME {
  ME::lam(mk_name("_"), BinderInfo::Default, dom, body)
}

pub fn nlam(name: &str, dom: ME, body: ME) -> ME {
  ME::lam(mk_name(name), BinderInfo::Default, dom, body)
}

pub fn app(f: ME, a: ME) -> ME {
  ME::app(f, a)
}

pub fn apps(f: ME, args: &[ME]) -> ME {
  let mut e = f;
  for a in args {
    e = ME::app(e, a.clone());
  }
  e
}

pub fn cnst(name: &str, us: &[MU]) -> ME {
  ME::cnst(mk_id(name), us.into())
}

pub fn let_(ty: ME, val: ME, body: ME) -> ME {
  ME::let_(mk_name("_"), ty, val, body, false)
}

// ---- Universes ----

pub fn uzero() -> MU {
  MU::zero()
}

pub fn usucc(u: MU) -> MU {
  MU::succ(u)
}

pub fn umax(a: MU, b: MU) -> MU {
  MU::max(a, b)
}

pub fn uimax(a: MU, b: MU) -> MU {
  MU::imax(a, b)
}

pub fn param(n: u64) -> MU {
  MU::param(n, mk_name("u"))
}

pub fn nparam(name: &str, n: u64) -> MU {
  MU::param(n, mk_name(name))
}

// ---- Constant builders ----

pub fn mk_defn(
  name: &str,
  lvls: u64,
  level_params: Vec<Name>,
  ty: ME,
  val: ME,
  hints: ReducibilityHints,
) -> (MId, KConst<Meta>) {
  let id = mk_id(name);
  let c = KConst::Defn {
    name: mk_name(name),
    level_params,
    kind: DefKind::Definition,
    safety: DefinitionSafety::Safe,
    hints,
    lvls,
    ty,
    val,
    lean_all: vec![id.clone()],
    block: id.clone(),
  };
  (id, c)
}

pub fn mk_thm(
  name: &str,
  lvls: u64,
  level_params: Vec<Name>,
  ty: ME,
  val: ME,
) -> (MId, KConst<Meta>) {
  let id = mk_id(name);
  let c = KConst::Defn {
    name: mk_name(name),
    level_params,
    kind: DefKind::Theorem,
    safety: DefinitionSafety::Safe,
    hints: ReducibilityHints::Opaque,
    lvls,
    ty,
    val,
    lean_all: vec![id.clone()],
    block: id.clone(),
  };
  (id, c)
}

pub fn mk_axiom(
  name: &str,
  lvls: u64,
  level_params: Vec<Name>,
  ty: ME,
) -> (MId, KConst<Meta>) {
  let id = mk_id(name);
  let c = KConst::Axio {
    name: mk_name(name),
    level_params,
    is_unsafe: false,
    lvls,
    ty,
  };
  (id, c)
}

// ---- Common environment builders ----

/// Add Eq.{u} and Eq.refl.{u} as axioms to the environment.
/// Eq : {α : Sort u} → α → α → Prop
/// Eq.refl : {α : Sort u} → (a : α) → Eq a a
pub fn add_eq_axioms(env: &KEnv<Meta>) {
  let eq_ty =
    ipi("α", sort(param(0)), npi("a", var(0), npi("b", var(1), sort0())));
  let (eq_id, eq_c) = mk_axiom("Eq", 1, vec![mk_name("u")], eq_ty);
  env.insert(eq_id, eq_c);

  let eq_refl_ty = ipi(
    "α",
    sort(param(0)),
    npi("a", var(0), apps(cnst("Eq", &[param(0)]), &[var(1), var(0), var(0)])),
  );
  let (refl_id, refl_c) =
    mk_axiom("Eq.refl", 1, vec![mk_name("u")], eq_refl_ty);
  env.insert(refl_id, refl_c);
}

/// Convenience: Eq.{u} α a b
pub fn eq_expr(u: MU, alpha: ME, a: ME, b: ME) -> ME {
  apps(cnst("Eq", &[u]), &[alpha, a, b])
}

/// Convenience: Eq.refl.{u} α a
pub fn eq_refl_expr(u: MU, alpha: ME, a: ME) -> ME {
  apps(cnst("Eq.refl", &[u]), &[alpha, a])
}

// ---- Test runner helpers ----

pub fn check_accepts(env: &Arc<KEnv<Meta>>, id: &MId) {
  let mut tc = TypeChecker::new(Arc::clone(env));
  match tc.check_const(id) {
    Ok(()) => {},
    Err(e) => panic!("expected {id} to be accepted, got error: {e:?}"),
  }
}

pub fn check_rejects(env: &Arc<KEnv<Meta>>, id: &MId) {
  let mut tc = TypeChecker::new(Arc::clone(env));
  match tc.check_const(id) {
    Err(_) => {},
    Ok(()) => panic!("expected {id} to be rejected, but it was accepted"),
  }
}

/// Check with custom primitives (needed for Nat literal tests etc.)
pub fn check_accepts_with_prims(
  env: &Arc<KEnv<Meta>>,
  id: &MId,
  prims: super::primitive::Primitives<Meta>,
) {
  let mut tc = TypeChecker::new(Arc::clone(env));
  tc.prims = prims;
  match tc.check_const(id) {
    Ok(()) => {},
    Err(e) => panic!("expected {id} to be accepted, got error: {e:?}"),
  }
}

/// Build Primitives resolved from a test environment.
/// The env should contain all the primitives the test needs.
pub fn test_prims(env: &KEnv<Meta>) -> super::primitive::Primitives<Meta> {
  super::primitive::Primitives::from_env(env)
}
