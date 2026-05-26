//! Congruence checks between Lean-side `ix::env` types and zero kernel types.
//!
//! Validates that Ixon ingress in Anon mode produces structurally correct
//! constants by comparing the Lean `ConstantInfo` against the loaded `KConst<Anon>`.

use crate::ix::address::Address;
use crate::ix::env::{self as lean, ConstantInfo as LeanCI, Literal, Name};

use super::constant::KConst;
use super::expr::{ExprData, KExpr};
use super::level::{KUniv, UnivData};
use super::mode::Anon;

/// Name-to-address resolver, built from the Ixon named map.
pub struct NameResolver {
  map: rustc_hash::FxHashMap<Name, Address>,
}

impl NameResolver {
  pub fn from_ixon_env(ixon_env: &crate::ix::ixon::env::Env) -> Self {
    let mut map = rustc_hash::FxHashMap::default();
    for entry in ixon_env.named.iter() {
      map.insert(entry.key().clone(), entry.value().addr.clone());
    }
    NameResolver { map }
  }

  pub fn resolve(&self, name: &Name) -> Option<&Address> {
    self.map.get(name)
  }
}

/// Check that a Lean-side Level matches a zero Univ structurally.
pub fn level_congruent(
  lean_lvl: &lean::Level,
  zero_univ: &KUniv<Anon>,
  _nr: &NameResolver,
) -> Result<(), String> {
  use lean::LevelData as LD;
  match (lean_lvl.as_data(), zero_univ.data()) {
    (LD::Zero(_), UnivData::Zero(_)) => Ok(()),
    (LD::Succ(a, _), UnivData::Succ(b, _)) => level_congruent(a, b, _nr),
    (LD::Max(a1, a2, _), UnivData::Max(b1, b2, _))
    | (LD::Imax(a1, a2, _), UnivData::IMax(b1, b2, _)) => {
      level_congruent(a1, b1, _nr)?;
      level_congruent(a2, b2, _nr)
    },
    (LD::Param(_, _), UnivData::Param(_, _, _)) => {
      // Lean uses named params, zero uses positional indices.
      // Can't check correspondence without level_params list.
      Ok(())
    },
    _ => Err(format!(
      "level mismatch: lean={} vs zero={}",
      lean_lvl_tag(lean_lvl),
      zero_univ_tag(zero_univ),
    )),
  }
}

/// Check that a Lean-side Expr matches a zero Expr<Anon> structurally.
pub fn expr_congruent(
  lean_expr: &lean::Expr,
  zero_expr: &KExpr<Anon>,
  nr: &NameResolver,
) -> Result<(), String> {
  use lean::ExprData as LE;
  match (lean_expr.as_data(), zero_expr.data()) {
    (LE::Bvar(n, _), ExprData::Var(m, _, _)) => {
      let n = n.to_u64().unwrap_or(u64::MAX);
      if n == *m {
        Ok(())
      } else {
        Err(format!("var mismatch: lean={n} vs zero={m}"))
      }
    },

    (LE::Sort(l, _), ExprData::Sort(u, _)) => level_congruent(l, u, nr),

    (LE::Const(name, levels, _), ExprData::Const(id, univs, _)) => {
      match nr.resolve(name) {
        Some(expected) if expected == &id.addr => {},
        Some(expected) => {
          return Err(format!(
            "const address mismatch for {name}: expected {}, got {}",
            expected.hex(),
            id.addr.hex()
          ));
        },
        None => {
          return Err(format!("const name not found in resolver: {name}"));
        },
      }
      if levels.len() != univs.len() {
        return Err(format!(
          "const {name}: level count mismatch: {} vs {}",
          levels.len(),
          univs.len()
        ));
      }
      for (l, u) in levels.iter().zip(univs.iter()) {
        level_congruent(l, u, nr)?;
      }
      Ok(())
    },

    (LE::App(f1, a1, _), ExprData::App(f2, a2, _)) => {
      expr_congruent(f1, f2, nr)?;
      expr_congruent(a1, a2, nr)
    },

    (LE::Lam(_, ty1, body1, _, _), ExprData::Lam(_, _, ty2, body2, _))
    | (LE::ForallE(_, ty1, body1, _, _), ExprData::All(_, _, ty2, body2, _)) =>
    {
      expr_congruent(ty1, ty2, nr)?;
      expr_congruent(body1, body2, nr)
    },

    (
      LE::LetE(_, ty1, val1, body1, _, _),
      ExprData::Let(_, ty2, val2, body2, _, _),
    ) => {
      expr_congruent(ty1, ty2, nr)?;
      expr_congruent(val1, val2, nr)?;
      expr_congruent(body1, body2, nr)
    },

    (LE::Lit(Literal::NatVal(_), _), ExprData::Nat(_, _, _))
    | (LE::Lit(Literal::StrVal(_), _), ExprData::Str(_, _, _)) => Ok(()),

    (LE::Proj(name, idx, struct_expr, _), ExprData::Prj(id, field, val, _)) => {
      match nr.resolve(name) {
        Some(expected) if expected == &id.addr => {},
        Some(expected) => {
          return Err(format!(
            "proj type mismatch for {name}: expected {}, got {}",
            expected.hex(),
            id.addr.hex()
          ));
        },
        None => return Err(format!("proj type name not found: {name}")),
      }
      if idx.to_u64().unwrap_or(u64::MAX) != *field {
        return Err(format!(
          "proj field mismatch: lean={} vs zero={field}",
          idx.to_u64().unwrap_or(u64::MAX)
        ));
      }
      expr_congruent(struct_expr, val, nr)
    },

    // Lean Mdata wraps an inner expr — zero strips it in Anon mode.
    (LE::Mdata(_, inner, _), _) => expr_congruent(inner, zero_expr, nr),

    (LE::Fvar(..) | LE::Mvar(..), _) => {
      Err("unexpected Fvar/Mvar in constant".to_string())
    },

    _ => Err(format!(
      "expr shape mismatch: lean={} vs zero={}",
      lean_expr_tag(lean_expr),
      zero_expr_tag(zero_expr),
    )),
  }
}

/// Check that a Lean `ConstantInfo` matches a `KConst<Anon>` structurally.
pub fn const_congruent(
  lean_ci: &LeanCI,
  zero_const: &KConst<Anon>,
  nr: &NameResolver,
) -> Result<(), String> {
  // Check type congruence
  let lean_type = lean_ci.get_type();
  let zero_type = zero_const.ty();
  expr_congruent(lean_type, zero_type, nr).map_err(|e| format!("type: {e}"))?;

  // Check lvls count
  let lean_lvls = lean_ci.get_level_params().len() as u64;
  let zero_lvls = zero_const.lvls();
  if lean_lvls != zero_lvls {
    return Err(format!("lvls: lean={lean_lvls} vs zero={zero_lvls}"));
  }

  // Variant-specific checks
  match (lean_ci, zero_const) {
    (LeanCI::AxiomInfo(_), KConst::Axio { .. })
    | (LeanCI::QuotInfo(_), KConst::Quot { .. }) => Ok(()),

    (LeanCI::DefnInfo(v), KConst::Defn { val, .. }) => {
      expr_congruent(&v.value, val, nr).map_err(|e| format!("value: {e}"))
    },

    (LeanCI::ThmInfo(v), KConst::Defn { val, .. }) => {
      expr_congruent(&v.value, val, nr).map_err(|e| format!("value: {e}"))
    },

    (LeanCI::OpaqueInfo(v), KConst::Defn { val, .. }) => {
      expr_congruent(&v.value, val, nr).map_err(|e| format!("value: {e}"))
    },

    (LeanCI::InductInfo(v), KConst::Indc { params, indices, ctors, .. }) => {
      let lp = v.num_params.to_u64().unwrap_or(u64::MAX);
      let li = v.num_indices.to_u64().unwrap_or(u64::MAX);
      if lp != *params {
        return Err(format!("params: lean={lp} vs zero={params}"));
      }
      if li != *indices {
        return Err(format!("indices: lean={li} vs zero={indices}"));
      }
      if v.ctors.len() != ctors.len() {
        return Err(format!(
          "ctor count: lean={} vs zero={}",
          v.ctors.len(),
          ctors.len()
        ));
      }
      Ok(())
    },

    (LeanCI::CtorInfo(v), KConst::Ctor { cidx, params, fields, .. }) => {
      let lc = v.cidx.to_u64().unwrap_or(u64::MAX);
      let lp = v.num_params.to_u64().unwrap_or(u64::MAX);
      let lf = v.num_fields.to_u64().unwrap_or(u64::MAX);
      if lc != *cidx {
        return Err(format!("cidx: lean={lc} vs zero={cidx}"));
      }
      if lp != *params {
        return Err(format!("params: lean={lp} vs zero={params}"));
      }
      if lf != *fields {
        return Err(format!("fields: lean={lf} vs zero={fields}"));
      }
      Ok(())
    },

    (
      LeanCI::RecInfo(v),
      KConst::Recr { params, indices, motives, minors, rules, k, .. },
    ) => {
      let lp = v.num_params.to_u64().unwrap_or(u64::MAX);
      let li = v.num_indices.to_u64().unwrap_or(u64::MAX);
      let lm = v.num_motives.to_u64().unwrap_or(u64::MAX);
      let ln = v.num_minors.to_u64().unwrap_or(u64::MAX);
      if lp != *params {
        return Err(format!("params: lean={lp} vs zero={params}"));
      }
      if li != *indices {
        return Err(format!("indices: lean={li} vs zero={indices}"));
      }
      if lm != *motives {
        return Err(format!("motives: lean={lm} vs zero={motives}"));
      }
      if ln != *minors {
        return Err(format!("minors: lean={ln} vs zero={minors}"));
      }
      if v.rules.len() != rules.len() {
        return Err(format!(
          "rule count: lean={} vs zero={}",
          v.rules.len(),
          rules.len()
        ));
      }
      if v.k != *k {
        return Err(format!("k: lean={} vs zero={k}", v.k));
      }
      for (i, (lean_rule, zero_rule)) in
        v.rules.iter().zip(rules.iter()).enumerate()
      {
        expr_congruent(&lean_rule.rhs, &zero_rule.rhs, nr)
          .map_err(|e| format!("rule[{i}].rhs: {e}"))?;
      }
      Ok(())
    },

    _ => Err(format!(
      "variant mismatch: lean={} vs zero={}",
      lean_ci_tag(lean_ci),
      zero_const_tag(zero_const),
    )),
  }
}

fn lean_lvl_tag(l: &lean::Level) -> &'static str {
  use lean::LevelData as LD;
  match l.as_data() {
    LD::Zero(_) => "Zero",
    LD::Succ(..) => "Succ",
    LD::Max(..) => "Max",
    LD::Imax(..) => "IMax",
    LD::Param(..) => "Param",
    LD::Mvar(..) => "Mvar",
  }
}

fn zero_univ_tag<M: super::mode::KernelMode>(u: &KUniv<M>) -> &'static str {
  match u.data() {
    UnivData::Zero(_) => "Zero",
    UnivData::Succ(..) => "Succ",
    UnivData::Max(..) => "Max",
    UnivData::IMax(..) => "IMax",
    UnivData::Param(..) => "Param",
  }
}

fn lean_expr_tag(e: &lean::Expr) -> &'static str {
  use lean::ExprData as LE;
  match e.as_data() {
    LE::Bvar(..) => "Bvar",
    LE::Fvar(..) => "Fvar",
    LE::Mvar(..) => "Mvar",
    LE::Sort(..) => "Sort",
    LE::Const(..) => "Const",
    LE::App(..) => "App",
    LE::Lam(..) => "Lam",
    LE::ForallE(..) => "ForallE",
    LE::LetE(..) => "LetE",
    LE::Lit(..) => "Lit",
    LE::Mdata(..) => "Mdata",
    LE::Proj(..) => "Proj",
  }
}

fn zero_expr_tag(e: &KExpr<Anon>) -> &'static str {
  match e.data() {
    ExprData::Var(..) => "Var",
    ExprData::FVar(..) => "FVar",
    ExprData::Sort(..) => "Sort",
    ExprData::Const(..) => "Const",
    ExprData::App(..) => "App",
    ExprData::Lam(..) => "Lam",
    ExprData::All(..) => "All",
    ExprData::Let(..) => "Let",
    ExprData::Prj(..) => "Prj",
    ExprData::Nat(..) => "Nat",
    ExprData::Str(..) => "Str",
  }
}

fn lean_ci_tag(ci: &LeanCI) -> &'static str {
  match ci {
    LeanCI::AxiomInfo(_) => "Axiom",
    LeanCI::DefnInfo(_) => "Defn",
    LeanCI::ThmInfo(_) => "Thm",
    LeanCI::OpaqueInfo(_) => "Opaque",
    LeanCI::QuotInfo(_) => "Quot",
    LeanCI::InductInfo(_) => "Induct",
    LeanCI::CtorInfo(_) => "Ctor",
    LeanCI::RecInfo(_) => "Rec",
  }
}

fn zero_const_tag<M: super::mode::KernelMode>(c: &KConst<M>) -> &'static str {
  match c {
    KConst::Defn { .. } => "Defn",
    KConst::Recr { .. } => "Recr",
    KConst::Axio { .. } => "Axio",
    KConst::Quot { .. } => "Quot",
    KConst::Indc { .. } => "Indc",
    KConst::Ctor { .. } => "Ctor",
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::ix::address::Address;
  use crate::ix::env::{
    self, AxiomVal, BinderInfo, ConstantVal, ConstructorVal, DefinitionSafety,
    DefinitionVal, InductiveVal, Level as LL, Name, OpaqueVal, QuotKind,
    QuotVal, RecursorRule as LeanRule, RecursorVal, ReducibilityHints,
    TheoremVal,
  };
  use crate::ix::ixon::env::{Env as IxonEnv, Named};
  use crate::ix::kernel::constant::KConst;
  use crate::ix::kernel::id::KId;
  use crate::ix::kernel::mode::Anon;

  /// `Nat` from a u64 via the public `From<u64>` impl.
  /// (The `Nat` type itself is a private re-export in `env.rs`.)
  fn n(x: u64) -> lean_ffi::nat::Nat {
    lean_ffi::nat::Nat::from(x)
  }

  // ---- test helpers ----

  fn mk_name(s: &str) -> Name {
    let mut n = Name::anon();
    for part in s.split('.') {
      n = Name::str(n, part.to_string());
    }
    n
  }

  fn mk_addr(s: &str) -> Address {
    Address::hash(s.as_bytes())
  }

  fn empty_resolver() -> NameResolver {
    NameResolver::from_ixon_env(&IxonEnv::new())
  }

  fn resolver_with(entries: &[(Name, Address)]) -> NameResolver {
    let env = IxonEnv::new();
    for (n, a) in entries {
      env.register_name(n.clone(), Named::with_addr(a.clone()));
    }
    NameResolver::from_ixon_env(&env)
  }

  // ---- level_congruent ----

  #[test]
  fn level_zero_matches() {
    let r = empty_resolver();
    let ll = LL::zero();
    let lu = KUniv::<Anon>::zero();
    level_congruent(&ll, &lu, &r).unwrap();
  }

  #[test]
  fn level_succ_matches() {
    let r = empty_resolver();
    let ll = LL::succ(LL::zero());
    let lu = KUniv::<Anon>::succ(KUniv::zero());
    level_congruent(&ll, &lu, &r).unwrap();
  }

  #[test]
  fn level_max_matches() {
    // KUniv::max / ::imax simplify at construction (e.g. `max(0, a) → a`),
    // so use two params so neither side is reducible at the Zero case.
    let r = empty_resolver();
    let u_name = Name::str(Name::anon(), "u".to_string());
    let v_name = Name::str(Name::anon(), "v".to_string());
    let ll = LL::max(LL::param(u_name), LL::param(v_name));
    let lu = KUniv::<Anon>::max(KUniv::param(0, ()), KUniv::param(1, ()));
    level_congruent(&ll, &lu, &r).unwrap();
  }

  #[test]
  fn level_imax_matches() {
    let r = empty_resolver();
    let u_name = Name::str(Name::anon(), "u".to_string());
    let v_name = Name::str(Name::anon(), "v".to_string());
    let ll = LL::imax(LL::param(u_name), LL::param(v_name));
    let lu = KUniv::<Anon>::imax(KUniv::param(0, ()), KUniv::param(1, ()));
    level_congruent(&ll, &lu, &r).unwrap();
  }

  #[test]
  fn level_param_matches() {
    // Lean Param has a name; zero Param has a positional index. Without a
    // level_params list the check must pass (see module comment).
    let r = empty_resolver();
    let ll = LL::param(mk_name("u"));
    let lu = KUniv::<Anon>::param(0, ());
    level_congruent(&ll, &lu, &r).unwrap();
  }

  #[test]
  fn level_zero_vs_succ_fails() {
    let r = empty_resolver();
    let ll = LL::zero();
    let lu = KUniv::<Anon>::succ(KUniv::zero());
    let e = level_congruent(&ll, &lu, &r).unwrap_err();
    assert!(e.contains("Zero"));
    assert!(e.contains("Succ"));
  }

  #[test]
  fn level_max_vs_imax_fails() {
    let r = empty_resolver();
    let u_name = Name::str(Name::anon(), "u".to_string());
    let v_name = Name::str(Name::anon(), "v".to_string());
    let ll = LL::max(LL::param(u_name), LL::param(v_name));
    let lu = KUniv::<Anon>::imax(KUniv::param(0, ()), KUniv::param(1, ()));
    let e = level_congruent(&ll, &lu, &r).unwrap_err();
    assert!(e.contains("Max"));
    assert!(e.contains("IMax"));
  }

  #[test]
  fn level_succ_inner_propagates_error() {
    let r = empty_resolver();
    // Succ(Zero) vs Succ(Succ(Zero)) — outer shape matches, inner differs.
    let ll = LL::succ(LL::zero());
    let lu = KUniv::<Anon>::succ(KUniv::succ(KUniv::zero()));
    let e = level_congruent(&ll, &lu, &r).unwrap_err();
    assert!(e.contains("Zero"));
    assert!(e.contains("Succ"));
  }

  // ---- expr_congruent ----

  #[test]
  fn expr_bvar_matches() {
    let r = empty_resolver();
    let lean_e = env::Expr::bvar(n(3));
    let zero_e = KExpr::<Anon>::var(3, ());
    expr_congruent(&lean_e, &zero_e, &r).unwrap();
  }

  #[test]
  fn expr_bvar_idx_mismatch_fails() {
    let r = empty_resolver();
    let lean_e = env::Expr::bvar(n(3));
    let zero_e = KExpr::<Anon>::var(5, ());
    let e = expr_congruent(&lean_e, &zero_e, &r).unwrap_err();
    assert!(e.contains("var mismatch"));
  }

  #[test]
  fn expr_sort_matches() {
    let r = empty_resolver();
    let lean_e = env::Expr::sort(LL::zero());
    let zero_e = KExpr::<Anon>::sort(KUniv::zero());
    expr_congruent(&lean_e, &zero_e, &r).unwrap();
  }

  #[test]
  fn expr_const_matches_by_address() {
    let name = mk_name("Nat");
    let addr = mk_addr("Nat");
    let r = resolver_with(&[(name.clone(), addr.clone())]);

    let lean_e = env::Expr::cnst(name.clone(), vec![]);
    let zero_e = KExpr::<Anon>::cnst(KId::new(addr, ()), Box::new([]));
    expr_congruent(&lean_e, &zero_e, &r).unwrap();
  }

  #[test]
  fn expr_const_addr_mismatch_fails() {
    let name = mk_name("Nat");
    let r = resolver_with(&[(name.clone(), mk_addr("Nat"))]);

    let lean_e = env::Expr::cnst(name.clone(), vec![]);
    // Wrong address in zero_e
    let zero_e =
      KExpr::<Anon>::cnst(KId::new(mk_addr("Bogus"), ()), Box::new([]));
    let e = expr_congruent(&lean_e, &zero_e, &r).unwrap_err();
    assert!(e.contains("address mismatch"));
  }

  #[test]
  fn expr_const_name_missing_from_resolver_fails() {
    let r = empty_resolver();
    let lean_e = env::Expr::cnst(mk_name("Nat"), vec![]);
    let zero_e =
      KExpr::<Anon>::cnst(KId::new(mk_addr("Nat"), ()), Box::new([]));
    let e = expr_congruent(&lean_e, &zero_e, &r).unwrap_err();
    assert!(e.contains("not found"));
  }

  #[test]
  fn expr_const_level_count_mismatch_fails() {
    let name = mk_name("Nat");
    let addr = mk_addr("Nat");
    let r = resolver_with(&[(name.clone(), addr.clone())]);

    let lean_e = env::Expr::cnst(name.clone(), vec![LL::zero()]);
    let zero_e = KExpr::<Anon>::cnst(KId::new(addr, ()), Box::new([]));
    let e = expr_congruent(&lean_e, &zero_e, &r).unwrap_err();
    assert!(e.contains("level count mismatch"));
  }

  #[test]
  fn expr_app_matches_recursively() {
    let r = empty_resolver();
    let lean_e =
      env::Expr::app(env::Expr::sort(LL::zero()), env::Expr::bvar(n(0)));
    let zero_e =
      KExpr::<Anon>::app(KExpr::sort(KUniv::zero()), KExpr::var(0, ()));
    expr_congruent(&lean_e, &zero_e, &r).unwrap();
  }

  #[test]
  fn expr_lam_matches() {
    let r = empty_resolver();
    let lean_e = env::Expr::lam(
      mk_name("x"),
      env::Expr::sort(LL::zero()),
      env::Expr::bvar(n(0)),
      BinderInfo::Default,
    );
    let zero_e =
      KExpr::<Anon>::lam((), (), KExpr::sort(KUniv::zero()), KExpr::var(0, ()));
    expr_congruent(&lean_e, &zero_e, &r).unwrap();
  }

  #[test]
  fn expr_forall_matches() {
    let r = empty_resolver();
    let lean_e = env::Expr::all(
      mk_name("x"),
      env::Expr::sort(LL::zero()),
      env::Expr::bvar(n(0)),
      BinderInfo::Default,
    );
    let zero_e =
      KExpr::<Anon>::all((), (), KExpr::sort(KUniv::zero()), KExpr::var(0, ()));
    expr_congruent(&lean_e, &zero_e, &r).unwrap();
  }

  #[test]
  fn expr_let_matches() {
    let r = empty_resolver();
    let lean_e = env::Expr::letE(
      mk_name("x"),
      env::Expr::sort(LL::zero()),
      env::Expr::bvar(n(0)),
      env::Expr::bvar(n(0)),
      false,
    );
    let zero_e = KExpr::<Anon>::let_(
      (),
      KExpr::sort(KUniv::zero()),
      KExpr::var(0, ()),
      KExpr::var(0, ()),
      false,
    );
    expr_congruent(&lean_e, &zero_e, &r).unwrap();
  }

  #[test]
  fn expr_mdata_is_transparent() {
    let r = empty_resolver();
    // Lean Mdata(_, Sort 0) must match the bare zero Sort 0.
    let inner = env::Expr::sort(LL::zero());
    let lean_e = env::Expr::mdata(vec![], inner);
    let zero_e = KExpr::<Anon>::sort(KUniv::zero());
    expr_congruent(&lean_e, &zero_e, &r).unwrap();
  }

  #[test]
  fn expr_nat_lit_matches() {
    let r = empty_resolver();
    let lean_e = env::Expr::lit(Literal::NatVal(n(42)));
    // Nat expr construction for the zero kernel.
    let zero_e = KExpr::<Anon>::nat(n(42), mk_addr("any"));
    expr_congruent(&lean_e, &zero_e, &r).unwrap();
  }

  #[test]
  fn expr_str_lit_matches() {
    let r = empty_resolver();
    let lean_e = env::Expr::lit(Literal::StrVal("hi".into()));
    let zero_e = KExpr::<Anon>::str("hi".into(), mk_addr("any"));
    expr_congruent(&lean_e, &zero_e, &r).unwrap();
  }

  #[test]
  fn expr_proj_matches() {
    let name = mk_name("MyStruct");
    let addr = mk_addr("MyStruct");
    let r = resolver_with(&[(name.clone(), addr.clone())]);

    let lean_e = env::Expr::proj(name.clone(), n(1), env::Expr::bvar(n(0)));
    let zero_e = KExpr::<Anon>::prj(KId::new(addr, ()), 1, KExpr::var(0, ()));
    expr_congruent(&lean_e, &zero_e, &r).unwrap();
  }

  #[test]
  fn expr_proj_field_mismatch_fails() {
    let name = mk_name("MyStruct");
    let addr = mk_addr("MyStruct");
    let r = resolver_with(&[(name.clone(), addr.clone())]);

    let lean_e = env::Expr::proj(name.clone(), n(2), env::Expr::bvar(n(0)));
    let zero_e = KExpr::<Anon>::prj(KId::new(addr, ()), 1, KExpr::var(0, ()));
    let e = expr_congruent(&lean_e, &zero_e, &r).unwrap_err();
    assert!(e.contains("proj field mismatch"));
  }

  #[test]
  fn expr_fvar_unexpected() {
    let r = empty_resolver();
    let lean_e = env::Expr::fvar(mk_name("x"));
    let zero_e = KExpr::<Anon>::var(0, ());
    let e = expr_congruent(&lean_e, &zero_e, &r).unwrap_err();
    assert!(e.contains("Fvar") || e.contains("unexpected"));
  }

  #[test]
  fn expr_shape_mismatch_fails() {
    let r = empty_resolver();
    let lean_e = env::Expr::sort(LL::zero());
    let zero_e = KExpr::<Anon>::var(0, ());
    let e = expr_congruent(&lean_e, &zero_e, &r).unwrap_err();
    assert!(e.contains("shape mismatch"));
  }

  // ---- const_congruent ----

  fn lean_axio(
    name: &str,
    lvls: Vec<Name>,
    typ: env::Expr,
  ) -> env::ConstantInfo {
    env::ConstantInfo::AxiomInfo(AxiomVal {
      cnst: ConstantVal { name: mk_name(name), level_params: lvls, typ },
      is_unsafe: false,
    })
  }

  fn zero_axio(lvls: u64, ty: KExpr<Anon>) -> KConst<Anon> {
    KConst::Axio { name: (), level_params: (), is_unsafe: false, lvls, ty }
  }

  #[test]
  fn const_axio_matches() {
    let r = empty_resolver();
    let ltyp = env::Expr::sort(LL::zero());
    let ztyp = KExpr::<Anon>::sort(KUniv::zero());
    let lci = lean_axio("A", vec![], ltyp);
    let kc = zero_axio(0, ztyp);
    const_congruent(&lci, &kc, &r).unwrap();
  }

  #[test]
  fn const_variant_mismatch_fails() {
    // Axiom on the Lean side, Defn on the zero side → variant mismatch error.
    let r = empty_resolver();
    let lci = lean_axio("A", vec![], env::Expr::sort(LL::zero()));
    let kc = KConst::<Anon>::Defn {
      name: (),
      level_params: (),
      kind: crate::ix::ixon::constant::DefKind::Definition,
      safety: DefinitionSafety::Safe,
      hints: ReducibilityHints::Opaque,
      lvls: 0,
      ty: KExpr::sort(KUniv::zero()),
      val: KExpr::sort(KUniv::zero()),
      lean_all: (),
      block: KId::new(mk_addr("A"), ()),
    };
    let e = const_congruent(&lci, &kc, &r).unwrap_err();
    assert!(e.contains("variant mismatch"));
  }

  #[test]
  fn const_lvls_count_mismatch_fails() {
    let r = empty_resolver();
    let lci = lean_axio(
      "A",
      vec![mk_name("u"), mk_name("v")],
      env::Expr::sort(LL::zero()),
    );
    let kc = zero_axio(1, KExpr::sort(KUniv::zero())); // claims 1 lvl
    let e = const_congruent(&lci, &kc, &r).unwrap_err();
    assert!(e.contains("lvls"));
  }

  #[test]
  fn const_defn_value_mismatch_propagates() {
    let r = empty_resolver();
    let lci = env::ConstantInfo::DefnInfo(DefinitionVal {
      cnst: ConstantVal {
        name: mk_name("f"),
        level_params: vec![],
        typ: env::Expr::sort(LL::zero()),
      },
      value: env::Expr::sort(LL::zero()), // value is Sort 0
      hints: ReducibilityHints::Opaque,
      safety: DefinitionSafety::Safe,
      all: vec![],
    });
    let kc = KConst::<Anon>::Defn {
      name: (),
      level_params: (),
      kind: crate::ix::ixon::constant::DefKind::Definition,
      safety: DefinitionSafety::Safe,
      hints: ReducibilityHints::Opaque,
      lvls: 0,
      ty: KExpr::sort(KUniv::zero()),
      // mismatched value: Var(0) instead of Sort 0
      val: KExpr::var(0, ()),
      lean_all: (),
      block: KId::new(mk_addr("f"), ()),
    };
    let e = const_congruent(&lci, &kc, &r).unwrap_err();
    assert!(e.contains("value"));
  }

  #[test]
  fn const_quot_matches_kind_free() {
    // QuotInfo ↔ Quot must succeed regardless of the QuotKind variant.
    let r = empty_resolver();
    let lci = env::ConstantInfo::QuotInfo(QuotVal {
      cnst: ConstantVal {
        name: mk_name("Quot"),
        level_params: vec![mk_name("u")],
        typ: env::Expr::sort(LL::succ(LL::zero())),
      },
      kind: QuotKind::Type,
    });
    let kc = KConst::<Anon>::Quot {
      name: (),
      level_params: (),
      kind: QuotKind::Type,
      lvls: 1,
      ty: KExpr::sort(KUniv::succ(KUniv::zero())),
    };
    const_congruent(&lci, &kc, &r).unwrap();
  }

  #[test]
  fn const_induct_param_count_mismatch_fails() {
    let r = empty_resolver();
    let lci = env::ConstantInfo::InductInfo(InductiveVal {
      cnst: ConstantVal {
        name: mk_name("A"),
        level_params: vec![],
        typ: env::Expr::sort(LL::zero()),
      },
      num_params: n(2),
      num_indices: n(0),
      all: vec![mk_name("A")],
      ctors: vec![],
      num_nested: n(0),
      is_rec: false,
      is_unsafe: false,
      is_reflexive: false,
    });
    let kc = KConst::<Anon>::Indc {
      name: (),
      level_params: (),
      params: 5, // wrong
      indices: 0,
      is_rec: false,
      is_refl: false,
      ctors: vec![],
      lvls: 0,
      ty: KExpr::sort(KUniv::zero()),
      lean_all: (),
      block: KId::new(mk_addr("A"), ()),
      is_unsafe: false,
      nested: 0,
      member_idx: 0,
    };
    let e = const_congruent(&lci, &kc, &r).unwrap_err();
    assert!(e.contains("params"));
  }

  #[test]
  fn const_ctor_field_count_mismatch_fails() {
    let r = empty_resolver();
    let lci = env::ConstantInfo::CtorInfo(ConstructorVal {
      cnst: ConstantVal {
        name: mk_name("A.mk"),
        level_params: vec![],
        typ: env::Expr::sort(LL::zero()),
      },
      induct: mk_name("A"),
      cidx: n(0),
      num_params: n(0),
      num_fields: n(3),
      is_unsafe: false,
    });
    let kc = KConst::<Anon>::Ctor {
      name: (),
      level_params: (),
      induct: KId::new(mk_addr("A"), ()),
      cidx: 0,
      params: 0,
      fields: 7, // wrong
      lvls: 0,
      ty: KExpr::sort(KUniv::zero()),
      is_unsafe: false,
    };
    let e = const_congruent(&lci, &kc, &r).unwrap_err();
    assert!(e.contains("fields"));
  }

  #[test]
  fn const_rec_rule_count_mismatch_fails() {
    let r = empty_resolver();
    let lci = env::ConstantInfo::RecInfo(RecursorVal {
      cnst: ConstantVal {
        name: mk_name("A.rec"),
        level_params: vec![],
        typ: env::Expr::sort(LL::zero()),
      },
      all: vec![mk_name("A")],
      num_params: n(0),
      num_indices: n(0),
      num_motives: n(1),
      num_minors: n(1),
      rules: vec![LeanRule {
        ctor: mk_name("A.mk"),
        n_fields: n(0),
        rhs: env::Expr::sort(LL::zero()),
      }],
      k: false,
      is_unsafe: false,
    });
    let kc = KConst::<Anon>::Recr {
      name: (),
      level_params: (),
      params: 0,
      indices: 0,
      motives: 1,
      minors: 1,
      rules: vec![], // wrong: empty
      k: false,
      lvls: 0,
      ty: KExpr::sort(KUniv::zero()),
      block: KId::new(mk_addr("A"), ()),
      member_idx: 0,
      lean_all: (),
      is_unsafe: false,
    };
    let e = const_congruent(&lci, &kc, &r).unwrap_err();
    assert!(e.contains("rule count"));
  }

  #[test]
  fn const_rec_k_mismatch_fails() {
    let r = empty_resolver();
    let lci = env::ConstantInfo::RecInfo(RecursorVal {
      cnst: ConstantVal {
        name: mk_name("A.rec"),
        level_params: vec![],
        typ: env::Expr::sort(LL::zero()),
      },
      all: vec![],
      num_params: n(0),
      num_indices: n(0),
      num_motives: n(1),
      num_minors: n(0),
      rules: vec![],
      k: true, // lean says k
      is_unsafe: false,
    });
    let kc = KConst::<Anon>::Recr {
      name: (),
      level_params: (),
      params: 0,
      indices: 0,
      motives: 1,
      minors: 0,
      rules: vec![],
      k: false, // zero says !k
      lvls: 0,
      ty: KExpr::sort(KUniv::zero()),
      block: KId::new(mk_addr("A.rec"), ()),
      member_idx: 0,
      lean_all: (),
      is_unsafe: false,
    };
    let e = const_congruent(&lci, &kc, &r).unwrap_err();
    assert!(e.contains("k:"));
  }

  #[test]
  fn const_thm_and_opaque_match_via_defn_side() {
    // Both ThmInfo and OpaqueInfo compare against KConst::Defn.
    let r = empty_resolver();

    let lthm = env::ConstantInfo::ThmInfo(TheoremVal {
      cnst: ConstantVal {
        name: mk_name("t"),
        level_params: vec![],
        typ: env::Expr::sort(LL::zero()),
      },
      value: env::Expr::sort(LL::zero()),
      all: vec![],
    });
    let k = KConst::<Anon>::Defn {
      name: (),
      level_params: (),
      kind: crate::ix::ixon::constant::DefKind::Theorem,
      safety: DefinitionSafety::Safe,
      hints: ReducibilityHints::Opaque,
      lvls: 0,
      ty: KExpr::sort(KUniv::zero()),
      val: KExpr::sort(KUniv::zero()),
      lean_all: (),
      block: KId::new(mk_addr("t"), ()),
    };
    const_congruent(&lthm, &k, &r).unwrap();

    let lop = env::ConstantInfo::OpaqueInfo(OpaqueVal {
      cnst: ConstantVal {
        name: mk_name("o"),
        level_params: vec![],
        typ: env::Expr::sort(LL::zero()),
      },
      value: env::Expr::sort(LL::zero()),
      is_unsafe: false,
      all: vec![],
    });
    const_congruent(&lop, &k, &r).unwrap();
  }
}
