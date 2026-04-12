//! Egress: convert zero kernel types (`Meta` mode) to `src/ix/env.rs` Lean types.
//!
//! Only works for `Meta` mode since it needs actual names and binder info.

use rayon::iter::{IntoParallelIterator, ParallelIterator};
use rustc_hash::FxHashMap;

use crate::ix::env::{
  self, AxiomVal, ConstantInfo as LeanCI, ConstantVal, ConstructorVal,
  DefinitionVal, InductiveVal, Name, OpaqueVal, QuotVal,
  RecursorRule as LeanRecRule, RecursorVal, TheoremVal,
};
use crate::ix::ixon::constant::DefKind;
use lean_ffi::nat::Nat;

use super::constant::KConst;
use super::env::KEnv;
use super::expr::{ExprData, KExpr, MData};
use super::id::KId;
use super::level::{KUniv, UnivData};
use super::mode::Meta;

/// Convert a zero kernel universe to a Lean level.
fn egress_level(u: &KUniv<Meta>, level_params: &[Name]) -> env::Level {
  match u.data() {
    UnivData::Zero(_) => env::Level::zero(),
    UnivData::Succ(inner, _) => {
      env::Level::succ(egress_level(inner, level_params))
    },
    UnivData::Max(a, b, _) => env::Level::max(
      egress_level(a, level_params),
      egress_level(b, level_params),
    ),
    UnivData::IMax(a, b, _) => env::Level::imax(
      egress_level(a, level_params),
      egress_level(b, level_params),
    ),
    UnivData::Param(idx, _, _) => {
      let pos = usize::try_from(*idx).expect("level param index exceeds usize");
      let name =
        level_params.get(pos).cloned().unwrap_or_else(Name::anon);
      env::Level::param(name)
    },
  }
}

fn egress_levels(
  levels: &[KUniv<Meta>],
  level_params: &[Name],
) -> Vec<env::Level> {
  levels.iter().map(|l| egress_level(l, level_params)).collect()
}

/// Expression egress cache, keyed by pointer identity.
type Cache = FxHashMap<usize, env::Expr>;

/// Convert a zero kernel expression to a Lean expression.
fn egress_expr(
  expr: &KExpr<Meta>,
  level_params: &[Name],
  cache: &mut Cache,
) -> env::Expr {
  let ptr = expr.ptr_key();
  if let Some(cached) = cache.get(&ptr) {
    return cached.clone();
  }

  let mdata: &Vec<MData> = expr.mdata();

  let inner = match expr.data() {
    ExprData::Var(idx, _, _) => env::Expr::bvar(Nat::from(*idx)),
    ExprData::Sort(u, _) => env::Expr::sort(egress_level(u, level_params)),
    ExprData::Const(id, levels, _) => {
      let lvls = egress_levels(levels, level_params);
      env::Expr::cnst(id.name.clone(), lvls)
    },
    ExprData::App(f, a, _) => {
      let ef = egress_expr(f, level_params, cache);
      let ea = egress_expr(a, level_params, cache);
      env::Expr::app(ef, ea)
    },
    ExprData::Lam(name, bi, ty, body, _) => {
      let ety = egress_expr(ty, level_params, cache);
      let ebody = egress_expr(body, level_params, cache);
      env::Expr::lam(name.clone(), ety, ebody, bi.clone())
    },
    ExprData::All(name, bi, ty, body, _) => {
      let ety = egress_expr(ty, level_params, cache);
      let ebody = egress_expr(body, level_params, cache);
      env::Expr::all(name.clone(), ety, ebody, bi.clone())
    },
    ExprData::Let(name, ty, val, body, nd, _) => {
      let ety = egress_expr(ty, level_params, cache);
      let eval = egress_expr(val, level_params, cache);
      let ebody = egress_expr(body, level_params, cache);
      env::Expr::letE(name.clone(), ety, eval, ebody, *nd)
    },
    ExprData::Prj(id, field, val, _) => {
      let eval = egress_expr(val, level_params, cache);
      env::Expr::proj(id.name.clone(), Nat::from(*field), eval)
    },
    ExprData::Nat(n, _, _) => env::Expr::lit(env::Literal::NatVal(n.clone())),
    ExprData::Str(s, _, _) => env::Expr::lit(env::Literal::StrVal(s.clone())),
  };

  // Re-wrap with mdata layers (innermost first via reverse iteration).
  let result = mdata
    .iter()
    .rev()
    .fold(inner, |acc, kvs| env::Expr::mdata(kvs.clone(), acc));

  cache.insert(ptr, result.clone());
  result
}

fn zids_to_names(ids: &[KId<Meta>]) -> Vec<Name> {
  ids.iter().map(|id| id.name.clone()).collect()
}

/// Convert a zero kernel constant to a Lean `ConstantInfo`.
pub fn egress_constant(zc: &KConst<Meta>) -> LeanCI {
  let mut cache = Cache::default();

  match zc {
    KConst::Defn {
      name,
      level_params,
      kind,
      safety,
      hints,
      ty,
      val,
      lean_all,
      ..
    } => {
      let lp: &Vec<Name> = level_params;
      let cnst = ConstantVal {
        name: name.clone(),
        level_params: lp.clone(),
        typ: egress_expr(ty, lp, &mut cache),
      };
      let value = egress_expr(val, lp, &mut cache);
      let all = zids_to_names(lean_all);
      match kind {
        DefKind::Definition => LeanCI::DefnInfo(DefinitionVal {
          cnst,
          value,
          hints: *hints,
          safety: *safety,
          all,
        }),
        DefKind::Theorem => LeanCI::ThmInfo(TheoremVal { cnst, value, all }),
        DefKind::Opaque => LeanCI::OpaqueInfo(OpaqueVal {
          cnst,
          value,
          is_unsafe: *safety == env::DefinitionSafety::Unsafe,
          all,
        }),
      }
    },

    KConst::Axio { name, level_params, is_unsafe, ty, .. } => {
      let lp: &Vec<Name> = level_params;
      LeanCI::AxiomInfo(AxiomVal {
        cnst: ConstantVal {
          name: name.clone(),
          level_params: lp.clone(),
          typ: egress_expr(ty, lp, &mut cache),
        },
        is_unsafe: *is_unsafe,
      })
    },

    KConst::Quot { name, level_params, kind, ty, .. } => {
      let lp: &Vec<Name> = level_params;
      LeanCI::QuotInfo(QuotVal {
        cnst: ConstantVal {
          name: name.clone(),
          level_params: lp.clone(),
          typ: egress_expr(ty, lp, &mut cache),
        },
        kind: *kind,
      })
    },

    KConst::Indc {
      name,
      level_params,
      params,
      indices,
      is_rec,
      is_refl,
      is_unsafe,
      nested,
      ty,
      ctors,
      lean_all,
      ..
    } => {
      let lp: &Vec<Name> = level_params;
      LeanCI::InductInfo(InductiveVal {
        cnst: ConstantVal {
          name: name.clone(),
          level_params: lp.clone(),
          typ: egress_expr(ty, lp, &mut cache),
        },
        num_params: Nat::from(*params),
        num_indices: Nat::from(*indices),
        all: zids_to_names(lean_all),
        ctors: zids_to_names(ctors),
        num_nested: Nat::from(*nested),
        is_rec: *is_rec,
        is_unsafe: *is_unsafe,
        is_reflexive: *is_refl,
      })
    },

    KConst::Ctor {
      name,
      level_params,
      induct,
      cidx,
      params,
      fields,
      is_unsafe,
      ty,
      ..
    } => {
      let lp: &Vec<Name> = level_params;
      LeanCI::CtorInfo(ConstructorVal {
        cnst: ConstantVal {
          name: name.clone(),
          level_params: lp.clone(),
          typ: egress_expr(ty, lp, &mut cache),
        },
        induct: induct.name.clone(),
        cidx: Nat::from(*cidx),
        num_params: Nat::from(*params),
        num_fields: Nat::from(*fields),
        is_unsafe: *is_unsafe,
      })
    },

    KConst::Recr {
      name,
      level_params,
      params,
      indices,
      motives,
      minors,
      ty,
      rules,
      k,
      is_unsafe,
      lean_all,
      ..
    } => {
      let lp: &Vec<Name> = level_params;
      let lean_rules: Vec<LeanRecRule> = rules
        .iter()
        .map(|r| LeanRecRule {
          ctor: Name::anon(),
          n_fields: Nat::from(r.fields),
          rhs: egress_expr(&r.rhs, lp, &mut cache),
        })
        .collect();
      let typ = egress_expr(ty, lp, &mut cache);
      // Surgery permutation is deferred — no source_motive_perm / source_minor_groups
      LeanCI::RecInfo(RecursorVal {
        cnst: ConstantVal { name: name.clone(), level_params: lp.clone(), typ },
        all: zids_to_names(lean_all),
        num_params: Nat::from(*params),
        num_indices: Nat::from(*indices),
        num_motives: Nat::from(*motives),
        num_minors: Nat::from(*minors),
        rules: lean_rules,
        k: *k,
        is_unsafe: *is_unsafe,
      })
    },
  }
}

/// Convert the entire zero kernel environment to a Lean environment.
pub fn egress_env(zenv: &KEnv<Meta>) -> env::Env {
  let entries: Vec<_> = zenv.iter().collect();

  let results: Vec<(Name, LeanCI)> = entries
    .into_par_iter()
    .map(|(id, zc)| (id.name.clone(), egress_constant(&zc)))
    .collect();

  let mut lean_env = env::Env::default();
  for (name, ci) in results {
    lean_env.insert(name, ci);
  }
  lean_env
}
