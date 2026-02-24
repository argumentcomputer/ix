//! Groundedness checking for Lean environment constants.
//!
//! A constant is "grounded" if all its references resolve to known constants, all
//! bound variables are in scope, and no metavariables remain. Ungroundedness
//! propagates through the reference graph: if A references ungrounded B, then A
//! is also ungrounded.

use rayon::iter::{IntoParallelRefIterator, ParallelIterator};
use rustc_hash::{FxHashMap, FxHashSet};
use std::collections::hash_map::Entry;

use crate::{
  ix::env::{
    ConstantInfo, Env, Expr, ExprData, InductiveVal, Level, LevelData, Name,
  },
  ix::graph::RefMap,
  lean::nat::Nat,
};

/// Reason a constant failed groundedness checking.
#[derive(Debug)]
pub enum GroundError<'a> {
  /// A universe level parameter or metavariable is not in scope.
  Level(Level, Vec<Name>),
  /// A referenced constant does not exist in the environment (or is itself ungrounded).
  Ref(Name),
  /// An expression-level metavariable was encountered.
  MVar(Expr),
  /// A free or out-of-scope bound variable was encountered.
  Var(Expr, usize),
  /// An inductive type's constructor is missing or has the wrong kind.
  Indc(&'a InductiveVal, Option<&'a ConstantInfo>),
  /// An invalid de Bruijn index.
  Idx(Nat),
}

/// Checks every constant in `env` for groundedness and returns a map of all ungrounded names.
///
/// First collects immediately ungrounded constants in parallel, then propagates
/// ungroundedness transitively through `in_refs` (the reverse reference graph).
pub fn ground_consts<'a>(
  env: &'a Env,
  in_refs: &RefMap,
) -> FxHashMap<Name, GroundError<'a>> {
  // Collect immediate ungrounded constants.
  let mut ungrounded: FxHashMap<_, _> = env
    .par_iter()
    .filter_map(|(name, constant)| {
      let univs = const_univs(constant);
      let mut stt = GroundState::default();
      if let Err(err) = ground_const(constant, env, univs, 0, &mut stt) {
        Some((name.clone(), err))
      } else {
        None
      }
    })
    .collect();

  // Proliferate ungroundedness through in-refs.
  let mut stack: Vec<_> = ungrounded.keys().cloned().collect();
  while let Some(popped) = stack.pop() {
    let Some(in_ref_set) = in_refs.get(&popped) else {
      continue;
    };
    for in_ref in in_ref_set {
      if let Entry::Vacant(entry) = ungrounded.entry(in_ref.clone()) {
        entry.insert(GroundError::Ref(popped.clone()));
        stack.push(in_ref.clone());
      }
    }
  }

  ungrounded
}

fn const_univs(constant: &ConstantInfo) -> &[Name] {
  match constant {
    ConstantInfo::AxiomInfo(val) => &val.cnst.level_params,
    ConstantInfo::DefnInfo(val) => &val.cnst.level_params,
    ConstantInfo::ThmInfo(val) => &val.cnst.level_params,
    ConstantInfo::OpaqueInfo(val) => &val.cnst.level_params,
    ConstantInfo::QuotInfo(val) => &val.cnst.level_params,
    ConstantInfo::InductInfo(val) => &val.cnst.level_params,
    ConstantInfo::CtorInfo(val) => &val.cnst.level_params,
    ConstantInfo::RecInfo(val) => &val.cnst.level_params,
  }
}

#[derive(Default)]
struct GroundState {
  expr_cache: FxHashSet<(usize, Expr)>,
  univ_cache: FxHashSet<Level>,
}

fn ground_const<'a>(
  constant: &'a ConstantInfo,
  env: &'a Env,
  univs: &[Name],
  binds: usize,
  stt: &mut GroundState,
) -> Result<(), GroundError<'a>> {
  match constant {
    ConstantInfo::AxiomInfo(val) => {
      ground_expr(&val.cnst.typ, env, univs, binds, stt)
    },
    ConstantInfo::DefnInfo(val) => {
      ground_expr(&val.cnst.typ, env, univs, binds, stt)?;
      ground_expr(&val.value, env, univs, binds, stt)
    },
    ConstantInfo::ThmInfo(val) => {
      ground_expr(&val.cnst.typ, env, univs, binds, stt)?;
      ground_expr(&val.value, env, univs, binds, stt)
    },
    ConstantInfo::OpaqueInfo(val) => {
      ground_expr(&val.cnst.typ, env, univs, binds, stt)?;
      ground_expr(&val.value, env, univs, binds, stt)
    },
    ConstantInfo::QuotInfo(val) => {
      ground_expr(&val.cnst.typ, env, univs, binds, stt)
    },
    ConstantInfo::InductInfo(val) => {
      for ctor in &val.ctors {
        match env.get(ctor) {
          Some(ConstantInfo::CtorInfo(_)) => (),
          c => return Err(GroundError::Indc(val, c)),
        }
      }
      ground_expr(&val.cnst.typ, env, univs, binds, stt)
    },
    ConstantInfo::CtorInfo(val) => {
      ground_expr(&val.cnst.typ, env, univs, binds, stt)
    },
    ConstantInfo::RecInfo(val) => {
      for rule in &val.rules {
        ground_expr(&rule.rhs, env, univs, binds, stt)?;
      }
      ground_expr(&val.cnst.typ, env, univs, binds, stt)
    },
  }
}

fn ground_expr<'a>(
  expr: &Expr,
  env: &'a Env,
  univs: &[Name],
  binds: usize,
  stt: &mut GroundState,
) -> Result<(), GroundError<'a>> {
  let key = (binds, expr.clone());
  if stt.expr_cache.contains(&key) {
    return Ok(());
  }
  stt.expr_cache.insert(key);
  match expr.as_data() {
    ExprData::Mdata(_, e, _) => ground_expr(e, env, univs, binds, stt),
    ExprData::Bvar(idx, _) => {
      if *idx >= Nat(binds.into()) {
        return Err(GroundError::Var(expr.clone(), binds));
      }
      Ok(())
    },
    ExprData::Sort(level, _) => ground_level(level, univs, stt),
    ExprData::Const(name, levels, _) => {
      for level in levels {
        ground_level(level, univs, stt)?;
      }
      if !env.contains_key(name) {
        return Err(GroundError::Ref(name.clone()));
      }
      Ok(())
    },
    ExprData::App(f, a, _) => {
      ground_expr(f, env, univs, binds, stt)?;
      ground_expr(a, env, univs, binds, stt)
    },
    ExprData::Lam(_, t, b, ..) | ExprData::ForallE(_, t, b, ..) => {
      ground_expr(t, env, univs, binds, stt)?;
      ground_expr(b, env, univs, binds + 1, stt)
    },
    ExprData::LetE(_, t, v, b, ..) => {
      ground_expr(t, env, univs, binds, stt)?;
      ground_expr(v, env, univs, binds, stt)?;
      ground_expr(b, env, univs, binds + 1, stt)
    },
    ExprData::Proj(name, _, e, _) => {
      if !env.contains_key(name) {
        return Err(GroundError::Ref(name.clone()));
      }
      ground_expr(e, env, univs, binds, stt)
    },
    ExprData::Lit(..) => Ok(()),
    ExprData::Mvar(..) => Err(GroundError::MVar(expr.clone())),
    ExprData::Fvar(..) => Err(GroundError::Var(expr.clone(), binds)),
  }
}

fn ground_level<'a>(
  level: &Level,
  univs: &[Name],
  stt: &mut GroundState,
) -> Result<(), GroundError<'a>> {
  let key = level.clone();
  if stt.univ_cache.contains(&key) {
    return Ok(());
  }
  stt.univ_cache.insert(key);
  match level.as_data() {
    LevelData::Zero(_) => Ok(()),
    LevelData::Succ(x, _) => ground_level(x, univs, stt),
    LevelData::Max(x, y, _) | LevelData::Imax(x, y, _) => {
      ground_level(x, univs, stt)?;
      ground_level(y, univs, stt)
    },
    LevelData::Param(n, _) => {
      if !univs.contains(n) {
        return Err(GroundError::Level(level.clone(), univs.to_vec()));
      }
      Ok(())
    },
    LevelData::Mvar(_, _) => {
      Err(GroundError::Level(level.clone(), univs.to_vec()))
    },
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::ix::env::*;
  use crate::ix::graph::build_ref_graph;

  fn n(s: &str) -> Name {
    Name::str(Name::anon(), s.to_string())
  }

  fn sort0() -> Expr {
    Expr::sort(Level::zero())
  }

  fn mk_cv(name: &str) -> ConstantVal {
    ConstantVal { name: n(name), level_params: vec![], typ: sort0() }
  }

  fn check(env: &Env) -> FxHashMap<Name, GroundError<'_>> {
    let graph = build_ref_graph(env);
    ground_consts(env, &graph.in_refs)
  }

  #[test]
  fn grounded_axiom() {
    let mut env = Env::default();
    env.insert(
      n("A"),
      ConstantInfo::AxiomInfo(AxiomVal { cnst: mk_cv("A"), is_unsafe: false }),
    );
    let errors = check(&env);
    assert!(errors.is_empty(), "well-formed axiom should be grounded");
  }

  #[test]
  fn grounded_defn_with_bvar_in_lam() {
    // fun (_ : Sort 0) => #0 is grounded (bvar(0) under one binder)
    let mut env = Env::default();
    let body = Expr::lam(
      Name::anon(),
      sort0(),
      Expr::bvar(Nat::from(0u64)),
      BinderInfo::Default,
    );
    env.insert(
      n("f"),
      ConstantInfo::DefnInfo(DefinitionVal {
        cnst: ConstantVal { name: n("f"), level_params: vec![], typ: sort0() },
        value: body,
        hints: ReducibilityHints::Opaque,
        safety: DefinitionSafety::Safe,
        all: vec![n("f")],
      }),
    );
    assert!(check(&env).is_empty());
  }

  #[test]
  fn ungrounded_missing_ref() {
    // Axiom A : B, but B is not in env
    let mut env = Env::default();
    env.insert(
      n("A"),
      ConstantInfo::AxiomInfo(AxiomVal {
        cnst: ConstantVal {
          name: n("A"),
          level_params: vec![],
          typ: Expr::cnst(n("B"), vec![]),
        },
        is_unsafe: false,
      }),
    );
    let errors = check(&env);
    assert!(errors.contains_key(&n("A")));
    assert!(matches!(errors[&n("A")], GroundError::Ref(_)));
  }

  #[test]
  fn ungrounded_bvar_out_of_scope() {
    // Axiom A : #0 (bvar with no enclosing binder)
    let mut env = Env::default();
    env.insert(
      n("A"),
      ConstantInfo::AxiomInfo(AxiomVal {
        cnst: ConstantVal {
          name: n("A"),
          level_params: vec![],
          typ: Expr::bvar(Nat::from(0u64)),
        },
        is_unsafe: false,
      }),
    );
    let errors = check(&env);
    assert!(errors.contains_key(&n("A")));
    assert!(matches!(errors[&n("A")], GroundError::Var(_, 0)));
  }

  #[test]
  fn ungrounded_mvar() {
    // Axiom A : ?m
    let mut env = Env::default();
    env.insert(
      n("A"),
      ConstantInfo::AxiomInfo(AxiomVal {
        cnst: ConstantVal {
          name: n("A"),
          level_params: vec![],
          typ: Expr::mvar(n("m")),
        },
        is_unsafe: false,
      }),
    );
    let errors = check(&env);
    assert!(errors.contains_key(&n("A")));
    assert!(matches!(errors[&n("A")], GroundError::MVar(_)));
  }

  #[test]
  fn ungrounded_level_param() {
    // Axiom A : Sort (Param "u"), but "u" not in level_params
    let mut env = Env::default();
    env.insert(
      n("A"),
      ConstantInfo::AxiomInfo(AxiomVal {
        cnst: ConstantVal {
          name: n("A"),
          level_params: vec![], // u is not declared
          typ: Expr::sort(Level::param(n("u"))),
        },
        is_unsafe: false,
      }),
    );
    let errors = check(&env);
    assert!(errors.contains_key(&n("A")));
    assert!(matches!(errors[&n("A")], GroundError::Level(_, _)));
  }

  #[test]
  fn grounded_level_param_when_declared() {
    // Axiom A.{u} : Sort u — "u" is declared
    let mut env = Env::default();
    env.insert(
      n("A"),
      ConstantInfo::AxiomInfo(AxiomVal {
        cnst: ConstantVal {
          name: n("A"),
          level_params: vec![n("u")],
          typ: Expr::sort(Level::param(n("u"))),
        },
        is_unsafe: false,
      }),
    );
    assert!(check(&env).is_empty());
  }

  #[test]
  fn propagation_through_in_refs() {
    // B is ungrounded (refs missing C), A refs B → A should also be ungrounded
    let mut env = Env::default();
    env.insert(
      n("B"),
      ConstantInfo::AxiomInfo(AxiomVal {
        cnst: ConstantVal {
          name: n("B"),
          level_params: vec![],
          typ: Expr::cnst(n("C"), vec![]), // C not in env
        },
        is_unsafe: false,
      }),
    );
    env.insert(
      n("A"),
      ConstantInfo::AxiomInfo(AxiomVal {
        cnst: ConstantVal {
          name: n("A"),
          level_params: vec![],
          typ: Expr::cnst(n("B"), vec![]),
        },
        is_unsafe: false,
      }),
    );
    let errors = check(&env);
    // B is directly ungrounded
    assert!(errors.contains_key(&n("B")));
    // A is transitively ungrounded via Ref(B)
    assert!(errors.contains_key(&n("A")));
    assert!(matches!(errors[&n("A")], GroundError::Ref(_)));
  }

  #[test]
  fn inductive_missing_ctor() {
    // Inductive T lists T.mk as a ctor, but T.mk is not in env
    let mut env = Env::default();
    env.insert(
      n("T"),
      ConstantInfo::InductInfo(InductiveVal {
        cnst: mk_cv("T"),
        num_params: Nat::from(0u64),
        num_indices: Nat::from(0u64),
        all: vec![n("T")],
        ctors: vec![n("T.mk")],
        num_nested: Nat::from(0u64),
        is_rec: false,
        is_unsafe: false,
        is_reflexive: false,
      }),
    );
    let errors = check(&env);
    assert!(errors.contains_key(&n("T")));
    assert!(matches!(errors[&n("T")], GroundError::Indc(_, _)));
  }

  #[test]
  fn inductive_ctor_wrong_kind() {
    // Inductive T lists T.mk as a ctor, but T.mk is an axiom not a ctor
    let mut env = Env::default();
    env.insert(
      n("T"),
      ConstantInfo::InductInfo(InductiveVal {
        cnst: mk_cv("T"),
        num_params: Nat::from(0u64),
        num_indices: Nat::from(0u64),
        all: vec![n("T")],
        ctors: vec![n("T.mk")],
        num_nested: Nat::from(0u64),
        is_rec: false,
        is_unsafe: false,
        is_reflexive: false,
      }),
    );
    env.insert(
      n("T.mk"),
      ConstantInfo::AxiomInfo(AxiomVal {
        cnst: mk_cv("T.mk"),
        is_unsafe: false,
      }),
    );
    let errors = check(&env);
    assert!(errors.contains_key(&n("T")));
    assert!(matches!(errors[&n("T")], GroundError::Indc(_, Some(_))));
  }

  #[test]
  fn binding_increments_depth() {
    // fun (_ : Sort 0) => #0 is grounded (bvar under 1 binder)
    // but fun (_ : Sort 0) => #1 is ungrounded (bvar escapes)
    let mut env = Env::default();

    // Grounded case
    env.insert(
      n("ok"),
      ConstantInfo::DefnInfo(DefinitionVal {
        cnst: ConstantVal { name: n("ok"), level_params: vec![], typ: sort0() },
        value: Expr::lam(
          Name::anon(),
          sort0(),
          Expr::bvar(Nat::from(0u64)),
          BinderInfo::Default,
        ),
        hints: ReducibilityHints::Opaque,
        safety: DefinitionSafety::Safe,
        all: vec![n("ok")],
      }),
    );

    // Ungrounded case
    env.insert(
      n("bad"),
      ConstantInfo::DefnInfo(DefinitionVal {
        cnst: ConstantVal {
          name: n("bad"),
          level_params: vec![],
          typ: sort0(),
        },
        value: Expr::lam(
          Name::anon(),
          sort0(),
          Expr::bvar(Nat::from(1u64)), // escapes the single binder
          BinderInfo::Default,
        ),
        hints: ReducibilityHints::Opaque,
        safety: DefinitionSafety::Safe,
        all: vec![n("bad")],
      }),
    );

    let errors = check(&env);
    assert!(!errors.contains_key(&n("ok")));
    assert!(errors.contains_key(&n("bad")));
    assert!(matches!(errors[&n("bad")], GroundError::Var(_, 1)));
  }

  #[test]
  fn fvar_is_ungrounded() {
    // Free variables should be ungrounded
    let mut env = Env::default();
    env.insert(
      n("A"),
      ConstantInfo::AxiomInfo(AxiomVal {
        cnst: ConstantVal {
          name: n("A"),
          level_params: vec![],
          typ: Expr::fvar(n("x")),
        },
        is_unsafe: false,
      }),
    );
    let errors = check(&env);
    assert!(errors.contains_key(&n("A")));
    assert!(matches!(errors[&n("A")], GroundError::Var(_, 0)));
  }
}
