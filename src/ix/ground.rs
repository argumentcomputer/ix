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

#[derive(Debug)]
pub enum GroundError<'a> {
  Level(Level, Vec<Name>),
  Ref(Name),
  MVar(Expr),
  Var(Expr, usize),
  Indc(&'a InductiveVal, Option<&'a ConstantInfo>),
  Idx(Nat),
}

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
