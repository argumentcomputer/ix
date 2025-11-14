use rayon::iter::{IntoParallelRefIterator, ParallelIterator};
use rustc_hash::{FxHashMap, FxHashSet};
use std::collections::hash_map::Entry;

use crate::{
  cons_list::ConsList,
  ix::env::{
    ConstMap, ConstantInfo, Expr, ExprData, InductiveVal, Level, LevelData,
    Name,
  },
  ix::graph::RefMap,
  lean::nat::Nat,
};

pub enum GroundError<'a> {
  Level(Level, ConsList<Name>),
  Ref(Name),
  MVar(Expr),
  Var(Expr, ConsList<Name>),
  Indc(&'a InductiveVal, Option<&'a ConstantInfo>),
  Idx(Nat),
}

pub fn ground_consts<'a>(
  const_map: &'a ConstMap,
  in_refs: &RefMap,
) -> FxHashMap<Name, GroundError<'a>> {
  // Collect immediate ungrounded constants.
  let mut ungrounded: FxHashMap<_, _> = const_map
    .par_iter()
    .filter_map(|(name, constant)| {
      let univs = const_univs(constant);
      let mut stt = GroundState::default();
      if let Err(err) =
        ground_const(constant, const_map, univs, ConsList::Nil, &mut stt)
      {
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

fn const_univs(constant: &ConstantInfo) -> ConsList<Name> {
  let univs = match constant {
    ConstantInfo::AxiomInfo(val) => &val.constant_val.level_params,
    ConstantInfo::DefnInfo(val) => &val.constant_val.level_params,
    ConstantInfo::ThmInfo(val) => &val.constant_val.level_params,
    ConstantInfo::OpaqueInfo(val) => &val.constant_val.level_params,
    ConstantInfo::QuotInfo(val) => &val.constant_val.level_params,
    ConstantInfo::InductInfo(val) => &val.constant_val.level_params,
    ConstantInfo::CtorInfo(val) => &val.constant_val.level_params,
    ConstantInfo::RecInfo(val) => &val.constant_val.level_params,
  };
  ConsList::from_iterator(univs.iter().cloned())
}

#[derive(Default)]
#[allow(clippy::type_complexity)]
struct GroundState {
  expr_cache: FxHashSet<(ConsList<Name>, ConsList<Name>, Expr)>,
  univ_cache: FxHashSet<(ConsList<Name>, Level)>,
}

fn ground_const<'a>(
  constant: &'a ConstantInfo,
  const_map: &'a ConstMap,
  univs: ConsList<Name>,
  binds: ConsList<Name>,
  stt: &mut GroundState,
) -> Result<(), GroundError<'a>> {
  match constant {
    ConstantInfo::AxiomInfo(val) => {
      ground_expr(&val.constant_val.typ, const_map, univs, binds, stt)
    },
    ConstantInfo::DefnInfo(val) => {
      ground_expr(
        &val.constant_val.typ,
        const_map,
        univs.clone(),
        binds.clone(),
        stt,
      )?;
      ground_expr(&val.value, const_map, univs, binds, stt)
    },
    ConstantInfo::ThmInfo(val) => {
      ground_expr(
        &val.constant_val.typ,
        const_map,
        univs.clone(),
        binds.clone(),
        stt,
      )?;
      ground_expr(&val.value, const_map, univs, binds, stt)
    },
    ConstantInfo::OpaqueInfo(val) => {
      ground_expr(
        &val.constant_val.typ,
        const_map,
        univs.clone(),
        binds.clone(),
        stt,
      )?;
      ground_expr(&val.value, const_map, univs, binds, stt)
    },
    ConstantInfo::QuotInfo(val) => {
      ground_expr(&val.constant_val.typ, const_map, univs, binds, stt)
    },
    ConstantInfo::InductInfo(val) => {
      for ctor in &val.ctors {
        match const_map.get(ctor) {
          Some(ConstantInfo::CtorInfo(_)) => (),
          c => return Err(GroundError::Indc(val, c)),
        }
      }
      ground_expr(&val.constant_val.typ, const_map, univs, binds, stt)
    },
    ConstantInfo::CtorInfo(val) => {
      ground_expr(&val.constant_val.typ, const_map, univs, binds, stt)
    },
    ConstantInfo::RecInfo(val) => {
      for rule in &val.rules {
        ground_expr(&rule.rhs, const_map, univs.clone(), binds.clone(), stt)?;
      }
      ground_expr(&val.constant_val.typ, const_map, univs, binds, stt)
    },
  }
}

fn ground_expr<'a>(
  expr: &Expr,
  const_map: &'a ConstMap,
  univs: ConsList<Name>,
  binds: ConsList<Name>,
  stt: &mut GroundState,
) -> Result<(), GroundError<'a>> {
  let key = (univs.clone(), binds.clone(), expr.clone());
  if stt.expr_cache.contains(&key) {
    return Ok(());
  }
  stt.expr_cache.insert(key);
  match expr.as_data() {
    ExprData::Mdata(_, e, _) => ground_expr(e, const_map, univs, binds, stt),
    ExprData::Bvar(idx, _) => {
      let mut idx_bytes = idx.to_le_bytes();
      if idx_bytes.len() > size_of::<usize>() {
        return Err(GroundError::Idx(idx.clone()));
      }
      idx_bytes.resize(size_of::<usize>(), 0);
      let idx_usize = usize::from_le_bytes(idx_bytes.try_into().unwrap());
      if idx_usize >= binds.len() {
        return Err(GroundError::Var(expr.clone(), binds.clone()));
      }
      Ok(())
    },
    ExprData::Sort(level, _) => ground_level(level, univs, stt),
    ExprData::Const(name, levels, _) => {
      for level in levels {
        ground_level(level, univs.clone(), stt)?;
      }
      if !const_map.contains_key(name)
        && name != &Name::str(Name::anon(), "_obj".to_string())
        && name != &Name::str(Name::anon(), "_neutral".to_string())
        && name != &Name::str(Name::anon(), "_unreachable".to_string())
      {
        return Err(GroundError::Ref(name.clone()));
      }
      Ok(())
    },
    ExprData::App(f, a, _) => {
      ground_expr(f, const_map, univs.clone(), binds.clone(), stt)?;
      ground_expr(a, const_map, univs, binds, stt)
    },
    ExprData::Lam(n, t, b, ..) | ExprData::ForallE(n, t, b, ..) => {
      ground_expr(t, const_map, univs.clone(), binds.clone(), stt)?;
      ground_expr(b, const_map, univs, binds.cons(n.clone()), stt)
    },
    ExprData::LetE(n, t, v, b, ..) => {
      ground_expr(t, const_map, univs.clone(), binds.clone(), stt)?;
      ground_expr(v, const_map, univs.clone(), binds.clone(), stt)?;
      ground_expr(b, const_map, univs, binds.cons(n.clone()), stt)
    },
    ExprData::Proj(name, _, e, _) => {
      if !const_map.contains_key(name) {
        return Err(GroundError::Ref(name.clone()));
      }
      ground_expr(e, const_map, univs, binds, stt)
    },
    ExprData::Lit(..) => Ok(()),
    ExprData::Mvar(..) => Err(GroundError::MVar(expr.clone())),
    ExprData::Fvar(..) => Err(GroundError::Var(expr.clone(), binds.clone())),
  }
}

fn ground_level<'a>(
  level: &Level,
  univs: ConsList<Name>,
  stt: &mut GroundState,
) -> Result<(), GroundError<'a>> {
  let key = (univs.clone(), level.clone());
  if stt.univ_cache.contains(&key) {
    return Ok(());
  }
  stt.univ_cache.insert(key);
  match level.as_data() {
    LevelData::Zero => Ok(()),
    LevelData::Succ(x) => ground_level(x, univs, stt),
    LevelData::Max(x, y) | LevelData::Imax(x, y) => {
      ground_level(x, univs.clone(), stt)?;
      ground_level(y, univs, stt)
    },
    LevelData::Param(n) => {
      if !univs.contains(n) {
        return Err(GroundError::Level(level.clone(), univs.clone()));
      }
      Ok(())
    },
    LevelData::Mvar(_) => Err(GroundError::Level(level.clone(), univs.clone())),
  }
}
