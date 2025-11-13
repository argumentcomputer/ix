use rayon::iter::{IntoParallelRefIterator, ParallelIterator};
use rustc_hash::{FxHashMap, FxHashSet};
use std::{collections::hash_map::Entry, sync::Arc};

use crate::{
    cons_list::ConsList,
    lean::nat::Nat,
    lean_env::{ConstMap, ConstantInfo, Expr, InductiveVal, Level, Name, ref_graph::RefMap},
};

pub enum GroundError<'a> {
    Level(Arc<Level>, ConsList<Arc<Name>>),
    Ref(Arc<Name>),
    MVar(Arc<Expr>),
    Var(Arc<Expr>, ConsList<Arc<Name>>),
    Indc(&'a InductiveVal, Option<&'a ConstantInfo>),
    Idx(Nat),
}

pub fn ground_consts<'a>(
    const_map: &'a ConstMap,
    in_refs: &RefMap,
) -> FxHashMap<Arc<Name>, GroundError<'a>> {
    // Collect immediate ungrounded constants.
    let mut ungrounded: FxHashMap<_, _> = const_map
        .par_iter()
        .filter_map(|(name, constant)| {
            let univs = const_univs(constant);
            let mut stt = GroundState::default();
            if let Err(err) = ground_const(constant, const_map, univs, ConsList::Nil, &mut stt) {
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

fn const_univs(constant: &ConstantInfo) -> ConsList<Arc<Name>> {
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
    expr_cache: FxHashSet<(ConsList<Arc<Name>>, ConsList<Arc<Name>>, Arc<Expr>)>,
    univ_cache: FxHashSet<(ConsList<Arc<Name>>, Arc<Level>)>,
}

fn ground_const<'a>(
    constant: &'a ConstantInfo,
    const_map: &'a ConstMap,
    univs: ConsList<Arc<Name>>,
    binds: ConsList<Arc<Name>>,
    stt: &mut GroundState,
) -> Result<(), GroundError<'a>> {
    match constant {
        ConstantInfo::AxiomInfo(val) => {
            ground_expr(val.constant_val.typ.clone(), const_map, univs, binds, stt)
        }
        ConstantInfo::DefnInfo(val) => {
            ground_expr(
                val.constant_val.typ.clone(),
                const_map,
                univs.clone(),
                binds.clone(),
                stt,
            )?;
            ground_expr(val.value.clone(), const_map, univs, binds, stt)
        }
        ConstantInfo::ThmInfo(val) => {
            ground_expr(
                val.constant_val.typ.clone(),
                const_map,
                univs.clone(),
                binds.clone(),
                stt,
            )?;
            ground_expr(val.value.clone(), const_map, univs, binds, stt)
        }
        ConstantInfo::OpaqueInfo(val) => {
            ground_expr(
                val.constant_val.typ.clone(),
                const_map,
                univs.clone(),
                binds.clone(),
                stt,
            )?;
            ground_expr(val.value.clone(), const_map, univs, binds, stt)
        }
        ConstantInfo::QuotInfo(val) => {
            ground_expr(val.constant_val.typ.clone(), const_map, univs, binds, stt)
        }
        ConstantInfo::InductInfo(val) => {
            for ctor in &val.ctors {
                match const_map.get(ctor) {
                    Some(ConstantInfo::CtorInfo(_)) => (),
                    c => return Err(GroundError::Indc(val, c)),
                }
            }
            ground_expr(val.constant_val.typ.clone(), const_map, univs, binds, stt)
        }
        ConstantInfo::CtorInfo(val) => {
            ground_expr(val.constant_val.typ.clone(), const_map, univs, binds, stt)
        }
        ConstantInfo::RecInfo(val) => {
            for rule in &val.rules {
                ground_expr(
                    rule.rhs.clone(),
                    const_map,
                    univs.clone(),
                    binds.clone(),
                    stt,
                )?;
            }
            ground_expr(val.constant_val.typ.clone(), const_map, univs, binds, stt)
        }
    }
}

fn ground_expr<'a>(
    expr: Arc<Expr>,
    const_map: &'a ConstMap,
    univs: ConsList<Arc<Name>>,
    binds: ConsList<Arc<Name>>,
    stt: &mut GroundState,
) -> Result<(), GroundError<'a>> {
    let key = (univs.clone(), binds.clone(), expr.clone());
    if stt.expr_cache.contains(&key) {
        return Ok(());
    }
    stt.expr_cache.insert(key);
    match expr.as_ref() {
        Expr::Mdata(_, e, _) => ground_expr(e.clone(), const_map, univs, binds, stt),
        Expr::Bvar(idx, _) => {
            let mut idx_bytes = idx.to_le_bytes();
            if idx_bytes.len() > size_of::<usize>() {
                return Err(GroundError::Idx(idx.clone()));
            }
            idx_bytes.resize(size_of::<usize>(), 0);
            let idx_usize = usize::from_le_bytes(idx_bytes.try_into().unwrap());
            if idx_usize >= binds.len() {
                return Err(GroundError::Var(expr, binds.clone()));
            }
            Ok(())
        }
        Expr::Sort(level, _) => ground_level(level.clone(), univs, stt),
        Expr::Const(name, levels, _) => {
            for level in levels {
                ground_level(level.clone(), univs.clone(), stt)?;
            }
            if !const_map.contains_key(name)
                && name.as_ref() != &Name::mk_str(Name::Anonymous.into(), "_obj".to_string())
                && name.as_ref() != &Name::mk_str(Name::Anonymous.into(), "_neutral".to_string())
                && name.as_ref()
                    != &Name::mk_str(Name::Anonymous.into(), "_unreachable".to_string())
            {
                return Err(GroundError::Ref(name.clone()));
            }
            Ok(())
        }
        Expr::App(f, a, _) => {
            ground_expr(f.clone(), const_map, univs.clone(), binds.clone(), stt)?;
            ground_expr(a.clone(), const_map, univs, binds, stt)
        }
        Expr::Lam(n, t, b, ..) | Expr::ForallE(n, t, b, ..) => {
            ground_expr(t.clone(), const_map, univs.clone(), binds.clone(), stt)?;
            ground_expr(b.clone(), const_map, univs, binds.cons(n.clone()), stt)
        }
        Expr::LetE(n, t, v, b, ..) => {
            ground_expr(t.clone(), const_map, univs.clone(), binds.clone(), stt)?;
            ground_expr(v.clone(), const_map, univs.clone(), binds.clone(), stt)?;
            ground_expr(b.clone(), const_map, univs, binds.cons(n.clone()), stt)
        }
        Expr::Proj(name, _, e, _) => {
            if !const_map.contains_key(name) {
                return Err(GroundError::Ref(name.clone()));
            }
            ground_expr(e.clone(), const_map, univs, binds, stt)
        }
        Expr::Lit(..) => Ok(()),
        Expr::Mvar(..) => Err(GroundError::MVar(expr)),
        Expr::Fvar(..) => Err(GroundError::Var(expr, binds.clone())),
    }
}

fn ground_level<'a>(
    level: Arc<Level>,
    univs: ConsList<Arc<Name>>,
    stt: &mut GroundState,
) -> Result<(), GroundError<'a>> {
    let key = (univs.clone(), level.clone());
    if stt.univ_cache.contains(&key) {
        return Ok(());
    }
    stt.univ_cache.insert(key);
    match level.as_ref() {
        Level::Zero => Ok(()),
        Level::Succ(x) => ground_level(x.clone(), univs, stt),
        Level::Max(x, y) | Level::Imax(x, y) => {
            ground_level(x.clone(), univs.clone(), stt)?;
            ground_level(y.clone(), univs, stt)
        }
        Level::Param(n) => {
            if !univs.contains(n) {
                return Err(GroundError::Level(level, univs.clone()));
            }
            Ok(())
        }
        Level::Mvar(_) => Err(GroundError::Level(level, univs.clone())),
    }
}
