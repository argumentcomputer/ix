use rayon::iter::{IntoParallelRefIterator, ParallelIterator};
use rustc_hash::{FxHashMap, FxHashSet};
use std::{collections::hash_map::Entry, sync::Arc};

use crate::{
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
    ConsList::from_iter(univs.iter().cloned())
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

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum ConsList<T> {
    Nil,
    Cons(T, Arc<ConsList<T>>, usize),
}

struct ConsListIter<'a, T>(&'a ConsList<T>);
impl<'a, T> Iterator for ConsListIter<'a, T> {
    type Item = &'a T;
    fn next(&mut self) -> Option<Self::Item> {
        match &self.0 {
            ConsList::Nil => None,
            ConsList::Cons(t, tail, _) => {
                self.0 = tail;
                Some(t)
            }
        }
    }
}

impl<T> ConsList<T> {
    fn cons(&self, t: T) -> Self
    where
        T: Clone,
    {
        match self {
            Self::Nil => Self::Cons(t, Arc::new(Self::Nil), 1),
            Self::Cons(.., len) => Self::Cons(t, Arc::new(self.clone()), len + 1),
        }
    }

    fn len(&self) -> usize {
        match self {
            Self::Nil => 0,
            Self::Cons(.., len) => *len,
        }
    }

    fn iter(&self) -> impl Iterator<Item = &T> {
        ConsListIter(self)
    }

    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self
    where
        T: Clone,
        <I as IntoIterator>::IntoIter: DoubleEndedIterator,
    {
        iter.into_iter().rev().fold(Self::Nil, |acc, t| acc.cons(t))
    }

    fn contains(&self, t: &T) -> bool
    where
        T: PartialEq,
    {
        self.iter().any(|x| x == t)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_empty_list_len_and_iter() {
        let list: ConsList<i32> = ConsList::Nil;
        assert_eq!(list.len(), 0);
        assert_eq!(list.iter().count(), 0);
        assert!(list.iter().next().is_none());
    }

    #[test]
    fn test_single_element_list() {
        let list = ConsList::Nil.cons(10);
        assert_eq!(list.len(), 1);

        let collected: Vec<_> = list.iter().cloned().collect();
        assert_eq!(collected, vec![10]);
    }

    #[test]
    fn test_multiple_elements_list() {
        let list = ConsList::Nil.cons(3).cons(2).cons(1);
        assert_eq!(list.len(), 3);

        // The elements are stored in cons order (head-first)
        let collected: Vec<_> = list.iter().cloned().collect();
        assert_eq!(collected, vec![1, 2, 3]);
    }

    #[test]
    fn test_from_iter() {
        let vec = vec![1, 2, 3];
        let list = ConsList::from_iter(vec.clone());
        assert_eq!(list.len(), 3);

        let collected: Vec<_> = list.iter().cloned().collect();
        assert_eq!(collected, vec);
    }

    #[test]
    fn test_contains() {
        let list = ConsList::from_iter(vec![10, 20, 30]);

        assert!(list.contains(&10));
        assert!(list.contains(&30));
        assert!(!list.contains(&99));
    }

    #[test]
    fn test_iter_mutation_order() {
        // Ensure iterator traverses the list without altering it
        let list = ConsList::from_iter(vec![1, 2, 3]);
        let mut iter = list.iter();

        assert_eq!(iter.next(), Some(&1));
        assert_eq!(iter.next(), Some(&2));
        assert_eq!(iter.next(), Some(&3));
        assert_eq!(iter.next(), None);

        // The original list should remain unchanged
        let collected: Vec<_> = list.iter().cloned().collect();
        assert_eq!(collected, vec![1, 2, 3]);
    }

    #[test]
    fn test_clone_and_eq() {
        let list1 = ConsList::from_iter(vec![1, 2, 3]);
        let list2 = list1.clone();
        assert_eq!(list1, list2);

        let different = ConsList::from_iter(vec![1, 2]);
        assert_ne!(list1, different);
    }

    #[test]
    fn test_cons_increases_length() {
        let mut list = ConsList::Nil;
        for i in 0..5 {
            list = list.cons(i);
            assert_eq!(list.len(), i + 1);
        }

        let collected: Vec<_> = list.iter().cloned().collect();
        assert_eq!(collected, vec![4, 3, 2, 1, 0]);
    }

    #[test]
    fn test_with_strings() {
        let list = ConsList::from_iter(vec!["a", "b"]);
        assert!(list.contains(&"a"));
        assert!(!list.contains(&"c"));

        let collected: Vec<_> = list.iter().cloned().collect();
        assert_eq!(collected, vec!["a", "b"]);
    }
}
