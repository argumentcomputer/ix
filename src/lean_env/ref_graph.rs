use rayon::iter::{IntoParallelRefIterator, ParallelIterator};
use rustc_hash::{FxHashMap, FxHashSet};
use std::{collections::hash_map::Entry, sync::Arc};

use crate::lean_env::{ConstMap, ConstantInfo, Expr, Name};

pub type NameSet = FxHashSet<Arc<Name>>;

/// Absorbs the elements of the smaller [`NameSet`] into the bigger one and returns
/// the merged set.
pub fn merge_name_sets(mut a: NameSet, mut b: NameSet) -> NameSet {
  if a.len() < b.len() {
    b.extend(a);
    b
  } else {
    a.extend(b);
    a
  }
}

/// A general-purpose map from names to name sets.
pub type RefMap = FxHashMap<Arc<Name>, NameSet>;

/// A reference graph of names.
/// ```ignored
/// A ──> B ──> C <── D ──> E
/// out_refs: [(A, [B]), (B, [C]), (C, []), (D, [C, E]), (E, [])]
/// in_refs:  [(A, []), (B, [A]), (C, [B, D]), (D, []), (E, [D])]
/// ```
#[derive(Default)]
pub struct RefGraph {
  /// Maps names to names referenced by them.
  pub out_refs: RefMap,
  /// Maps names to names that reference them.
  pub in_refs: RefMap,
}

pub fn build_ref_graph(const_map: &ConstMap) -> RefGraph {
  let mk_in_refs = |name: &Arc<Name>, deps: &NameSet| -> RefMap {
    let mut in_refs = RefMap::from_iter([(name.clone(), NameSet::default())]);
    for dep in deps {
      match in_refs.entry(dep.clone()) {
        Entry::Vacant(entry) => {
          entry.insert(NameSet::from_iter([name.clone()]));
        },
        Entry::Occupied(mut entry) => {
          entry.get_mut().insert(name.clone());
        },
      }
    }
    in_refs
  };

  let merge = |l: RefMap, r: RefMap| -> RefMap {
    let (smaller, mut bigger) = if l.len() < r.len() { (l, r) } else { (r, l) };
    for (name, set) in smaller {
      match bigger.entry(name) {
        Entry::Vacant(entry) => {
          entry.insert(set);
        },
        Entry::Occupied(mut entry) => {
          entry.get_mut().extend(set);
        },
      }
    }
    bigger
  };

  let (out_refs, in_refs) = const_map
    .par_iter()
    .map(|(name, constant)| {
      let deps = get_constant_info_references(constant);
      let in_refs = mk_in_refs(name, &deps);
      let out_refs = RefMap::from_iter([(name.clone(), deps)]);
      (out_refs, in_refs)
    })
    .reduce(
      || (RefMap::default(), RefMap::default()),
      |(out_l, in_l), (out_r, in_r)| (merge(out_l, out_r), merge(in_l, in_r)),
    );

  assert_eq!(const_map.len(), out_refs.len());
  assert_eq!(out_refs.len(), in_refs.len());
  RefGraph { out_refs, in_refs }
}

fn get_constant_info_references(constant_info: &ConstantInfo) -> NameSet {
  let cache = &mut FxHashMap::default();
  match constant_info {
    ConstantInfo::AxiomInfo(val) => {
      get_expr_references(&val.constant_val.typ, cache)
    },
    ConstantInfo::DefnInfo(val) => merge_name_sets(
      get_expr_references(&val.constant_val.typ, cache),
      get_expr_references(&val.value, cache),
    ),
    ConstantInfo::ThmInfo(val) => merge_name_sets(
      get_expr_references(&val.constant_val.typ, cache),
      get_expr_references(&val.value, cache),
    ),
    ConstantInfo::OpaqueInfo(val) => merge_name_sets(
      get_expr_references(&val.constant_val.typ, cache),
      get_expr_references(&val.value, cache),
    ),
    ConstantInfo::QuotInfo(val) => {
      get_expr_references(&val.constant_val.typ, cache)
    },
    ConstantInfo::InductInfo(val) => {
      let name_set = get_expr_references(&val.constant_val.typ, cache);
      let ctors_name_set = val.ctors.iter().cloned().collect();
      merge_name_sets(name_set, ctors_name_set)
    },
    ConstantInfo::CtorInfo(val) => {
      let mut name_set = get_expr_references(&val.constant_val.typ, cache);
      name_set.insert(val.induct.clone());
      name_set
    },
    ConstantInfo::RecInfo(val) => {
      let name_set = get_expr_references(&val.constant_val.typ, cache);
      val.rules.iter().fold(name_set, |mut acc, rule| {
        acc.insert(rule.ctor.clone());
        merge_name_sets(acc, get_expr_references(&rule.rhs, cache))
      })
    },
  }
}

fn get_expr_references<'a>(
  expr: &'a Expr,
  cache: &mut FxHashMap<&'a Expr, NameSet>,
) -> NameSet {
  if let Some(cached) = cache.get(expr) {
    return cached.clone();
  }
  let name_set = match expr {
    Expr::Const(name, ..) => NameSet::from_iter([name.clone()]),
    Expr::App(f, a, _) => {
      let f_name_set = get_expr_references(f, cache);
      let a_name_set = get_expr_references(a, cache);
      merge_name_sets(f_name_set, a_name_set)
    },
    Expr::Lam(_, typ, body, ..) | Expr::ForallE(_, typ, body, ..) => {
      let typ_name_set = get_expr_references(typ, cache);
      let body_name_set = get_expr_references(body, cache);
      merge_name_sets(typ_name_set, body_name_set)
    },
    Expr::LetE(_, typ, value, body, ..) => {
      let typ_name_set = get_expr_references(typ, cache);
      let value_name_set = get_expr_references(value, cache);
      let body_name_set = get_expr_references(body, cache);
      merge_name_sets(
        typ_name_set,
        merge_name_sets(value_name_set, body_name_set),
      )
    },
    Expr::Mdata(_, expr, _) | Expr::Proj(_, _, expr, _) => {
      get_expr_references(expr, cache)
    },
    _ => NameSet::default(),
  };
  cache.insert(expr, name_set.clone());
  name_set
}
