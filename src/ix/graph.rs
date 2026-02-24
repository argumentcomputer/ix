//! Builds a reference graph from a Lean environment.
//!
//! The graph tracks which constants reference which other constants, maintaining
//! both forward (`out_refs`) and reverse (`in_refs`) edges. This is used to
//! compute SCCs (strongly connected components) for mutual block detection.
//! Construction is parallelized via rayon.

use rayon::iter::{IntoParallelRefIterator, ParallelIterator};
use rustc_hash::{FxHashMap, FxHashSet};
use std::collections::hash_map::Entry;

use crate::ix::env::{ConstantInfo, Env, Expr, ExprData, Name};

/// A set of [`Name`]s, used to represent the neighbors of a node in the reference graph.
pub type NameSet = FxHashSet<Name>;

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

/// Maps each [`Name`] to the set of [`Name`]s it is associated with.
pub type RefMap = FxHashMap<Name, NameSet>;

/// A bidirectional reference graph over [`Name`]s, storing both forward and reverse edges.
/// ```ignored
/// A ──> B ──> C <── D ──> E
/// out_refs: [(A, [B]), (B, [C]), (C, []), (D, [C, E]), (E, [])]
/// in_refs:  [(A, []), (B, [A]), (C, [B, D]), (D, []), (E, [D])]
/// ```
#[derive(Default)]
pub struct RefGraph {
  /// Maps names to the names they reference
  pub out_refs: RefMap,
  /// Maps names to the names that reference them
  pub in_refs: RefMap,
}

/// Builds a [`RefGraph`] from a Lean [`Env`] by collecting all constant references in parallel.
///
/// For each constant, extracts the set of names it references (from types, values, constructors,
/// and recursor rules), then assembles both the forward and reverse edge maps.
pub fn build_ref_graph(env: &Env) -> RefGraph {
  let mk_in_refs = |name: &Name, deps: &NameSet| -> RefMap {
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

  let (out_refs, in_refs) = env
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

  //assert_eq!(env.len(), out_refs.len());
  //assert_eq!(out_refs.len(), in_refs.len());
  RefGraph { out_refs, in_refs }
}

fn get_constant_info_references(constant_info: &ConstantInfo) -> NameSet {
  let cache = &mut FxHashMap::default();
  match constant_info {
    ConstantInfo::AxiomInfo(val) => get_expr_references(&val.cnst.typ, cache),
    ConstantInfo::DefnInfo(val) => merge_name_sets(
      get_expr_references(&val.cnst.typ, cache),
      get_expr_references(&val.value, cache),
    ),
    ConstantInfo::ThmInfo(val) => merge_name_sets(
      get_expr_references(&val.cnst.typ, cache),
      get_expr_references(&val.value, cache),
    ),
    ConstantInfo::OpaqueInfo(val) => merge_name_sets(
      get_expr_references(&val.cnst.typ, cache),
      get_expr_references(&val.value, cache),
    ),
    ConstantInfo::QuotInfo(val) => get_expr_references(&val.cnst.typ, cache),
    ConstantInfo::InductInfo(val) => {
      let name_set = get_expr_references(&val.cnst.typ, cache);
      let ctors_name_set = val.ctors.iter().cloned().collect();
      merge_name_sets(name_set, ctors_name_set)
    },
    ConstantInfo::CtorInfo(val) => {
      let mut name_set = get_expr_references(&val.cnst.typ, cache);
      name_set.insert(val.induct.clone());
      name_set
    },
    ConstantInfo::RecInfo(val) => {
      let name_set = get_expr_references(&val.cnst.typ, cache);
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
  let name_set = match expr.as_data() {
    ExprData::Const(name, ..) => NameSet::from_iter([name.clone()]),
    ExprData::App(f, a, _) => {
      let f_name_set = get_expr_references(f, cache);
      let a_name_set = get_expr_references(a, cache);
      merge_name_sets(f_name_set, a_name_set)
    },
    ExprData::Lam(_, typ, body, ..) | ExprData::ForallE(_, typ, body, ..) => {
      let typ_name_set = get_expr_references(typ, cache);
      let body_name_set = get_expr_references(body, cache);
      merge_name_sets(typ_name_set, body_name_set)
    },
    ExprData::LetE(_, typ, value, body, ..) => {
      let typ_name_set = get_expr_references(typ, cache);
      let value_name_set = get_expr_references(value, cache);
      let body_name_set = get_expr_references(body, cache);
      merge_name_sets(
        typ_name_set,
        merge_name_sets(value_name_set, body_name_set),
      )
    },
    ExprData::Mdata(_, expr, _) => get_expr_references(expr, cache),
    ExprData::Proj(type_name, _, expr, _) => {
      let mut name_set = get_expr_references(expr, cache);
      name_set.insert(type_name.clone());
      name_set
    },
    _ => NameSet::default(),
  };
  cache.insert(expr, name_set.clone());
  name_set
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::ix::env::*;
  use crate::lean::nat::Nat;

  fn n(s: &str) -> Name {
    Name::str(Name::anon(), s.to_string())
  }

  fn sort0() -> Expr {
    Expr::sort(Level::zero())
  }

  fn mk_cv(name: &str) -> ConstantVal {
    ConstantVal { name: n(name), level_params: vec![], typ: sort0() }
  }

  #[test]
  fn empty_env() {
    let env = Env::default();
    let graph = build_ref_graph(&env);
    assert!(graph.out_refs.is_empty());
    assert!(graph.in_refs.is_empty());
  }

  #[test]
  fn axiom_no_deps() {
    // Axiom A : Sort 0 — references nothing
    let mut env = Env::default();
    env.insert(
      n("A"),
      ConstantInfo::AxiomInfo(AxiomVal { cnst: mk_cv("A"), is_unsafe: false }),
    );
    let graph = build_ref_graph(&env);
    assert!(graph.out_refs[&n("A")].is_empty());
    assert!(graph.in_refs[&n("A")].is_empty());
  }

  #[test]
  fn defn_with_const_refs() {
    // B : Sort 0, defn A : B := B
    // A's type refs B, A's value refs B
    let mut env = Env::default();
    env.insert(
      n("B"),
      ConstantInfo::AxiomInfo(AxiomVal { cnst: mk_cv("B"), is_unsafe: false }),
    );
    let b_ref = Expr::cnst(n("B"), vec![]);
    env.insert(
      n("A"),
      ConstantInfo::DefnInfo(DefinitionVal {
        cnst: ConstantVal {
          name: n("A"),
          level_params: vec![],
          typ: b_ref.clone(),
        },
        value: b_ref,
        hints: ReducibilityHints::Opaque,
        safety: DefinitionSafety::Safe,
        all: vec![n("A")],
      }),
    );
    let graph = build_ref_graph(&env);
    // A references B
    assert!(graph.out_refs[&n("A")].contains(&n("B")));
    // B is referenced by A
    assert!(graph.in_refs[&n("B")].contains(&n("A")));
    // B references nothing
    assert!(graph.out_refs[&n("B")].is_empty());
  }

  #[test]
  fn inductive_includes_ctors() {
    // Inductive T with constructors T.mk1, T.mk2
    let mut env = Env::default();
    env.insert(
      n("T"),
      ConstantInfo::InductInfo(InductiveVal {
        cnst: mk_cv("T"),
        num_params: Nat::from(0u64),
        num_indices: Nat::from(0u64),
        all: vec![n("T")],
        ctors: vec![n("T.mk1"), n("T.mk2")],
        num_nested: Nat::from(0u64),
        is_rec: false,
        is_unsafe: false,
        is_reflexive: false,
      }),
    );
    // Add constructors to env so they can be referenced
    env.insert(
      n("T.mk1"),
      ConstantInfo::CtorInfo(ConstructorVal {
        cnst: mk_cv("T.mk1"),
        induct: n("T"),
        cidx: Nat::from(0u64),
        num_params: Nat::from(0u64),
        num_fields: Nat::from(0u64),
        is_unsafe: false,
      }),
    );
    env.insert(
      n("T.mk2"),
      ConstantInfo::CtorInfo(ConstructorVal {
        cnst: mk_cv("T.mk2"),
        induct: n("T"),
        cidx: Nat::from(1u64),
        num_params: Nat::from(0u64),
        num_fields: Nat::from(0u64),
        is_unsafe: false,
      }),
    );

    let graph = build_ref_graph(&env);
    // T references T.mk1 and T.mk2 (from ctors list)
    assert!(graph.out_refs[&n("T")].contains(&n("T.mk1")));
    assert!(graph.out_refs[&n("T")].contains(&n("T.mk2")));
  }

  #[test]
  fn ctor_includes_induct() {
    // Constructor T.mk references its parent T
    let mut env = Env::default();
    env.insert(
      n("T"),
      ConstantInfo::AxiomInfo(AxiomVal { cnst: mk_cv("T"), is_unsafe: false }),
    );
    env.insert(
      n("T.mk"),
      ConstantInfo::CtorInfo(ConstructorVal {
        cnst: mk_cv("T.mk"),
        induct: n("T"),
        cidx: Nat::from(0u64),
        num_params: Nat::from(0u64),
        num_fields: Nat::from(0u64),
        is_unsafe: false,
      }),
    );
    let graph = build_ref_graph(&env);
    assert!(graph.out_refs[&n("T.mk")].contains(&n("T")));
  }

  #[test]
  fn in_refs_bidirectional() {
    // A -> B, C -> B
    let mut env = Env::default();
    let b_ref = Expr::cnst(n("B"), vec![]);
    env.insert(
      n("B"),
      ConstantInfo::AxiomInfo(AxiomVal { cnst: mk_cv("B"), is_unsafe: false }),
    );
    env.insert(
      n("A"),
      ConstantInfo::AxiomInfo(AxiomVal {
        cnst: ConstantVal {
          name: n("A"),
          level_params: vec![],
          typ: b_ref.clone(),
        },
        is_unsafe: false,
      }),
    );
    env.insert(
      n("C"),
      ConstantInfo::AxiomInfo(AxiomVal {
        cnst: ConstantVal { name: n("C"), level_params: vec![], typ: b_ref },
        is_unsafe: false,
      }),
    );
    let graph = build_ref_graph(&env);
    // B's in_refs should contain both A and C
    let b_in = &graph.in_refs[&n("B")];
    assert!(b_in.contains(&n("A")));
    assert!(b_in.contains(&n("C")));
  }

  #[test]
  fn recursor_refs_rules() {
    // Recursor T.rec with a rule for T.mk whose rhs references Q
    let mut env = Env::default();
    env.insert(
      n("T.mk"),
      ConstantInfo::AxiomInfo(AxiomVal {
        cnst: mk_cv("T.mk"),
        is_unsafe: false,
      }),
    );
    env.insert(
      n("Q"),
      ConstantInfo::AxiomInfo(AxiomVal { cnst: mk_cv("Q"), is_unsafe: false }),
    );
    env.insert(
      n("T.rec"),
      ConstantInfo::RecInfo(RecursorVal {
        cnst: mk_cv("T.rec"),
        all: vec![n("T")],
        num_params: Nat::from(0u64),
        num_indices: Nat::from(0u64),
        num_motives: Nat::from(1u64),
        num_minors: Nat::from(1u64),
        rules: vec![RecursorRule {
          ctor: n("T.mk"),
          n_fields: Nat::from(0u64),
          rhs: Expr::cnst(n("Q"), vec![]),
        }],
        k: false,
        is_unsafe: false,
      }),
    );
    let graph = build_ref_graph(&env);
    let rec_out = &graph.out_refs[&n("T.rec")];
    // References the ctor from the rule
    assert!(rec_out.contains(&n("T.mk")));
    // References Q from the rule's rhs
    assert!(rec_out.contains(&n("Q")));
  }

  #[test]
  fn expr_references_through_app_lam_let() {
    // Test that get_expr_references traverses App, Lam, LetE, Proj
    let mut env = Env::default();
    env.insert(
      n("X"),
      ConstantInfo::AxiomInfo(AxiomVal { cnst: mk_cv("X"), is_unsafe: false }),
    );
    env.insert(
      n("Y"),
      ConstantInfo::AxiomInfo(AxiomVal { cnst: mk_cv("Y"), is_unsafe: false }),
    );
    env.insert(
      n("Z"),
      ConstantInfo::AxiomInfo(AxiomVal { cnst: mk_cv("Z"), is_unsafe: false }),
    );
    // Build: fun (_ : X) => let _ : Y := #0 in Z
    let x_ref = Expr::cnst(n("X"), vec![]);
    let y_ref = Expr::cnst(n("Y"), vec![]);
    let z_ref = Expr::cnst(n("Z"), vec![]);
    let body = Expr::letE(
      Name::anon(),
      y_ref,
      Expr::bvar(Nat::from(0u64)),
      z_ref,
      false,
    );
    let lam = Expr::lam(Name::anon(), x_ref, body, BinderInfo::Default);
    env.insert(
      n("W"),
      ConstantInfo::AxiomInfo(AxiomVal {
        cnst: ConstantVal { name: n("W"), level_params: vec![], typ: lam },
        is_unsafe: false,
      }),
    );
    let graph = build_ref_graph(&env);
    let w_out = &graph.out_refs[&n("W")];
    assert!(w_out.contains(&n("X")));
    assert!(w_out.contains(&n("Y")));
    assert!(w_out.contains(&n("Z")));
  }

  #[test]
  fn proj_references_type_name() {
    // Proj references the type name it projects from
    let mut env = Env::default();
    env.insert(
      n("S"),
      ConstantInfo::AxiomInfo(AxiomVal { cnst: mk_cv("S"), is_unsafe: false }),
    );
    let proj_expr =
      Expr::proj(n("S"), Nat::from(0u64), Expr::bvar(Nat::from(0u64)));
    env.insert(
      n("P"),
      ConstantInfo::AxiomInfo(AxiomVal {
        cnst: ConstantVal {
          name: n("P"),
          level_params: vec![],
          typ: proj_expr,
        },
        is_unsafe: false,
      }),
    );
    let graph = build_ref_graph(&env);
    assert!(graph.out_refs[&n("P")].contains(&n("S")));
  }
}
