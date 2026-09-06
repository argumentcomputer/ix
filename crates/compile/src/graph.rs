//! Builds a reference graph from a Lean environment.
//!
//! The graph tracks which constants reference which other constants, maintaining
//! both forward (`out_refs`) and reverse (`in_refs`) edges. This is used to
//! compute SCCs (strongly connected components) for mutual block detection.
//! Construction is parallelized via rayon.

use rayon::iter::{IntoParallelIterator, ParallelIterator};
use rustc_hash::{FxHashMap, FxHashSet};
use std::collections::hash_map::Entry;

use ix_common::env::{ConstantInfo, Env, Expr, ExprData, Name};

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
/// Everything the compile-env setup needs from a whole-env pass: the
/// reference graph, the immediately-ungrounded set (before transitive
/// proliferation), and the inductive mutual-block groups
/// (`all[0] → all`, for flag validation).
pub struct SetupScan {
  pub graph: RefGraph,
  pub immediate_ungrounded: FxHashMap<Name, crate::ground::GroundError>,
  pub ind_groups: FxHashMap<Name, Vec<Name>>,
}

/// Fused whole-env setup pass: one decode per constant feeding the ref
/// graph, the groundedness check, and inductive-group collection.
/// The compile path's lazy environment can decode a constant on each
/// access, so one scan avoids the repeat decodes of separate graph,
/// grounding, and inductive-group scans. Outputs match those passes.
///
/// Fold directly into chunk-local maps instead of allocating and merging
/// graph fragments for every constant. Reverse edges to a common dependency
/// share one set within the chunk; only completed chunk maps are reduced.
/// Rayon chooses the chunks dynamically, retaining work-stealing balance
/// when some constants take much longer to decode and traverse than others.
pub fn setup_scan(env: &Env) -> SetupScan {
  #[derive(Default)]
  struct Acc {
    out_refs: RefMap,
    in_refs: RefMap,
    ungrounded: FxHashMap<Name, crate::ground::GroundError>,
    ind_groups: FxHashMap<Name, Vec<Name>>,
  }

  let names: Vec<&Name> = env.keys().collect();
  let acc = names
    .into_par_iter()
    .fold(Acc::default, |mut acc, name| {
      let Some(constant) = env.get(name) else {
        return acc;
      };
      let deps = get_constant_info_references(&constant);
      // Keep an empty reverse-edge entry even for an isolated constant.
      // Missing referenced names also retain their incoming edges, as in
      // the reference graph used by ungroundedness propagation.
      acc.in_refs.entry(name.clone()).or_default();
      for dep in &deps {
        acc.in_refs.entry(dep.clone()).or_default().insert(name.clone());
      }
      acc.out_refs.insert(name.clone(), deps);
      if let Err(err) = crate::ground::ground_const_check(&constant, env) {
        acc.ungrounded.insert(name.clone(), err);
      }
      // Members of one mutual family share the same `all`, so
      // first-wins insertion is value-identical regardless of which
      // member lands first.
      if let ConstantInfo::InductInfo(v) = &*constant
        && let Some(first) = v.all.first()
      {
        acc.ind_groups.entry(first.clone()).or_insert_with(|| v.all.clone());
      }
      acc
    })
    .reduce(Acc::default, |mut l, r| {
      l.out_refs = merge_ref_maps(l.out_refs, r.out_refs);
      l.in_refs = merge_ref_maps(l.in_refs, r.in_refs);
      l.ungrounded.extend(r.ungrounded);
      for (k, v) in r.ind_groups {
        l.ind_groups.entry(k).or_insert(v);
      }
      l
    });

  SetupScan {
    graph: RefGraph { out_refs: acc.out_refs, in_refs: acc.in_refs },
    immediate_ungrounded: acc.ungrounded,
    ind_groups: acc.ind_groups,
  }
}

/// Size-aware map union (drain the smaller side into the bigger).
fn merge_ref_maps(l: RefMap, r: RefMap) -> RefMap {
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
}

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

  let names: Vec<&Name> = env.keys().collect();
  let (out_refs, in_refs) = names
    .into_par_iter()
    .filter_map(|name| {
      let constant = env.get(name)?;
      let deps = get_constant_info_references(&constant);
      let in_refs = mk_in_refs(name, &deps);
      let out_refs = RefMap::from_iter([(name.clone(), deps)]);
      Some((out_refs, in_refs))
    })
    .reduce(
      || (RefMap::default(), RefMap::default()),
      |(out_l, in_l), (out_r, in_r)| (merge(out_l, out_r), merge(in_l, in_r)),
    );

  //assert_eq!(env.len(), out_refs.len());
  //assert_eq!(out_refs.len(), in_refs.len());
  RefGraph { out_refs, in_refs }
}

pub fn get_constant_info_references(constant_info: &ConstantInfo) -> NameSet {
  let mut acc = NameSet::default();
  let mut visited: FxHashSet<&Expr> = FxHashSet::default();
  match constant_info {
    ConstantInfo::AxiomInfo(val) => {
      collect_expr_references(&val.cnst.typ, &mut visited, &mut acc);
    },
    ConstantInfo::DefnInfo(val) => {
      collect_expr_references(&val.cnst.typ, &mut visited, &mut acc);
      collect_expr_references(&val.value, &mut visited, &mut acc);
    },
    ConstantInfo::ThmInfo(val) => {
      collect_expr_references(&val.cnst.typ, &mut visited, &mut acc);
      collect_expr_references(&val.value, &mut visited, &mut acc);
    },
    ConstantInfo::OpaqueInfo(val) => {
      collect_expr_references(&val.cnst.typ, &mut visited, &mut acc);
      collect_expr_references(&val.value, &mut visited, &mut acc);
    },
    ConstantInfo::QuotInfo(val) => {
      collect_expr_references(&val.cnst.typ, &mut visited, &mut acc);
    },
    ConstantInfo::InductInfo(val) => {
      collect_expr_references(&val.cnst.typ, &mut visited, &mut acc);
      acc.extend(val.ctors.iter().cloned());
    },
    ConstantInfo::CtorInfo(val) => {
      collect_expr_references(&val.cnst.typ, &mut visited, &mut acc);
      acc.insert(val.induct.clone());
    },
    ConstantInfo::RecInfo(val) => {
      collect_expr_references(&val.cnst.typ, &mut visited, &mut acc);
      for rule in &val.rules {
        acc.insert(rule.ctor.clone());
        collect_expr_references(&rule.rhs, &mut visited, &mut acc);
      }
    },
  }
  acc
}

/// Iterative DAG walk pushing every `Const`/`Proj` head into one shared
/// accumulator. `visited` keys on `Expr`'s digest-backed `Hash`/`Eq`
/// (Arc pointer fast path), so each distinct subterm — structurally
/// shared or not — is expanded once, exactly the dedup the old
/// per-constant memo provided. Θ(n + r) total: the old walk returned a
/// fresh `NameSet` per node and merged/cloned it into every parent
/// (Θ(n·r) allocations on ref-heavy constants). This feeds both
/// compile's `setup_scan` and decompile's Pass-2 ingress BFS. The
/// accumulated set is value-identical to the old result; no downstream
/// consumer reads set iteration order into output bytes (SCC members
/// and serialized sections are canonically re-sorted).
fn collect_expr_references<'a>(
  expr: &'a Expr,
  visited: &mut FxHashSet<&'a Expr>,
  acc: &mut NameSet,
) {
  let mut stack: Vec<&'a Expr> = vec![expr];
  while let Some(e) = stack.pop() {
    if !visited.insert(e) {
      continue;
    }
    match e.as_data() {
      ExprData::Const(name, ..) => {
        acc.insert(name.clone());
      },
      ExprData::App(f, a, _) => {
        stack.push(f);
        stack.push(a);
      },
      ExprData::Lam(_, typ, body, ..) | ExprData::ForallE(_, typ, body, ..) => {
        stack.push(typ);
        stack.push(body);
      },
      ExprData::LetE(_, typ, value, body, ..) => {
        stack.push(typ);
        stack.push(value);
        stack.push(body);
      },
      ExprData::Mdata(_, inner, _) => stack.push(inner),
      ExprData::Proj(type_name, _, inner, _) => {
        acc.insert(type_name.clone());
        stack.push(inner);
      },
      _ => {},
    }
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use bignat::Nat;
  use ix_common::env::*;

  fn n(s: &str) -> Name {
    Name::str(Name::anon(), s.to_string())
  }

  fn sort0() -> Expr {
    Expr::sort(Level::zero())
  }

  fn mk_cv(name: &str) -> ConstantVal {
    ConstantVal { name: n(name), level_params: vec![], typ: sort0() }
  }

  /// Frozen per-constant map/reduce implementation for differential tests
  /// and the opt-in performance comparison below.
  fn setup_scan_reference(env: &Env) -> SetupScan {
    let empty = || SetupScan {
      graph: RefGraph::default(),
      immediate_ungrounded: FxHashMap::default(),
      ind_groups: FxHashMap::default(),
    };
    let names: Vec<_> = env.keys().collect();
    names
      .into_par_iter()
      .filter_map(|name| {
        let constant = env.get(name)?;
        let deps = get_constant_info_references(&constant);
        let mut scan = empty();
        scan.graph.in_refs =
          RefMap::from_iter([(name.clone(), NameSet::default())]);
        for dep in &deps {
          match scan.graph.in_refs.entry(dep.clone()) {
            Entry::Vacant(entry) => {
              entry.insert(NameSet::from_iter([name.clone()]));
            },
            Entry::Occupied(mut entry) => {
              entry.get_mut().insert(name.clone());
            },
          }
        }
        scan.graph.out_refs = RefMap::from_iter([(name.clone(), deps)]);
        if let Err(err) = crate::ground::ground_const_check(&constant, env) {
          scan.immediate_ungrounded.insert(name.clone(), err);
        }
        if let ConstantInfo::InductInfo(v) = &*constant
          && let Some(first) = v.all.first()
        {
          scan.ind_groups.insert(first.clone(), v.all.clone());
        }
        Some(scan)
      })
      .reduce(empty, |mut l, r| {
        l.graph.out_refs = merge_ref_maps(l.graph.out_refs, r.graph.out_refs);
        l.graph.in_refs = merge_ref_maps(l.graph.in_refs, r.graph.in_refs);
        l.immediate_ungrounded.extend(r.immediate_ungrounded);
        for (k, v) in r.ind_groups {
          l.ind_groups.entry(k).or_insert(v);
        }
        l
      })
  }

  fn assert_same_scan(actual: &SetupScan, expected: &SetupScan) {
    assert_eq!(actual.graph.out_refs, expected.graph.out_refs);
    assert_eq!(actual.graph.in_refs, expected.graph.in_refs);
    assert_eq!(actual.ind_groups, expected.ind_groups);
    assert_eq!(
      actual.immediate_ungrounded.len(),
      expected.immediate_ungrounded.len()
    );
    for (name, expected) in &expected.immediate_ungrounded {
      assert_eq!(
        format!("{:?}", actual.immediate_ungrounded.get(name).unwrap()),
        format!("{expected:?}"),
        "grounding error for {name}",
      );
    }
  }

  /// Well-typed aliases with both shared and local dependencies. The input
  /// graph has no cycles, while many reverse edges meet at the same names.
  fn setup_fixture(count: usize) -> Env {
    let mut env = Env::default();
    let typ = Expr::sort(Level::succ(Level::zero()));
    for name in ["Base", "Isolated"] {
      env.insert(
        n(name),
        ConstantInfo::AxiomInfo(AxiomVal {
          cnst: ConstantVal {
            name: n(name),
            level_params: vec![],
            typ: typ.clone(),
          },
          is_unsafe: false,
        }),
      );
    }
    let names: Vec<_> = (0..count).map(|i| n(&format!("alias_{i}"))).collect();
    let base = Expr::cnst(n("Base"), vec![]);
    for (i, name) in names.iter().enumerate() {
      let mut value = base.clone();
      for offset in [1, 3, 17, 127] {
        let dep =
          i.checked_sub(offset).map_or_else(|| n("Base"), |j| names[j].clone());
        value = Expr::all(
          Name::anon(),
          Expr::cnst(dep, vec![]),
          value,
          BinderInfo::Default,
        );
      }
      env.insert(
        name.clone(),
        ConstantInfo::DefnInfo(DefinitionVal {
          cnst: ConstantVal {
            name: name.clone(),
            level_params: vec![],
            typ: typ.clone(),
          },
          value,
          hints: ReducibilityHints::Abbrev,
          safety: DefinitionSafety::Safe,
          all: vec![name.clone()],
        }),
      );
    }
    env
  }

  #[test]
  fn setup_scan_matches_reference_across_worker_counts() {
    let mut env = setup_fixture(1024);
    // Cover isolated nodes, self/cyclic edges, missing names, each family of
    // grounding error, and mutual-group deduplication across fold chunks.
    for (name, typ) in [
      ("Self", Expr::cnst(n("Self"), vec![])),
      ("CycleA", Expr::cnst(n("CycleB"), vec![])),
      ("CycleB", Expr::cnst(n("CycleA"), vec![])),
      ("Missing", Expr::cnst(n("Absent"), vec![])),
      ("Bvar", Expr::bvar(Nat::from(0u64))),
      ("Fvar", Expr::fvar(n("local"))),
      ("Mvar", Expr::mvar(n("hole"))),
      ("Universe", Expr::sort(Level::param(n("u")))),
    ] {
      env.insert(
        n(name),
        ConstantInfo::AxiomInfo(AxiomVal {
          cnst: ConstantVal { name: n(name), level_params: vec![], typ },
          is_unsafe: false,
        }),
      );
    }
    for (name, all, ctors) in [
      ("MutA", vec![n("MutA"), n("MutB")], vec![]),
      ("MutB", vec![n("MutA"), n("MutB")], vec![]),
      ("EmptyGroup", vec![], vec![]),
      ("BadCtor", vec![n("BadCtor")], vec![n("AbsentCtor")]),
    ] {
      env.insert(
        n(name),
        ConstantInfo::InductInfo(InductiveVal {
          cnst: mk_cv(name),
          num_params: Nat::from(0u64),
          num_indices: Nat::from(0u64),
          all,
          ctors,
          num_nested: Nat::from(0u64),
          is_rec: false,
          is_unsafe: false,
          is_reflexive: false,
        }),
      );
    }
    let expected = setup_scan_reference(&env);
    assert_eq!(expected.immediate_ungrounded.len(), 6);
    assert!(expected.graph.in_refs[&n("Isolated")].is_empty());
    assert_eq!(expected.ind_groups.len(), 2);
    let graph = build_ref_graph(&env);
    assert_eq!(expected.graph.out_refs, graph.out_refs);
    assert_eq!(expected.graph.in_refs, graph.in_refs);
    for workers in [1, 2, 4, 8] {
      let pool =
        rayon::ThreadPoolBuilder::new().num_threads(workers).build().unwrap();
      pool.install(|| {
        assert_same_scan(&setup_scan(&env), &expected);
        assert_same_scan(
          &setup_scan(&Env::default()),
          &setup_scan_reference(&Env::default()),
        );
      });
    }
  }

  #[test]
  fn setup_scan_fetches_each_lazy_entry_once_and_skips_unavailable_entries() {
    use std::sync::{
      Arc,
      atomic::{AtomicUsize, Ordering},
    };
    let backing = setup_fixture(256);
    let expected = setup_scan_reference(&backing);
    let mut names: Vec<_> = backing.keys().cloned().collect();
    names.push(n("Unavailable"));
    let calls = Arc::new(AtomicUsize::new(0));
    let counted = Arc::clone(&calls);
    let count = names.len();
    let env = Env::new_lazy(
      names,
      Box::new(move |name| {
        counted.fetch_add(1, Ordering::Relaxed);
        backing.get(name).map(|entry| entry.cloned())
      }),
      16,
    );
    assert_same_scan(&setup_scan(&env), &expected);
    assert_eq!(calls.load(Ordering::Relaxed), count);
  }

  #[test]
  fn setup_scan_preserves_compiled_fixture_bytes() {
    use crate::compile::{CompileOptions, compile_env_with_options};
    let source = std::sync::Arc::new(setup_fixture(32));
    for workers in [1, 4] {
      let compiled = compile_env_with_options(
        &source,
        CompileOptions { max_workers: Some(workers) },
      )
      .unwrap();
      assert!(compiled.ungrounded.is_empty());
      let mut bytes = Vec::new();
      compiled.env.put(&mut bytes).unwrap();
      // Captured from the per-constant scanner before the fold change.
      assert_eq!(
        blake3::hash(&bytes).to_hex().as_str(),
        "d0a1c1490fad7e9e9236792c62ac3697dc7d3b541e3b3db12e00b9dd29ba36ed"
      );
    }
  }

  /// Run explicitly in release mode: cargo test -p ix-compile --release
  /// setup_scan_benchmark -- --ignored --nocapture --test-threads=1
  #[test]
  #[ignore = "synthetic setup-scan timing comparison; run in release mode"]
  fn setup_scan_benchmark() {
    use std::time::{Duration, Instant};
    for count in [50_000, 250_000] {
      let env = setup_fixture(count);
      for workers in [1, 8, 32] {
        let pool =
          rayon::ThreadPoolBuilder::new().num_threads(workers).build().unwrap();
        pool.install(|| {
          assert_same_scan(&setup_scan(&env), &setup_scan_reference(&env));
          let mut elapsed = [Duration::ZERO; 2];
          for trial in 0..6 {
            // Alternate order to reduce allocator/cache warmup bias. Exclude
            // destruction, which the compiler likewise performs after setup.
            for index in [trial % 2, 1 - trial % 2] {
              let start = Instant::now();
              let result = if index == 0 {
                setup_scan_reference(&env)
              } else {
                setup_scan(&env)
              };
              elapsed[index] += start.elapsed();
              std::hint::black_box(result);
            }
          }
          eprintln!(
            "setup_scan: {} constants, {workers} workers: per-constant {:.3}s, chunked {:.3}s ({:.2}x)",
            env.len(),
            elapsed[0].as_secs_f64() / 6.0,
            elapsed[1].as_secs_f64() / 6.0,
            elapsed[0].as_secs_f64() / elapsed[1].as_secs_f64()
          );
        });
      }
    }
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
  fn inductive_all_members_are_not_graph_edges() {
    // `InductiveVal.all` is Lean source metadata. The canonical compiler
    // must still split inductive declarations into their minimal SCCs, so
    // members that do not structurally reference each other are not graph
    // dependencies merely because Lean recorded them in the same `all` list.
    let mut env = Env::default();
    for name in ["A", "B"] {
      env.insert(
        n(name),
        ConstantInfo::InductInfo(InductiveVal {
          cnst: mk_cv(name),
          num_params: Nat::from(0u64),
          num_indices: Nat::from(0u64),
          all: vec![n("A"), n("B")],
          ctors: vec![],
          num_nested: Nat::from(0u64),
          is_rec: false,
          is_unsafe: false,
          is_reflexive: false,
        }),
      );
    }

    let graph = build_ref_graph(&env);
    assert!(!graph.out_refs[&n("A")].contains(&n("B")));
    assert!(!graph.out_refs[&n("B")].contains(&n("A")));
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
    // `RecursorVal.all` is metadata; structural references come from the
    // recursor type and rules.
    assert!(!rec_out.contains(&n("T")));
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
