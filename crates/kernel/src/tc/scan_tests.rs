//! Differential and work-bound tests for syntactic expression inspection.

use super::*;
use crate::expr::FVarId;
use crate::mode::{Anon, Meta};
use bignat::Nat;
use ix_common::env::{BinderInfo, Name};

// Frozen tree walker: keep it independent of the DAG-aware implementation.
fn mentions_reference<M: KernelMode>(e: &KExpr<M>, addr: &Address) -> bool {
  let mut stack = vec![e];
  while let Some(e) = stack.pop() {
    match e.data() {
      ExprData::Const(id, _, _) => {
        if &id.addr == addr {
          return true;
        }
      },
      ExprData::App(f, a, _) => stack.extend([f, a]),
      ExprData::Lam(_, _, t, b, _) | ExprData::All(_, _, t, b, _) => {
        stack.extend([t, b]);
      },
      ExprData::Let(_, t, v, b, _, _) => stack.extend([t, v, b]),
      ExprData::Prj(id, _, v, _) => {
        if &id.addr == addr {
          return true;
        }
        stack.push(v);
      },
      ExprData::Var(..)
      | ExprData::FVar(..)
      | ExprData::Sort(..)
      | ExprData::Nat(..)
      | ExprData::Str(..) => {},
    }
  }
  false
}

fn differential<M: KernelMode>() {
  let a = Address::hash(b"A");
  let b = Address::hash(b"B");
  let missing = Address::hash(b"absent");
  let name = || M::meta_field(Name::anon());
  let bi = || M::meta_field(BinderInfo::Default);
  let mut nodes: Vec<KExpr<M>> = vec![
    KExpr::var(0, name()),
    KExpr::fvar(FVarId(0), name()),
    KExpr::sort(KUniv::zero()),
    KExpr::cnst(KId::new(a.clone(), name()), Box::new([])),
    KExpr::cnst(KId::new(b.clone(), name()), Box::new([])),
    KExpr::nat(Nat::from(17u64), Address::hash(b"17")),
    KExpr::str("hello".to_owned(), Address::hash(b"hello")),
  ];
  for i in 0..24 {
    let x = nodes[i].clone();
    let y = nodes[(i * 7 + 3) % nodes.len()].clone();
    let z = nodes[(i + 4) % nodes.len()].clone();
    nodes.push(match i % 5 {
      0 => KExpr::app(x, y),
      1 => KExpr::lam(name(), bi(), x, y),
      2 => KExpr::all(name(), bi(), x, y),
      3 => KExpr::let_(name(), x, y, z, i % 2 == 0),
      _ => KExpr::prj(KId::new(a.clone(), name()), 2, x),
    });
  }
  for node in &nodes {
    for targets in [
      vec![],
      vec![missing.clone()],
      vec![a.clone()],
      vec![b.clone()],
      vec![missing.clone(), b.clone()],
      vec![a.clone(), a.clone(), b.clone()],
    ] {
      let expected = targets.iter().any(|a| mentions_reference(node, a));
      assert_eq!(expr_mentions_any_addr(node, &targets), expected);
      for addr in &targets {
        assert_eq!(
          expr_mentions_addr(node, addr),
          mentions_reference(node, addr)
        );
      }
    }
  }
}

#[test]
fn occurrence_queries_match_tree_reference_in_both_modes() {
  differential::<Meta>();
  differential::<Anon>();
}

#[test]
fn occurrence_queries_visit_diamond_edges_linearly() {
  let target = Address::hash(b"present");
  let mut root =
    KExpr::<Anon>::cnst(KId::new(target.clone(), ()), Box::new([]));
  let depth = 60;
  for _ in 0..depth {
    root = KExpr::app(root.clone(), root);
  }
  let mut visits = 0;
  assert!(!expr_mentions_any_addr_impl(
    &root,
    &[Address::hash(b"missing"), Address::hash(b"also missing")],
    || {
      visits += 1;
      assert!(
        visits <= 2 * OCCURRENCE_TREE_BUDGET + 2 * depth + 1,
        "expanded shared DAG as a tree"
      );
    },
  ));
  assert!(visits > 2 * depth);
  // Neither the visited set nor a negative result survives a query.
  assert!(expr_mentions_addr(&root, &target));
  assert!(!expr_mentions_any_addr_impl(&root, &[], || panic!(
    "empty query walked"
  )));
}

#[test]
fn occurrence_query_checks_every_binder_and_projection_position() {
  let id = KId::<Anon>::new(Address::hash(b"target"), ());
  let hit = KExpr::cnst(id.clone(), Box::new([]));
  let miss = KExpr::var(0, ());
  for e in [
    KExpr::lam((), (), hit.clone(), miss.clone()),
    KExpr::lam((), (), miss.clone(), hit.clone()),
    KExpr::all((), (), hit.clone(), miss.clone()),
    KExpr::all((), (), miss.clone(), hit.clone()),
    KExpr::let_((), hit.clone(), miss.clone(), miss.clone(), false),
    KExpr::let_((), miss.clone(), hit.clone(), miss.clone(), false),
    KExpr::let_((), miss.clone(), miss.clone(), hit.clone(), true),
    KExpr::prj(id.clone(), 0, miss),
    KExpr::prj(KId::new(Address::hash(b"other"), ()), 0, hit),
  ] {
    assert!(expr_mentions_addr(&e, &id.addr));
  }
}

#[test]
fn borrowed_app_head_matches_owned_collector_by_pointer() {
  for head in [
    KExpr::<Anon>::cnst(KId::new(Address::hash(b"f"), ()), Box::new([])),
    KExpr::var(0, ()),
    KExpr::prj(KId::new(Address::hash(b"S"), ()), 0, KExpr::var(1, ())),
  ] {
    let mut e = head.clone();
    // Holding each prefix also keeps final cleanup from recursively dropping
    // a deep unique spine on the test runner's small stack.
    let mut prefixes = Vec::new();
    for n in 0..1024 {
      if [0, 1, 2, 3, 8, 1023].contains(&n) {
        let (owned_head, args) = collect_app_spine(&e);
        assert!(app_head(&e).ptr_eq(&owned_head));
        assert!(app_head(&e).ptr_eq(&head));
        assert_eq!(args.len(), n);
      }
      prefixes.push(e.clone());
      e = KExpr::app(e, KExpr::var(0, ()));
    }
    drop(e);
    while prefixes.pop().is_some() {}
  }
}

#[test]
fn eager_reduce_requires_exactly_two_arguments_and_correct_head() {
  let mut env = KEnv::<Meta>::new();
  let tc = TypeChecker::new(&mut env);
  for id in [
    tc.prims.eager_reduce.clone(),
    KId::new(Address::hash(b"other"), Name::anon()),
  ] {
    let mut e = KExpr::cnst(id.clone(), Box::new([]));
    for arity in 0..5 {
      assert_eq!(
        tc.is_eager_reduce(&e),
        arity == 2 && id == tc.prims.eager_reduce
      );
      e = KExpr::app(e, KExpr::var(0, Name::anon()));
    }
  }
  let non_const = KExpr::app(
    KExpr::app(KExpr::var(0, Name::anon()), KExpr::var(1, Name::anon())),
    KExpr::var(2, Name::anon()),
  );
  assert!(!tc.is_eager_reduce(&non_const));
}

#[test]
#[ignore = "manual release benchmark; no wall-clock assertions"]
fn benchmark_occurrence_and_head_walks() {
  use std::{hint::black_box, time::Instant};
  let absent = Address::hash(b"absent");
  for depth in [0, 4, 16, 20] {
    let mut e = KExpr::<Anon>::var(0, ());
    for _ in 0..depth {
      e = KExpr::app(e.clone(), e);
    }
    let repeats = if depth <= 4 { 100_000 } else { 4 };
    for dag in [false, true, true, false] {
      let start = Instant::now();
      for _ in 0..repeats {
        black_box(if dag {
          expr_mentions_addr(&e, &absent)
        } else {
          mentions_reference(&e, &absent)
        });
      }
      eprintln!(
        "occurrence dag={dag} depth={depth} repeats={repeats} elapsed={:?}",
        start.elapsed()
      );
    }
  }
  for arity in [0, 2, 8, 64] {
    let mut e = KExpr::<Anon>::var(0, ());
    for _ in 0..arity {
      e = KExpr::app(e, KExpr::var(1, ()));
    }
    for borrowed in [false, true, true, false] {
      let start = Instant::now();
      for _ in 0..100_000 {
        if borrowed {
          black_box(app_head(&e));
        } else {
          black_box(collect_app_spine(&e));
        }
      }
      eprintln!(
        "head borrowed={borrowed} arity={arity} elapsed={:?}",
        start.elapsed()
      );
    }
  }
}
