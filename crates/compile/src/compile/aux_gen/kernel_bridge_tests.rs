//! Differential and sharing regressions for the aux-generation kernel bridge.

use super::*;
use crate::compile::CompileState;
use crate::compile::aux_gen::kernel_bridge_reference as reference;
use ix_common::env::{BinderInfo, DataValue, Literal};
use ix_kernel::expr::{ExprData as KED, KExpr};
use ix_kernel::id::KId;
use ix_kernel::level::KUniv;

fn name(s: &str) -> Name {
  Name::str(Name::anon(), s.to_owned())
}

fn diamond(mut leaf: LeanExpr, depth: usize) -> LeanExpr {
  for _ in 0..depth {
    leaf = LeanExpr::app(leaf.clone(), leaf);
  }
  leaf
}

fn metadata(label: &str) -> Vec<(Name, DataValue)> {
  vec![(name("tag"), DataValue::OfString(label.to_owned()))]
}

fn assert_same_lean(actual: &LeanExpr, expected: &LeanExpr) {
  // Full Lean digests include display names, binder info and mdata. Avoid
  // formatting an exponentially large tree when a sharing regression fails.
  assert_eq!(actual.get_hash(), expected.get_hash());
}

#[test]
fn kernel_bridge_matches_tree_reference_across_scopes() {
  let stt = CompileState::new_empty();
  let params = [name("u"), name("v")];
  let fvars = FxHashMap::from_iter([(name("x"), 0), (name("y"), 1)]);
  let u = Level::param(params[0].clone());
  let v = Level::param(params[1].clone());
  let shared = LeanExpr::app(
    LeanExpr::cnst(
      name("C"),
      vec![Level::max(u.clone(), v.clone()), Level::imax(v, u)],
    ),
    LeanExpr::fvar(name("x")),
  );
  let sort = LeanExpr::sort(Level::succ(Level::zero()));
  let body = LeanExpr::app(
    LeanExpr::proj(name("P"), Nat::from(2u64), shared.clone()),
    LeanExpr::app(LeanExpr::bvar(Nat::from(0u64)), shared.clone()),
  );
  let mut fixtures = vec![
    shared.clone(),
    diamond(shared.clone(), 5),
    LeanExpr::lit(Literal::NatVal(Nat::from(123u64))),
    LeanExpr::lit(Literal::StrVal("bridge".to_owned())),
    LeanExpr::fvar(name("unregistered")),
    LeanExpr::mvar(name("unresolved")),
    LeanExpr::mdata(metadata("outer"), shared.clone()),
  ];
  for bi in [
    BinderInfo::Default,
    BinderInfo::Implicit,
    BinderInfo::StrictImplicit,
    BinderInfo::InstImplicit,
  ] {
    fixtures.push(LeanExpr::all(
      name("a"),
      shared.clone(),
      body.clone(),
      bi.clone(),
    ));
    fixtures.push(LeanExpr::lam(name("b"), sort.clone(), body.clone(), bi));
  }
  for non_dep in [false, true] {
    fixtures.push(LeanExpr::letE(
      name("c"),
      sort.clone(),
      shared.clone(),
      body.clone(),
      non_dep,
    ));
  }
  for depth in [2, 3] {
    for source in &fixtures {
      let old =
        reference::to_kexpr_static(source, &fvars, depth, &params, &stt);
      let new = to_kexpr_static(source, &fvars, depth, &params, &stt);
      assert_eq!(new, old);
      let expected = reference::kexpr_to_lean(&old, depth, &fvars, 0, &params);
      assert_same_lean(
        &reference::kexpr_to_lean(&new, depth, &fvars, 0, &params),
        &expected,
      );
      assert_same_lean(
        &kexpr_to_lean(&old, depth, &fvars, 0, &params),
        &expected,
      );
      assert_same_lean(
        &kexpr_to_lean(&new, depth, &fvars, 0, &params),
        &expected,
      );
    }
  }
}

#[test]
fn kernel_bridge_cache_keys_include_binder_depth() {
  let stt = CompileState::new_empty();
  let fvars = FxHashMap::from_iter([(name("x"), 0)]);
  let x = LeanExpr::fvar(name("x"));
  let source = LeanExpr::app(
    x.clone(),
    LeanExpr::lam(
      name("bound"),
      LeanExpr::sort(Level::zero()),
      x,
      BinderInfo::Default,
    ),
  );
  let ingressed = to_kexpr_static(&source, &fvars, 1, &[], &stt);
  let KED::App(outer, lam, _) = ingressed.data() else { panic!("app") };
  let KED::Lam(_, _, _, inner, _) = lam.data() else { panic!("lam") };
  assert!(matches!(outer.data(), KED::Var(0, ..)));
  assert!(matches!(inner.data(), KED::Var(1, ..)));
  assert_same_lean(&kexpr_to_lean(&ingressed, 1, &fvars, 0, &[]), &source);

  // One kernel node is free at the root but bound under the lambda.
  let var = KExpr::var(0, Name::anon());
  let kernel = KExpr::app(
    var.clone(),
    KExpr::lam(
      name("bound"),
      BinderInfo::Default,
      KExpr::sort(KUniv::zero()),
      var,
    ),
  );
  let expected = reference::kexpr_to_lean(&kernel, 1, &fvars, 0, &[]);
  assert_same_lean(&kexpr_to_lean(&kernel, 1, &fvars, 0, &[]), &expected);
  let ExprData::App(outer, lam, _) = expected.as_data() else { panic!("app") };
  let ExprData::Lam(_, _, inner, _, _) = lam.as_data() else { panic!("lam") };
  assert!(matches!(outer.as_data(), ExprData::Fvar(..)));
  assert!(matches!(inner.as_data(), ExprData::Bvar(..)));
}

#[test]
fn kernel_egress_distinguishes_metadata_nodes_with_the_same_uid() {
  let address = Address::hash(b"alias class");
  let a = KExpr::<Meta>::cnst_mdata(
    KId::new(address.clone(), name("A")),
    Box::new([]),
    vec![metadata("outer-A"), metadata("inner-A")],
  );
  let mut b_info = a.info().clone();
  b_info.mdata = vec![metadata("B")];
  let b =
    KExpr::new(KED::Const(KId::new(address, name("B")), Box::new([]), b_info));
  assert_eq!(a.hash_key(), b.hash_key());
  let kernel = KExpr::app(a, b);
  let fvars = FxHashMap::default();
  let expected = reference::kexpr_to_lean(&kernel, 0, &fvars, 0, &[]);
  assert_same_lean(&kexpr_to_lean(&kernel, 0, &fvars, 0, &[]), &expected);
  let ExprData::App(a, b, _) = expected.as_data() else { panic!("app") };
  assert_ne!(a.get_hash(), b.get_hash());
  assert_same_lean(
    a,
    &LeanExpr::mdata(
      metadata("outer-A"),
      LeanExpr::mdata(metadata("inner-A"), LeanExpr::cnst(name("A"), vec![])),
    ),
  );
}

#[test]
fn kernel_bridge_caches_do_not_outlive_their_context() {
  let stt = CompileState::new_empty();
  let source = LeanExpr::app(
    LeanExpr::cnst(name("C"), vec![Level::param(name("u"))]),
    LeanExpr::fvar(name("x")),
  );
  for (i, params) in
    [[name("u"), name("v")], [name("v"), name("u")]].iter().enumerate()
  {
    let address = Address::hash(&[i as u8]);
    stt.name_to_addr.insert(name("C"), address.clone());
    let fvars = FxHashMap::from_iter([(name("x"), i)]);
    let kernel = to_kexpr_static(&source, &fvars, 2, params, &stt);
    let KED::App(c, x, _) = kernel.data() else { panic!("app") };
    let KED::Const(id, levels, _) = c.data() else { panic!("const") };
    assert_eq!(id.addr, address);
    assert_eq!(
      levels[0],
      lean_level_to_kuniv(&Level::param(name("u")), params)
    );
    assert!(matches!(x.data(), KED::Var(idx, ..) if *idx == (1 - i) as u64));
    assert_same_lean(&kexpr_to_lean(&kernel, 2, &fvars, 0, params), &source);
  }
}

#[test]
fn source_restoration_matches_reference_and_preserves_occurrence_names() {
  let stt = CompileState::new_empty();
  for alias in ["G", "A", "B"] {
    stt.name_to_addr.insert(name(alias), Address::hash(b"same declaration"));
  }
  let g = LeanExpr::cnst(name("G"), vec![Level::zero()]);
  let a = LeanExpr::cnst(name("A"), vec![Level::succ(Level::zero())]);
  let b = LeanExpr::cnst(name("B"), vec![]);
  let generated = LeanExpr::app(g.clone(), g.clone());
  let source = LeanExpr::app(a.clone(), b.clone());
  let restored = restore_source_names_same_content(&generated, &source, &stt);
  assert_same_lean(
    &restored,
    &reference::restore_source_names_same_content(&generated, &source, &stt),
  );
  assert_same_lean(
    &restored,
    &LeanExpr::app(
      LeanExpr::cnst(name("A"), vec![Level::zero()]),
      LeanExpr::cnst(name("B"), vec![Level::zero()]),
    ),
  );
  // Also cover binders, non-dependency flags, projection indices, mismatches
  // and independent source/generated metadata layers.
  let pairs = [
    (
      LeanExpr::all(name("g"), g.clone(), g.clone(), BinderInfo::Implicit),
      LeanExpr::all(name("s"), a.clone(), b.clone(), BinderInfo::Default),
    ),
    (
      LeanExpr::lam(name("g"), g.clone(), g.clone(), BinderInfo::InstImplicit),
      LeanExpr::lam(name("s"), a.clone(), b.clone(), BinderInfo::Default),
    ),
    (
      LeanExpr::letE(name("g"), g.clone(), g.clone(), g.clone(), true),
      LeanExpr::letE(name("s"), a.clone(), b.clone(), a.clone(), false),
    ),
    (
      LeanExpr::proj(name("G"), Nat::from(0u64), g.clone()),
      LeanExpr::proj(name("A"), Nat::from(0u64), b.clone()),
    ),
    (
      LeanExpr::proj(name("G"), Nat::from(0u64), g.clone()),
      LeanExpr::proj(name("A"), Nat::from(1u64), b.clone()),
    ),
    (
      LeanExpr::mdata(metadata("generated"), generated),
      LeanExpr::mdata(metadata("source"), source),
    ),
    (g.clone(), LeanExpr::cnst(name("unrelated"), vec![])),
    (g.clone(), LeanExpr::sort(Level::zero())),
    (g.clone(), LeanExpr::mdata(metadata("source"), g)),
  ];
  for (generated, source) in pairs {
    assert_same_lean(
      &restore_source_names_same_content(&generated, &source, &stt),
      &reference::restore_source_names_same_content(&generated, &source, &stt),
    );
  }
}

#[test]
fn kernel_bridge_preserves_a_trillion_path_dag() {
  let stt = CompileState::new_empty();
  for alias in ["A", "B"] {
    stt.name_to_addr.insert(name(alias), Address::hash(b"shared leaf"));
  }
  // 41 unique nodes, but 2^40 leaf occurrences if expanded as a tree.
  let depth = 40;
  let source = diamond(LeanExpr::cnst(name("A"), vec![]), depth);
  let aliases = diamond(LeanExpr::cnst(name("B"), vec![]), depth);
  let fvars = FxHashMap::default();
  let mut ingress_cache = FxHashMap::default();
  let kernel =
    to_kexpr_cached(&source, &fvars, 0, &[], &stt, &mut ingress_cache);
  assert_eq!(ingress_cache.len(), depth + 1);
  let mut cursor = &kernel;
  for _ in 0..depth {
    let KED::App(f, a, _) = cursor.data() else { panic!("app") };
    assert!(std::ptr::eq(f.data(), a.data()));
    cursor = f;
  }
  let mut egress_cache = FxHashMap::default();
  let generated =
    kexpr_to_lean_cached(&kernel, 0, &fvars, 0, &[], &mut egress_cache);
  assert_eq!(egress_cache.len(), depth + 1);
  assert_same_lean(&generated, &source);
  let mut restore_cache = FxHashMap::default();
  let restored =
    restore_source_names_cached(&generated, &aliases, &stt, &mut restore_cache);
  assert_eq!(restore_cache.len(), depth + 1);
  assert_same_lean(&restored, &aliases);
  for root in [&generated, &restored] {
    let mut cursor = root;
    for _ in 0..depth {
      let ExprData::App(f, a, _) = cursor.as_data() else { panic!("app") };
      assert!(std::ptr::eq(f.as_data(), a.as_data()));
      cursor = f;
    }
  }
  let mut refs = FxHashSet::default();
  collect_lean_const_refs(&source, &mut refs);
  assert_eq!(refs, FxHashSet::from_iter([name("A")]));
}

#[test]
#[ignore = "manual release-mode comparison against the pre-memoization bridge"]
fn kernel_bridge_shared_dag_benchmark() {
  use std::time::Instant;
  let stt = CompileState::new_empty();
  for alias in ["A", "B"] {
    stt.name_to_addr.insert(name(alias), Address::hash(b"shared leaf"));
  }
  let fvars = FxHashMap::default();
  for depth in [12, 16, 18] {
    let source = diamond(LeanExpr::cnst(name("A"), vec![]), depth);
    let aliases = diamond(LeanExpr::cnst(name("B"), vec![]), depth);
    let start = Instant::now();
    let old_k = reference::to_kexpr_static(&source, &fvars, 0, &[], &stt);
    let old_l = reference::kexpr_to_lean(&old_k, 0, &fvars, 0, &[]);
    let old_r =
      reference::restore_source_names_same_content(&old_l, &aliases, &stt);
    let old_time = start.elapsed();
    let start = Instant::now();
    let new_k = to_kexpr_static(&source, &fvars, 0, &[], &stt);
    let new_l = kexpr_to_lean(&new_k, 0, &fvars, 0, &[]);
    let new_r = restore_source_names_same_content(&new_l, &aliases, &stt);
    let new_time = start.elapsed();
    assert_same_lean(&new_r, &old_r);
    eprintln!(
      "bridge DAG: {} unique nodes / {} leaf paths: old={old_time:?} new={new_time:?}",
      depth + 1,
      1usize << depth
    );
  }
}
