//! Differential semantics, collision handling, context, and DAG regressions.

use super::super::source_name_hints_reference as reference;
use super::*;
use crate::compile::CompileState;
use ix_common::env::DataValue;
use std::hash::{BuildHasherDefault, Hasher};

fn name(s: &str) -> Name {
  Name::str(Name::anon(), s.to_owned())
}

fn state() -> CompileState {
  let stt = CompileState::new_empty();
  for alias in ["A", "B"] {
    stt.name_to_addr.insert(name(alias), Address::hash(b"alias class"));
  }
  stt.aux_name_to_addr.insert(name("P"), Address::hash(b"projection class"));
  stt.name_to_addr.insert(name("Q"), Address::hash(b"projection class"));
  stt
}

fn tag(s: &str) -> Vec<(Name, DataValue)> {
  vec![(name("tag"), DataValue::OfString(s.to_owned()))]
}

fn application(alias: &str) -> LeanExpr {
  LeanExpr::app(LeanExpr::cnst(name(alias), vec![]), LeanExpr::fvar(name("x")))
}

fn diamond(mut leaf: LeanExpr, depth: usize) -> LeanExpr {
  for _ in 0..depth {
    leaf = LeanExpr::app(leaf.clone(), leaf);
  }
  leaf
}

fn fixtures(alias: &str) -> Vec<LeanExpr> {
  let u = Level::param(name("u"));
  let v = Level::param(name("v"));
  let shared = application(alias);
  let mut roots = vec![
    LeanExpr::bvar(Nat::from(0u64)),
    LeanExpr::fvar(name("x")),
    LeanExpr::fvar(name("unregistered")),
    LeanExpr::mvar(name("unresolved")),
    LeanExpr::sort(Level::zero()),
    LeanExpr::cnst(
      name(alias),
      vec![u.clone(), Level::imax(v.clone(), u.clone())],
    ),
    shared.clone(),
    diamond(shared.clone(), 4),
    LeanExpr::proj(
      name(if alias == "A" { "P" } else { "Q" }),
      Nat::from(1u64),
      shared.clone(),
    ),
    LeanExpr::lit(Literal::NatVal(Nat::from(42u64))),
    LeanExpr::lit(Literal::StrVal("a string".to_owned())),
    LeanExpr::mdata(tag(alias), shared.clone()),
    LeanExpr::mdata(tag(alias), LeanExpr::mdata(tag("inner"), shared.clone())),
  ];
  for level in [
    u.clone(),
    Level::succ(u.clone()),
    Level::max(u.clone(), Level::zero()),
    Level::max(u.clone(), v.clone()),
    Level::max(v.clone(), u.clone()),
    Level::imax(u, Level::zero()),
  ] {
    roots.push(LeanExpr::sort(level));
  }
  for bi in [
    BinderInfo::Default,
    BinderInfo::Implicit,
    BinderInfo::StrictImplicit,
    BinderInfo::InstImplicit,
  ] {
    roots.push(LeanExpr::lam(
      name(alias),
      shared.clone(),
      LeanExpr::bvar(Nat::from(0u64)),
      bi.clone(),
    ));
    roots.push(LeanExpr::all(name(alias), shared.clone(), shared.clone(), bi));
  }
  for nd in [false, true] {
    roots.push(LeanExpr::letE(
      name(alias),
      shared.clone(),
      shared.clone(),
      shared.clone(),
      nd,
    ));
  }
  roots
}

fn old_restore(
  generated: &LeanExpr,
  source: &LeanExpr,
  fvars: &FxHashMap<Name, usize>,
  depth: usize,
  params: &[Name],
  stt: &CompileState,
) -> LeanExpr {
  let mut hints = FxHashMap::default();
  reference::collect_lean_source_name_hints(
    source, fvars, depth, params, stt, &mut hints,
  );
  reference::restore_lean_source_name_hints(
    generated, fvars, depth, params, stt, &hints,
  )
}

#[test]
fn source_hints_match_reference_including_all_metadata() {
  let stt = state();
  let fvars = FxHashMap::from_iter([(name("x"), 0)]);
  let params = [name("u"), name("v")];
  for depth in [1, 3] {
    for (source, generated) in fixtures("A").iter().zip(fixtures("B")) {
      // A real reduction can introduce a different surrounding telescope.
      let generated = LeanExpr::lam(
        name("generated binder"),
        LeanExpr::sort(Level::zero()),
        LeanExpr::app(generated, LeanExpr::bvar(Nat::from(0u64))),
        BinderInfo::InstImplicit,
      );
      let expected =
        old_restore(&generated, source, &fvars, depth, &params, &stt);
      let actual = restore(&generated, source, &fvars, depth, &params, &stt);
      assert_eq!(actual, expected);
      assert_eq!(actual.get_hash(), expected.get_hash());
    }
  }
}

#[test]
fn structural_ids_match_kernel_equality_and_include_conversion_depth() {
  let stt = state();
  let fvars = FxHashMap::from_iter([(name("x"), 0)]);
  let params = [name("u"), name("v")];
  let roots: Vec<_> = fixtures("A").into_iter().chain(fixtures("B")).collect();
  let mut addresses = FxHashMap::default();
  for root in &roots {
    addresses.extend(capture_addresses(root, root, &stt));
  }
  let mut table =
    ContentTable::<rustc_hash::FxBuildHasher>::new(&addresses, &fvars, &params);
  let mut ids = Vec::new();
  let mut kernel = Vec::new();
  for depth in [1, 3] {
    for root in &roots {
      ids.push(table.content(root, depth));
      kernel.push(to_kexpr_static(root, &fvars, depth, &params, &stt));
    }
  }
  for i in 0..ids.len() {
    for j in 0..ids.len() {
      assert_eq!(ids[i] == ids[j], kernel[i] == kernel[j], "pair {i}/{j}");
    }
  }
}

#[test]
fn first_hint_wins_in_original_preorder() {
  let stt = state();
  let fvars = FxHashMap::from_iter([(name("x"), 0)]);
  let a = application("A");
  let b = application("B");
  for (first, second) in [(&a, &b), (&b, &a)] {
    let source = LeanExpr::app(
      first.clone(),
      LeanExpr::app(second.clone(), first.clone()),
    );
    let actual = restore(second, &source, &fvars, 1, &[], &stt);
    assert!(same_node(&actual, first));
    assert_eq!(actual, old_restore(second, &source, &fvars, 1, &[], &stt));
  }
}

#[test]
fn eligibility_still_excludes_any_bvar_even_when_bound() {
  let stt = state();
  let fvars = FxHashMap::from_iter([(name("x"), 0)]);
  let params = [name("u"), name("v")];
  let roots = fixtures("A");
  for root in &roots {
    let addresses = capture_addresses(root, root, &stt);
    let mut pass = Pass::new(&addresses, &fvars, 1, &params);
    assert_eq!(pass.has_bvar(root), reference::expr_has_bvar(root));
  }
  let bound = LeanExpr::app(
    LeanExpr::cnst(name("A"), vec![]),
    LeanExpr::lam(
      name("bound"),
      LeanExpr::sort(Level::zero()),
      LeanExpr::bvar(Nat::from(0u64)),
      BinderInfo::Default,
    ),
  );
  let addresses = capture_addresses(&bound, &bound, &stt);
  let mut pass = Pass::new(&addresses, &fvars, 1, &params);
  assert!(pass.has_bvar(&bound));
  assert!(!pass.candidate(&bound));
  let mut hints = FxHashMap::default();
  pass.collect(&bound, &mut hints);
  assert!(hints.is_empty());
}

#[test]
fn restored_memo_distinguishes_alias_metadata_when_no_hint_matches() {
  let stt = state();
  let fvars = FxHashMap::from_iter([(name("x"), 0)]);
  let a = LeanExpr::mdata(tag("A"), application("A"));
  let b = LeanExpr::mdata(tag("B"), application("B"));
  let root = LeanExpr::app(a.clone(), b.clone());
  let addresses = capture_addresses(&root, &root, &stt);
  let mut pass = Pass::new(&addresses, &fvars, 1, &[]);
  assert_eq!(pass.content.content(&a, 1), pass.content.content(&b, 1));
  let result = pass.restore(&root, &FxHashMap::default());
  assert!(same_node(&result, &root));
  let ExprData::App(lhs, rhs, _) = result.as_data() else { panic!("app") };
  assert!(same_node(lhs, &a));
  assert!(same_node(rhs, &b));
  assert_ne!(lhs.get_hash(), rhs.get_hash());
}

#[test]
fn resolution_is_frozen_within_pass_but_fresh_on_the_next_call() {
  let stt = CompileState::new_empty();
  let fvars = FxHashMap::from_iter([(name("x"), 0)]);
  let source = application("A");
  let generated = application("B");
  stt.name_to_addr.insert(name("A"), Address::hash(b"a"));
  let before_publication = capture_addresses(&source, &generated, &stt);
  stt.aux_name_to_addr.insert(name("B"), Address::hash(b"a"));
  let mut pass = Pass::new(&before_publication, &fvars, 1, &[]);
  let mut hints = FxHashMap::default();
  pass.collect(&source, &mut hints);
  assert!(same_node(&pass.restore(&generated, &hints), &generated));
  assert!(same_node(
    &restore(&generated, &source, &fvars, 1, &[], &stt),
    &source
  ));

  // A new primary entry takes precedence over the already-captured aux entry.
  let before_override = capture_addresses(&source, &generated, &stt);
  stt.name_to_addr.insert(name("B"), Address::hash(b"b"));
  let mut pass = Pass::new(&before_override, &fvars, 1, &[]);
  let mut hints = FxHashMap::default();
  pass.collect(&source, &mut hints);
  assert!(same_node(&pass.restore(&generated, &hints), &source));
  assert!(same_node(
    &restore(&generated, &source, &fvars, 1, &[], &stt),
    &generated
  ));
}

#[test]
fn shared_dag_visits_unique_nodes_and_preserves_sharing() {
  let stt = state();
  let fvars = FxHashMap::from_iter([(name("x"), 0)]);
  let source = application("A");
  let generated = diamond(application("B"), 60);
  let addresses = capture_addresses(&source, &generated, &stt);
  let mut pass = Pass::new(&addresses, &fvars, 1, &[]);
  let mut hints = FxHashMap::default();
  pass.collect(&source, &mut hints);
  let result = pass.restore(&generated, &hints);
  assert!(pass.restored.len() < 70);
  assert!(pass.content.converted.len() < 70);
  assert!(pass.has_bvar.len() < 70);
  let mut cursor = &result;
  for _ in 0..60 {
    let ExprData::App(a, b, _) = cursor.as_data() else { panic!("app") };
    assert!(same_node(a, b));
    cursor = a;
  }
  assert!(same_node(cursor, &source));

  let source = diamond(source, 60);
  let unmatched = diamond(application("unmatched"), 60);
  let addresses = capture_addresses(&source, &unmatched, &stt);
  let mut pass = Pass::new(&addresses, &fvars, 1, &[]);
  let mut hints = FxHashMap::default();
  pass.collect(&source, &mut hints);
  assert!(pass.collected.len() < 70);
  assert!(hints.len() < 70);
  let result = pass.restore(&unmatched, &hints);
  assert!(same_node(&result, &unmatched));
  assert!(pass.content.converted.len() < 140);
}

#[derive(Default)]
struct AlwaysZero;
impl Hasher for AlwaysZero {
  fn write(&mut self, _: &[u8]) {}
  fn finish(&self) -> u64 {
    0
  }
}

#[test]
fn structural_hash_collisions_cannot_merge_distinct_terms() {
  let stt = state();
  let fvars = FxHashMap::from_iter([(name("x"), 0)]);
  let params = [name("u"), name("v")];
  let roots: Vec<_> = fixtures("A").into_iter().chain(fixtures("B")).collect();
  let mut addresses = FxHashMap::default();
  for root in &roots {
    addresses.extend(capture_addresses(root, root, &stt));
  }
  let mut table = ContentTable::<BuildHasherDefault<AlwaysZero>>::new(
    &addresses, &fvars, &params,
  );
  let ids: Vec<_> = roots.iter().map(|e| table.content(e, 1)).collect();
  let kernel: Vec<_> = roots
    .iter()
    .map(|e| to_kexpr_static(e, &fvars, 1, &params, &stt))
    .collect();
  for i in 0..ids.len() {
    for j in 0..ids.len() {
      assert_eq!(
        ids[i] == ids[j],
        kernel[i] == kernel[j],
        "collision pair {i}/{j}"
      );
    }
  }
}

#[test]
#[ignore = "manual release benchmark against the pre-cache restoration"]
fn source_name_hints_shared_dag_benchmark() {
  use std::time::Instant;
  let stt = state();
  let fvars = FxHashMap::from_iter([(name("x"), 0)]);
  for depth in [8, 12, 16] {
    let source = diamond(application("A"), depth);
    let generated = diamond(application("unmatched"), depth);
    let start = Instant::now();
    let expected = old_restore(&generated, &source, &fvars, 1, &[], &stt);
    let old_time = start.elapsed();
    let start = Instant::now();
    let result = restore(&generated, &source, &fvars, 1, &[], &stt);
    let new_time = start.elapsed();
    assert_eq!(result.get_hash(), expected.get_hash());
    eprintln!("depth={depth}: old={old_time:?}, cached={new_time:?}");
  }
}
