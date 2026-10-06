//! Differential and sharing regressions for the aux-generation kernel bridge.

use super::*;
use crate::compile::CompileState;
use crate::compile::aux_gen::kernel_bridge_reference as reference;
use ix_common::env::ConstantInfo;
use ix_common::env::{BinderInfo, DataValue, Literal};
use ix_kernel::expr::{ExprData as KED, KExpr};
use ix_kernel::id::KId;
use ix_kernel::ingress::lean_level_to_kuniv;
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
      let new = to_kexpr_static(source, &fvars, depth, &params, &stt).unwrap();
      assert_eq!(new, old);
      let expected = reference::kexpr_to_lean(&old, depth, &fvars, 0, &params);
      assert_same_lean(
        &reference::kexpr_to_lean(&new, depth, &fvars, 0, &params),
        &expected,
      );
      assert_same_lean(
        &kexpr_to_lean(&old, depth, &fvars, 0, &params).unwrap(),
        &expected,
      );
      assert_same_lean(
        &kexpr_to_lean(&new, depth, &fvars, 0, &params).unwrap(),
        &expected,
      );
    }
  }
  // The frozen reference turned an unregistered free variable and a
  // metavariable into `Sort 0`; the bridge now refuses both, as the Lean
  // bridge's `toKexprStatic` does.
  for depth in [2, 3] {
    for (source, text) in [
      (
        LeanExpr::fvar(name("unregistered")),
        "aux kernel bridge: to_kexpr_static: unknown free variable unregistered",
      ),
      (
        LeanExpr::mvar(name("unresolved")),
        "aux kernel bridge: to_kexpr_static: expression metavariable",
      ),
    ] {
      let old =
        reference::to_kexpr_static(&source, &fvars, depth, &params, &stt);
      assert_eq!(old, KExpr::sort(KUniv::zero()));
      assert_refused(
        to_kexpr_static(&source, &fvars, depth, &params, &stt),
        text,
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
  let ingressed = to_kexpr_static(&source, &fvars, 1, &[], &stt).unwrap();
  let KED::App(outer, lam, _) = ingressed.data() else { panic!("app") };
  let KED::Lam(_, _, _, inner, _) = lam.data() else { panic!("lam") };
  assert!(matches!(outer.data(), KED::Var(0, ..)));
  assert!(matches!(inner.data(), KED::Var(1, ..)));
  assert_same_lean(
    &kexpr_to_lean(&ingressed, 1, &fvars, 0, &[]).unwrap(),
    &source,
  );

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
  assert_same_lean(
    &kexpr_to_lean(&kernel, 1, &fvars, 0, &[]).unwrap(),
    &expected,
  );
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
  assert_same_lean(
    &kexpr_to_lean(&kernel, 0, &fvars, 0, &[]).unwrap(),
    &expected,
  );
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
    let kernel = to_kexpr_static(&source, &fvars, 2, params, &stt).unwrap();
    let KED::App(c, x, _) = kernel.data() else { panic!("app") };
    let KED::Const(id, levels, _) = c.data() else { panic!("const") };
    assert_eq!(id.addr, address);
    assert_eq!(
      levels[0],
      lean_level_to_kuniv(&Level::param(name("u")), params).unwrap()
    );
    assert!(matches!(x.data(), KED::Var(idx, ..) if *idx == (1 - i) as u64));
    assert_same_lean(
      &kexpr_to_lean(&kernel, 2, &fvars, 0, params).unwrap(),
      &source,
    );
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
    to_kexpr_cached(&source, &fvars, 0, &[], &stt, &mut ingress_cache).unwrap();
  assert_eq!(ingress_cache.len(), depth + 1);
  let mut cursor = &kernel;
  for _ in 0..depth {
    let KED::App(f, a, _) = cursor.data() else { panic!("app") };
    assert!(std::ptr::eq(f.data(), a.data()));
    cursor = f;
  }
  let mut egress_cache = FxHashMap::default();
  let generated =
    kexpr_to_lean_cached(&kernel, 0, &fvars, 0, &[], &mut egress_cache)
      .unwrap();
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
    let new_k = to_kexpr_static(&source, &fvars, 0, &[], &stt).unwrap();
    let new_l = kexpr_to_lean(&new_k, 0, &fvars, 0, &[]).unwrap();
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

fn assert_refused<T: std::fmt::Debug>(
  result: Result<T, ixon::CompileError>,
  text: &str,
) {
  match result {
    Err(ixon::CompileError::UnsupportedExpr { desc }) => {
      assert_eq!(desc, text);
    },
    other => panic!("expected the refusal {text:?}, got {other:?}"),
  }
}

/// The Lean bridge refuses (`toKexprStatic`) a free variable whose level is
/// not below the context depth; Rust used to underflow.
#[test]
fn to_kexpr_static_refuses_free_variable_outside_context_depth() {
  let stt = CompileState::new_empty();
  let fvars = FxHashMap::from_iter([(name("x"), 2)]);
  let source = LeanExpr::fvar(name("x"));
  assert_refused(
    to_kexpr_static(&source, &fvars, 2, &[], &stt),
    "aux kernel bridge: to_kexpr_static: free variable x outside context depth 2",
  );
  // Valid neighbour: one binder deeper, the variable is in scope.
  let kernel = to_kexpr_static(&source, &fvars, 3, &[], &stt).unwrap();
  assert!(matches!(kernel.data(), KED::Var(0, ..)));
}

/// An unknown free variable is refused, never turned into `Sort 0`.
#[test]
fn to_kexpr_static_refuses_unknown_free_variable() {
  let stt = CompileState::new_empty();
  let fvars = FxHashMap::from_iter([(name("x"), 0)]);
  let source =
    LeanExpr::app(LeanExpr::fvar(name("x")), LeanExpr::fvar(name("y")));
  assert_refused(
    to_kexpr_static(&source, &fvars, 1, &[], &stt),
    "aux kernel bridge: to_kexpr_static: unknown free variable y",
  );
  // Valid neighbour: both variables registered.
  let fvars = FxHashMap::from_iter([(name("x"), 0), (name("y"), 1)]);
  let kernel = to_kexpr_static(&source, &fvars, 2, &[], &stt).unwrap();
  let KED::App(f, a, _) = kernel.data() else { panic!("app") };
  assert!(matches!(f.data(), KED::Var(1, ..)));
  assert!(matches!(a.data(), KED::Var(0, ..)));
}

/// An unknown universe parameter is refused (it used to panic in
/// `lean_level_to_kuniv`).
#[test]
fn to_kexpr_static_refuses_unknown_universe_parameter() {
  let stt = CompileState::new_empty();
  let fvars = FxHashMap::default();
  let params = [name("u")];
  assert_refused(
    to_kexpr_static(
      &LeanExpr::sort(Level::param(name("w"))),
      &fvars,
      0,
      &params,
      &stt,
    ),
    "aux kernel bridge: unknown level param `w` not found in param_names [u]",
  );
  let kernel = to_kexpr_static(
    &LeanExpr::sort(Level::param(name("u"))),
    &fvars,
    0,
    &params,
    &stt,
  )
  .unwrap();
  assert_eq!(
    kernel,
    KExpr::sort(
      lean_level_to_kuniv(&Level::param(name("u")), &params).unwrap()
    )
  );
}

/// The Lean bridge refuses (`kunivToLevel`) a universe parameter index
/// outside the parameter names; Rust used to invent `u_{idx}`.
#[test]
fn kuniv_to_level_refuses_out_of_range_parameter() {
  let params = [name("u")];
  assert_refused(
    super::super::below::kuniv_to_level(&KUniv::param(1, name("v")), &params),
    "aux kernel bridge: kuniv_to_level: universe parameter index 1 out of range",
  );
  assert_eq!(
    super::super::below::kuniv_to_level(
      &KUniv::succ(KUniv::param(0, name("u"))),
      &params,
    )
    .unwrap(),
    Level::succ(Level::param(name("u")))
  );
}

/// Kernel-to-Lean conversion refuses what the Lean bridge's `kexprToLean`
/// refuses: a `Var` above the outer context, a level with no or with two
/// registered free variables, and a leaked kernel free variable.
#[test]
fn kexpr_to_lean_refuses_unresolvable_variables() {
  let x = FxHashMap::from_iter([(name("x"), 0)]);
  assert_refused(
    kexpr_to_lean(&KExpr::var(1, Name::anon()), 1, &x, 0, &[]),
    "aux kernel bridge: kexpr_to_lean: Var index out of range of outer context",
  );
  assert_refused(
    kexpr_to_lean(&KExpr::var(0, Name::anon()), 2, &x, 0, &[]),
    "aux kernel bridge: kexpr_to_lean: missing free variable at outer level 1",
  );
  let twice = FxHashMap::from_iter([(name("x"), 0), (name("y"), 0)]);
  assert_refused(
    kexpr_to_lean(&KExpr::var(0, Name::anon()), 1, &twice, 0, &[]),
    "aux kernel bridge: kexpr_to_lean: duplicate free variable identities at outer level 0",
  );
  assert_refused(
    kexpr_to_lean(&KExpr::sort(KUniv::param(0, name("u"))), 0, &x, 0, &[]),
    "aux kernel bridge: kuniv_to_level: universe parameter index 0 out of range",
  );
  // Valid neighbour: the registered variable and a bound one.
  let kernel = KExpr::lam(
    name("b"),
    BinderInfo::Default,
    KExpr::sort(KUniv::zero()),
    KExpr::app(KExpr::var(1, Name::anon()), KExpr::var(0, Name::anon())),
  );
  let lean = kexpr_to_lean(&kernel, 1, &x, 0, &[]).unwrap();
  let ExprData::Lam(_, _, body, _, _) = lean.as_data() else { panic!("lam") };
  let ExprData::App(f, a, _) = body.as_data() else { panic!("app") };
  assert!(matches!(f.as_data(), ExprData::Fvar(n, _) if *n == name("x")));
  assert!(matches!(a.as_data(), ExprData::Bvar(..)));
}

/// A scope refuses a WHNF query over an unknown free variable rather than
/// reducing a substituted `Sort 0`.
#[test]
fn tc_scope_refuses_unknown_free_variable() {
  let stt = CompileState::new_empty();
  let mut kctx = crate::compile::KernelCtx::new();
  let a = LocalDecl {
    fvar_name: name("A"),
    binder_name: name("A"),
    domain: LeanExpr::sort(Level::succ(Level::zero())),
    info: BinderInfo::Default,
  };
  let mut scope =
    TcScope::new(std::slice::from_ref(&a), &[], &stt, &mut kctx).unwrap();
  assert_refused(
    scope.whnf_lean(&LeanExpr::fvar(name("z"))),
    "aux kernel bridge: to_kexpr_static: unknown free variable z",
  );
  assert_refused(
    scope.push_locals(&[LocalDecl {
      fvar_name: name("x"),
      binder_name: name("x"),
      domain: LeanExpr::fvar(name("z")),
      info: BinderInfo::Default,
    }]),
    "aux kernel bridge: to_kexpr_static: unknown free variable z",
  );
  // Valid neighbour: the registered variable, and a push that refers to it.
  let a_ref = LeanExpr::fvar(name("A"));
  assert_same_lean(&scope.whnf_lean(&a_ref).unwrap(), &a_ref);
  scope
    .push_locals(&[LocalDecl {
      fvar_name: name("x"),
      binder_name: name("x"),
      domain: a_ref.clone(),
      info: BinderInfo::Default,
    }])
    .unwrap();
  assert_same_lean(
    &scope.infer_lean(&LeanExpr::fvar(name("x"))).unwrap().unwrap(),
    &a_ref,
  );
}

fn sort_decl(s: &str) -> LocalDecl {
  LocalDecl {
    fvar_name: name(s),
    binder_name: name(s),
    domain: LeanExpr::sort(Level::zero()),
    info: BinderInfo::Default,
  }
}

/// Scope discipline, mirroring `Tests/Ix/Compile/BridgeScopes.lean`: each
/// violation is refused with the Lean bridge's text.
#[test]
fn tc_scope_refuses_scope_discipline_violations() {
  let stt = CompileState::new_empty();
  let mut kctx = crate::compile::KernelCtx::new();
  let x = sort_decl("x");
  let y = sort_decl("y");
  assert_refused(
    TcScope::new(&[x.clone(), x.clone()], &[], &stt, &mut kctx).map(|_| ()),
    "aux kernel bridge: duplicate outer free variable 'x'",
  );
  let uu = [name("u"), name("u")];
  assert_refused(
    TcScope::new(&[], &uu, &stt, &mut kctx).map(|_| ()),
    "aux kernel bridge: duplicate universe parameter 'u'",
  );
  {
    let mut scope =
      TcScope::new(std::slice::from_ref(&x), &[], &stt, &mut kctx).unwrap();
    assert_refused(
      scope.push_locals(std::slice::from_ref(&x)),
      "aux kernel bridge: duplicate pushed free variable 'x'",
    );
    assert_refused(
      scope.pop_locals(std::slice::from_ref(&x)),
      "aux kernel bridge: pop_locals exceeds pushed local count",
    );
  }
  let mut scope = TcScope::new(&[], &[], &stt, &mut kctx).unwrap();
  assert_refused(
    scope.push_locals(&[x.clone(), x.clone()]),
    "aux kernel bridge: duplicate pushed free variable 'x'",
  );
  // The refused telescope left nothing behind.
  assert_eq!(scope.tc.ctx.len(), 0);
  assert_eq!(scope.extra_locals, 0);
  assert!(!scope.fvar_levels.contains_key(&name("x")));
  scope.push_locals(&[x.clone(), y.clone()]).unwrap();
  assert_refused(
    scope.pop_locals(std::slice::from_ref(&x)),
    "aux kernel bridge: pop_locals is not LIFO at 'x'",
  );
  // A type checker context out of step with the scope is refused.
  scope.tc.push_local(KExpr::sort(KUniv::zero()));
  assert_refused(
    scope.push_locals(&[sort_decl("z")]),
    "aux kernel bridge: stale scope depth before push_locals",
  );
  assert_refused(
    scope.pop_locals(&[]),
    "aux kernel bridge: stale scope depth before pop_locals",
  );
  scope.tc.pop_local();
  // Valid neighbour: the actual LIFO telescope pops and leaves the scope
  // balanced; a dependent telescope infers through its outer variable.
  scope.pop_locals(&[x.clone(), y.clone()]).unwrap();
  assert_eq!(scope.tc.ctx.len(), 0);
  assert_eq!(scope.extra_locals, 0);
  assert!(scope.fvar_levels.is_empty());
}

#[test]
fn tc_scope_balanced_dependent_telescope() {
  let stt = CompileState::new_empty();
  let mut kctx = crate::compile::KernelCtx::new();
  let a = LocalDecl {
    fvar_name: name("A"),
    binder_name: name("A"),
    domain: LeanExpr::sort(Level::succ(Level::zero())),
    info: BinderInfo::Default,
  };
  let x = LocalDecl {
    fvar_name: name("x"),
    binder_name: name("x"),
    domain: LeanExpr::fvar(name("A")),
    info: BinderInfo::Default,
  };
  let mut scope =
    TcScope::new(std::slice::from_ref(&a), &[], &stt, &mut kctx).unwrap();
  scope.push_locals(std::slice::from_ref(&x)).unwrap();
  assert_same_lean(
    &scope.infer_lean(&LeanExpr::fvar(name("x"))).unwrap().unwrap(),
    &LeanExpr::fvar(name("A")),
  );
  scope.pop_locals(std::slice::from_ref(&x)).unwrap();
  assert_eq!(scope.depth(), 1);
  assert_eq!(scope.tc.ctx.len(), 1);
  assert_eq!(scope.fvar_levels.get(&name("A")), Some(&0));
  assert!(!scope.fvar_levels.contains_key(&name("x")));
}

/// From `2188b10d`: a real reduction exposing a bare source inductive that
/// shares a primitive's address keeps its own source name. This line's
/// egress never renames to a primitive's name, so the property holds without
/// the codex fix; the test guards it.
#[test]
fn reduced_inductive_alias_retains_source_name_at_primitive_pin() {
  let stt = CompileState::new_empty();
  let pin = ix_common::prim_addrs::PrimAddrs::new().nat;
  let alias = name("SourceInductiveAlias");
  stt.name_to_addr.insert(name("Nat"), pin.clone());
  stt.name_to_addr.insert(alias.clone(), pin.clone());
  let mut kctx = crate::compile::KernelCtx::new();
  kctx.kenv.insert(
    KId::new(pin, alias.clone()),
    ix_kernel::constant::KConst::Axio {
      name: alias.clone(),
      level_params: vec![],
      is_unsafe: false,
      lvls: 0,
      ty: KExpr::sort(KUniv::succ(KUniv::zero())),
    },
  );
  let mut scope = TcScope::new(&[], &[], &stt, &mut kctx).unwrap();
  let member = LeanExpr::cnst(alias, vec![]);
  let identity = LeanExpr::lam(
    Name::anon(),
    LeanExpr::sort(Level::succ(Level::zero())),
    LeanExpr::bvar(Nat::from(0u64)),
    BinderInfo::Default,
  );
  assert_same_lean(
    &scope.whnf_lean(&LeanExpr::app(identity, member.clone())).unwrap(),
    &member,
  );
}

// =========================================================================
// The aux_gen loaders return the kernel crate's Lean-ingress errors (M1-h)
// =========================================================================

fn loader_def(
  n: &str,
  lps: &[Name],
  typ: LeanExpr,
  value: LeanExpr,
) -> (Name, ConstantInfo) {
  use ix_common::env::{
    ConstantVal, DefinitionSafety, DefinitionVal, ReducibilityHints,
  };
  let nm = name(n);
  (
    nm.clone(),
    ConstantInfo::DefnInfo(DefinitionVal {
      cnst: ConstantVal { name: nm, level_params: lps.to_vec(), typ },
      value,
      hints: ReducibilityHints::Abbrev,
      safety: DefinitionSafety::Safe,
      all: vec![],
    }),
  )
}

fn assert_ingress_refused<T: std::fmt::Debug>(
  result: Result<T, ixon::CompileError>,
  constant: &str,
  kernel_text: &str,
) {
  match result {
    Err(ixon::CompileError::UnsupportedExpr { desc }) => {
      let prefix = format!("aux kernel ingress of {constant}: ");
      assert!(
        desc.starts_with(&prefix),
        "{desc:?} does not start with {prefix:?}"
      );
      assert!(desc.contains(kernel_text), "{desc:?} lacks {kernel_text:?}");
    },
    other => panic!("expected an ingress refusal of {constant}, got {other:?}"),
  }
}

fn kenv_has(
  kctx: &crate::compile::KernelCtx,
  stt: &CompileState,
  n: &Name,
) -> bool {
  let addr = resolve_lean_name_addr(
    n,
    Some(&stt.name_to_addr),
    Some(&stt.aux_name_to_addr),
  );
  kctx.kenv.get(&KId::new(addr, n.clone())).is_some()
}

/// A constant whose type names a universe parameter it does not declare, or
/// whose value has a free variable, is refused by every loader with an error
/// (before M1-h: a panic with the kernel's text); the valid neighbour (the
/// parameter declared, a closed value) loads.
#[test]
fn loaders_refuse_ill_formed_constants() {
  let stt = CompileState::new_empty();
  let u = name("u");
  let sort_u = LeanExpr::sort(Level::param(u.clone()));
  let type0 = LeanExpr::sort(Level::succ(Level::zero()));
  let mut env = ix_common::env::Env::default();
  for (n, ci) in [
    loader_def("BadLevel", &[], sort_u.clone(), LeanExpr::sort(Level::zero())),
    loader_def(
      "GoodLevel",
      std::slice::from_ref(&u),
      sort_u.clone(),
      LeanExpr::sort(Level::zero()),
    ),
    loader_def("BadFvar", &[], type0.clone(), LeanExpr::fvar(name("x"))),
    loader_def("GoodValue", &[], type0.clone(), LeanExpr::sort(Level::zero())),
  ] {
    env.insert(n, ci);
  }
  type Loader = fn(
    &Name,
    &ix_common::env::Env,
    &CompileState,
    &mut crate::compile::KernelCtx,
  ) -> Result<(), ixon::CompileError>;
  let loaders: [(&str, Loader); 4] = [
    ("ensure_in_kenv_of", ensure_in_kenv_of),
    ("ensure_full_in_kenv_of", ensure_full_in_kenv_of),
    ("ensure_in_kenv_of_prewarm", ensure_in_kenv_of_prewarm),
    ("ensure_in_kenv", ensure_in_kenv),
  ];
  for (label, load) in loaders {
    let mut kctx = crate::compile::KernelCtx::new();
    assert_ingress_refused(
      load(&name("BadLevel"), &env, &stt, &mut kctx),
      "BadLevel",
      "unknown level param `u`",
    );
    assert!(
      !kenv_has(&kctx, &stt, &name("BadLevel")),
      "{label}: BadLevel inserted"
    );
    // The prewarm loader stubs only theorem/opaque values; a definition's
    // value is ingressed by all four.
    assert_ingress_refused(
      load(&name("BadFvar"), &env, &stt, &mut kctx),
      "BadFvar",
      "unexpected FVar(x)",
    );
    assert!(
      !kenv_has(&kctx, &stt, &name("BadFvar")),
      "{label}: BadFvar inserted"
    );
    // Valid neighbours.
    load(&name("GoodLevel"), &env, &stt, &mut kctx).unwrap();
    load(&name("GoodValue"), &env, &stt, &mut kctx).unwrap();
    assert!(
      kenv_has(&kctx, &stt, &name("GoodLevel")),
      "{label}: GoodLevel missing"
    );
    assert!(
      kenv_has(&kctx, &stt, &name("GoodValue")),
      "{label}: GoodValue missing"
    );
  }
}

/// `populate_canon_kenv_with_below` returns the error of a `.below`
/// definition it cannot ingress; the valid neighbour loads.
#[test]
fn populate_canon_kenv_with_below_refuses_ill_formed_below() {
  use crate::compile::aux_gen::below::{BelowConstant, BelowDef};
  let stt = CompileState::new_empty();
  let env = ix_common::env::Env::default();
  let below = |n: &str, lps: Vec<Name>| {
    BelowConstant::Def(BelowDef {
      name: name(n),
      level_params: lps,
      typ: LeanExpr::sort(Level::param(name("u"))),
      value: LeanExpr::sort(Level::zero()),
      is_unsafe: false,
    })
  };
  let mut kctx = crate::compile::KernelCtx::new();
  assert_ingress_refused(
    crate::compile::aux_gen::populate_canon_kenv_with_below(
      &[below("T.below", vec![])],
      &[],
      &env,
      &stt,
      &mut kctx,
    ),
    "T.below",
    "unknown level param `u`",
  );
  crate::compile::aux_gen::populate_canon_kenv_with_below(
    &[below("T.below", vec![name("u")])],
    &[],
    &env,
    &stt,
    &mut kctx,
  )
  .unwrap();
  assert!(kenv_has(&kctx, &stt, &name("T.below")));
}
