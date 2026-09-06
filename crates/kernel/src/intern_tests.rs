//! Differential semantics and DAG-work bounds for the kernel interner.

use super::*;
use crate::expr::{ExprData, FVarId, MData, fresh_uid};
use crate::level::UnivData;
use crate::mode::{Anon, Meta};
use crate::profile::take_op_counts;
use bignat::Nat;
use ix_common::env::{BinderInfo, DataValue, Name};
use ixon::univ::Univ;

fn name(s: &str) -> Name {
  Name::str(Name::anon(), s.to_owned())
}

fn metadata(s: &str) -> Vec<MData> {
  vec![vec![(name("tag"), DataValue::OfString(s.to_owned()))]]
}

// Unlike KExpr/KUniv equality, these comparisons include ALL metadata and
// cached annotations, ignoring only fresh ephemeral uids. Compare DAGs without
// expanding shared subtrees or formatting an enormous expression on failure.
fn assert_same_univ<M: KernelMode>(a: &KUniv<M>, b: &KUniv<M>) {
  let mut pending = vec![(a, b)];
  let mut seen = FxHashSet::default();
  while let Some((a, b)) = pending.pop() {
    if !seen.insert((
      std::ptr::from_ref(a.data()).addr(),
      std::ptr::from_ref(b.data()).addr(),
    )) {
      continue;
    }
    match (a.data(), b.data()) {
      (UnivData::Zero(_), UnivData::Zero(_)) => {},
      (UnivData::Param(i, n, _), UnivData::Param(j, m, _)) => {
        assert_eq!(i, j);
        assert_eq!(n, m);
      },
      (UnivData::Succ(a, _), UnivData::Succ(b, _)) => pending.push((a, b)),
      (UnivData::Max(a, b, _), UnivData::Max(c, d, _))
      | (UnivData::IMax(a, b, _), UnivData::IMax(c, d, _)) => {
        pending.extend([(a, c), (b, d)]);
      },
      _ => panic!("universe variants differ"),
    }
  }
}

fn assert_same_expr<M: KernelMode>(a: &KExpr<M>, b: &KExpr<M>) {
  let mut pending = vec![(a, b)];
  let mut seen = FxHashSet::default();
  while let Some((a, b)) = pending.pop() {
    if !seen.insert((
      std::ptr::from_ref(a.data()).addr(),
      std::ptr::from_ref(b.data()).addr(),
    )) {
      continue;
    }
    assert_eq!(a.lbr(), b.lbr());
    assert_eq!(a.count_0(), b.count_0());
    assert_eq!(a.info().has_fvars, b.info().has_fvars);
    assert_eq!(a.mdata(), b.mdata());
    assert_eq!(a.univ_decor(), b.univ_decor());
    match (a.data(), b.data()) {
      (ExprData::Var(i, n, _), ExprData::Var(j, m, _)) => {
        assert_eq!(i, j);
        assert_eq!(n, m);
      },
      (ExprData::FVar(i, n, _), ExprData::FVar(j, m, _)) => {
        assert_eq!(i, j);
        assert_eq!(n, m);
      },
      (ExprData::Sort(u, _), ExprData::Sort(v, _)) => assert_same_univ(u, v),
      (ExprData::Const(i, us, _), ExprData::Const(j, vs, _)) => {
        assert_eq!(i, j);
        assert_eq!(us.len(), vs.len());
        for (u, v) in us.iter().zip(vs) {
          assert_same_univ(u, v);
        }
      },
      (ExprData::App(f, a, _), ExprData::App(g, b, _)) => {
        pending.extend([(f, g), (a, b)]);
      },
      (ExprData::Lam(n, bi, t, b, _), ExprData::Lam(m, bj, u, c, _))
      | (ExprData::All(n, bi, t, b, _), ExprData::All(m, bj, u, c, _)) => {
        assert_eq!(n, m);
        assert_eq!(bi, bj);
        pending.extend([(t, u), (b, c)]);
      },
      (ExprData::Let(n, t, v, b, nd, _), ExprData::Let(m, u, w, c, md, _)) => {
        assert_eq!(n, m);
        assert_eq!(nd, md);
        pending.extend([(t, u), (v, w), (b, c)]);
      },
      (ExprData::Prj(i, f, v, _), ExprData::Prj(j, g, w, _)) => {
        assert_eq!(i, j);
        assert_eq!(f, g);
        pending.push((v, w));
      },
      (ExprData::Nat(n, a, _), ExprData::Nat(m, b, _)) => {
        assert_eq!(n, m);
        assert_eq!(a, b);
      },
      (ExprData::Str(s, a, _), ExprData::Str(t, b, _)) => {
        assert_eq!(s, t);
        assert_eq!(a, b);
      },
      _ => panic!("expression variants differ"),
    }
  }
}

fn expr_dag<M: KernelMode>(mut leaf: KExpr<M>, depth: usize) -> KExpr<M> {
  for _ in 0..depth {
    leaf = KExpr::all(
      M::meta_field(name("x")),
      M::meta_field(BinderInfo::Default),
      leaf.clone(),
      leaf,
    );
  }
  leaf
}

fn univ_dag<M: KernelMode>(mut leaf: KUniv<M>, depth: usize) -> KUniv<M> {
  for _ in 0..depth {
    // Use raw constructors: interning must preserve even unsimplified Max.
    leaf = KUniv::new(UnivData::Max(leaf.clone(), leaf, fresh_uid()));
  }
  leaf
}

fn fixtures<M: KernelMode>(label: &str) -> Vec<KExpr<M>> {
  let n = M::meta_field(name(label));
  let md = M::meta_field(metadata(label));
  let id = KId::new(Address::hash(b"constant"), n.clone());
  let u = KUniv::param(0, n.clone());
  let v = KUniv::param(1, n.clone());
  let levels = vec![
    KUniv::zero(),
    KUniv::succ(u.clone()),
    KUniv::new(UnivData::Max(u.clone(), v.clone(), fresh_uid())),
    KUniv::new(UnivData::IMax(v, u.clone(), fresh_uid())),
    u,
  ];
  let var = KExpr::var_mdata(0, n.clone(), md.clone());
  let fvar = KExpr::fvar_mdata(FVarId(7), n.clone(), md.clone());
  let cnst = KExpr::cnst_mdata(id.clone(), levels.clone().into(), md.clone());
  let shared = KExpr::app_mdata(cnst.clone(), fvar.clone(), md.clone());
  let mut roots = vec![
    var.clone(),
    fvar,
    cnst,
    shared.clone(),
    KExpr::prj_mdata(id, 2, shared.clone(), md.clone()),
    KExpr::nat_mdata(Nat::from(17u64), Address::hash(b"17"), md.clone()),
    KExpr::str_mdata("hello".to_owned(), Address::hash(b"hello"), md.clone()),
    expr_dag(shared.clone(), 6),
  ];
  for level in levels {
    roots.push(KExpr::sort_mdata(level, md.clone()));
  }
  for bi in [
    BinderInfo::Default,
    BinderInfo::Implicit,
    BinderInfo::StrictImplicit,
    BinderInfo::InstImplicit,
  ] {
    roots.push(KExpr::lam_mdata(
      n.clone(),
      M::meta_field(bi.clone()),
      shared.clone(),
      var.clone(),
      md.clone(),
    ));
    roots.push(KExpr::all_mdata(
      n.clone(),
      M::meta_field(bi),
      shared.clone(),
      var.clone(),
      md.clone(),
    ));
  }
  for non_dep in [false, true] {
    roots.push(KExpr::let_mdata(
      n.clone(),
      shared.clone(),
      var.clone(),
      shared.clone(),
      non_dep,
      md.clone(),
    ));
  }
  roots
}

fn differential<M: KernelMode>() {
  for seeded in [false, true] {
    let mut old = InternTable::<M>::new();
    let mut new = InternTable::<M>::new();
    if seeded {
      for seed in fixtures("first") {
        old.intern_expr_reference(seed.clone());
        new.intern_expr(seed);
      }
    }
    for root in fixtures("second") {
      let expected = old.intern_expr_reference(root.clone());
      let actual = new.intern_expr(root.clone());
      assert_same_expr(&actual, &expected);
      assert!(new.intern_expr(root).ptr_eq(&actual));
      take_op_counts();
      assert!(new.intern_expr(actual.clone()).ptr_eq(&actual));
      assert_eq!(take_op_counts().intern_nodes, 1);
    }
    assert_eq!(new.exprs.len(), old.exprs.len());
    assert_eq!(new.univs.len(), old.univs.len());
    assert_eq!(new.canon_exprs.len(), old.canon_exprs.len());
    assert_eq!(new.canon_univs.len(), old.canon_univs.len());
  }
}

#[test]
fn interning_matches_reference_in_both_modes_and_seeded_tables() {
  differential::<Meta>();
  differential::<Anon>();
}

#[test]
fn shared_expression_dag_visits_edges_not_expanded_tree() {
  let depth = 60;
  let mut intern = InternTable::<Anon>::new();
  intern.intern_expr(KExpr::sort(KUniv::zero()));
  let root = expr_dag(KExpr::sort(KUniv::zero()), depth);
  let mut previous: Option<KExpr<Anon>> = None;
  for _ in 0..2 {
    take_op_counts();
    let result = intern.intern_expr(root.clone());
    assert_eq!(take_op_counts().intern_nodes, (2 * depth + 2) as u64);
    if let Some(previous) = previous.replace(result.clone()) {
      assert!(previous.ptr_eq(&result));
    }
    let mut cursor = &result;
    for _ in 0..depth {
      let ExprData::All(_, _, ty, body, _) = cursor.data() else {
        panic!("all")
      };
      assert!(ty.ptr_eq(body));
      cursor = ty;
    }
    assert_eq!(intern.exprs.len(), depth + 1);
    assert!(!intern.canon_exprs.contains(root.addr()));
  }
}

#[test]
fn shared_universe_dag_is_memoized_across_constant_arguments() {
  let depth = 60;
  let mut intern = InternTable::<Anon>::new();
  intern.intern_univ(KUniv::zero());
  let level = univ_dag(KUniv::zero(), depth);
  take_op_counts();
  let canonical = intern.intern_univ(level.clone());
  assert_eq!(take_op_counts().intern_nodes, (2 * depth + 1) as u64);
  let root = KExpr::cnst(
    KId::new(Address::hash(b"C"), ()),
    vec![level.clone(); 64].into(),
  );
  take_op_counts();
  let result = intern.intern_expr(root);
  assert_eq!(take_op_counts().intern_nodes, (2 * depth + 65) as u64);
  let ExprData::Const(_, levels, _) = result.data() else { panic!("const") };
  assert!(levels.iter().all(|u| u.ptr_eq(&canonical)));
  let mut cursor = &canonical;
  for _ in 0..depth {
    let UnivData::Max(a, b, _) = cursor.data() else { panic!("max") };
    assert!(a.ptr_eq(b));
    cursor = a;
  }
  assert_eq!(intern.univs.len(), depth + 1);
  assert!(!intern.canon_univs.contains(level.addr()));
}

#[test]
fn unchanged_inputs_use_canonical_fast_path_without_memo_entries() {
  let mut intern = InternTable::<Anon>::new();
  let root = expr_dag(KExpr::sort(KUniv::zero()), 40);
  let mut memo = InternMemo::default();
  let result = intern.intern_expr_cached(&root, &mut memo);
  assert!(result.ptr_eq(&root));
  assert_eq!(memo.exprs.capacity(), 0);
  assert_eq!(memo.univs.capacity(), 0);
}

#[test]
fn input_pointer_keys_preserve_same_uid_spelling_twins() {
  for is_const in [false, true] {
    let level = KUniv::zero();
    let a = if is_const {
      KExpr::<Meta>::cnst_mdata(
        KId::new(Address::hash(b"C"), name("A")),
        vec![level.clone()].into(),
        metadata("A"),
      )
    } else {
      KExpr::sort_mdata(level.clone(), metadata("A"))
    };
    let mut info = a.info().clone();
    info.mdata = metadata("B");
    let spelling = Univ::imax(Univ::succ(Univ::zero()), Univ::zero());
    let b = if is_const {
      info.univ_decor = Some(UnivDecor::Const(vec![spelling].into()));
      KExpr::new(ExprData::Const(
        KId::new(Address::hash(b"C"), name("B")),
        vec![level].into(),
        info,
      ))
    } else {
      info.univ_decor = Some(UnivDecor::Sort(spelling));
      KExpr::new(ExprData::Sort(level, info))
    };
    assert_eq!(a.addr(), b.addr());
    assert!(!a.ptr_eq(&b));
    let root = KExpr::app(a.clone(), KExpr::app(b, a));
    let mut old = InternTable::new();
    let mut new = InternTable::new();
    // Force both spelling occurrences to be rebuilt, so their shared input
    // uid never becomes canonical and a uid-keyed memo would conflate them.
    old.intern_univ_reference(KUniv::zero());
    new.intern_univ(KUniv::zero());
    let expected = old.intern_expr_reference(root.clone());
    let result = new.intern_expr(root);
    assert_same_expr(&result, &expected);
    let ExprData::App(a, rest, _) = result.data() else { panic!("app") };
    let ExprData::App(b, again, _) = rest.data() else { panic!("app") };
    assert!(!a.ptr_eq(b));
    assert!(a.ptr_eq(again));
    assert_eq!(a.mdata(), &metadata("A"));
    assert_eq!(b.mdata(), &metadata("B"));
    assert_ne!(a.univ_decor(), b.univ_decor());
  }
}

#[test]
fn already_canonical_uid_fast_path_preserves_occurrence_metadata() {
  let a = KExpr::<Meta>::var(0, name("A"));
  let mut info = a.info().clone();
  info.mdata = metadata("B");
  let b = KExpr::new(ExprData::Var(0, name("B"), info));
  let root = KExpr::app(a, b.clone());
  let expected = InternTable::new().intern_expr_reference(root.clone());
  let result = InternTable::new().intern_expr(root);
  assert_same_expr(&result, &expected);
  let ExprData::App(_, rhs, _) = result.data() else { panic!("app") };
  assert!(rhs.ptr_eq(&b));
}

#[test]
fn memo_does_not_survive_calls_or_environment_clears() {
  let mut env = KEnv::<Meta>::new();
  let leaf = KExpr::var(0, name("input"));
  let root = expr_dag(leaf, 6);
  for label in ["first", "second", "third"] {
    env.clear();
    let seed = KExpr::var_mdata(0, name(label), metadata(label));
    env.intern.intern_expr(seed.clone());
    let result = env.intern.intern_expr(root.clone());
    let mut old = InternTable::new();
    old.intern_expr_reference(seed);
    assert_same_expr(&result, &old.intern_expr_reference(root.clone()));
    assert!(env.intern.intern_expr(root.clone()).ptr_eq(&result));
  }
}

#[test]
#[ignore = "manual release benchmark; no wall-clock assertions"]
fn benchmark_shared_dag_interning() {
  use std::time::Instant;
  for depth in [12, 16, 20] {
    let root = expr_dag(KExpr::sort(KUniv::zero()), depth);
    let mut old = InternTable::<Anon>::new();
    let mut new = InternTable::<Anon>::new();
    old.intern_expr_reference(KExpr::sort(KUniv::zero()));
    new.intern_expr(KExpr::sort(KUniv::zero()));
    take_op_counts();
    let start = Instant::now();
    let expected = old.intern_expr_reference(root.clone());
    let old_time = start.elapsed();
    let old_visits = take_op_counts().intern_nodes;
    let start = Instant::now();
    let result = new.intern_expr(root.clone());
    let new_time = start.elapsed();
    let new_visits = take_op_counts().intern_nodes;
    assert_same_expr(&result, &expected);
    eprintln!(
      "depth={depth}: tree={old_time:?} ({old_visits} visits), \
       dag={new_time:?} ({new_visits} visits)"
    );
  }
}

#[test]
#[ignore = "manual release benchmark; no wall-clock assertions"]
fn benchmark_small_expression_interning() {
  use std::hint::black_box;
  use std::time::Instant;
  for workload in ["canonical", "duplicate leaf", "duplicate app", "fresh app"]
  {
    for reference in [true, false] {
      let intern: fn(&mut InternTable<Anon>, KExpr<Anon>) -> KExpr<Anon> =
        if reference {
          InternTable::intern_expr_reference
        } else {
          InternTable::intern_expr
        };
      let mut table = InternTable::new();
      let f = intern(&mut table, KExpr::var(1, ()));
      let a = intern(&mut table, KExpr::var(0, ()));
      let start = Instant::now();
      for i in 0..100_000 {
        let input = match workload {
          "canonical" => a.clone(),
          "duplicate leaf" => KExpr::var(0, ()),
          "duplicate app" => KExpr::app(f.clone(), a.clone()),
          "fresh app" => {
            let arg = intern(&mut table, KExpr::var(i + 2, ()));
            KExpr::app(f.clone(), arg)
          },
          _ => unreachable!(),
        };
        black_box(intern(&mut table, input));
      }
      eprintln!("{workload}, reference={reference}: {:?}", start.elapsed());
    }
  }
}
