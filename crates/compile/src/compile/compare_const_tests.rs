//! `compare_const` and its cache in both argument orders: a comparison is
//! returned in the orientation of the call, and a cached result read back
//! for the swapped pair is reversed. Every case runs with each member on the
//! left first, so one of the two runs has `x.name() > y.name()` whichever way
//! the names order.

use super::*;
use ix_common::env::{ConstantVal, DefinitionSafety};
use ixon::constant::DefKind;

fn name(s: &str) -> Name {
  Name::str(Name::anon(), s.to_string())
}

/// A definition with `levels` universe parameters and `Sort 0` as its type
/// and value.
fn defn(s: &str, levels: usize) -> MutConst {
  MutConst::Defn(Def {
    name: name(s),
    level_params: (0..levels).map(|i| name(&format!("u{i}"))).collect(),
    typ: LeanExpr::sort(Level::zero()),
    kind: DefKind::Definition,
    value: LeanExpr::sort(Level::zero()),
    hints: ReducibilityHints::Opaque,
    safety: DefinitionSafety::Safe,
    all: vec![],
  })
}

fn empty_ind(s: &str) -> MutConst {
  let n = name(s);
  MutConst::Indc(Ind {
    ind: InductiveVal {
      cnst: ConstantVal {
        name: n.clone(),
        level_params: vec![],
        typ: LeanExpr::sort(Level::succ(Level::zero())),
      },
      num_params: Nat::from(0u64),
      num_indices: Nat::from(0u64),
      all: vec![n],
      ctors: vec![],
      num_nested: Nat::from(0u64),
      is_rec: false,
      is_unsafe: false,
      is_reflexive: false,
    },
    ctors: vec![],
  })
}

fn cmp(x: &MutConst, y: &MutConst, cache: &mut BlockCache) -> Ordering {
  compare_const(x, y, &MutCtx::default(), cache, &CompileState::default())
    .unwrap()
}

/// `small` sorts before `large`: a fresh comparison in either orientation,
/// then the cached result read back for the swapped pair and for the same
/// pair.
fn check_pair(small: &MutConst, large: &MutConst) {
  let expected = |a: &MutConst| {
    if std::ptr::eq(a, small) { Ordering::Less } else { Ordering::Greater }
  };
  for (first, second) in [(small, large), (large, small)] {
    let mut cache = BlockCache::default();
    assert_eq!(cmp(first, second, &mut cache), expected(first));
    assert_eq!(cmp(second, first, &mut cache), expected(second));
    assert_eq!(cmp(first, second, &mut cache), expected(first));
  }
}

#[test]
fn fresh_and_cached_comparisons_keep_the_call_orientation() {
  check_pair(&defn("CmpOrientA", 0), &defn("CmpOrientB", 1));
  check_pair(&defn("CmpOrientB", 0), &defn("CmpOrientA", 1));
}

#[test]
fn mixed_kinds_order_by_kind_tag_in_both_orientations() {
  check_pair(&defn("CmpKindD", 0), &empty_ind("CmpKindI"));
  check_pair(&defn("CmpKindI2", 0), &empty_ind("CmpKindD2"));
}

#[test]
fn equal_members_compare_equal_in_both_orientations() {
  let x = defn("CmpEqualX", 0);
  let y = defn("CmpEqualY", 0);
  let mut cache = BlockCache::default();
  assert_eq!(cmp(&x, &y, &mut cache), Ordering::Equal);
  assert_eq!(cmp(&y, &x, &mut cache), Ordering::Equal);
  assert_eq!(cmp(&x, &y, &mut cache), Ordering::Equal);
}

#[test]
fn sort_consts_orders_by_content_whatever_the_names() {
  for (small, large) in [("CmpSortA", "CmpSortB"), ("CmpSortB", "CmpSortA")] {
    let members = [defn(large, 1), defn(small, 0)];
    let classes = sort_consts(
      &[&members[0], &members[1]],
      &mut BlockCache::default(),
      &CompileState::default(),
    )
    .unwrap();
    let reps: Vec<Name> = classes.iter().map(|c| c[0].name()).collect();
    assert_eq!(reps, vec![name(small), name(large)]);
  }
}

/// A definition of type `Type` whose value is `let x : Type := Prop; #body`
/// with the binder name `binder` and the nondependency bit `non_dep` (`let`
/// when false, `have` when true).
fn let_defn(s: &str, binder: &str, body: u64, non_dep: bool) -> MutConst {
  let ty = LeanExpr::sort(Level::succ(Level::zero()));
  let value = LeanExpr::letE(
    name(binder),
    ty.clone(),
    LeanExpr::sort(Level::zero()),
    LeanExpr::bvar(Nat::from(body)),
    non_dep,
  );
  MutConst::Defn(Def {
    name: name(s),
    level_params: vec![],
    typ: ty,
    kind: DefKind::Definition,
    value,
    hints: ReducibilityHints::Opaque,
    safety: DefinitionSafety::Safe,
    all: vec![],
  })
}

#[test]
fn let_non_dep_is_a_key_after_the_let_children() {
  // equal type, value and body: the bit decides, `let` before `have`
  check_pair(
    &let_defn("CmpLetA", "x", 0, false),
    &let_defn("CmpLetB", "x", 0, true),
  );
  check_pair(
    &let_defn("CmpLetB2", "x", 0, false),
    &let_defn("CmpLetA2", "x", 0, true),
  );
  // the body decides before the bit, whichever way the bits go
  check_pair(
    &let_defn("CmpLetBodyA", "x", 0, true),
    &let_defn("CmpLetBodyB", "x", 1, false),
  );
  // the same bit under another binder name: equal
  let x = let_defn("CmpLetSameX", "x", 0, false);
  let y = let_defn("CmpLetSameY", "y", 0, false);
  let mut cache = BlockCache::default();
  assert_eq!(cmp(&x, &y, &mut cache), Ordering::Equal);
  assert_eq!(cmp(&y, &x, &mut cache), Ordering::Equal);
}

#[test]
fn members_that_differ_only_in_a_let_bit_are_two_classes() {
  let have_form = let_defn("CmpLetClassHave", "x", 0, true);
  let let_form = let_defn("CmpLetClassLet", "x", 0, false);
  for members in [[&have_form, &let_form], [&let_form, &have_form]] {
    let classes = sort_consts(
      &members,
      &mut BlockCache::default(),
      &CompileState::default(),
    )
    .unwrap();
    let shape: Vec<Vec<Name>> =
      classes.iter().map(|c| c.iter().map(|m| m.name()).collect()).collect();
    assert_eq!(
      shape,
      vec![vec![name("CmpLetClassLet")], vec![name("CmpLetClassHave")]]
    );
  }
  // the same bit under another binder name: one class
  let neighbour = let_defn("CmpLetClassNeighbour", "y", 0, false);
  let classes = sort_consts(
    &[&let_form, &neighbour],
    &mut BlockCache::default(),
    &CompileState::default(),
  )
  .unwrap();
  assert_eq!(classes.len(), 1);
  assert_eq!(classes[0].len(), 2);
}
