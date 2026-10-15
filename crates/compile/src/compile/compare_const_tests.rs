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
