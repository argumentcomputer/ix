//! C6 ordering controls. Raw flag mutations test the comparator's full input
//! domain; they are not claims that Lean admits inconsistent mutual blocks.

use super::*;
use ix_common::env::ConstantVal;

fn name(s: &str) -> Name {
  Name::str(Name::anon(), s.to_string())
}

fn empty_ind(s: &str) -> Ind {
  let n = name(s);
  Ind {
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
  }
}

fn compare(x: &Ind, y: &Ind) -> Result<SOrd, CompileError> {
  compare_indc(
    x,
    y,
    &MutCtx::default(),
    &mut BlockCache::default(),
    &CompileState::default(),
  )
}

fn env_of(ind: &Ind) -> LeanEnv {
  let mut env = LeanEnv::default();
  env.insert(
    ind.ind.cnst.name.clone(),
    LeanConstantInfo::InductInfo(ind.ind.clone()),
  );
  for ctor in &ind.ctors {
    env.insert(
      ctor.cnst.name.clone(),
      LeanConstantInfo::CtorInfo(ctor.clone()),
    );
  }
  env
}

#[test]
fn flag_only_differences_compare_equal_in_both_directions() {
  let x = empty_ind("C6Left");
  for (is_rec, is_unsafe) in
    [(false, false), (true, false), (false, true), (true, true)]
  {
    let mut y = empty_ind("C6Right");
    y.ind.is_rec = is_rec;
    y.ind.is_unsafe = is_unsafe;
    for (a, b) in [(&x, &y), (&y, &x)] {
      let result = compare(a, b).unwrap();
      assert_eq!(result.ordering, Ordering::Equal);
      assert!(result.strong);
    }
    // The actual partitioner must also use the common content key.
    let members = [MutConst::Indc(x.clone()), MutConst::Indc(y)];
    let classes = sort_consts(
      &[&members[0], &members[1]],
      &mut BlockCache::default(),
      &CompileState::default(),
    )
    .unwrap();
    assert_eq!(classes.len(), 1);
    assert_eq!(classes[0].len(), 2);
  }
}

#[test]
fn content_keys_decide_even_when_flags_order_the_other_way() {
  let mut x = empty_ind("C6Left");
  x.ind.is_rec = true;
  x.ind.is_unsafe = true;
  let base = empty_ind("C6Right");
  let mut universe = base.clone();
  universe.ind.cnst.level_params.push(name("u"));
  let mut params = base.clone();
  params.ind.num_params = Nat::from(1u64);
  let mut indices = base.clone();
  indices.ind.num_indices = Nat::from(1u64);
  let mut ctors = base.clone();
  ctors.ind.ctors.push(name("mk"));
  let mut typ = base;
  typ.ind.cnst.typ = LeanExpr::sort(Level::succ(Level::succ(Level::zero())));
  // These header mutations isolate individual keys; validation is separate.
  for y in [universe, params, indices, ctors, typ] {
    let forward = compare(&x, &y).unwrap();
    let backward = compare(&y, &x).unwrap();
    assert_eq!(forward.ordering, Ordering::Less);
    assert_eq!(backward.ordering, Ordering::Greater);
    assert!(forward.strong && backward.strong);
  }
}

#[test]
fn differing_flags_do_not_hide_comparison_errors() {
  let x = empty_ind("C6Left");
  let mut y = empty_ind("C6Right");
  y.ind.is_rec = true;
  y.ind.cnst.typ = LeanExpr::fvar(name("free"));
  assert!(matches!(
    compare(&x, &y),
    Err(CompileError::UnsupportedExpr { desc }) if desc == "fvar in comparison"
  ));
  y.ind.is_rec = false;
  y.ind.is_unsafe = true;
  y.ind.cnst.typ = LeanExpr::sort(Level::param(name("unbound")));
  assert!(matches!(
    compare(&x, &y),
    Err(CompileError::UnknownUnivParam { .. })
  ));
  // A valid structural neighbour still compares successfully.
  y.ind.cnst.typ = x.ind.cnst.typ.clone();
  assert_eq!(compare(&x, &y).unwrap().ordering, Ordering::Equal);
}

#[test]
fn recursion_flag_validation_still_rejects_before_compilation() {
  use super::aux_gen::nested::validate_lean_ind_flags;
  let good = empty_ind("C6Empty");
  assert!(validate_lean_ind_flags(&env_of(&good)).is_ok());
  let mut bad = good.clone();
  bad.ind.is_rec = true;
  assert_eq!(compare(&good, &bad).unwrap().ordering, Ordering::Equal);
  let env = env_of(&bad);
  assert!(matches!(
    validate_lean_ind_flags(&env),
    Err(CompileError::InvalidMutualBlock { reason })
      if reason.contains("non-canonical inductive flags")
  ));
  assert!(matches!(
    compile_env(&Arc::new(env)),
    Err(CompileError::InvalidMutualBlock { reason })
      if reason.contains("non-canonical inductive flags")
  ));
}

#[test]
fn serialization_retains_safety_after_comparator_equality() {
  let safe = empty_ind("C6Empty");
  let mut unsafe_ind = safe.clone();
  unsafe_ind.ind.is_unsafe = true;
  assert_eq!(compare(&safe, &unsafe_ind).unwrap().ordering, Ordering::Equal);
  for ind in [safe, unsafe_ind] {
    let (compiled, _, _) = compile_inductive(
      &ind,
      &MutCtx::default(),
      &[],
      &mut BlockCache::default(),
      &CompileState::default(),
    )
    .unwrap();
    assert_eq!(compiled.is_unsafe, ind.ind.is_unsafe);
  }
}

#[test]
fn kernel_safety_check_rejects_disagreement_and_accepts_neighbours() {
  use ix_kernel::{
    constant::KConst, env::KEnv, error::TcError, expr::KExpr, id::KId,
    level::KUniv, mode::Anon, tc::TypeChecker,
  };
  // Two empty members of one block: no constructor or recursion issue can
  // mask the safety check. This exercises the unchanged kernel validation.
  for (left, right) in
    [(false, false), (true, true), (false, true), (true, false)]
  {
    let mut env = KEnv::<Anon>::new();
    let block = KId::new(Address::hash(b"C6Block"), ());
    let ids = [
      KId::new(Address::hash(b"C6Left"), ()),
      KId::new(Address::hash(b"C6Right"), ()),
    ];
    for (i, is_unsafe) in [left, right].into_iter().enumerate() {
      env.insert(
        ids[i].clone(),
        KConst::Indc {
          name: (),
          level_params: (),
          lvls: 0,
          params: 0,
          indices: 0,
          is_unsafe,
          block: block.clone(),
          member_idx: i as u64,
          ty: KExpr::sort(KUniv::succ(KUniv::zero())),
          ctors: vec![],
          lean_all: (),
        },
      );
    }
    env.blocks.insert(block, ids.to_vec());
    let result = TypeChecker::new(&mut env).check_const(&ids[0]);
    if left == right {
      assert!(result.is_ok(), "valid safety neighbour: {result:?}");
    } else {
      assert!(matches!(
        result,
        Err(TcError::Other(reason)) if reason.contains("same safety flag")
      ));
    }
  }
}
