//! Inductive flag controls. Raw flag mutations are not claims that Lean admits
//! inconsistent mutual blocks: the flags check refuses a wrong recursion flag,
//! the safety flag survives compilation, and the kernel refuses a block whose
//! members disagree on it.

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

fn env_of(ind: &Ind) -> LeanEnv {
  let mut env = LeanEnv::default();
  env.insert(
    ind.ind.cnst.name.clone(),
    LeanConstantInfo::InductInfo(ind.ind.clone()),
  );
  for ctor in &ind.ctors {
    env
      .insert(ctor.cnst.name.clone(), LeanConstantInfo::CtorInfo(ctor.clone()));
  }
  env
}

#[test]
fn recursion_flag_validation_still_rejects_before_compilation() {
  use super::ind_flags::validate_lean_ind_flags;
  let good = empty_ind("C6Empty");
  assert!(validate_lean_ind_flags(&env_of(&good)).is_ok());
  let mut bad = good.clone();
  bad.ind.is_rec = true;
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
fn serialization_retains_safety() {
  let safe = empty_ind("C6Empty");
  let mut unsafe_ind = safe.clone();
  unsafe_ind.ind.is_unsafe = true;
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
