use crate::ix::env::*;
use crate::lean::nat::Nat;

use super::error::TcError;
use super::level;
use super::tc::TypeChecker;
use super::whnf::{inst, unfold_apps};

type TcResult<T> = Result<T, TcError>;

/// Validate an inductive type declaration.
/// Performs structural checks: constructors exist, belong to this inductive,
/// and have well-formed types. Mutual types are verified to exist.
pub fn check_inductive(
  ind: &InductiveVal,
  tc: &mut TypeChecker,
) -> TcResult<()> {
  // Verify the type is well-formed
  tc.check_declar_info(&ind.cnst)?;

  // Verify all constructors exist and belong to this inductive
  for ctor_name in &ind.ctors {
    let ctor_ci = tc.env.get(ctor_name).ok_or_else(|| {
      TcError::UnknownConst { name: ctor_name.clone() }
    })?;
    let ctor = match ctor_ci {
      ConstantInfo::CtorInfo(c) => c,
      _ => {
        return Err(TcError::KernelException {
          msg: format!(
            "{} is not a constructor",
            ctor_name.pretty()
          ),
        })
      },
    };
    // Verify constructor's induct field matches
    if ctor.induct != ind.cnst.name {
      return Err(TcError::KernelException {
        msg: format!(
          "constructor {} belongs to {} but expected {}",
          ctor_name.pretty(),
          ctor.induct.pretty(),
          ind.cnst.name.pretty()
        ),
      });
    }
    // Verify constructor type is well-formed
    tc.check_declar_info(&ctor.cnst)?;
  }

  // Verify constructor return types and positivity
  for ctor_name in &ind.ctors {
    let ctor = match tc.env.get(ctor_name) {
      Some(ConstantInfo::CtorInfo(c)) => c,
      _ => continue, // already checked above
    };
    check_ctor_return_type(ctor, ind, tc)?;
    if !ind.is_unsafe {
      check_ctor_positivity(ctor, ind, tc)?;
      check_field_universe_constraints(ctor, ind, tc)?;
    }
  }

  // Verify all mutual types exist
  for name in &ind.all {
    if tc.env.get(name).is_none() {
      return Err(TcError::UnknownConst { name: name.clone() });
    }
  }

  Ok(())
}

/// Validate that a recursor's K flag is consistent with the inductive's structure.
/// K-target requires: non-mutual, in Prop, single constructor, zero fields.
/// If `rec.k == true` but conditions don't hold, reject.
pub fn validate_k_flag(
  rec: &RecursorVal,
  env: &Env,
) -> TcResult<()> {
  if !rec.k {
    return Ok(()); // conservative false is always fine
  }

  // Must be non-mutual: `rec.all` should have exactly 1 inductive
  if rec.all.len() != 1 {
    return Err(TcError::KernelException {
      msg: "recursor claims K but inductive is mutual".into(),
    });
  }

  let ind_name = &rec.all[0];
  let ind = match env.get(ind_name) {
    Some(ConstantInfo::InductInfo(iv)) => iv,
    _ => {
      return Err(TcError::KernelException {
        msg: format!(
          "recursor claims K but {} is not an inductive",
          ind_name.pretty()
        ),
      })
    },
  };

  // Must be in Prop (Sort 0)
  // Walk type telescope past all binders to get the sort
  let mut ty = ind.cnst.typ.clone();
  loop {
    match ty.as_data() {
      ExprData::ForallE(_, _, body, _, _) => {
        ty = body.clone();
      },
      _ => break,
    }
  }
  let is_prop = match ty.as_data() {
    ExprData::Sort(l, _) => level::is_zero(l),
    _ => false,
  };
  if !is_prop {
    return Err(TcError::KernelException {
      msg: format!(
        "recursor claims K but {} is not in Prop",
        ind_name.pretty()
      ),
    });
  }

  // Must have single constructor
  if ind.ctors.len() != 1 {
    return Err(TcError::KernelException {
      msg: format!(
        "recursor claims K but {} has {} constructors (need 1)",
        ind_name.pretty(),
        ind.ctors.len()
      ),
    });
  }

  // Constructor must have zero fields (all args are params)
  let ctor_name = &ind.ctors[0];
  if let Some(ConstantInfo::CtorInfo(c)) = env.get(ctor_name) {
    if c.num_fields != Nat::ZERO {
      return Err(TcError::KernelException {
        msg: format!(
          "recursor claims K but constructor {} has {} fields (need 0)",
          ctor_name.pretty(),
          c.num_fields
        ),
      });
    }
  }

  Ok(())
}

/// Check if an expression mentions a constant by name.
fn expr_mentions_const(e: &Expr, name: &Name) -> bool {
  let mut stack: Vec<&Expr> = vec![e];
  while let Some(e) = stack.pop() {
    match e.as_data() {
      ExprData::Const(n, _, _) => {
        if n == name {
          return true;
        }
      },
      ExprData::App(f, a, _) => {
        stack.push(f);
        stack.push(a);
      },
      ExprData::Lam(_, t, b, _, _) | ExprData::ForallE(_, t, b, _, _) => {
        stack.push(t);
        stack.push(b);
      },
      ExprData::LetE(_, t, v, b, _, _) => {
        stack.push(t);
        stack.push(v);
        stack.push(b);
      },
      ExprData::Proj(_, _, s, _) => stack.push(s),
      ExprData::Mdata(_, inner, _) => stack.push(inner),
      _ => {},
    }
  }
  false
}

/// Check that no inductive name from `ind.all` appears in a negative position
/// in the constructor's field types.
fn check_ctor_positivity(
  ctor: &ConstructorVal,
  ind: &InductiveVal,
  tc: &mut TypeChecker,
) -> TcResult<()> {
  let num_params = ind.num_params.to_u64().unwrap() as usize;
  let mut ty = ctor.cnst.typ.clone();

  // Skip parameter binders
  for _ in 0..num_params {
    let whnf_ty = tc.whnf(&ty);
    match whnf_ty.as_data() {
      ExprData::ForallE(name, binder_type, body, _, _) => {
        let local = tc.mk_local(name, binder_type);
        ty = inst(body, &[local]);
      },
      _ => return Ok(()), // fewer binders than params — odd but not our problem
    }
  }

  // For each remaining field, check its domain for positivity
  loop {
    let whnf_ty = tc.whnf(&ty);
    match whnf_ty.as_data() {
      ExprData::ForallE(name, binder_type, body, _, _) => {
        // The domain is the field type — check strict positivity
        check_strict_positivity(binder_type, &ind.all, tc)?;
        let local = tc.mk_local(name, binder_type);
        ty = inst(body, &[local]);
      },
      _ => break,
    }
  }

  Ok(())
}

/// Check strict positivity of a field type w.r.t. a set of inductive names.
///
/// Strict positivity for `T` w.r.t. `I`:
/// - If `T` doesn't mention `I`, OK.
/// - If `T = I args...`, OK (the inductive itself at the head).
/// - If `T = (x : A) → B`, then `A` must NOT mention `I` at all,
///   and `B` must satisfy strict positivity w.r.t. `I`.
/// - Otherwise (I appears but not at head and not in Pi), reject.
fn check_strict_positivity(
  ty: &Expr,
  ind_names: &[Name],
  tc: &mut TypeChecker,
) -> TcResult<()> {
  let mut current = ty.clone();
  loop {
    let whnf_ty = tc.whnf(&current);

    // If no inductive name is mentioned, we're fine
    if !ind_names.iter().any(|n| expr_mentions_const(&whnf_ty, n)) {
      return Ok(());
    }

    match whnf_ty.as_data() {
      ExprData::ForallE(_, domain, body, _, _) => {
        // Domain must NOT mention any inductive name
        for ind_name in ind_names {
          if expr_mentions_const(domain, ind_name) {
            return Err(TcError::KernelException {
              msg: format!(
                "inductive {} occurs in negative position (strict positivity violation)",
                ind_name.pretty()
              ),
            });
          }
        }
        // Continue with body (was tail-recursive)
        current = body.clone();
      },
      _ => {
        // The inductive is mentioned and we're not in a Pi — check if
        // it's simply an application `I args...` (which is OK).
        let (head, _) = unfold_apps(&whnf_ty);
        match head.as_data() {
          ExprData::Const(name, _, _)
            if ind_names.iter().any(|n| n == name) =>
          {
            return Ok(());
          },
          _ => {
            return Err(TcError::KernelException {
              msg: "inductive type occurs in a non-positive position".into(),
            });
          },
        }
      },
    }
  }
}

/// Check that constructor field types live in universes ≤ the inductive's universe.
fn check_field_universe_constraints(
  ctor: &ConstructorVal,
  ind: &InductiveVal,
  tc: &mut TypeChecker,
) -> TcResult<()> {
  // Walk the inductive type telescope past num_params binders to find the sort level.
  let num_params = ind.num_params.to_u64().unwrap() as usize;
  let mut ind_ty = ind.cnst.typ.clone();
  for _ in 0..num_params {
    let whnf_ty = tc.whnf(&ind_ty);
    match whnf_ty.as_data() {
      ExprData::ForallE(name, binder_type, body, _, _) => {
        let local = tc.mk_local(name, binder_type);
        ind_ty = inst(body, &[local]);
      },
      _ => return Ok(()),
    }
  }
  // Skip remaining binders (indices) to get to the target sort
  loop {
    let whnf_ty = tc.whnf(&ind_ty);
    match whnf_ty.as_data() {
      ExprData::ForallE(name, binder_type, body, _, _) => {
        let local = tc.mk_local(name, binder_type);
        ind_ty = inst(body, &[local]);
      },
      _ => {
        ind_ty = whnf_ty;
        break;
      },
    }
  }
  let ind_level = match ind_ty.as_data() {
    ExprData::Sort(l, _) => l.clone(),
    _ => return Ok(()), // can't extract sort, skip
  };

  // Walk ctor type, skip params, then check each field
  let mut ctor_ty = ctor.cnst.typ.clone();
  for _ in 0..num_params {
    let whnf_ty = tc.whnf(&ctor_ty);
    match whnf_ty.as_data() {
      ExprData::ForallE(name, binder_type, body, _, _) => {
        let local = tc.mk_local(name, binder_type);
        ctor_ty = inst(body, &[local]);
      },
      _ => return Ok(()),
    }
  }

  // For each remaining field binder, check its sort level ≤ ind_level
  loop {
    let whnf_ty = tc.whnf(&ctor_ty);
    match whnf_ty.as_data() {
      ExprData::ForallE(name, binder_type, body, _, _) => {
        // Infer the sort of the binder_type
        if let Ok(field_level) = tc.infer_sort_of(binder_type) {
          if !level::leq(&field_level, &ind_level) {
            return Err(TcError::KernelException {
              msg: format!(
                "constructor {} field type lives in a universe larger than the inductive's universe",
                ctor.cnst.name.pretty()
              ),
            });
          }
        }
        let local = tc.mk_local(name, binder_type);
        ctor_ty = inst(body, &[local]);
      },
      _ => break,
    }
  }

  Ok(())
}

/// Verify that a constructor's return type targets the parent inductive.
/// Walks the constructor type telescope, then checks that the resulting
/// type is an application of the parent inductive with at least `num_params` args.
fn check_ctor_return_type(
  ctor: &ConstructorVal,
  ind: &InductiveVal,
  tc: &mut TypeChecker,
) -> TcResult<()> {
  let mut ty = ctor.cnst.typ.clone();

  // Walk past all Pi binders
  loop {
    let whnf_ty = tc.whnf(&ty);
    match whnf_ty.as_data() {
      ExprData::ForallE(name, binder_type, body, _, _) => {
        let local = tc.mk_local(name, binder_type);
        ty = inst(body, &[local]);
      },
      _ => {
        ty = whnf_ty;
        break;
      },
    }
  }

  // The return type should be `I args...`
  let (head, args) = unfold_apps(&ty);
  let head_name = match head.as_data() {
    ExprData::Const(name, _, _) => name,
    _ => {
      return Err(TcError::KernelException {
        msg: format!(
          "constructor {} return type head is not a constant",
          ctor.cnst.name.pretty()
        ),
      })
    },
  };

  if head_name != &ind.cnst.name {
    return Err(TcError::KernelException {
      msg: format!(
        "constructor {} returns {} but should return {}",
        ctor.cnst.name.pretty(),
        head_name.pretty(),
        ind.cnst.name.pretty()
      ),
    });
  }

  let num_params = ind.num_params.to_u64().unwrap() as usize;
  if args.len() < num_params {
    return Err(TcError::KernelException {
      msg: format!(
        "constructor {} return type has {} args but inductive has {} params",
        ctor.cnst.name.pretty(),
        args.len(),
        num_params
      ),
    });
  }

  Ok(())
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::ix::kernel::tc::TypeChecker;
  use crate::lean::nat::Nat;

  fn mk_name(s: &str) -> Name {
    Name::str(Name::anon(), s.into())
  }

  fn mk_name2(a: &str, b: &str) -> Name {
    Name::str(Name::str(Name::anon(), a.into()), b.into())
  }

  fn nat_type() -> Expr {
    Expr::cnst(mk_name("Nat"), vec![])
  }

  fn mk_nat_env() -> Env {
    let mut env = Env::default();
    let nat_name = mk_name("Nat");
    env.insert(
      nat_name.clone(),
      ConstantInfo::InductInfo(InductiveVal {
        cnst: ConstantVal {
          name: nat_name.clone(),
          level_params: vec![],
          typ: Expr::sort(Level::succ(Level::zero())),
        },
        num_params: Nat::from(0u64),
        num_indices: Nat::from(0u64),
        all: vec![nat_name.clone()],
        ctors: vec![mk_name2("Nat", "zero"), mk_name2("Nat", "succ")],
        num_nested: Nat::from(0u64),
        is_rec: true,
        is_unsafe: false,
        is_reflexive: false,
      }),
    );
    let zero_name = mk_name2("Nat", "zero");
    env.insert(
      zero_name.clone(),
      ConstantInfo::CtorInfo(ConstructorVal {
        cnst: ConstantVal {
          name: zero_name.clone(),
          level_params: vec![],
          typ: nat_type(),
        },
        induct: mk_name("Nat"),
        cidx: Nat::from(0u64),
        num_params: Nat::from(0u64),
        num_fields: Nat::from(0u64),
        is_unsafe: false,
      }),
    );
    let succ_name = mk_name2("Nat", "succ");
    env.insert(
      succ_name.clone(),
      ConstantInfo::CtorInfo(ConstructorVal {
        cnst: ConstantVal {
          name: succ_name.clone(),
          level_params: vec![],
          typ: Expr::all(
            mk_name("n"),
            nat_type(),
            nat_type(),
            BinderInfo::Default,
          ),
        },
        induct: mk_name("Nat"),
        cidx: Nat::from(1u64),
        num_params: Nat::from(0u64),
        num_fields: Nat::from(1u64),
        is_unsafe: false,
      }),
    );
    env
  }

  #[test]
  fn check_nat_inductive_passes() {
    let env = mk_nat_env();
    let ind = match env.get(&mk_name("Nat")).unwrap() {
      ConstantInfo::InductInfo(v) => v,
      _ => panic!(),
    };
    let mut tc = TypeChecker::new(&env);
    assert!(check_inductive(ind, &mut tc).is_ok());
  }

  #[test]
  fn check_ctor_wrong_return_type() {
    let mut env = mk_nat_env();
    let bool_name = mk_name("Bool");
    env.insert(
      bool_name.clone(),
      ConstantInfo::InductInfo(InductiveVal {
        cnst: ConstantVal {
          name: bool_name.clone(),
          level_params: vec![],
          typ: Expr::sort(Level::succ(Level::zero())),
        },
        num_params: Nat::from(0u64),
        num_indices: Nat::from(0u64),
        all: vec![bool_name.clone()],
        ctors: vec![mk_name2("Bool", "bad")],
        num_nested: Nat::from(0u64),
        is_rec: false,
        is_unsafe: false,
        is_reflexive: false,
      }),
    );
    // Constructor returns Nat instead of Bool
    let bad_ctor_name = mk_name2("Bool", "bad");
    env.insert(
      bad_ctor_name.clone(),
      ConstantInfo::CtorInfo(ConstructorVal {
        cnst: ConstantVal {
          name: bad_ctor_name.clone(),
          level_params: vec![],
          typ: nat_type(),
        },
        induct: bool_name.clone(),
        cidx: Nat::from(0u64),
        num_params: Nat::from(0u64),
        num_fields: Nat::from(0u64),
        is_unsafe: false,
      }),
    );

    let ind = match env.get(&bool_name).unwrap() {
      ConstantInfo::InductInfo(v) => v,
      _ => panic!(),
    };
    let mut tc = TypeChecker::new(&env);
    assert!(check_inductive(ind, &mut tc).is_err());
  }

  // ==========================================================================
  // Positivity checking
  // ==========================================================================

  fn bool_type() -> Expr {
    Expr::cnst(mk_name("Bool"), vec![])
  }

  /// Helper to make a simple inductive + ctor env for positivity tests.
  fn mk_single_ctor_env(
    ind_name: &str,
    ctor_name: &str,
    ctor_typ: Expr,
    num_fields: u64,
  ) -> Env {
    let mut env = mk_nat_env();
    // Bool
    let bool_name = mk_name("Bool");
    env.insert(
      bool_name.clone(),
      ConstantInfo::InductInfo(InductiveVal {
        cnst: ConstantVal {
          name: bool_name.clone(),
          level_params: vec![],
          typ: Expr::sort(Level::succ(Level::zero())),
        },
        num_params: Nat::from(0u64),
        num_indices: Nat::from(0u64),
        all: vec![bool_name],
        ctors: vec![mk_name2("Bool", "true"), mk_name2("Bool", "false")],
        num_nested: Nat::from(0u64),
        is_rec: false,
        is_unsafe: false,
        is_reflexive: false,
      }),
    );
    let iname = mk_name(ind_name);
    let cname = mk_name2(ind_name, ctor_name);
    env.insert(
      iname.clone(),
      ConstantInfo::InductInfo(InductiveVal {
        cnst: ConstantVal {
          name: iname.clone(),
          level_params: vec![],
          typ: Expr::sort(Level::succ(Level::zero())),
        },
        num_params: Nat::from(0u64),
        num_indices: Nat::from(0u64),
        all: vec![iname.clone()],
        ctors: vec![cname.clone()],
        num_nested: Nat::from(0u64),
        is_rec: num_fields > 0,
        is_unsafe: false,
        is_reflexive: false,
      }),
    );
    env.insert(
      cname.clone(),
      ConstantInfo::CtorInfo(ConstructorVal {
        cnst: ConstantVal {
          name: cname,
          level_params: vec![],
          typ: ctor_typ,
        },
        induct: iname,
        cidx: Nat::from(0u64),
        num_params: Nat::from(0u64),
        num_fields: Nat::from(num_fields),
        is_unsafe: false,
      }),
    );
    env
  }

  #[test]
  fn positivity_bad_negative() {
    // inductive Bad | mk : (Bad → Bool) → Bad
    let bad = mk_name("Bad");
    let ctor_ty = Expr::all(
      mk_name("f"),
      Expr::all(mk_name("x"), Expr::cnst(bad, vec![]), bool_type(), BinderInfo::Default),
      Expr::cnst(mk_name("Bad"), vec![]),
      BinderInfo::Default,
    );
    let env = mk_single_ctor_env("Bad", "mk", ctor_ty, 1);
    let ind = match env.get(&mk_name("Bad")).unwrap() {
      ConstantInfo::InductInfo(v) => v,
      _ => panic!(),
    };
    let mut tc = TypeChecker::new(&env);
    assert!(check_inductive(ind, &mut tc).is_err());
  }

  #[test]
  fn positivity_nat_succ_ok() {
    // Nat.succ : Nat → Nat (positive)
    let env = mk_nat_env();
    let ind = match env.get(&mk_name("Nat")).unwrap() {
      ConstantInfo::InductInfo(v) => v,
      _ => panic!(),
    };
    let mut tc = TypeChecker::new(&env);
    assert!(check_inductive(ind, &mut tc).is_ok());
  }

  #[test]
  fn positivity_tree_positive_function() {
    // inductive Tree | node : (Nat → Tree) → Tree
    // Tree appears positive in `Nat → Tree`
    let tree = mk_name("Tree");
    let ctor_ty = Expr::all(
      mk_name("f"),
      Expr::all(mk_name("n"), nat_type(), Expr::cnst(tree.clone(), vec![]), BinderInfo::Default),
      Expr::cnst(tree, vec![]),
      BinderInfo::Default,
    );
    let env = mk_single_ctor_env("Tree", "node", ctor_ty, 1);
    let ind = match env.get(&mk_name("Tree")).unwrap() {
      ConstantInfo::InductInfo(v) => v,
      _ => panic!(),
    };
    let mut tc = TypeChecker::new(&env);
    assert!(check_inductive(ind, &mut tc).is_ok());
  }

  #[test]
  fn positivity_depth2_negative() {
    // inductive Bad2 | mk : ((Bad2 → Nat) → Nat) → Bad2
    // Bad2 appears in negative position at depth 2
    let bad2 = mk_name("Bad2");
    let inner = Expr::all(
      mk_name("g"),
      Expr::all(mk_name("x"), Expr::cnst(bad2.clone(), vec![]), nat_type(), BinderInfo::Default),
      nat_type(),
      BinderInfo::Default,
    );
    let ctor_ty = Expr::all(
      mk_name("f"),
      inner,
      Expr::cnst(bad2, vec![]),
      BinderInfo::Default,
    );
    let env = mk_single_ctor_env("Bad2", "mk", ctor_ty, 1);
    let ind = match env.get(&mk_name("Bad2")).unwrap() {
      ConstantInfo::InductInfo(v) => v,
      _ => panic!(),
    };
    let mut tc = TypeChecker::new(&env);
    assert!(check_inductive(ind, &mut tc).is_err());
  }

  // ==========================================================================
  // Field universe constraints
  // ==========================================================================

  #[test]
  fn field_universe_nat_field_in_type1_ok() {
    // Nat : Sort 1, Nat.succ field is Nat : Sort 1 — leq(1, 1) passes
    let env = mk_nat_env();
    let ind = match env.get(&mk_name("Nat")).unwrap() {
      ConstantInfo::InductInfo(v) => v,
      _ => panic!(),
    };
    let mut tc = TypeChecker::new(&env);
    assert!(check_inductive(ind, &mut tc).is_ok());
  }

  #[test]
  fn field_universe_prop_inductive_with_type_field_fails() {
    // inductive PropBad : Prop | mk : Nat → PropBad
    // PropBad lives in Sort 0, Nat lives in Sort 1 — leq(1, 0) fails
    let mut env = mk_nat_env();
    let pb_name = mk_name("PropBad");
    let pb_mk = mk_name2("PropBad", "mk");
    env.insert(
      pb_name.clone(),
      ConstantInfo::InductInfo(InductiveVal {
        cnst: ConstantVal {
          name: pb_name.clone(),
          level_params: vec![],
          typ: Expr::sort(Level::zero()), // Prop
        },
        num_params: Nat::from(0u64),
        num_indices: Nat::from(0u64),
        all: vec![pb_name.clone()],
        ctors: vec![pb_mk.clone()],
        num_nested: Nat::from(0u64),
        is_rec: false,
        is_unsafe: false,
        is_reflexive: false,
      }),
    );
    env.insert(
      pb_mk.clone(),
      ConstantInfo::CtorInfo(ConstructorVal {
        cnst: ConstantVal {
          name: pb_mk,
          level_params: vec![],
          typ: Expr::all(
            mk_name("n"),
            nat_type(),        // Nat : Sort 1
            Expr::cnst(pb_name.clone(), vec![]),
            BinderInfo::Default,
          ),
        },
        induct: pb_name.clone(),
        cidx: Nat::from(0u64),
        num_params: Nat::from(0u64),
        num_fields: Nat::from(1u64),
        is_unsafe: false,
      }),
    );

    let ind = match env.get(&pb_name).unwrap() {
      ConstantInfo::InductInfo(v) => v,
      _ => panic!(),
    };
    let mut tc = TypeChecker::new(&env);
    assert!(check_inductive(ind, &mut tc).is_err());
  }
}
