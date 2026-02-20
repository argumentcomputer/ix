use crate::ix::env::*;

use super::error::TcError;

type TcResult<T> = Result<T, TcError>;

/// Verify that the quotient declarations are consistent with the environment.
/// Checks that Quot is an inductive, Quot.mk is its constructor, and
/// Quot.lift and Quot.ind exist.
pub fn check_quot(env: &Env) -> TcResult<()> {
  let quot_name = Name::str(Name::anon(), "Quot".into());
  let quot_mk_name =
    Name::str(Name::str(Name::anon(), "Quot".into()), "mk".into());
  let quot_lift_name =
    Name::str(Name::str(Name::anon(), "Quot".into()), "lift".into());
  let quot_ind_name =
    Name::str(Name::str(Name::anon(), "Quot".into()), "ind".into());

  // Check Quot exists and is an inductive
  let quot =
    env.get(&quot_name).ok_or(TcError::UnknownConst { name: quot_name })?;
  match quot {
    ConstantInfo::InductInfo(_) => {},
    _ => {
      return Err(TcError::KernelException {
        msg: "Quot is not an inductive type".into(),
      })
    },
  }

  // Check Quot.mk exists and is a constructor of Quot
  let mk = env
    .get(&quot_mk_name)
    .ok_or(TcError::UnknownConst { name: quot_mk_name })?;
  match mk {
    ConstantInfo::CtorInfo(c)
      if c.induct
        == Name::str(Name::anon(), "Quot".into()) => {},
    _ => {
      return Err(TcError::KernelException {
        msg: "Quot.mk is not a constructor of Quot".into(),
      })
    },
  }

  // Check Eq exists as an inductive with exactly 1 universe param and 1 ctor
  let eq_name = Name::str(Name::anon(), "Eq".into());
  if let Some(eq_ci) = env.get(&eq_name) {
    match eq_ci {
      ConstantInfo::InductInfo(iv) => {
        if iv.cnst.level_params.len() != 1 {
          return Err(TcError::KernelException {
            msg: format!(
              "Eq should have 1 universe parameter, found {}",
              iv.cnst.level_params.len()
            ),
          });
        }
        if iv.ctors.len() != 1 {
          return Err(TcError::KernelException {
            msg: format!(
              "Eq should have 1 constructor, found {}",
              iv.ctors.len()
            ),
          });
        }
      },
      _ => {
        return Err(TcError::KernelException {
          msg: "Eq is not an inductive type".into(),
        })
      },
    }
  } else {
    return Err(TcError::KernelException {
      msg: "Eq not found in environment (required for quotient types)".into(),
    });
  }

  // Check Quot has exactly 1 level param
  match quot {
    ConstantInfo::InductInfo(iv) if iv.cnst.level_params.len() != 1 => {
      return Err(TcError::KernelException {
        msg: format!(
          "Quot should have 1 universe parameter, found {}",
          iv.cnst.level_params.len()
        ),
      })
    },
    _ => {},
  }

  // Check Quot.mk has 1 level param
  match mk {
    ConstantInfo::CtorInfo(c) if c.cnst.level_params.len() != 1 => {
      return Err(TcError::KernelException {
        msg: format!(
          "Quot.mk should have 1 universe parameter, found {}",
          c.cnst.level_params.len()
        ),
      })
    },
    _ => {},
  }

  // Check Quot.lift exists and has 2 level params
  let lift = env
    .get(&quot_lift_name)
    .ok_or(TcError::UnknownConst { name: quot_lift_name })?;
  if lift.get_level_params().len() != 2 {
    return Err(TcError::KernelException {
      msg: format!(
        "Quot.lift should have 2 universe parameters, found {}",
        lift.get_level_params().len()
      ),
    });
  }

  // Check Quot.ind exists and has 1 level param
  let ind = env
    .get(&quot_ind_name)
    .ok_or(TcError::UnknownConst { name: quot_ind_name })?;
  if ind.get_level_params().len() != 1 {
    return Err(TcError::KernelException {
      msg: format!(
        "Quot.ind should have 1 universe parameter, found {}",
        ind.get_level_params().len()
      ),
    });
  }

  Ok(())
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::lean::nat::Nat;

  fn mk_name(s: &str) -> Name {
    Name::str(Name::anon(), s.into())
  }

  fn mk_name2(a: &str, b: &str) -> Name {
    Name::str(Name::str(Name::anon(), a.into()), b.into())
  }

  /// Build a well-formed quotient environment.
  fn mk_quot_env() -> Env {
    let mut env = Env::default();
    let u = mk_name("u");
    let v = mk_name("v");
    let dummy_ty = Expr::sort(Level::param(u.clone()));

    // Eq.{u} — 1 uparam, 1 ctor
    let eq_name = mk_name("Eq");
    let eq_refl = mk_name2("Eq", "refl");
    env.insert(
      eq_name.clone(),
      ConstantInfo::InductInfo(InductiveVal {
        cnst: ConstantVal {
          name: eq_name.clone(),
          level_params: vec![u.clone()],
          typ: dummy_ty.clone(),
        },
        num_params: Nat::from(2u64),
        num_indices: Nat::from(1u64),
        all: vec![eq_name],
        ctors: vec![eq_refl.clone()],
        num_nested: Nat::from(0u64),
        is_rec: false,
        is_unsafe: false,
        is_reflexive: true,
      }),
    );
    env.insert(
      eq_refl.clone(),
      ConstantInfo::CtorInfo(ConstructorVal {
        cnst: ConstantVal {
          name: eq_refl,
          level_params: vec![u.clone()],
          typ: dummy_ty.clone(),
        },
        induct: mk_name("Eq"),
        cidx: Nat::from(0u64),
        num_params: Nat::from(2u64),
        num_fields: Nat::from(0u64),
        is_unsafe: false,
      }),
    );

    // Quot.{u} — 1 uparam
    let quot_name = mk_name("Quot");
    let quot_mk = mk_name2("Quot", "mk");
    env.insert(
      quot_name.clone(),
      ConstantInfo::InductInfo(InductiveVal {
        cnst: ConstantVal {
          name: quot_name.clone(),
          level_params: vec![u.clone()],
          typ: dummy_ty.clone(),
        },
        num_params: Nat::from(2u64),
        num_indices: Nat::from(0u64),
        all: vec![quot_name],
        ctors: vec![quot_mk.clone()],
        num_nested: Nat::from(0u64),
        is_rec: false,
        is_unsafe: false,
        is_reflexive: false,
      }),
    );
    env.insert(
      quot_mk.clone(),
      ConstantInfo::CtorInfo(ConstructorVal {
        cnst: ConstantVal {
          name: quot_mk,
          level_params: vec![u.clone()],
          typ: dummy_ty.clone(),
        },
        induct: mk_name("Quot"),
        cidx: Nat::from(0u64),
        num_params: Nat::from(2u64),
        num_fields: Nat::from(1u64),
        is_unsafe: false,
      }),
    );

    // Quot.lift.{u,v} — 2 uparams
    let quot_lift = mk_name2("Quot", "lift");
    env.insert(
      quot_lift.clone(),
      ConstantInfo::AxiomInfo(AxiomVal {
        cnst: ConstantVal {
          name: quot_lift,
          level_params: vec![u.clone(), v.clone()],
          typ: dummy_ty.clone(),
        },
        is_unsafe: false,
      }),
    );

    // Quot.ind.{u} — 1 uparam
    let quot_ind = mk_name2("Quot", "ind");
    env.insert(
      quot_ind.clone(),
      ConstantInfo::AxiomInfo(AxiomVal {
        cnst: ConstantVal {
          name: quot_ind,
          level_params: vec![u],
          typ: dummy_ty,
        },
        is_unsafe: false,
      }),
    );

    env
  }

  #[test]
  fn check_quot_well_formed() {
    let env = mk_quot_env();
    assert!(check_quot(&env).is_ok());
  }

  #[test]
  fn check_quot_missing_eq() {
    let mut env = mk_quot_env();
    env.remove(&mk_name("Eq"));
    assert!(check_quot(&env).is_err());
  }

  #[test]
  fn check_quot_wrong_lift_levels() {
    let mut env = mk_quot_env();
    // Replace Quot.lift with 1 level param instead of 2
    let quot_lift = mk_name2("Quot", "lift");
    env.insert(
      quot_lift.clone(),
      ConstantInfo::AxiomInfo(AxiomVal {
        cnst: ConstantVal {
          name: quot_lift,
          level_params: vec![mk_name("u")],
          typ: Expr::sort(Level::param(mk_name("u"))),
        },
        is_unsafe: false,
      }),
    );
    assert!(check_quot(&env).is_err());
  }
}
