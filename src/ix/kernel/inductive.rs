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

/// Validate recursor rules against the inductive's constructors.
/// Checks:
/// - One rule per constructor
/// - Each rule's constructor exists and belongs to the inductive
/// - Each rule's n_fields matches the constructor's actual field count
/// - Rules are in constructor order
pub fn validate_recursor_rules(
  rec: &RecursorVal,
  env: &Env,
) -> TcResult<()> {
  // Find the primary inductive
  if rec.all.is_empty() {
    return Err(TcError::KernelException {
      msg: "recursor has no associated inductives".into(),
    });
  }
  let ind_name = &rec.all[0];
  let ind = match env.get(ind_name) {
    Some(ConstantInfo::InductInfo(iv)) => iv,
    _ => {
      return Err(TcError::KernelException {
        msg: format!(
          "recursor's inductive {} is not an inductive type",
          ind_name.pretty()
        ),
      })
    },
  };

  // For mutual inductives, collect all constructors in order
  let mut all_ctors: Vec<Name> = Vec::new();
  for iname in &rec.all {
    if let Some(ConstantInfo::InductInfo(iv)) = env.get(iname) {
      all_ctors.extend(iv.ctors.iter().cloned());
    }
  }

  // Check rule count matches total constructor count
  if rec.rules.len() != all_ctors.len() {
    return Err(TcError::KernelException {
      msg: format!(
        "recursor has {} rules but inductive(s) have {} constructors",
        rec.rules.len(),
        all_ctors.len()
      ),
    });
  }

  // Check each rule
  for (i, rule) in rec.rules.iter().enumerate() {
    // Rule's constructor must match expected constructor in order
    if rule.ctor != all_ctors[i] {
      return Err(TcError::KernelException {
        msg: format!(
          "recursor rule {} has constructor {} but expected {}",
          i,
          rule.ctor.pretty(),
          all_ctors[i].pretty()
        ),
      });
    }

    // Look up the constructor and validate n_fields
    let ctor = match env.get(&rule.ctor) {
      Some(ConstantInfo::CtorInfo(c)) => c,
      _ => {
        return Err(TcError::KernelException {
          msg: format!(
            "recursor rule constructor {} not found or not a constructor",
            rule.ctor.pretty()
          ),
        })
      },
    };

    if rule.n_fields != ctor.num_fields {
      return Err(TcError::KernelException {
        msg: format!(
          "recursor rule for {} has n_fields={} but constructor has {} fields",
          rule.ctor.pretty(),
          rule.n_fields,
          ctor.num_fields
        ),
      });
    }
  }

  // Validate structural counts against the inductive
  let expected_params = ind.num_params.to_u64().unwrap();
  let rec_params = rec.num_params.to_u64().unwrap();
  if rec_params != expected_params {
    return Err(TcError::KernelException {
      msg: format!(
        "recursor num_params={} but inductive has {} params",
        rec_params, expected_params
      ),
    });
  }

  let expected_indices = ind.num_indices.to_u64().unwrap();
  let rec_indices = rec.num_indices.to_u64().unwrap();
  if rec_indices != expected_indices {
    return Err(TcError::KernelException {
      msg: format!(
        "recursor num_indices={} but inductive has {} indices",
        rec_indices, expected_indices
      ),
    });
  }

  // Validate elimination restriction for Prop inductives.
  // If the inductive is in Prop and requires elimination only at universe zero,
  // then the recursor must not have extra universe parameters beyond the inductive's.
  if !rec.is_unsafe {
    if let Some(elim_zero) = elim_only_at_universe_zero(ind, env) {
      if elim_zero {
        // Recursor should have same number of level params as the inductive
        // (no extra universe parameter for the motive's result sort)
        let ind_level_count = ind.cnst.level_params.len();
        let rec_level_count = rec.cnst.level_params.len();
        if rec_level_count > ind_level_count {
          return Err(TcError::KernelException {
            msg: format!(
              "recursor has {} universe params but inductive has {} — \
               large elimination is not allowed for this Prop inductive",
              rec_level_count, ind_level_count
            ),
          });
        }
      }
    }
  }

  Ok(())
}

/// Compute whether a Prop inductive can only eliminate to Prop (universe zero).
///
/// Returns `Some(true)` if elimination is restricted to Prop,
/// `Some(false)` if large elimination is allowed,
/// `None` if the inductive is not in Prop (no restriction applies).
///
/// Matches the C++ kernel's `elim_only_at_universe_zero`:
/// 1. If result universe is always non-zero: None (not a predicate)
/// 2. If mutual: restricted
/// 3. If >1 constructor: restricted
/// 4. If 0 constructors: not restricted (e.g., False)
/// 5. If 1 constructor: restricted iff any non-Prop field doesn't appear in result indices
fn elim_only_at_universe_zero(
  ind: &InductiveVal,
  env: &Env,
) -> Option<bool> {
  // Check if the inductive's result is in Prop.
  // Walk past all binders to find the final Sort.
  let mut ty = ind.cnst.typ.clone();
  loop {
    match ty.as_data() {
      ExprData::ForallE(_, _, body, _, _) => {
        ty = body.clone();
      },
      _ => break,
    }
  }
  let result_level = match ty.as_data() {
    ExprData::Sort(l, _) => l,
    _ => return None,
  };

  // If the result sort is definitively non-zero (e.g., Sort 1, Sort (u+1)),
  // this is not a predicate.
  if !level::could_be_zero(result_level) {
    return None;
  }

  // Must be possibly Prop. Apply the 5 conditions.

  // Condition 2: Mutual inductives → restricted
  if ind.all.len() > 1 {
    return Some(true);
  }

  // Condition 3: >1 constructor → restricted
  if ind.ctors.len() > 1 {
    return Some(true);
  }

  // Condition 4: 0 constructors → not restricted (e.g., False)
  if ind.ctors.is_empty() {
    return Some(false);
  }

  // Condition 5: Single constructor — check fields
  let ctor = match env.get(&ind.ctors[0]) {
    Some(ConstantInfo::CtorInfo(c)) => c,
    _ => return Some(true), // can't look up ctor, be conservative
  };

  // If zero fields, not restricted
  if ctor.num_fields == Nat::ZERO {
    return Some(false);
  }

  // For single-constructor with fields: restricted if any non-Prop field
  // doesn't appear in the result type's indices.
  // Conservative approximation: if any field exists that could be non-Prop,
  // assume restricted. This is safe (may reject some valid large eliminations
  // but never allows unsound ones).
  Some(true)
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
/// Also validates:
/// - The first `num_params` arguments are definitionally equal to the inductive's parameters.
/// - Index arguments (after params) don't mention the inductive being declared.
fn check_ctor_return_type(
  ctor: &ConstructorVal,
  ind: &InductiveVal,
  tc: &mut TypeChecker,
) -> TcResult<()> {
  let num_params = ind.num_params.to_u64().unwrap() as usize;

  // Walk the inductive's type telescope to collect parameter locals.
  let mut ind_ty = ind.cnst.typ.clone();
  let mut param_locals = Vec::with_capacity(num_params);
  for _ in 0..num_params {
    let whnf_ty = tc.whnf(&ind_ty);
    match whnf_ty.as_data() {
      ExprData::ForallE(name, binder_type, body, _, _) => {
        let local = tc.mk_local(name, binder_type);
        param_locals.push(local.clone());
        ind_ty = inst(body, &[local]);
      },
      _ => break,
    }
  }

  // Walk past all Pi binders in the constructor type.
  let mut ty = ctor.cnst.typ.clone();
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

  // Check that the first num_params arguments match the inductive's parameters.
  for i in 0..num_params {
    if i < param_locals.len() && !tc.def_eq(&args[i], &param_locals[i]) {
      return Err(TcError::KernelException {
        msg: format!(
          "constructor {} parameter {} does not match inductive's parameter",
          ctor.cnst.name.pretty(),
          i
        ),
      });
    }
  }

  // Check that index arguments (after params) don't mention the inductive.
  for i in num_params..args.len() {
    for ind_name in &ind.all {
      if expr_mentions_const(&args[i], ind_name) {
        return Err(TcError::KernelException {
          msg: format!(
            "constructor {} index argument {} mentions the inductive {}",
            ctor.cnst.name.pretty(),
            i - num_params,
            ind_name.pretty()
          ),
        });
      }
    }
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

  // ==========================================================================
  // Recursor rule validation
  // ==========================================================================

  #[test]
  fn validate_rec_rules_wrong_count() {
    // Nat has 2 ctors but we provide 1 rule
    let env = mk_nat_env();
    let rec = RecursorVal {
      cnst: ConstantVal {
        name: mk_name2("Nat", "rec"),
        level_params: vec![mk_name("u")],
        typ: Expr::sort(Level::param(mk_name("u"))),
      },
      all: vec![mk_name("Nat")],
      num_params: Nat::from(0u64),
      num_indices: Nat::from(0u64),
      num_motives: Nat::from(1u64),
      num_minors: Nat::from(2u64),
      rules: vec![RecursorRule {
        ctor: mk_name2("Nat", "zero"),
        n_fields: Nat::from(0u64),
        rhs: Expr::sort(Level::zero()),
      }],
      k: false,
      is_unsafe: false,
    };
    assert!(validate_recursor_rules(&rec, &env).is_err());
  }

  #[test]
  fn validate_rec_rules_wrong_ctor_order() {
    // Provide rules in wrong order (succ first, zero second)
    let env = mk_nat_env();
    let rec = RecursorVal {
      cnst: ConstantVal {
        name: mk_name2("Nat", "rec"),
        level_params: vec![mk_name("u")],
        typ: Expr::sort(Level::param(mk_name("u"))),
      },
      all: vec![mk_name("Nat")],
      num_params: Nat::from(0u64),
      num_indices: Nat::from(0u64),
      num_motives: Nat::from(1u64),
      num_minors: Nat::from(2u64),
      rules: vec![
        RecursorRule {
          ctor: mk_name2("Nat", "succ"),
          n_fields: Nat::from(1u64),
          rhs: Expr::sort(Level::zero()),
        },
        RecursorRule {
          ctor: mk_name2("Nat", "zero"),
          n_fields: Nat::from(0u64),
          rhs: Expr::sort(Level::zero()),
        },
      ],
      k: false,
      is_unsafe: false,
    };
    assert!(validate_recursor_rules(&rec, &env).is_err());
  }

  #[test]
  fn validate_rec_rules_wrong_nfields() {
    // zero has 0 fields but we claim 3
    let env = mk_nat_env();
    let rec = RecursorVal {
      cnst: ConstantVal {
        name: mk_name2("Nat", "rec"),
        level_params: vec![mk_name("u")],
        typ: Expr::sort(Level::param(mk_name("u"))),
      },
      all: vec![mk_name("Nat")],
      num_params: Nat::from(0u64),
      num_indices: Nat::from(0u64),
      num_motives: Nat::from(1u64),
      num_minors: Nat::from(2u64),
      rules: vec![
        RecursorRule {
          ctor: mk_name2("Nat", "zero"),
          n_fields: Nat::from(3u64), // wrong!
          rhs: Expr::sort(Level::zero()),
        },
        RecursorRule {
          ctor: mk_name2("Nat", "succ"),
          n_fields: Nat::from(1u64),
          rhs: Expr::sort(Level::zero()),
        },
      ],
      k: false,
      is_unsafe: false,
    };
    assert!(validate_recursor_rules(&rec, &env).is_err());
  }

  #[test]
  fn validate_rec_rules_bogus_ctor() {
    // Rule references a non-existent constructor
    let env = mk_nat_env();
    let rec = RecursorVal {
      cnst: ConstantVal {
        name: mk_name2("Nat", "rec"),
        level_params: vec![mk_name("u")],
        typ: Expr::sort(Level::param(mk_name("u"))),
      },
      all: vec![mk_name("Nat")],
      num_params: Nat::from(0u64),
      num_indices: Nat::from(0u64),
      num_motives: Nat::from(1u64),
      num_minors: Nat::from(2u64),
      rules: vec![
        RecursorRule {
          ctor: mk_name2("Nat", "zero"),
          n_fields: Nat::from(0u64),
          rhs: Expr::sort(Level::zero()),
        },
        RecursorRule {
          ctor: mk_name2("Nat", "bogus"), // doesn't exist
          n_fields: Nat::from(1u64),
          rhs: Expr::sort(Level::zero()),
        },
      ],
      k: false,
      is_unsafe: false,
    };
    assert!(validate_recursor_rules(&rec, &env).is_err());
  }

  #[test]
  fn validate_rec_rules_correct() {
    // Correct rules for Nat
    let env = mk_nat_env();
    let rec = RecursorVal {
      cnst: ConstantVal {
        name: mk_name2("Nat", "rec"),
        level_params: vec![mk_name("u")],
        typ: Expr::sort(Level::param(mk_name("u"))),
      },
      all: vec![mk_name("Nat")],
      num_params: Nat::from(0u64),
      num_indices: Nat::from(0u64),
      num_motives: Nat::from(1u64),
      num_minors: Nat::from(2u64),
      rules: vec![
        RecursorRule {
          ctor: mk_name2("Nat", "zero"),
          n_fields: Nat::from(0u64),
          rhs: Expr::sort(Level::zero()),
        },
        RecursorRule {
          ctor: mk_name2("Nat", "succ"),
          n_fields: Nat::from(1u64),
          rhs: Expr::sort(Level::zero()),
        },
      ],
      k: false,
      is_unsafe: false,
    };
    assert!(validate_recursor_rules(&rec, &env).is_ok());
  }

  #[test]
  fn validate_rec_rules_wrong_num_params() {
    // Recursor claims 5 params but Nat has 0
    let env = mk_nat_env();
    let rec = RecursorVal {
      cnst: ConstantVal {
        name: mk_name2("Nat", "rec"),
        level_params: vec![mk_name("u")],
        typ: Expr::sort(Level::param(mk_name("u"))),
      },
      all: vec![mk_name("Nat")],
      num_params: Nat::from(5u64), // wrong
      num_indices: Nat::from(0u64),
      num_motives: Nat::from(1u64),
      num_minors: Nat::from(2u64),
      rules: vec![
        RecursorRule {
          ctor: mk_name2("Nat", "zero"),
          n_fields: Nat::from(0u64),
          rhs: Expr::sort(Level::zero()),
        },
        RecursorRule {
          ctor: mk_name2("Nat", "succ"),
          n_fields: Nat::from(1u64),
          rhs: Expr::sort(Level::zero()),
        },
      ],
      k: false,
      is_unsafe: false,
    };
    assert!(validate_recursor_rules(&rec, &env).is_err());
  }

  // ==========================================================================
  // K-flag validation
  // ==========================================================================

  /// Build a Prop inductive with 1 ctor and 0 fields (Eq-like).
  fn mk_k_valid_env() -> Env {
    let mut env = mk_nat_env();
    let eq_name = mk_name("KEq");
    let eq_refl = mk_name2("KEq", "refl");
    let u = mk_name("u");

    // KEq.{u} (α : Sort u) (a b : α) : Prop
    let eq_ty = Expr::all(
      mk_name("α"),
      Expr::sort(Level::param(u.clone())),
      Expr::all(
        mk_name("a"),
        Expr::bvar(Nat::from(0u64)),
        Expr::all(
          mk_name("b"),
          Expr::bvar(Nat::from(1u64)),
          Expr::sort(Level::zero()), // Prop
          BinderInfo::Default,
        ),
        BinderInfo::Default,
      ),
      BinderInfo::Default,
    );
    env.insert(
      eq_name.clone(),
      ConstantInfo::InductInfo(InductiveVal {
        cnst: ConstantVal {
          name: eq_name.clone(),
          level_params: vec![u.clone()],
          typ: eq_ty,
        },
        num_params: Nat::from(2u64),
        num_indices: Nat::from(1u64),
        all: vec![eq_name.clone()],
        ctors: vec![eq_refl.clone()],
        num_nested: Nat::from(0u64),
        is_rec: false,
        is_unsafe: false,
        is_reflexive: true,
      }),
    );
    // KEq.refl.{u} (α : Sort u) (a : α) : KEq α a a
    let refl_ty = Expr::all(
      mk_name("α"),
      Expr::sort(Level::param(u.clone())),
      Expr::all(
        mk_name("a"),
        Expr::bvar(Nat::from(0u64)),
        Expr::app(
          Expr::app(
            Expr::app(
              Expr::cnst(eq_name.clone(), vec![Level::param(u.clone())]),
              Expr::bvar(Nat::from(1u64)),
            ),
            Expr::bvar(Nat::from(0u64)),
          ),
          Expr::bvar(Nat::from(0u64)),
        ),
        BinderInfo::Default,
      ),
      BinderInfo::Default,
    );
    env.insert(
      eq_refl.clone(),
      ConstantInfo::CtorInfo(ConstructorVal {
        cnst: ConstantVal {
          name: eq_refl,
          level_params: vec![u],
          typ: refl_ty,
        },
        induct: eq_name,
        cidx: Nat::from(0u64),
        num_params: Nat::from(2u64),
        num_fields: Nat::from(0u64),
        is_unsafe: false,
      }),
    );
    env
  }

  #[test]
  fn validate_k_flag_valid_prop_single_zero_fields() {
    let env = mk_k_valid_env();
    let rec = RecursorVal {
      cnst: ConstantVal {
        name: mk_name2("KEq", "rec"),
        level_params: vec![mk_name("u")],
        typ: Expr::sort(Level::param(mk_name("u"))),
      },
      all: vec![mk_name("KEq")],
      num_params: Nat::from(2u64),
      num_indices: Nat::from(1u64),
      num_motives: Nat::from(1u64),
      num_minors: Nat::from(1u64),
      rules: vec![RecursorRule {
        ctor: mk_name2("KEq", "refl"),
        n_fields: Nat::from(0u64),
        rhs: Expr::sort(Level::zero()),
      }],
      k: true,
      is_unsafe: false,
    };
    assert!(validate_k_flag(&rec, &env).is_ok());
  }

  #[test]
  fn validate_k_flag_fails_not_prop() {
    // Nat is in Sort 1, not Prop — K should fail
    let env = mk_nat_env();
    let rec = RecursorVal {
      cnst: ConstantVal {
        name: mk_name2("Nat", "rec"),
        level_params: vec![mk_name("u")],
        typ: Expr::sort(Level::param(mk_name("u"))),
      },
      all: vec![mk_name("Nat")],
      num_params: Nat::from(0u64),
      num_indices: Nat::from(0u64),
      num_motives: Nat::from(1u64),
      num_minors: Nat::from(2u64),
      rules: vec![],
      k: true,
      is_unsafe: false,
    };
    assert!(validate_k_flag(&rec, &env).is_err());
  }

  #[test]
  fn validate_k_flag_fails_multiple_ctors() {
    // Even a Prop inductive with 2 ctors can't be K
    // We need a Prop inductive with 2 ctors for this test
    let mut env = Env::default();
    let p_name = mk_name("P");
    let mk1 = mk_name2("P", "mk1");
    let mk2 = mk_name2("P", "mk2");
    env.insert(
      p_name.clone(),
      ConstantInfo::InductInfo(InductiveVal {
        cnst: ConstantVal {
          name: p_name.clone(),
          level_params: vec![],
          typ: Expr::sort(Level::zero()), // Prop
        },
        num_params: Nat::from(0u64),
        num_indices: Nat::from(0u64),
        all: vec![p_name.clone()],
        ctors: vec![mk1.clone(), mk2.clone()],
        num_nested: Nat::from(0u64),
        is_rec: false,
        is_unsafe: false,
        is_reflexive: false,
      }),
    );
    env.insert(
      mk1.clone(),
      ConstantInfo::CtorInfo(ConstructorVal {
        cnst: ConstantVal {
          name: mk1,
          level_params: vec![],
          typ: Expr::cnst(p_name.clone(), vec![]),
        },
        induct: p_name.clone(),
        cidx: Nat::from(0u64),
        num_params: Nat::from(0u64),
        num_fields: Nat::from(0u64),
        is_unsafe: false,
      }),
    );
    env.insert(
      mk2.clone(),
      ConstantInfo::CtorInfo(ConstructorVal {
        cnst: ConstantVal {
          name: mk2,
          level_params: vec![],
          typ: Expr::cnst(p_name.clone(), vec![]),
        },
        induct: p_name,
        cidx: Nat::from(1u64),
        num_params: Nat::from(0u64),
        num_fields: Nat::from(0u64),
        is_unsafe: false,
      }),
    );
    let rec = RecursorVal {
      cnst: ConstantVal {
        name: mk_name2("P", "rec"),
        level_params: vec![],
        typ: Expr::sort(Level::zero()),
      },
      all: vec![mk_name("P")],
      num_params: Nat::from(0u64),
      num_indices: Nat::from(0u64),
      num_motives: Nat::from(1u64),
      num_minors: Nat::from(2u64),
      rules: vec![],
      k: true,
      is_unsafe: false,
    };
    assert!(validate_k_flag(&rec, &env).is_err());
  }

  #[test]
  fn validate_k_flag_false_always_ok() {
    // k=false is always conservative, never rejected
    let env = mk_nat_env();
    let rec = RecursorVal {
      cnst: ConstantVal {
        name: mk_name2("Nat", "rec"),
        level_params: vec![mk_name("u")],
        typ: Expr::sort(Level::param(mk_name("u"))),
      },
      all: vec![mk_name("Nat")],
      num_params: Nat::from(0u64),
      num_indices: Nat::from(0u64),
      num_motives: Nat::from(1u64),
      num_minors: Nat::from(2u64),
      rules: vec![],
      k: false,
      is_unsafe: false,
    };
    assert!(validate_k_flag(&rec, &env).is_ok());
  }

  #[test]
  fn validate_k_flag_fails_mutual() {
    // K requires all.len() == 1
    let env = mk_k_valid_env();
    let rec = RecursorVal {
      cnst: ConstantVal {
        name: mk_name2("KEq", "rec"),
        level_params: vec![mk_name("u")],
        typ: Expr::sort(Level::param(mk_name("u"))),
      },
      all: vec![mk_name("KEq"), mk_name("OtherInd")], // mutual
      num_params: Nat::from(2u64),
      num_indices: Nat::from(1u64),
      num_motives: Nat::from(1u64),
      num_minors: Nat::from(1u64),
      rules: vec![],
      k: true,
      is_unsafe: false,
    };
    assert!(validate_k_flag(&rec, &env).is_err());
  }

  // ==========================================================================
  // Elimination restriction
  // ==========================================================================

  #[test]
  fn elim_restriction_non_prop_is_none() {
    // Nat is in Sort 1, not Prop — no restriction applies
    let env = mk_nat_env();
    let ind = match env.get(&mk_name("Nat")).unwrap() {
      ConstantInfo::InductInfo(v) => v,
      _ => panic!(),
    };
    assert_eq!(elim_only_at_universe_zero(ind, &env), None);
  }

  #[test]
  fn elim_restriction_prop_2_ctors_restricted() {
    // A Prop inductive with 2 constructors: restricted to Prop elimination
    let mut env = Env::default();
    let p_name = mk_name("P2");
    let mk1 = mk_name2("P2", "mk1");
    let mk2 = mk_name2("P2", "mk2");
    env.insert(
      p_name.clone(),
      ConstantInfo::InductInfo(InductiveVal {
        cnst: ConstantVal {
          name: p_name.clone(),
          level_params: vec![],
          typ: Expr::sort(Level::zero()),
        },
        num_params: Nat::from(0u64),
        num_indices: Nat::from(0u64),
        all: vec![p_name.clone()],
        ctors: vec![mk1.clone(), mk2.clone()],
        num_nested: Nat::from(0u64),
        is_rec: false,
        is_unsafe: false,
        is_reflexive: false,
      }),
    );
    env.insert(mk1.clone(), ConstantInfo::CtorInfo(ConstructorVal {
      cnst: ConstantVal { name: mk1, level_params: vec![], typ: Expr::cnst(p_name.clone(), vec![]) },
      induct: p_name.clone(), cidx: Nat::from(0u64), num_params: Nat::from(0u64), num_fields: Nat::from(0u64), is_unsafe: false,
    }));
    env.insert(mk2.clone(), ConstantInfo::CtorInfo(ConstructorVal {
      cnst: ConstantVal { name: mk2, level_params: vec![], typ: Expr::cnst(p_name.clone(), vec![]) },
      induct: p_name.clone(), cidx: Nat::from(1u64), num_params: Nat::from(0u64), num_fields: Nat::from(0u64), is_unsafe: false,
    }));
    let ind = match env.get(&p_name).unwrap() {
      ConstantInfo::InductInfo(v) => v,
      _ => panic!(),
    };
    assert_eq!(elim_only_at_universe_zero(ind, &env), Some(true));
  }

  #[test]
  fn elim_restriction_prop_0_ctors_not_restricted() {
    // Empty Prop inductive (like False): can eliminate to any universe
    let env_name = mk_name("MyFalse");
    let mut env = Env::default();
    env.insert(
      env_name.clone(),
      ConstantInfo::InductInfo(InductiveVal {
        cnst: ConstantVal {
          name: env_name.clone(),
          level_params: vec![],
          typ: Expr::sort(Level::zero()),
        },
        num_params: Nat::from(0u64),
        num_indices: Nat::from(0u64),
        all: vec![env_name.clone()],
        ctors: vec![],
        num_nested: Nat::from(0u64),
        is_rec: false,
        is_unsafe: false,
        is_reflexive: false,
      }),
    );
    let ind = match env.get(&env_name).unwrap() {
      ConstantInfo::InductInfo(v) => v,
      _ => panic!(),
    };
    assert_eq!(elim_only_at_universe_zero(ind, &env), Some(false));
  }

  #[test]
  fn elim_restriction_prop_1_ctor_0_fields_not_restricted() {
    // Prop inductive, 1 ctor, 0 fields (like True): not restricted
    let mut env = Env::default();
    let t_name = mk_name("MyTrue");
    let t_mk = mk_name2("MyTrue", "intro");
    env.insert(
      t_name.clone(),
      ConstantInfo::InductInfo(InductiveVal {
        cnst: ConstantVal {
          name: t_name.clone(),
          level_params: vec![],
          typ: Expr::sort(Level::zero()),
        },
        num_params: Nat::from(0u64),
        num_indices: Nat::from(0u64),
        all: vec![t_name.clone()],
        ctors: vec![t_mk.clone()],
        num_nested: Nat::from(0u64),
        is_rec: false,
        is_unsafe: false,
        is_reflexive: false,
      }),
    );
    env.insert(
      t_mk.clone(),
      ConstantInfo::CtorInfo(ConstructorVal {
        cnst: ConstantVal {
          name: t_mk,
          level_params: vec![],
          typ: Expr::cnst(t_name.clone(), vec![]),
        },
        induct: t_name.clone(),
        cidx: Nat::from(0u64),
        num_params: Nat::from(0u64),
        num_fields: Nat::from(0u64),
        is_unsafe: false,
      }),
    );
    let ind = match env.get(&t_name).unwrap() {
      ConstantInfo::InductInfo(v) => v,
      _ => panic!(),
    };
    assert_eq!(elim_only_at_universe_zero(ind, &env), Some(false));
  }

  #[test]
  fn elim_restriction_prop_1_ctor_with_fields_restricted() {
    // Prop inductive, 1 ctor with fields: conservatively restricted
    // (like Exists)
    let mut env = Env::default();
    let ex_name = mk_name("MyExists");
    let ex_mk = mk_name2("MyExists", "intro");
    // For simplicity: MyExists : Prop, MyExists.intro : Prop → MyExists
    // (simplified from the real Exists which is polymorphic)
    env.insert(
      ex_name.clone(),
      ConstantInfo::InductInfo(InductiveVal {
        cnst: ConstantVal {
          name: ex_name.clone(),
          level_params: vec![],
          typ: Expr::sort(Level::zero()),
        },
        num_params: Nat::from(0u64),
        num_indices: Nat::from(0u64),
        all: vec![ex_name.clone()],
        ctors: vec![ex_mk.clone()],
        num_nested: Nat::from(0u64),
        is_rec: false,
        is_unsafe: false,
        is_reflexive: false,
      }),
    );
    env.insert(
      ex_mk.clone(),
      ConstantInfo::CtorInfo(ConstructorVal {
        cnst: ConstantVal {
          name: ex_mk,
          level_params: vec![],
          typ: Expr::all(
            mk_name("h"),
            Expr::sort(Level::zero()), // a Prop field
            Expr::cnst(ex_name.clone(), vec![]),
            BinderInfo::Default,
          ),
        },
        induct: ex_name.clone(),
        cidx: Nat::from(0u64),
        num_params: Nat::from(0u64),
        num_fields: Nat::from(1u64),
        is_unsafe: false,
      }),
    );
    let ind = match env.get(&ex_name).unwrap() {
      ConstantInfo::InductInfo(v) => v,
      _ => panic!(),
    };
    // Conservative: any fields means restricted
    assert_eq!(elim_only_at_universe_zero(ind, &env), Some(true));
  }

  // ==========================================================================
  // Index-mentions-inductive check
  // ==========================================================================

  #[test]
  fn index_mentions_inductive_rejected() {
    // Construct an inductive with 1 param and 1 index where the index
    // mentions the inductive itself. This should be rejected.
    //
    // inductive Bad (α : Type) : Bad α → Type
    //   | mk : Bad α
    //
    // The ctor return type is `Bad α (Bad.mk α)`, but for the test
    // we manually build a ctor whose index arg mentions `Bad`.
    let mut env = mk_nat_env();
    let bad_name = mk_name("BadIdx");
    let bad_mk = mk_name2("BadIdx", "mk");

    // BadIdx (α : Sort 1) : Sort 1
    // (For simplicity, we make it have 1 param and 1 index)
    env.insert(
      bad_name.clone(),
      ConstantInfo::InductInfo(InductiveVal {
        cnst: ConstantVal {
          name: bad_name.clone(),
          level_params: vec![],
          typ: Expr::all(
            mk_name("α"),
            Expr::sort(Level::succ(Level::zero())),
            Expr::all(
              mk_name("_idx"),
              nat_type(), // index of type Nat
              Expr::sort(Level::succ(Level::zero())),
              BinderInfo::Default,
            ),
            BinderInfo::Default,
          ),
        },
        num_params: Nat::from(1u64),
        num_indices: Nat::from(1u64),
        all: vec![bad_name.clone()],
        ctors: vec![bad_mk.clone()],
        num_nested: Nat::from(0u64),
        is_rec: false,
        is_unsafe: false,
        is_reflexive: false,
      }),
    );

    // BadIdx.mk (α : Sort 1) : BadIdx α <expr mentioning BadIdx>
    // The return type's index argument mentions BadIdx
    let bad_idx_expr = Expr::app(
      Expr::cnst(bad_name.clone(), vec![]),
      Expr::bvar(Nat::from(0u64)), // dummy
    );
    let ctor_ret = Expr::app(
      Expr::app(
        Expr::cnst(bad_name.clone(), vec![]),
        Expr::bvar(Nat::from(0u64)), // param α
      ),
      bad_idx_expr, // index mentions BadIdx!
    );
    env.insert(
      bad_mk.clone(),
      ConstantInfo::CtorInfo(ConstructorVal {
        cnst: ConstantVal {
          name: bad_mk,
          level_params: vec![],
          typ: Expr::all(
            mk_name("α"),
            Expr::sort(Level::succ(Level::zero())),
            ctor_ret,
            BinderInfo::Default,
          ),
        },
        induct: bad_name.clone(),
        cidx: Nat::from(0u64),
        num_params: Nat::from(1u64),
        num_fields: Nat::from(0u64),
        is_unsafe: false,
      }),
    );

    let ind = match env.get(&bad_name).unwrap() {
      ConstantInfo::InductInfo(v) => v,
      _ => panic!(),
    };
    let mut tc = TypeChecker::new(&env);
    assert!(check_inductive(ind, &mut tc).is_err());
  }

  // ==========================================================================
  // expr_mentions_const
  // ==========================================================================

  #[test]
  fn expr_mentions_const_direct() {
    let name = mk_name("Foo");
    let e = Expr::cnst(name.clone(), vec![]);
    assert!(expr_mentions_const(&e, &name));
  }

  #[test]
  fn expr_mentions_const_nested_app() {
    let name = mk_name("Foo");
    let e = Expr::app(
      Expr::cnst(mk_name("bar"), vec![]),
      Expr::cnst(name.clone(), vec![]),
    );
    assert!(expr_mentions_const(&e, &name));
  }

  #[test]
  fn expr_mentions_const_absent() {
    let name = mk_name("Foo");
    let e = Expr::app(
      Expr::cnst(mk_name("bar"), vec![]),
      Expr::cnst(mk_name("baz"), vec![]),
    );
    assert!(!expr_mentions_const(&e, &name));
  }

  #[test]
  fn expr_mentions_const_in_forall_domain() {
    let name = mk_name("Foo");
    let e = Expr::all(
      mk_name("x"),
      Expr::cnst(name.clone(), vec![]),
      Expr::sort(Level::zero()),
      BinderInfo::Default,
    );
    assert!(expr_mentions_const(&e, &name));
  }

  #[test]
  fn expr_mentions_const_in_let() {
    let name = mk_name("Foo");
    let e = Expr::letE(
      mk_name("x"),
      Expr::sort(Level::zero()),
      Expr::cnst(name.clone(), vec![]),
      Expr::bvar(Nat::from(0u64)),
      false,
    );
    assert!(expr_mentions_const(&e, &name));
  }
}
