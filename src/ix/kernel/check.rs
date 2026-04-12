//! Constant checking dispatch.

use crate::ix::env::{DefinitionSafety, QuotKind};
use crate::ix::ixon::constant::DefKind;

use super::constant::KConst;
use super::error::TcError;
use super::expr::{ExprData, KExpr};
use super::id::KId;
use super::level::{KUniv, univ_eq};
use super::mode::{CheckDupLevelParams, KernelMode};
use super::tc::TypeChecker;

impl<'env, M: KernelMode> TypeChecker<'env, M> {
  /// Type-check a single constant. Clears per-constant caches first.
  pub fn check_const(&mut self, id: &KId<M>) -> Result<(), TcError<M>>
  where
    M::MField<Vec<crate::ix::env::Name>>: CheckDupLevelParams,
  {
    self.clear_caches();

    let c = self
      .env
      .get(id)
      .ok_or_else(|| TcError::UnknownConst(id.addr.clone()))?
      .clone();

    if c.level_params().has_duplicate_level_params() {
      return Err(TcError::Other("duplicate universe level parameter".into()));
    }

    match &c {
      KConst::Axio { ty, .. } => {
        let t = self.infer(ty)?;
        self.ensure_sort(&t)?;
        Ok(())
      },

      KConst::Defn { ty, val, safety, kind, .. } => {
        let t = self.infer(ty)?;
        let lvl = self.ensure_sort(&t)?;
        // Theorems must have types in Prop (Sort 0)
        if *kind == DefKind::Theorem && !univ_eq(&lvl, &KUniv::zero()) {
          return Err(TcError::Other(
            "theorem type must be a proposition (Sort 0)".into(),
          ));
        }
        let val_ty = self.infer(val)?;
        if !self.is_def_eq(&val_ty, ty)? {
          return Err(TcError::DeclTypeMismatch);
        }
        // #9: Safety level checking — safe/partial defs must not reference unsafe/partial constants
        if *safety != DefinitionSafety::Unsafe {
          self.check_no_unsafe_refs(ty, *safety)?;
          self.check_no_unsafe_refs(val, *safety)?;
        }
        Ok(())
      },

      KConst::Quot { ty, kind, lvls, .. } => {
        let t = self.infer(ty)?;
        self.ensure_sort(&t)?;
        self.check_quot(id, *kind, *lvls, ty)?;
        Ok(())
      },

      KConst::Recr { ty, .. } => {
        let t = self.infer(ty)?;
        self.ensure_sort(&t)?;
        self.check_recursor(id)?;
        Ok(())
      },

      KConst::Indc { ty, .. } => {
        let t = self.infer(ty)?;
        self.ensure_sort(&t)?;
        self.check_inductive(id)?;
        Ok(())
      },

      KConst::Ctor { ty, induct, .. } => {
        let t = self.infer(ty)?;
        self.ensure_sort(&t)?;
        // Validate against the parent inductive (A1–A4 checks).
        // This ensures standalone ctorInfo is rejected if it doesn't
        // match its declared inductive.
        let induct = induct.clone();
        self.check_ctor_against_inductive(id, &induct)?;
        Ok(())
      },
    }
  }

  // -----------------------------------------------------------------------
  // #5: Quotient type validation
  // -----------------------------------------------------------------------

  /// Validate quotient constant structure.
  ///
  /// Checks:
  /// - Correct address matches the expected QuotKind
  /// - Correct universe parameter count per variant
  /// - Eq type exists with correct shape (1 universe param, 1 ctor Eq.refl)
  fn check_quot(
    &mut self,
    id: &KId<M>,
    kind: QuotKind,
    lvls: u64,
    ty: &KExpr<M>,
  ) -> Result<(), TcError<M>> {
    // Validate address ↔ kind consistency
    let expected_kind = if id.addr == self.prims.quot_type.addr {
      QuotKind::Type
    } else if id.addr == self.prims.quot_ctor.addr {
      QuotKind::Ctor
    } else if id.addr == self.prims.quot_lift.addr {
      QuotKind::Lift
    } else if id.addr == self.prims.quot_ind.addr {
      QuotKind::Ind
    } else {
      return Err(TcError::Other(format!(
        "check_quot: unknown quot address {}",
        &id.addr.hex()[..8]
      )));
    };

    if kind != expected_kind {
      return Err(TcError::Other(format!(
        "check_quot: kind mismatch: declared {:?} but address matches {:?}",
        kind, expected_kind
      )));
    }

    // Validate universe parameter count per variant
    // Quot: 1 (u), Quot.mk: 1 (u), Quot.lift: 2 (u,v), Quot.ind: 1 (u)
    let expected_lvls = match kind {
      QuotKind::Type => 1,
      QuotKind::Ctor => 1,
      QuotKind::Lift => 2,
      QuotKind::Ind => 1,
    };
    if lvls != expected_lvls {
      return Err(TcError::Other(format!(
        "check_quot: {:?} expects {} universe params, got {}",
        kind, expected_lvls, lvls
      )));
    }

    // For Quot.lift (the main eliminator), verify Eq is properly formed.
    // This is a prerequisite for the quot reduction rule to be sound.
    if kind == QuotKind::Lift {
      self.check_eq_type()?;
    }

    // Validate the type has the correct number of forall binders.
    // Quot: 2 (α, r)
    // Quot.mk: 3 (α, r, a)
    // Quot.lift: 6 (α, r, β, f, h, q)
    // Quot.ind: 5 (α, r, β, h, q)
    let expected_foralls = match kind {
      QuotKind::Type => 2,
      QuotKind::Ctor => 3,
      QuotKind::Lift => 6,
      QuotKind::Ind => 5,
    };
    let n_foralls = self.count_foralls(ty)?;
    if n_foralls < expected_foralls {
      return Err(TcError::Other(format!(
        "check_quot: {:?} expects at least {} foralls, got {}",
        kind, expected_foralls, n_foralls
      )));
    }

    Ok(())
  }

  /// Verify Eq type has the expected shape: 1 universe param, 1 constructor (Eq.refl).
  fn check_eq_type(&self) -> Result<(), TcError<M>> {
    // Find Eq inductive in the environment by address.
    // Search all constants for one matching the Eq address.
    let eq_const = self
      .env
      .iter()
      .find(|(id, _)| id.addr == self.prims.eq.addr)
      .map(|(id, c)| (id.clone(), c.clone()));
    let (_eq_id, eq_c) = eq_const.ok_or_else(|| {
      TcError::Other("check_eq_type: Eq not found in environment".into())
    })?;
    match &eq_c {
      KConst::Indc { lvls, ctors, params, .. } => {
        if *lvls != 1 {
          return Err(TcError::Other(format!(
            "check_eq_type: Eq expects 1 universe param, got {}",
            lvls
          )));
        }
        // Eq : {α : Sort u} → α → α → Prop
        // numParams = 2 (α, a are uniform across Eq.refl), numIndices = 1 (b)
        if *params != 2 {
          return Err(TcError::Other(format!(
            "check_eq_type: Eq expects 2 params (α, a), got {}",
            params
          )));
        }
        if ctors.len() != 1 {
          return Err(TcError::Other(format!(
            "check_eq_type: Eq expects 1 constructor, got {}",
            ctors.len()
          )));
        }
        // Verify the constructor is Eq.refl
        if ctors[0].addr != self.prims.eq_refl.addr {
          return Err(TcError::Other(
            "check_eq_type: Eq's constructor is not Eq.refl".into(),
          ));
        }
        Ok(())
      },
      _ => Err(TcError::Other(
        "check_eq_type: Eq not found or not inductive".into(),
      )),
    }
  }

  /// Count the number of leading foralls in a type.
  fn count_foralls(&mut self, ty: &KExpr<M>) -> Result<usize, TcError<M>> {
    let saved = self.save_depth();
    let mut n = 0;
    let mut cur = ty.clone();
    loop {
      let w = self.whnf(&cur)?;
      match w.data() {
        ExprData::All(_, _, dom, body, _) => {
          n += 1;
          self.push_local(dom.clone());
          cur = body.clone();
        },
        _ => {
          self.restore_depth(saved);
          return Ok(n);
        },
      }
    }
  }

  // -----------------------------------------------------------------------
  // #9: Safety level checking
  // -----------------------------------------------------------------------

  /// Verify that an expression does not reference constants with weaker safety.
  /// `caller_safety` is the safety level of the definition being checked.
  /// - Safe defs cannot reference unsafe or partial constants
  /// - Partial defs cannot reference unsafe constants
  fn check_no_unsafe_refs(
    &self,
    e: &KExpr<M>,
    caller_safety: DefinitionSafety,
  ) -> Result<(), TcError<M>> {
    self.walk_for_unsafe(e, caller_safety)
  }

  /// Iterative (stack-based) walk — immune to stack overflow on deeply nested input.
  fn walk_for_unsafe(
    &self,
    root: &KExpr<M>,
    caller_safety: DefinitionSafety,
  ) -> Result<(), TcError<M>> {
    let mut stack: Vec<&KExpr<M>> = vec![root];
    while let Some(e) = stack.pop() {
      match e.data() {
        ExprData::Var(..)
        | ExprData::Sort(..)
        | ExprData::Nat(..)
        | ExprData::Str(..) => {},
        ExprData::Const(id, _, _) => match self.env.get(id) {
          Some(KConst::Axio { is_unsafe: true, .. }) => {
            return Err(TcError::Other(format!(
              "safe definition references unsafe axiom {}",
              &id.addr.hex()[..8]
            )));
          },
          Some(KConst::Defn { safety: DefinitionSafety::Unsafe, .. }) => {
            return Err(TcError::Other(format!(
              "safe definition references unsafe definition {}",
              &id.addr.hex()[..8]
            )));
          },
          Some(KConst::Defn { safety: DefinitionSafety::Partial, .. })
            if caller_safety == DefinitionSafety::Safe =>
          {
            return Err(TcError::Other(format!(
              "safe definition references partial definition {}",
              &id.addr.hex()[..8]
            )));
          },
          _ => {},
        },
        ExprData::App(f, a, _) => {
          stack.push(f);
          stack.push(a);
        },
        ExprData::Lam(_, _, ty, body, _) | ExprData::All(_, _, ty, body, _) => {
          stack.push(ty);
          stack.push(body);
        },
        ExprData::Let(_, ty, val, body, _, _) => {
          stack.push(ty);
          stack.push(val);
          stack.push(body);
        },
        ExprData::Prj(_, _, val, _) => {
          stack.push(val);
        },
      }
    }
    Ok(())
  }
}

#[cfg(test)]
mod tests {
  use super::super::constant::KConst;
  use super::super::env::{InternTable, KEnv};
  use super::super::expr::{ExprData, KExpr};
  use super::super::id::KId;
  use super::super::level::KUniv;
  use super::super::mode::Anon;
  use super::super::tc::TypeChecker;
  use crate::ix::address::Address;
  use crate::ix::env::{DefinitionSafety, ReducibilityHints};
  use crate::ix::ixon::constant::DefKind;

  type AE = KExpr<Anon>;
  type AU = KUniv<Anon>;

  fn mk_addr(s: &str) -> Address {
    Address::hash(s.as_bytes())
  }
  fn mk_id(s: &str) -> KId<Anon> {
    KId::new(mk_addr(s), ())
  }
  fn sort0() -> AE {
    AE::sort(AU::zero())
  }
  fn sort1() -> AE {
    AE::sort(AU::succ(AU::zero()))
  }

  fn test_env() -> KEnv<Anon> {
    let mut env = KEnv::new();
    // Axiom: Nat : Sort 1
    env.insert(
      mk_id("Nat"),
      KConst::Axio {
        name: (),
        level_params: (),
        is_unsafe: false,
        lvls: 0,
        ty: sort1(),
      },
    );
    // Definition: id : Sort 0 → Sort 0 := λ x. x
    let id_ty = AE::all((), (), sort0(), sort0());
    let id_val = AE::lam((), (), sort0(), AE::var(0, ()));
    env.insert(
      mk_id("id"),
      KConst::Defn {
        name: (),
        level_params: (),
        kind: DefKind::Definition,
        safety: DefinitionSafety::Safe,
        hints: ReducibilityHints::Abbrev,
        lvls: 0,
        ty: id_ty,
        val: id_val,
        lean_all: (),
        block: mk_id("id"),
      },
    );
    // Bad definition: wrong_id : Sort 0 → Sort 0 := Sort 1 (type mismatch)
    let wrong_ty = AE::all((), (), sort0(), sort0());
    let wrong_val = sort1(); // Sort 1, but declared type says Sort 0 → Sort 0
    env.insert(
      mk_id("wrong"),
      KConst::Defn {
        name: (),
        level_params: (),
        kind: DefKind::Definition,
        safety: DefinitionSafety::Safe,
        hints: ReducibilityHints::Regular(0),
        lvls: 0,
        ty: wrong_ty,
        val: wrong_val,
        lean_all: (),
        block: mk_id("wrong"),
      },
    );
    env
  }

  #[test]
  fn check_axiom() {
    let env = test_env();
    let mut tc = TypeChecker::new(&env, InternTable::new());
    assert!(tc.check_const(&mk_id("Nat")).is_ok());
  }

  #[test]
  fn check_defn_ok() {
    let env = test_env();
    let mut tc = TypeChecker::new(&env, InternTable::new());
    assert!(tc.check_const(&mk_id("id")).is_ok());
  }

  #[test]
  fn check_defn_mismatch() {
    let env = test_env();
    let mut tc = TypeChecker::new(&env, InternTable::new());
    assert!(tc.check_const(&mk_id("wrong")).is_err());
  }

  #[test]
  fn check_unknown_const() {
    let env = test_env();
    let mut tc = TypeChecker::new(&env, InternTable::new());
    assert!(tc.check_const(&mk_id("nonexistent")).is_err());
  }

  #[test]
  fn check_clears_caches() {
    let env = test_env();
    let mut tc = TypeChecker::new(&env, InternTable::new());
    tc.check_const(&mk_id("Nat")).unwrap();
    // def_eq_depth should be reset
    assert_eq!(tc.def_eq_depth, 0);
    assert_eq!(tc.def_eq_peak, 0);
  }
}
