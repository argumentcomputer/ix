//! Constant checking dispatch.

use std::sync::LazyLock;

use crate::ix::env::{DefinitionSafety, QuotKind};
use crate::ix::ixon::constant::DefKind;

use super::constant::KConst;
use super::error::TcError;
use super::expr::{ExprData, KExpr};
use super::id::KId;
use super::level::{KUniv, univ_eq};
use super::mode::{CheckDupLevelParams, KernelMode};
use super::tc::TypeChecker;

/// Emit `[decl diff]` when a `Defn`'s value fails the `is_def_eq(val_ty,
/// ty)` check. The error itself (`DeclTypeMismatch`) carries no payload,
/// so without this gate the only signal is the constant's name. Under
/// `IX_DECL_DIFF=1` we dump `val_ty` / `ty` and their whnf forms to
/// pinpoint which sub-expression is stuck \u2014 sister tool to
/// `IX_APP_DIFF` in `infer.rs`.
static IX_DECL_DIFF: LazyLock<bool> =
  LazyLock::new(|| std::env::var("IX_DECL_DIFF").is_ok());

/// Per-phase timing for `Defn` checks (infer-ty, infer-val, is_def_eq,
/// safety-ty, safety-val). Set `IX_PHASE_TIMING=1` to see where a slow
/// constant spends its time. Noisy — gate on a single constant via
/// focus mode so only one line is printed.
static IX_PHASE_TIMING: LazyLock<bool> =
  LazyLock::new(|| std::env::var("IX_PHASE_TIMING").is_ok());

impl<M: KernelMode> TypeChecker<M> {
  /// Type-check a single constant. Clears per-constant caches first.
  pub fn check_const(&mut self, id: &KId<M>) -> Result<(), TcError<M>>
  where
    M::MField<Vec<crate::ix::env::Name>>: CheckDupLevelParams,
  {
    self.reset();

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
        // Phase timing (guarded): give each phase its own instant so
        // we can see where a slow check spends its time. The caller
        // typically runs this via a focus-mode batch of one constant
        // so the single `[phase]` line is easy to read.
        let overall =
          if *IX_PHASE_TIMING { Some(std::time::Instant::now()) } else { None };

        let t_infer_ty_start = overall.map(|_| std::time::Instant::now());
        let t = self.infer(ty)?;
        let lvl = self.ensure_sort(&t)?;
        let infer_ty_elapsed = t_infer_ty_start.map(|s| s.elapsed());

        // Theorems must have types in Prop (Sort 0)
        if *kind == DefKind::Theorem && !univ_eq(&lvl, &KUniv::zero()) {
          return Err(TcError::Other(
            "theorem type must be a proposition (Sort 0)".into(),
          ));
        }

        let t_infer_val_start = overall.map(|_| std::time::Instant::now());
        let val_ty = self.infer(val)?;
        let infer_val_elapsed = t_infer_val_start.map(|s| s.elapsed());

        let t_def_eq_start = overall.map(|_| std::time::Instant::now());
        let def_eq_ok = self.is_def_eq(&val_ty, ty)?;
        let def_eq_elapsed = t_def_eq_start.map(|s| s.elapsed());

        if !def_eq_ok {
          if *IX_DECL_DIFF {
            // Post-whnf forms on both sides so we can see where
            // reduction terminates and hence which reduction rule
            // (delta, iota, native, ...) is missing for convergence.
            let val_ty_whnf = self.whnf(&val_ty);
            let ty_whnf = self.whnf(ty);
            eprintln!("[decl diff] DeclTypeMismatch");
            eprintln!("  val_ty:      {val_ty}");
            eprintln!("  ty:          {ty}");
            match &val_ty_whnf {
              Ok(w) => eprintln!("  val_ty whnf: {w}"),
              Err(e) => eprintln!("  val_ty whnf: ERR {e}"),
            }
            match &ty_whnf {
              Ok(w) => eprintln!("  ty     whnf: {w}"),
              Err(e) => eprintln!("  ty     whnf: ERR {e}"),
            }
          }
          return Err(TcError::DeclTypeMismatch);
        }

        // #9: Safety level checking — safe/partial defs must not reference unsafe/partial constants
        let t_safety_start = overall.map(|_| std::time::Instant::now());
        if *safety != DefinitionSafety::Unsafe {
          self.check_no_unsafe_refs(ty, *safety)?;
          self.check_no_unsafe_refs(val, *safety)?;
        }
        let safety_elapsed = t_safety_start.map(|s| s.elapsed());

        if let Some(t0) = overall {
          eprintln!(
            "[phase] {} total={:>8.1?} infer_ty={:>8.1?} infer_val={:>8.1?} def_eq={:>8.1?} safety={:>8.1?}",
            id,
            t0.elapsed(),
            infer_ty_elapsed.unwrap_or_default(),
            infer_val_elapsed.unwrap_or_default(),
            def_eq_elapsed.unwrap_or_default(),
            safety_elapsed.unwrap_or_default(),
          );
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
        // `check_recursor` runs the full kernel-driven verification:
        // coherence (major inductive passes A1–A4, K-target flag
        // matches), plus generated-canonical-vs-stored rule comparison
        // via `is_def_eq`. The rule generator (shared between the
        // kernel and the compile-time aux_gen) produces the same
        // output for original and canonical inductives, so the
        // syntactic compare is sound against either env.
        //
        // The old Array vs `_nested.Array_1` false positives are
        // resolved by the two-env split: `check_originals` runs
        // against `stt.kctx.orig_kenv` (pristine `lean_ingress`), and
        // the post-compile FFI check runs against the `ixon_ingress`'d
        // canonical env (aux-restored). Neither carries the compile-
        // time overlay pollution that motivated removing the syntactic
        // path earlier.
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
      QuotKind::Lift => 2,
      QuotKind::Type | QuotKind::Ctor | QuotKind::Ind => 1,
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
  use std::sync::Arc;

  use super::super::constant::KConst;
  use super::super::env::KEnv;
  use super::super::error::TcError;
  use super::super::expr::KExpr;
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

  fn test_env() -> Arc<KEnv<Anon>> {
    let env = Arc::new(KEnv::new());
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
    let mut tc = TypeChecker::new(Arc::clone(&env));
    assert!(tc.check_const(&mk_id("Nat")).is_ok());
  }

  #[test]
  fn check_defn_ok() {
    let env = test_env();
    let mut tc = TypeChecker::new(Arc::clone(&env));
    assert!(tc.check_const(&mk_id("id")).is_ok());
  }

  #[test]
  fn check_defn_mismatch() {
    let env = test_env();
    let mut tc = TypeChecker::new(Arc::clone(&env));
    assert!(tc.check_const(&mk_id("wrong")).is_err());
  }

  #[test]
  fn check_unknown_const() {
    let env = test_env();
    let mut tc = TypeChecker::new(Arc::clone(&env));
    assert!(tc.check_const(&mk_id("nonexistent")).is_err());
  }

  #[test]
  fn check_clears_caches() {
    let env = test_env();
    let mut tc = TypeChecker::new(Arc::clone(&env));
    tc.check_const(&mk_id("Nat")).unwrap();
    // def_eq_depth should be reset
    assert_eq!(tc.def_eq_depth, 0);
    assert_eq!(tc.def_eq_peak, 0);
  }

  // =========================================================================
  // Theorem must land in Prop
  // =========================================================================

  #[test]
  fn check_theorem_with_type_in_prop_ok() {
    let env = Arc::new(KEnv::<Anon>::new());
    // Axiom P : Prop.
    env.insert(
      mk_id("P"),
      KConst::Axio {
        name: (),
        level_params: (),
        is_unsafe: false,
        lvls: 0,
        ty: sort0(),
      },
    );
    // Axiom p : P.
    env.insert(
      mk_id("p"),
      KConst::Axio {
        name: (),
        level_params: (),
        is_unsafe: false,
        lvls: 0,
        ty: AE::cnst(mk_id("P"), Box::new([])),
      },
    );
    // Theorem thm : P := p.
    env.insert(
      mk_id("thm"),
      KConst::Defn {
        name: (),
        level_params: (),
        kind: DefKind::Theorem,
        safety: DefinitionSafety::Safe,
        hints: ReducibilityHints::Opaque,
        lvls: 0,
        ty: AE::cnst(mk_id("P"), Box::new([])),
        val: AE::cnst(mk_id("p"), Box::new([])),
        lean_all: (),
        block: mk_id("thm"),
      },
    );
    let mut tc = TypeChecker::new(Arc::clone(&env));
    tc.check_const(&mk_id("thm")).unwrap();
  }

  #[test]
  fn check_theorem_with_non_prop_type_rejected() {
    let env = Arc::new(KEnv::<Anon>::new());
    // Theorem claiming to inhabit Sort 1 (not Prop) — must be rejected.
    env.insert(
      mk_id("thm_bad"),
      KConst::Defn {
        name: (),
        level_params: (),
        kind: DefKind::Theorem,
        safety: DefinitionSafety::Safe,
        hints: ReducibilityHints::Opaque,
        lvls: 0,
        ty: sort1(), // Type, not Prop
        val: sort0(),
        lean_all: (),
        block: mk_id("thm_bad"),
      },
    );
    let mut tc = TypeChecker::new(Arc::clone(&env));
    match tc.check_const(&mk_id("thm_bad")) {
      Err(TcError::Other(s)) => {
        assert!(s.contains("theorem type must be a proposition"));
      },
      other => panic!("expected theorem-must-be-Prop error, got {other:?}"),
    }
  }

  // =========================================================================
  // Axiom type must be a Sort
  // =========================================================================

  #[test]
  fn check_axiom_with_non_sort_type_rejected() {
    // Axiom whose declared type is `id` (a definition, not a Sort) → error.
    let base = test_env();
    let env = Arc::clone(&base);
    // Add an axiom with a bogus type — the type expression is valid, but its
    // _inferred type_ (the type of its type) is `Sort 0 → Sort 0`'s type,
    // which is a Sort. To actually hit `TypeExpected` we need a type that
    // infers to something non-Sort — take a projection into a non-struct.
    // Easier: declare a type that's a Var in an empty context (out-of-range).
    env.insert(
      mk_id("bad_ax"),
      KConst::Axio {
        name: (),
        level_params: (),
        is_unsafe: false,
        lvls: 0,
        // Var(0) in the empty context — infer will return VarOutOfRange.
        ty: AE::var(0, ()),
      },
    );
    let mut tc = TypeChecker::new(Arc::clone(&env));
    assert!(tc.check_const(&mk_id("bad_ax")).is_err());
  }

  // =========================================================================
  // Duplicate level-param names
  // =========================================================================

  #[test]
  fn check_duplicate_level_params_rejected() {
    use crate::ix::kernel::mode::Meta;
    type ME = KExpr<Meta>;
    type MU = KUniv<Meta>;

    let env = Arc::new(KEnv::<Meta>::new());
    let dup_name =
      crate::ix::env::Name::str(crate::ix::env::Name::anon(), "u".into());
    let id = KId::new(mk_addr("T"), dup_name.clone());
    env.insert(
      id.clone(),
      KConst::Axio {
        name: dup_name.clone(),
        level_params: vec![dup_name.clone(), dup_name.clone()],
        is_unsafe: false,
        lvls: 2,
        ty: ME::sort(MU::succ(MU::zero())),
      },
    );
    let mut tc = TypeChecker::new(Arc::clone(&env));
    match tc.check_const(&id) {
      Err(TcError::Other(s)) => {
        assert!(s.contains("duplicate universe level parameter"));
      },
      other => panic!("expected duplicate-level-param error, got {other:?}"),
    }
  }

  // =========================================================================
  // Caching: check_const is idempotent
  // =========================================================================

  #[test]
  fn check_const_idempotent() {
    let env = test_env();
    let mut tc = TypeChecker::new(Arc::clone(&env));
    tc.check_const(&mk_id("id")).unwrap();
    tc.check_const(&mk_id("id")).unwrap();
    tc.check_const(&mk_id("id")).unwrap();
  }

  // =========================================================================
  // Axiom with unknown referent in its type errors
  // =========================================================================

  #[test]
  fn check_axiom_referencing_unknown_const_errors() {
    let env = Arc::new(KEnv::<Anon>::new());
    env.insert(
      mk_id("x"),
      KConst::Axio {
        name: (),
        level_params: (),
        is_unsafe: false,
        lvls: 0,
        ty: AE::cnst(mk_id("UnknownType"), Box::new([])),
      },
    );
    let mut tc = TypeChecker::new(Arc::clone(&env));
    match tc.check_const(&mk_id("x")) {
      Err(TcError::UnknownConst(_)) => {},
      other => panic!("expected UnknownConst, got {other:?}"),
    }
  }
}
