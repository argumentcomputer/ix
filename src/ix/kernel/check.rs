//! Constant checking dispatch.

use std::sync::LazyLock;
use std::time::{Duration, Instant};

use rustc_hash::FxHashSet;

use crate::ix::address::Address;
use crate::ix::env::{DefinitionSafety, QuotKind};
use crate::ix::ixon::constant::DefKind;

use super::constant::KConst;
use super::env::Addr;
use super::error::{TcError, u64_to_usize};
use super::expr::{ExprData, KExpr};
use super::id::KId;
use super::lctx::LocalDecl;
use super::level::{KUniv, UnivData, univ_eq};
use super::mode::{CheckDupLevelParams, KernelMode};
use super::subst::instantiate_rev;
use super::tc::TypeChecker;

/// Emit `[decl diff]` when a `Defn`'s value fails the `is_def_eq(val_ty,
/// ty)` check. The error itself (`DeclTypeMismatch`) carries no payload,
/// so without this gate the only signal is the constant's name. Under
/// `IX_DECL_DIFF=1` we dump `val_ty` / `ty` and their whnf forms to
/// pinpoint which sub-expression is stuck \u2014 sister tool to
/// `IX_APP_DIFF` in `infer.rs`.
static IX_DECL_DIFF: LazyLock<bool> =
  LazyLock::new(|| std::env::var("IX_DECL_DIFF").is_ok());

/// Per-phase timing for `Defn` checks. Set `IX_PHASE_TIMING=1` to see where a
/// slow constant spends its time. Noisy — gate on a single constant via focus
/// mode so only one line is printed.
static IX_PHASE_TIMING: LazyLock<bool> =
  LazyLock::new(|| std::env::var("IX_PHASE_TIMING").is_ok());

#[derive(Clone, Copy, Debug, Default)]
struct ValidationTiming {
  ty: Duration,
  val: Duration,
  rules: Duration,
  univ: Duration,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum CheckBlockKind {
  Defn,
  Inductive,
  Recursor,
}

impl<M: KernelMode> TypeChecker<'_, M> {
  /// Return the whole-block check key for a constant when its block has a
  /// supported homogeneous shape. This is used by batch schedulers to avoid
  /// assigning multiple workers to members of the same block.
  pub fn coordinated_check_block_for_const(
    &mut self,
    id: &KId<M>,
  ) -> Result<Option<KId<M>>, TcError<M>> {
    let Some(c) = self.try_get_const(id)? else {
      return Ok(None);
    };
    self.coordinated_block_for(&c)
  }

  /// Type-check a single constant. Clears per-constant caches first.
  pub fn check_const(&mut self, id: &KId<M>) -> Result<(), TcError<M>>
  where
    M::MField<Vec<crate::ix::env::Name>>: CheckDupLevelParams,
  {
    let c = self.get_const(id)?;
    if let Some(block) = self.coordinated_block_for(&c)? {
      if let Some(result) = self.env.block_check_results.get(&block).cloned() {
        return result;
      }
      let result = self.check_block_body(&block, id);
      self.env.block_check_results.insert(block, result.clone());
      return result;
    }

    self.check_const_member_fresh(id)
  }

  fn check_const_member_fresh(&mut self, id: &KId<M>) -> Result<(), TcError<M>>
  where
    M::MField<Vec<crate::ix::env::Name>>: CheckDupLevelParams,
  {
    self.reset();

    let c = self.get_const(id)?;
    self.check_const_member(id, &c)
  }

  fn check_const_member(
    &mut self,
    id: &KId<M>,
    c: &KConst<M>,
  ) -> Result<(), TcError<M>>
  where
    M::MField<Vec<crate::ix::env::Name>>: CheckDupLevelParams,
  {
    let phase_timing = *IX_PHASE_TIMING;
    let overall = if phase_timing { Some(Instant::now()) } else { None };

    let dup_start = overall.map(|_| Instant::now());
    if c.level_params().has_duplicate_level_params() {
      return Err(TcError::Other("duplicate universe level parameter".into()));
    }
    let dup_elapsed = dup_start.map(|s| s.elapsed());

    let mut validation_timing = ValidationTiming::default();
    let validate_start = overall.map(|_| Instant::now());
    if phase_timing {
      self.validate_const_well_scoped_timed(c, Some(&mut validation_timing))?;
    } else {
      self.validate_const_well_scoped(c)?;
    }
    let validate_elapsed = validate_start.map(|s| s.elapsed());

    match &c {
      KConst::Axio { ty, .. } => {
        let t = self.infer(ty)?;
        self.ensure_sort(&t)?;
        Ok(())
      },

      KConst::Defn { ty, val, safety, kind, .. } => {
        let t_infer_ty_start = overall.map(|_| Instant::now());
        let t = self.infer(ty)?;
        let lvl = self.ensure_sort(&t)?;
        let infer_ty_elapsed = t_infer_ty_start.map(|s| s.elapsed());

        // Theorems must have types in Prop (Sort 0)
        if *kind == DefKind::Theorem && !univ_eq(&lvl, &KUniv::zero()) {
          return Err(TcError::Other(
            "theorem type must be a proposition (Sort 0)".into(),
          ));
        }

        let t_infer_val_start = overall.map(|_| Instant::now());
        let val_ty = self.infer(val)?;
        let infer_val_elapsed = t_infer_val_start.map(|s| s.elapsed());

        let t_def_eq_start = overall.map(|_| Instant::now());
        let def_eq_ok = self.is_def_eq(&val_ty, ty)?;
        let def_eq_elapsed = t_def_eq_start.map(|s| s.elapsed());

        if !def_eq_ok {
          if *IX_DECL_DIFF && self.debug_label_matches_env() {
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
        let t_safety_start = overall.map(|_| Instant::now());
        let mut safety_ty_elapsed = None;
        let mut safety_val_elapsed = None;
        if *safety != DefinitionSafety::Unsafe {
          let t_safety_ty_start = overall.map(|_| Instant::now());
          self.check_no_unsafe_refs(ty, *safety)?;
          safety_ty_elapsed = t_safety_ty_start.map(|s| s.elapsed());

          let t_safety_val_start = overall.map(|_| Instant::now());
          self.check_no_unsafe_refs(val, *safety)?;
          safety_val_elapsed = t_safety_val_start.map(|s| s.elapsed());
        }
        let safety_elapsed = t_safety_start.map(|s| s.elapsed());

        if let Some(t0) = overall
          && self.phase_timing_label_matches(id)
        {
          eprintln!(
            "[phase] {} total={:>8.1?} dup_lvls={:>8.1?} validate={:>8.1?} validate_ty={:>8.1?} validate_val={:>8.1?} validate_rules={:>8.1?} validate_univ={:>8.1?} infer_ty={:>8.1?} infer_val={:>8.1?} def_eq={:>8.1?} safety={:>8.1?} safety_ty={:>8.1?} safety_val={:>8.1?}",
            id,
            t0.elapsed(),
            dup_elapsed.unwrap_or_default(),
            validate_elapsed.unwrap_or_default(),
            validation_timing.ty,
            validation_timing.val,
            validation_timing.rules,
            validation_timing.univ,
            infer_ty_elapsed.unwrap_or_default(),
            infer_val_elapsed.unwrap_or_default(),
            def_eq_elapsed.unwrap_or_default(),
            safety_elapsed.unwrap_or_default(),
            safety_ty_elapsed.unwrap_or_default(),
            safety_val_elapsed.unwrap_or_default(),
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
        // coherence (major inductive passes A1–A4, K-target flag matches),
        // plus generated-canonical-vs-stored rule comparison via
        // `is_def_eq`. The rule generator is shared between the kernel and
        // the compile-time aux_gen, with the nested-aux ordering selected
        // by `KEnv::recursor_aux_order`, so the syntactic compare is sound
        // against the canonical aux-restored env produced by `ixon_ingress`.
        self.check_recursor_member(id)?;
        Ok(())
      },

      KConst::Indc { ty, .. } => {
        let t = self.infer(ty)?;
        self.ensure_sort(&t)?;
        self.check_inductive_member(id)?;
        Ok(())
      },

      KConst::Ctor { ty, induct, .. } => {
        let t = self.infer(ty)?;
        self.ensure_sort(&t)?;
        // Validate against the parent inductive (A1–A4 checks).
        // This ensures standalone ctorInfo is rejected if it doesn't
        // match its declared inductive.
        let induct = induct.clone();
        self.check_ctor_against_inductive_member(id, &induct)?;
        Ok(())
      },
    }
  }

  fn coordinated_block_for(
    &mut self,
    c: &KConst<M>,
  ) -> Result<Option<KId<M>>, TcError<M>> {
    match c {
      KConst::Defn { block, .. } => {
        self.coordinated_block_if_kind(block, CheckBlockKind::Defn)
      },
      KConst::Indc { block, .. } => {
        self.coordinated_block_if_kind(block, CheckBlockKind::Inductive)
      },
      KConst::Ctor { induct, .. } => {
        let Some(parent) = self.try_get_const(induct)? else {
          return Ok(None);
        };
        match parent {
          KConst::Indc { block, .. } => {
            self.coordinated_block_if_kind(&block, CheckBlockKind::Inductive)
          },
          _ => Ok(None),
        }
      },
      KConst::Recr { block, .. } => {
        self.coordinated_block_if_kind(block, CheckBlockKind::Recursor)
      },
      KConst::Axio { .. } | KConst::Quot { .. } => Ok(None),
    }
  }

  fn coordinated_block_if_kind(
    &mut self,
    block: &KId<M>,
    expected: CheckBlockKind,
  ) -> Result<Option<KId<M>>, TcError<M>> {
    let Some(members) = self.try_get_block(block)? else {
      return Ok(None);
    };
    match self.classify_block(&members) {
      Ok(kind) if kind == expected => Ok(Some(block.clone())),
      Ok(_) | Err(_) => Ok(None),
    }
  }

  fn classify_block(
    &mut self,
    members: &[KId<M>],
  ) -> Result<CheckBlockKind, TcError<M>> {
    if members.is_empty() {
      return Err(TcError::Other("empty check block".into()));
    }

    let mut saw_defn = false;
    let mut saw_recr = false;
    let mut saw_inductive_like = false;
    for member in members {
      match self.get_const(member)? {
        KConst::Defn { .. } => saw_defn = true,
        KConst::Recr { .. } => saw_recr = true,
        KConst::Indc { .. } | KConst::Ctor { .. } => {
          saw_inductive_like = true;
        },
        KConst::Axio { .. } | KConst::Quot { .. } => {
          return Err(TcError::Other(format!(
            "unsupported check block {member}: axiom/quotient member"
          )));
        },
      }
    }

    match (saw_defn, saw_inductive_like, saw_recr) {
      (true, false, false) => Ok(CheckBlockKind::Defn),
      (false, true, false) => Ok(CheckBlockKind::Inductive),
      (false, false, true) => Ok(CheckBlockKind::Recursor),
      _ => Err(TcError::Other(
        "unsupported mixed check block: expected only definitions, only inductives/constructors, or only recursors"
          .into(),
      )),
    }
  }

  fn check_block_body(
    &mut self,
    block: &KId<M>,
    requested: &KId<M>,
  ) -> Result<(), TcError<M>>
  where
    M::MField<Vec<crate::ix::env::Name>>: CheckDupLevelParams,
  {
    let phase_timing = *IX_PHASE_TIMING;
    let overall = if phase_timing { Some(Instant::now()) } else { None };

    let get_members_start = overall.map(|_| Instant::now());
    let members =
      self.try_get_block(block)?.unwrap_or_else(|| vec![requested.clone()]);
    let get_members_elapsed = get_members_start.map(|s| s.elapsed());

    let classify_start = overall.map(|_| Instant::now());
    let kind = self.classify_block(&members)?;
    let classify_elapsed = classify_start.map(|s| s.elapsed());

    let mut validation_timing = ValidationTiming::default();
    let prevalidate_start = overall.map(|_| Instant::now());
    if kind != CheckBlockKind::Defn {
      for member in &members {
        let c = self.get_const(member)?;
        if c.level_params().has_duplicate_level_params() {
          return Err(TcError::Other(
            "duplicate universe level parameter".into(),
          ));
        }
        if phase_timing {
          self.validate_const_well_scoped_timed(
            &c,
            Some(&mut validation_timing),
          )?;
        } else {
          self.validate_const_well_scoped(&c)?;
        }
      }
    }
    let prevalidate_elapsed = prevalidate_start.map(|s| s.elapsed());

    let body_start = overall.map(|_| Instant::now());
    let result = match kind {
      CheckBlockKind::Defn => {
        let mut peak = 0;
        for member in &members {
          self.check_const_member_fresh(member)?;
          peak = peak.max(self.def_eq_peak);
        }
        self.def_eq_peak = peak;
        Ok(())
      },
      CheckBlockKind::Inductive => self.check_inductive_block(block, &members),
      CheckBlockKind::Recursor => self.check_recursor_block(block, &members),
    };
    let body_elapsed = body_start.map(|s| s.elapsed());

    if let Some(t0) = overall
      && self.phase_timing_label_matches(block)
    {
      eprintln!(
        "[phase-block] {} kind={:?} members={} total={:>8.1?} get_members={:>8.1?} prevalidate={:>8.1?} validate_ty={:>8.1?} validate_val={:>8.1?} validate_rules={:>8.1?} validate_univ={:>8.1?} classify={:>8.1?} body={:>8.1?}",
        block,
        kind,
        members.len(),
        t0.elapsed(),
        get_members_elapsed.unwrap_or_default(),
        prevalidate_elapsed.unwrap_or_default(),
        validation_timing.ty,
        validation_timing.val,
        validation_timing.rules,
        validation_timing.univ,
        classify_elapsed.unwrap_or_default(),
        body_elapsed.unwrap_or_default(),
      );
    }

    result
  }

  // -----------------------------------------------------------------------
  // #5: Quotient type validation
  // -----------------------------------------------------------------------

  /// Validate declaration expressions before inference.
  ///
  /// This is the Ix equivalent of Lean's declaration-admission closure and
  /// universe-param checks: declarations must be closed at the top level, and
  /// every `Param(idx)` in their type/value/rules must refer to one of the
  /// declaration's own universe parameters.
  pub(crate) fn validate_const_well_scoped(
    &mut self,
    c: &KConst<M>,
  ) -> Result<(), TcError<M>> {
    self.validate_const_well_scoped_timed(c, None)
  }

  fn validate_const_well_scoped_timed(
    &mut self,
    c: &KConst<M>,
    mut timing: Option<&mut ValidationTiming>,
  ) -> Result<(), TcError<M>> {
    let lvl_bound = u64_to_usize::<M>(c.lvls())?;
    let ty_start = timing.as_ref().map(|_| Instant::now());
    self.validate_expr_well_scoped(
      c.ty(),
      0,
      lvl_bound,
      timing.as_deref_mut(),
    )?;
    if let (Some(t), Some(start)) = (timing.as_deref_mut(), ty_start) {
      t.ty += start.elapsed();
    }
    match c {
      KConst::Defn { val, .. } => {
        let val_start = timing.as_ref().map(|_| Instant::now());
        self.validate_expr_well_scoped(
          val,
          0,
          lvl_bound,
          timing.as_deref_mut(),
        )?;
        if let (Some(t), Some(start)) = (timing.as_deref_mut(), val_start) {
          t.val += start.elapsed();
        }
      },
      KConst::Recr { rules, .. } => {
        let rules_start = timing.as_ref().map(|_| Instant::now());
        for rule in rules {
          self.validate_expr_well_scoped(
            &rule.rhs,
            0,
            lvl_bound,
            timing.as_deref_mut(),
          )?;
        }
        if let (Some(t), Some(start)) = (timing, rules_start) {
          t.rules += start.elapsed();
        }
      },
      KConst::Axio { .. }
      | KConst::Quot { .. }
      | KConst::Indc { .. }
      | KConst::Ctor { .. } => {},
    }
    Ok(())
  }

  fn phase_timing_label_matches(&self, id: &KId<M>) -> bool {
    match std::env::var("IX_KERNEL_DEBUG_CONST") {
      Ok(filter) if filter.is_empty() => true,
      Ok(filter) => {
        id.to_string().contains(&filter)
          || self
            .debug_label
            .as_ref()
            .is_some_and(|label| label.contains(&filter))
      },
      Err(_) => true,
    }
  }

  fn validate_expr_well_scoped(
    &mut self,
    root: &KExpr<M>,
    root_depth: u64,
    lvl_bound: usize,
    mut timing: Option<&mut ValidationTiming>,
  ) -> Result<(), TcError<M>> {
    let mut stack: Vec<(&KExpr<M>, u64)> = vec![(root, root_depth)];
    let mut seen_exprs: FxHashSet<(Addr, u64)> = FxHashSet::default();
    let mut seen_univs: FxHashSet<Addr> = FxHashSet::default();
    while let Some((e, depth)) = stack.pop() {
      if !seen_exprs.insert((e.hash_key(), depth)) {
        continue;
      }
      match e.data() {
        ExprData::Var(idx, _, _) => {
          if *idx >= depth {
            let ctx_len = usize::try_from(depth).unwrap_or(usize::MAX);
            return Err(TcError::VarOutOfRange { idx: *idx, ctx_len });
          }
        },
        ExprData::Sort(u, _) => {
          let univ_start = timing.as_ref().map(|_| Instant::now());
          self.validate_univ_params_seen(u, lvl_bound, &mut seen_univs)?;
          if let (Some(t), Some(start)) = (timing.as_deref_mut(), univ_start) {
            t.univ += start.elapsed();
          }
        },
        ExprData::Const(id, us, _) => {
          let c = self.get_const(id)?;
          if u64_to_usize::<M>(c.lvls())? != us.len() {
            return Err(TcError::UnivParamMismatch {
              expected: c.lvls(),
              got: us.len(),
            });
          }
          for u in us {
            let univ_start = timing.as_ref().map(|_| Instant::now());
            self.validate_univ_params_seen(u, lvl_bound, &mut seen_univs)?;
            if let (Some(t), Some(start)) = (timing.as_deref_mut(), univ_start)
            {
              t.univ += start.elapsed();
            }
          }
        },
        ExprData::App(f, a, _) => {
          stack.push((f, depth));
          stack.push((a, depth));
        },
        ExprData::Lam(_, _, ty, body, _) | ExprData::All(_, _, ty, body, _) => {
          stack.push((ty, depth));
          let body_depth = depth.checked_add(1).ok_or_else(|| {
            TcError::Other("binder depth overflow during validation".into())
          })?;
          stack.push((body, body_depth));
        },
        ExprData::Let(_, ty, val, body, _, _) => {
          stack.push((ty, depth));
          stack.push((val, depth));
          let body_depth = depth.checked_add(1).ok_or_else(|| {
            TcError::Other("binder depth overflow during validation".into())
          })?;
          stack.push((body, body_depth));
        },
        ExprData::Prj(id, _, val, _) => {
          if !self.has_const(id)? {
            return Err(TcError::UnknownConst(id.addr.clone()));
          }
          stack.push((val, depth));
        },
        // FVars carry no de Bruijn index, so the depth check does not apply.
        // They are leaves with no further children to traverse.
        ExprData::FVar(..) | ExprData::Nat(..) | ExprData::Str(..) => {},
      }
    }
    Ok(())
  }

  fn validate_univ_params_seen(
    &self,
    root: &KUniv<M>,
    bound: usize,
    seen: &mut FxHashSet<Addr>,
  ) -> Result<(), TcError<M>> {
    let mut stack = vec![root];
    while let Some(u) = stack.pop() {
      if !seen.insert(*u.addr()) {
        continue;
      }
      match u.data() {
        UnivData::Zero(_) => {},
        UnivData::Succ(inner, _) => stack.push(inner),
        UnivData::Max(a, b, _) | UnivData::IMax(a, b, _) => {
          stack.push(a);
          stack.push(b);
        },
        UnivData::Param(idx, _, _) => {
          if u64_to_usize::<M>(*idx)? >= bound {
            return Err(TcError::UnivParamOutOfRange { idx: *idx, bound });
          }
        },
      }
    }
    Ok(())
  }

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
    let saved = self.lctx.len();
    let mut n = 0;
    let mut cur = ty.clone();
    loop {
      let w = self.whnf(&cur)?;
      match w.data() {
        ExprData::All(name, bi, dom, body, _) => {
          n += 1;
          let fv_id = self.fresh_fvar_id();
          let fv = self.intern(KExpr::fvar(fv_id, name.clone()));
          self.lctx.push(
            fv_id,
            LocalDecl::CDecl {
              name: name.clone(),
              bi: bi.clone(),
              ty: dom.clone(),
            },
          );
          cur = instantiate_rev(&mut self.env.intern, body, &[fv]);
        },
        _ => {
          self.lctx.truncate(saved);
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
    &mut self,
    e: &KExpr<M>,
    caller_safety: DefinitionSafety,
  ) -> Result<(), TcError<M>> {
    self.walk_for_unsafe(e, caller_safety)
  }

  /// Iterative (stack-based) walk — immune to stack overflow on deeply nested input.
  fn walk_for_unsafe(
    &mut self,
    root: &KExpr<M>,
    caller_safety: DefinitionSafety,
  ) -> Result<(), TcError<M>> {
    let mut stack: Vec<&KExpr<M>> = vec![root];
    let mut seen_exprs: FxHashSet<Addr> = FxHashSet::default();
    let mut seen_consts: FxHashSet<Address> = FxHashSet::default();
    while let Some(e) = stack.pop() {
      if !seen_exprs.insert(e.hash_key()) {
        continue;
      }
      match e.data() {
        ExprData::Var(..)
        | ExprData::FVar(..)
        | ExprData::Sort(..)
        | ExprData::Nat(..)
        | ExprData::Str(..) => {},
        ExprData::Const(id, _, _) => {
          if !seen_consts.insert(id.addr.clone()) {
            continue;
          }
          match self.try_get_const(id)? {
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
            Some(KConst::Defn {
              safety: DefinitionSafety::Partial, ..
            }) if caller_safety == DefinitionSafety::Safe => {
              return Err(TcError::Other(format!(
                "safe definition references partial definition {}",
                &id.addr.hex()[..8]
              )));
            },
            Some(KConst::Recr { is_unsafe: true, .. }) => {
              return Err(TcError::Other(format!(
                "safe definition references unsafe recursor {}",
                &id.addr.hex()[..8]
              )));
            },
            Some(KConst::Indc { is_unsafe: true, .. }) => {
              return Err(TcError::Other(format!(
                "safe definition references unsafe inductive {}",
                &id.addr.hex()[..8]
              )));
            },
            Some(KConst::Ctor { is_unsafe: true, .. }) => {
              return Err(TcError::Other(format!(
                "safe definition references unsafe constructor {}",
                &id.addr.hex()[..8]
              )));
            },
            _ => {},
          }
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
    let mut env = test_env();
    let mut tc = TypeChecker::new(&mut env);
    assert!(tc.check_const(&mk_id("Nat")).is_ok());
  }

  #[test]
  fn check_defn_ok() {
    let mut env = test_env();
    let mut tc = TypeChecker::new(&mut env);
    assert!(tc.check_const(&mk_id("id")).is_ok());
  }

  #[test]
  fn check_defn_mismatch() {
    let mut env = test_env();
    let mut tc = TypeChecker::new(&mut env);
    assert!(tc.check_const(&mk_id("wrong")).is_err());
  }

  #[test]
  fn check_unknown_const() {
    let mut env = test_env();
    let mut tc = TypeChecker::new(&mut env);
    assert!(tc.check_const(&mk_id("nonexistent")).is_err());
  }

  #[test]
  fn check_clears_caches() {
    let mut env = test_env();
    let mut tc = TypeChecker::new(&mut env);
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
    let mut env = KEnv::<Anon>::new();
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
    let mut tc = TypeChecker::new(&mut env);
    tc.check_const(&mk_id("thm")).unwrap();
  }

  #[test]
  fn check_theorem_with_non_prop_type_rejected() {
    let mut env = KEnv::<Anon>::new();
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
    let mut tc = TypeChecker::new(&mut env);
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
    let mut env = test_env();
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
    let mut tc = TypeChecker::new(&mut env);
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

    let mut env = KEnv::<Meta>::new();
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
    let mut tc = TypeChecker::new(&mut env);
    match tc.check_const(&id) {
      Err(TcError::Other(s)) => {
        assert!(s.contains("duplicate universe level parameter"));
      },
      other => panic!("expected duplicate-level-param error, got {other:?}"),
    }
  }

  #[test]
  fn check_loose_var_in_decl_rejected_before_infer() {
    let mut env = KEnv::<Anon>::new();
    env.insert(
      mk_id("bad_loose"),
      KConst::Axio {
        name: (),
        level_params: (),
        is_unsafe: false,
        lvls: 0,
        ty: AE::all((), (), sort0(), AE::var(1, ())),
      },
    );
    let mut tc = TypeChecker::new(&mut env);
    match tc.check_const(&mk_id("bad_loose")) {
      Err(TcError::VarOutOfRange { idx: 1, ctx_len: 1 }) => {},
      other => panic!("expected closure VarOutOfRange, got {other:?}"),
    }
  }

  #[test]
  fn check_out_of_range_universe_param_rejected() {
    let mut env = KEnv::<Anon>::new();
    env.insert(
      mk_id("bad_univ"),
      KConst::Axio {
        name: (),
        level_params: (),
        is_unsafe: false,
        lvls: 1,
        ty: AE::sort(AU::param(1, ())),
      },
    );
    let mut tc = TypeChecker::new(&mut env);
    match tc.check_const(&mk_id("bad_univ")) {
      Err(TcError::UnivParamOutOfRange { idx: 1, bound: 1 }) => {},
      other => panic!("expected universe-param range error, got {other:?}"),
    }
  }

  // =========================================================================
  // Caching: check_const is idempotent
  // =========================================================================

  #[test]
  fn check_const_idempotent() {
    let mut env = test_env();
    let mut tc = TypeChecker::new(&mut env);
    tc.check_const(&mk_id("id")).unwrap();
    tc.check_const(&mk_id("id")).unwrap();
    tc.check_const(&mk_id("id")).unwrap();
  }

  #[test]
  fn safe_definition_rejects_unsafe_inductive_ref() {
    let mut env = KEnv::<Anon>::new();
    let unsafe_ty = mk_id("UnsafeTy");
    env.insert(
      unsafe_ty.clone(),
      KConst::Indc {
        name: (),
        level_params: (),
        lvls: 0,
        params: 0,
        indices: 0,
        is_rec: false,
        is_refl: false,
        is_unsafe: true,
        nested: 0,
        block: unsafe_ty.clone(),
        member_idx: 0,
        ty: sort1(),
        ctors: vec![],
        lean_all: (),
      },
    );

    let unsafe_expr = AE::cnst(unsafe_ty, Box::new([]));
    env.insert(
      mk_id("useUnsafe"),
      KConst::Defn {
        name: (),
        level_params: (),
        kind: DefKind::Definition,
        safety: DefinitionSafety::Safe,
        hints: ReducibilityHints::Regular(0),
        lvls: 0,
        ty: AE::all((), (), unsafe_expr.clone(), unsafe_expr.clone()),
        val: AE::lam((), (), unsafe_expr, AE::var(0, ())),
        lean_all: (),
        block: mk_id("useUnsafe"),
      },
    );

    let mut tc = TypeChecker::new(&mut env);
    match tc.check_const(&mk_id("useUnsafe")) {
      Err(TcError::Other(s)) => assert!(s.contains("unsafe inductive")),
      other => {
        panic!("expected unsafe-inductive reference error, got {other:?}")
      },
    }
  }

  fn insert_id_def(env: &mut KEnv<Anon>, id: KId<Anon>, block: KId<Anon>) {
    env.insert(
      id,
      KConst::Defn {
        name: (),
        level_params: (),
        kind: DefKind::Definition,
        safety: DefinitionSafety::Safe,
        hints: ReducibilityHints::Abbrev,
        lvls: 0,
        ty: AE::all((), (), sort0(), sort0()),
        val: AE::lam((), (), sort0(), AE::var(0, ())),
        lean_all: (),
        block,
      },
    );
  }

  #[test]
  fn checking_one_definition_checks_sibling_block() {
    let mut env = KEnv::<Anon>::new();
    let block = mk_id("def_block");
    let good = mk_id("good");
    let bad = mk_id("bad");
    insert_id_def(&mut env, good.clone(), block.clone());
    env.insert(
      bad.clone(),
      KConst::Defn {
        name: (),
        level_params: (),
        kind: DefKind::Definition,
        safety: DefinitionSafety::Safe,
        hints: ReducibilityHints::Regular(0),
        lvls: 0,
        ty: AE::all((), (), sort0(), sort0()),
        val: sort1(),
        lean_all: (),
        block: block.clone(),
      },
    );
    env.insert_block(block.clone(), vec![good.clone(), bad.clone()]);

    let first = {
      let mut tc = TypeChecker::new(&mut env);
      tc.check_const(&good).unwrap_err()
    };
    let second = {
      let mut tc2 = TypeChecker::new(&mut env);
      tc2.check_const(&bad).unwrap_err()
    };

    assert_eq!(format!("{first}"), format!("{second}"));
    assert!(env.block_check_results.get(&block).is_some_and(|r| r.is_err()));
  }

  // Note: the previous `concurrent_definition_block_checks_share_result`
  // test exercised cross-thread block-check coordination via the old
  // `Arc<KEnv>` + `Mutex/Condvar` machinery. With the per-worker
  // single-threaded `KEnv` design, there is no shared block-check
  // coordination to test — each worker owns its env and the
  // `block_check_results` cache is purely a within-worker memo.

  // =========================================================================
  // Axiom with unknown referent in its type errors
  // =========================================================================

  #[test]
  fn check_axiom_referencing_unknown_const_errors() {
    let mut env = KEnv::<Anon>::new();
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
    let mut tc = TypeChecker::new(&mut env);
    match tc.check_const(&mk_id("x")) {
      Err(TcError::UnknownConst(_)) => {},
      other => panic!("expected UnknownConst, got {other:?}"),
    }
  }
}
