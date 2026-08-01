//! Constant checking dispatch.

use std::time::{Duration, Instant};

use rustc_hash::FxHashSet;

use ix_common::address::Address;
use ix_common::env::{BinderInfo, DefinitionSafety, Name, QuotKind};
use ixon::constant::DefKind;

use super::constant::KConst;
use super::env::Addr;
use super::error::{TcError, u64_to_usize};
use super::expr::{ExprData, KExpr};
use super::id::KId;
use super::level::{KUniv, UnivData, univ_eq};
use super::mode::{CheckDupLevelParams, KernelMode};
use super::primitive::Primitives;
use super::tc::TypeChecker;

/// Emit `[decl diff]` when a `Defn`'s value fails the `is_def_eq(val_ty,
/// ty)` check. The error itself (`DeclTypeMismatch`) carries no payload,
/// so without this gate the only signal is the constant's name. Under
/// `IX_DECL_DIFF=1` we dump `val_ty` / `ty` and their whnf forms to
/// pinpoint which sub-expression is stuck \u2014 sister tool to
/// `IX_APP_DIFF` in `infer.rs`.
#[cfg(not(target_arch = "riscv64"))]
static IX_DECL_DIFF: crate::EnvFlag =
  crate::EnvFlag::new(|| crate::env_var("IX_DECL_DIFF").is_ok());
#[cfg(target_arch = "riscv64")]
static IX_DECL_DIFF: crate::EnvFlag = crate::EnvFlag::new(|| false);

/// Per-phase timing for `Defn` checks. Set `IX_PHASE_TIMING=1` to see where a
/// slow constant spends its time. Noisy — gate on a single constant via focus
/// mode so only one line is printed.
#[cfg(not(target_arch = "riscv64"))]
static IX_PHASE_TIMING: crate::EnvFlag =
  crate::EnvFlag::new(|| crate::env_var("IX_PHASE_TIMING").is_ok());
#[cfg(target_arch = "riscv64")]
static IX_PHASE_TIMING: crate::EnvFlag = crate::EnvFlag::new(|| false);

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

fn canonical_var<M: KernelMode>(idx: u64) -> KExpr<M> {
  KExpr::var(idx, M::meta_field(Name::anon()))
}

fn canonical_all<M: KernelMode>(
  bi: BinderInfo,
  dom: KExpr<M>,
  body: KExpr<M>,
) -> KExpr<M> {
  KExpr::all(M::meta_field(Name::anon()), M::meta_field(bi), dom, body)
}

fn canonical_arrow<M: KernelMode>(dom: KExpr<M>, body: KExpr<M>) -> KExpr<M> {
  canonical_all(BinderInfo::Default, dom, body)
}

fn canonical_apps<M: KernelMode>(
  mut head: KExpr<M>,
  args: &[KExpr<M>],
) -> KExpr<M> {
  for arg in args {
    head = KExpr::app(head, arg.clone());
  }
  head
}

fn canonical_const<M: KernelMode>(id: &KId<M>, us: &[KUniv<M>]) -> KExpr<M> {
  KExpr::cnst(id.clone(), us.iter().cloned().collect())
}

/// `α → α → Prop` at a point where `α` is `Var(0)`.
fn canonical_quot_relation<M: KernelMode>() -> KExpr<M> {
  canonical_arrow(
    canonical_var(0),
    canonical_arrow(canonical_var(1), KExpr::sort(KUniv::zero())),
  )
}

/// Exact semantic type required of the `Eq` prerequisite used by
/// `Environment.addQuot`.
fn canonical_eq_type<M: KernelMode>() -> KExpr<M> {
  let u = KUniv::param(0, M::meta_field(Name::anon()));
  canonical_all(
    BinderInfo::Implicit,
    KExpr::sort(u),
    canonical_all(
      BinderInfo::Default,
      canonical_var(0),
      canonical_all(
        BinderInfo::Default,
        canonical_var(1),
        KExpr::sort(KUniv::zero()),
      ),
    ),
  )
}

/// Exact semantic type required of the `Eq.refl` prerequisite used by
/// `Environment.addQuot`.
fn canonical_eq_refl_type<M: KernelMode>(prims: &Primitives<M>) -> KExpr<M> {
  let u = KUniv::param(0, M::meta_field(Name::anon()));
  let result = canonical_apps(
    canonical_const(&prims.eq, std::slice::from_ref(&u)),
    &[canonical_var(1), canonical_var(0), canonical_var(0)],
  );
  canonical_all(
    BinderInfo::Implicit,
    KExpr::sort(u),
    canonical_all(BinderInfo::Default, canonical_var(0), result),
  )
}

/// Canonical type installed by Lean's `Environment.addQuot` for each
/// reserved quotient primitive. Binder names/info are metadata in `KExpr`;
/// the returned de Bruijn structure, universes, primitive heads, and domains
/// are the semantic contract.
fn canonical_quot_type<M: KernelMode>(
  prims: &Primitives<M>,
  kind: QuotKind,
) -> KExpr<M> {
  let u = KUniv::param(0, M::meta_field(Name::anon()));
  let v = KUniv::param(1, M::meta_field(Name::anon()));
  let sort_u = KExpr::sort(u.clone());
  let prop = KExpr::sort(KUniv::zero());

  match kind {
    // Quot.{u} {α : Sort u} (r : α → α → Prop) : Sort u
    QuotKind::Type => canonical_all(
      BinderInfo::Implicit,
      sort_u.clone(),
      canonical_all(BinderInfo::Default, canonical_quot_relation(), sort_u),
    ),

    // Quot.mk.{u} {α : Sort u} (r : α → α → Prop) (a : α) : Quot α r
    QuotKind::Ctor => {
      let result = canonical_apps(
        canonical_const(&prims.quot_type, std::slice::from_ref(&u)),
        &[canonical_var(2), canonical_var(1)],
      );
      canonical_all(
        BinderInfo::Implicit,
        sort_u,
        canonical_all(
          BinderInfo::Default,
          canonical_quot_relation(),
          canonical_all(BinderInfo::Default, canonical_var(1), result),
        ),
      )
    },

    // Quot.lift.{u,v} {α} {r} {β} (f) (h) (q) : β
    QuotKind::Lift => {
      let f_ty = canonical_arrow(canonical_var(2), canonical_var(1));
      let rab =
        canonical_apps(canonical_var(4), &[canonical_var(1), canonical_var(0)]);
      let fa = KExpr::app(canonical_var(3), canonical_var(2));
      let fb = KExpr::app(canonical_var(3), canonical_var(1));
      let fa_eq_fb = canonical_apps(
        canonical_const(&prims.eq, std::slice::from_ref(&v)),
        &[canonical_var(4), fa, fb],
      );
      let h_ty = canonical_all(
        BinderInfo::Default,
        canonical_var(3),
        canonical_all(
          BinderInfo::Default,
          canonical_var(4),
          canonical_arrow(rab, fa_eq_fb),
        ),
      );
      let quot_r = canonical_apps(
        canonical_const(&prims.quot_type, std::slice::from_ref(&u)),
        &[canonical_var(4), canonical_var(3)],
      );
      canonical_all(
        BinderInfo::Implicit,
        sort_u,
        canonical_all(
          BinderInfo::Implicit,
          canonical_quot_relation(),
          canonical_all(
            BinderInfo::Implicit,
            KExpr::sort(v),
            canonical_all(
              BinderInfo::Default,
              f_ty,
              canonical_all(
                BinderInfo::Default,
                h_ty,
                canonical_arrow(quot_r, canonical_var(3)),
              ),
            ),
          ),
        ),
      )
    },

    // Quot.ind.{u} {α} {r} {β : Quot α r → Prop} (mk) {q} : β q
    QuotKind::Ind => {
      let quot_r_d2 = canonical_apps(
        canonical_const(&prims.quot_type, std::slice::from_ref(&u)),
        &[canonical_var(1), canonical_var(0)],
      );
      let beta_ty = canonical_arrow(quot_r_d2, prop);
      let quot_mk_a = canonical_apps(
        canonical_const(&prims.quot_ctor, std::slice::from_ref(&u)),
        &[canonical_var(3), canonical_var(2), canonical_var(0)],
      );
      let mk_minor = canonical_all(
        BinderInfo::Default,
        canonical_var(2),
        KExpr::app(canonical_var(1), quot_mk_a),
      );
      let quot_r_d4 = canonical_apps(
        canonical_const(&prims.quot_type, std::slice::from_ref(&u)),
        &[canonical_var(3), canonical_var(2)],
      );
      let result = KExpr::app(canonical_var(2), canonical_var(0));
      canonical_all(
        BinderInfo::Implicit,
        sort_u,
        canonical_all(
          BinderInfo::Implicit,
          canonical_quot_relation(),
          canonical_all(
            BinderInfo::Implicit,
            beta_ty,
            canonical_all(
              BinderInfo::Default,
              mk_minor,
              canonical_all(BinderInfo::Implicit, quot_r_d4, result),
            ),
          ),
        ),
      )
    },
  }
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
    M::MField<Vec<Name>>: CheckDupLevelParams,
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
    M::MField<Vec<Name>>: CheckDupLevelParams,
  {
    self.reset();
    self.begin_const(id);

    let c = self.get_const(id)?;
    self.check_const_member(id, &c)
  }

  fn check_const_member(
    &mut self,
    id: &KId<M>,
    c: &KConst<M>,
  ) -> Result<(), TcError<M>>
  where
    M::MField<Vec<Name>>: CheckDupLevelParams,
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
            log::info!("[decl diff] DeclTypeMismatch");
            log::info!("  val_ty:      {val_ty}");
            log::info!("  ty:          {ty}");
            match &val_ty_whnf {
              Ok(w) => log::info!("  val_ty whnf: {w}"),
              Err(e) => log::info!("  val_ty whnf: ERR {e}"),
            }
            match &ty_whnf {
              Ok(w) => log::info!("  ty     whnf: {w}"),
              Err(e) => log::info!("  ty     whnf: ERR {e}"),
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
          log::info!(
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
        // Reject a forged reserved primitive before invoking inference or
        // reduction on attacker-controlled syntax.
        self.check_quot(id, *kind, *lvls, ty)?;
        let t = self.infer(ty)?;
        self.ensure_sort(&t)?;
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
    M::MField<Vec<Name>>: CheckDupLevelParams,
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
      log::info!(
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
    match crate::env_var("IX_KERNEL_DEBUG_CONST") {
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
  /// - The complete type is the canonical type installed by `addQuot`
  /// - Eq and Eq.refl have exact canonical metadata/types for Quot.lift
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

    let expected_ty = canonical_quot_type(&self.prims, kind);
    if ty != &expected_ty {
      return Err(TcError::Other(format!(
        "check_quot: {:?} type is not canonical",
        kind
      )));
    }

    // For Quot.lift (the main eliminator), verify Eq is properly formed.
    // This is a prerequisite for the quot reduction rule to be sound.
    if kind == QuotKind::Lift {
      self.check_eq_type()?;
    }

    Ok(())
  }

  /// Verify the exact Eq/Eq.refl prerequisite checked by Lean before it
  /// installs the quotient primitives.
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
      KConst::Indc { lvls, params, indices, is_unsafe, ty, ctors, .. } => {
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
        if *indices != 1 {
          return Err(TcError::Other(format!(
            "check_eq_type: Eq expects 1 index, got {}",
            indices
          )));
        }
        if *is_unsafe {
          return Err(TcError::Other("check_eq_type: Eq must be safe".into()));
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
        if ty != &canonical_eq_type() {
          return Err(TcError::Other(
            "check_eq_type: Eq type is not canonical".into(),
          ));
        }
      },
      _ => {
        return Err(TcError::Other(
          "check_eq_type: Eq not found or not inductive".into(),
        ));
      },
    }

    let refl_c = self
      .env
      .iter()
      .find(|(id, _)| id.addr == self.prims.eq_refl.addr)
      .map(|(_, c)| c.clone())
      .ok_or_else(|| {
        TcError::Other("check_eq_type: Eq.refl not found".into())
      })?;
    match refl_c {
      KConst::Ctor {
        is_unsafe,
        lvls,
        induct,
        cidx,
        params,
        fields,
        ty,
        ..
      } => {
        if is_unsafe
          || lvls != 1
          || induct.addr != self.prims.eq.addr
          || cidx != 0
          || params != 2
          || fields != 0
        {
          return Err(TcError::Other(
            "check_eq_type: Eq.refl metadata is not canonical".into(),
          ));
        }
        if ty != canonical_eq_refl_type(&self.prims) {
          return Err(TcError::Other(
            "check_eq_type: Eq.refl type is not canonical".into(),
          ));
        }
      },
      _ => {
        return Err(TcError::Other(
          "check_eq_type: Eq.refl not found or not a constructor".into(),
        ));
      },
    }
    Ok(())
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
  use super::super::primitive::Primitives;
  use super::super::tc::TypeChecker;
  use ix_common::address::Address;
  use ix_common::env::{DefinitionSafety, QuotKind, ReducibilityHints};
  use ixon::constant::DefKind;

  #[test]
  fn profile_sink_records_delta_edge_and_fuel() {
    use crate::mode::Meta;
    use crate::profile::ProfileSink;
    use crate::testing as t;

    // g : Sort 2 := Sort 1 — a Definition, delta-reducible to Sort 1.
    let (g_id, g) = t::mk_defn(
      "g",
      0,
      vec![],
      t::sort(t::usucc(t::usucc(t::uzero()))),
      t::sort1(),
      ReducibilityHints::Regular(5),
    );
    // f : g := Sort 0 — checking f must whnf (delta-unfold) g → Sort 1 to match
    // infer(Sort 0) = Sort 1, so the recorder must capture the edge f→g.
    let (f_id, f) = t::mk_defn(
      "f",
      0,
      vec![],
      t::cnst("g", &[]),
      t::sort0(),
      ReducibilityHints::Regular(5),
    );

    let mut env = KEnv::<Meta>::new();
    env.insert(g_id.clone(), g);
    env.insert(f_id.clone(), f);
    env.profile_sink = Some(ProfileSink::new(true));

    {
      let mut tc = TypeChecker::new(&mut env);
      tc.check_const(&g_id).unwrap();
      tc.check_const(&f_id).unwrap();
      tc.finish_constant_accounting(); // flush the last constant's record
    }

    let sink = env.profile_sink.as_ref().unwrap();
    let f_rec = sink.records.get(&f_id.addr).expect("f should be recorded");
    assert!(
      f_rec.producers.contains(&g_id.addr),
      "checking f must record a delta-unfold of g"
    );
    assert!(f_rec.fuel > 0, "checking f consumes heartbeats");
    // g unfolds nothing of its own.
    if let Some(g_rec) = sink.records.get(&g_id.addr) {
      assert!(!g_rec.producers.contains(&g_id.addr));
    }
  }

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

  fn canonical_quot_env() -> (KEnv<Anon>, Primitives<Anon>) {
    let mut env = KEnv::<Anon>::new();
    let prims = Primitives::from_env(&env);

    env.insert(
      prims.eq.clone(),
      KConst::Indc {
        name: (),
        level_params: (),
        lvls: 1,
        params: 2,
        indices: 1,
        is_unsafe: false,
        block: prims.eq.clone(),
        member_idx: 0,
        ty: super::canonical_eq_type(),
        ctors: vec![prims.eq_refl.clone()],
        lean_all: (),
      },
    );
    env.insert(
      prims.eq_refl.clone(),
      KConst::Ctor {
        name: (),
        level_params: (),
        is_unsafe: false,
        lvls: 1,
        induct: prims.eq.clone(),
        cidx: 0,
        params: 2,
        fields: 0,
        ty: super::canonical_eq_refl_type(&prims),
      },
    );

    for (id, kind, lvls) in [
      (prims.quot_type.clone(), QuotKind::Type, 1),
      (prims.quot_ctor.clone(), QuotKind::Ctor, 1),
      (prims.quot_lift.clone(), QuotKind::Lift, 2),
      (prims.quot_ind.clone(), QuotKind::Ind, 1),
    ] {
      env.insert(
        id,
        KConst::Quot {
          name: (),
          level_params: (),
          kind,
          lvls,
          ty: super::canonical_quot_type(&prims, kind),
        },
      );
    }
    (env, prims)
  }

  fn replace_quot_type(env: &mut KEnv<Anon>, id: &KId<Anon>, ty: AE) {
    let KConst::Quot { kind, lvls, .. } = env.get(id).expect("quot fixture")
    else {
      panic!("expected quotient fixture")
    };
    env.insert(
      id.clone(),
      KConst::Quot { name: (), level_params: (), kind, lvls, ty },
    );
  }

  fn replace_quot_metadata(
    env: &mut KEnv<Anon>,
    id: &KId<Anon>,
    kind: QuotKind,
    lvls: u64,
  ) {
    let KConst::Quot { ty, .. } = env.get(id).expect("quot fixture") else {
      panic!("expected quotient fixture")
    };
    env.insert(
      id.clone(),
      KConst::Quot { name: (), level_params: (), kind, lvls, ty },
    );
  }

  fn replace_eq_type(env: &mut KEnv<Anon>, prims: &Primitives<Anon>, ty: AE) {
    env.insert(
      prims.eq.clone(),
      KConst::Indc {
        name: (),
        level_params: (),
        lvls: 1,
        params: 2,
        indices: 1,
        is_unsafe: false,
        block: prims.eq.clone(),
        member_idx: 0,
        ty,
        ctors: vec![prims.eq_refl.clone()],
        lean_all: (),
      },
    );
  }

  fn replace_eq_refl_type(
    env: &mut KEnv<Anon>,
    prims: &Primitives<Anon>,
    ty: AE,
  ) {
    env.insert(
      prims.eq_refl.clone(),
      KConst::Ctor {
        name: (),
        level_params: (),
        is_unsafe: false,
        lvls: 1,
        induct: prims.eq.clone(),
        cidx: 0,
        params: 2,
        fields: 0,
        ty,
      },
    );
  }

  /// A well-typed type with the old minimum number of leading foralls but no
  /// quotient semantics. Every variant below was accepted by the former
  /// arity-only gate when installed directly at a reserved primitive KId.
  fn forged_forall_type(n: usize) -> AE {
    (0..n).fold(sort0(), |body, _| AE::all((), (), sort0(), body))
  }

  fn forged_eq_type() -> AE {
    let u = AU::param(0, ());
    AE::all(
      (),
      (),
      AE::sort(u),
      AE::all((), (), AE::var(0, ()), AE::all((), (), AE::var(1, ()), sort1())),
    )
  }

  fn assert_not_canonical(err: TcError<Anon>, label: &str) {
    match err {
      TcError::Other(s) => assert!(
        s.contains("not canonical"),
        "expected canonicality error for {label}, got {s}"
      ),
      other => panic!("expected canonicality error for {label}, got {other:?}"),
    }
  }

  #[test]
  fn canonical_quotient_bundle_is_accepted() {
    let (mut env, prims) = canonical_quot_env();
    for id in
      [prims.quot_type, prims.quot_ctor, prims.quot_lift, prims.quot_ind]
    {
      TypeChecker::new(&mut env).check_const(&id).unwrap();
    }
  }

  #[test]
  fn reject_quot_kind_address_mismatch() {
    let (mut env, prims) = canonical_quot_env();
    replace_quot_metadata(&mut env, &prims.quot_type, QuotKind::Ctor, 1);
    let err =
      TypeChecker::new(&mut env).check_const(&prims.quot_type).unwrap_err();
    match err {
      TcError::Other(s) => assert!(s.contains("kind mismatch"), "got {s}"),
      other => panic!("expected kind mismatch, got {other:?}"),
    }
  }

  #[test]
  fn reject_quot_universe_count_mismatch() {
    let (mut env, prims) = canonical_quot_env();
    replace_quot_metadata(&mut env, &prims.quot_lift, QuotKind::Lift, 3);
    let err =
      TypeChecker::new(&mut env).check_const(&prims.quot_lift).unwrap_err();
    match err {
      TcError::Other(s) => {
        assert!(s.contains("expects 2 universe params"), "got {s}")
      },
      other => panic!("expected universe-count mismatch, got {other:?}"),
    }
  }

  #[test]
  fn reject_forged_quot_type_with_two_foralls() {
    let (mut env, prims) = canonical_quot_env();
    replace_quot_type(&mut env, &prims.quot_type, forged_forall_type(2));
    let err =
      TypeChecker::new(&mut env).check_const(&prims.quot_type).unwrap_err();
    assert_not_canonical(err, "Quot");
  }

  #[test]
  fn reject_forged_quot_mk_type_with_three_foralls() {
    let (mut env, prims) = canonical_quot_env();
    replace_quot_type(&mut env, &prims.quot_ctor, forged_forall_type(3));
    let err =
      TypeChecker::new(&mut env).check_const(&prims.quot_ctor).unwrap_err();
    assert_not_canonical(err, "Quot.mk");
  }

  #[test]
  fn reject_forged_quot_lift_type_with_six_foralls() {
    let (mut env, prims) = canonical_quot_env();
    replace_quot_type(&mut env, &prims.quot_lift, forged_forall_type(6));
    let err =
      TypeChecker::new(&mut env).check_const(&prims.quot_lift).unwrap_err();
    assert_not_canonical(err, "Quot.lift");
  }

  #[test]
  fn reject_forged_quot_ind_type_with_five_foralls() {
    let (mut env, prims) = canonical_quot_env();
    replace_quot_type(&mut env, &prims.quot_ind, forged_forall_type(5));
    let err =
      TypeChecker::new(&mut env).check_const(&prims.quot_ind).unwrap_err();
    assert_not_canonical(err, "Quot.ind");
  }

  #[test]
  fn reject_quot_lift_when_eq_type_is_not_canonical() {
    let (mut env, prims) = canonical_quot_env();
    replace_eq_type(&mut env, &prims, forged_eq_type());
    let err =
      TypeChecker::new(&mut env).check_const(&prims.quot_lift).unwrap_err();
    assert_not_canonical(err, "Eq");
  }

  #[test]
  fn reject_quot_lift_when_eq_refl_type_is_not_canonical() {
    let (mut env, prims) = canonical_quot_env();
    replace_eq_refl_type(&mut env, &prims, forged_forall_type(2));
    let err =
      TypeChecker::new(&mut env).check_const(&prims.quot_lift).unwrap_err();
    assert_not_canonical(err, "Eq.refl");
  }

  #[test]
  fn reject_quot_lift_when_eq_refl_metadata_is_not_canonical() {
    let (mut env, prims) = canonical_quot_env();
    env.insert(
      prims.eq_refl.clone(),
      KConst::Ctor {
        name: (),
        level_params: (),
        is_unsafe: false,
        lvls: 1,
        induct: prims.eq.clone(),
        cidx: 0,
        params: 2,
        fields: 1,
        ty: super::canonical_eq_refl_type(&prims),
      },
    );
    let err =
      TypeChecker::new(&mut env).check_const(&prims.quot_lift).unwrap_err();
    match err {
      TcError::Other(s) => {
        assert!(s.contains("Eq.refl metadata is not canonical"), "got {s}")
      },
      other => panic!("expected Eq.refl metadata mismatch, got {other:?}"),
    }
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
    use crate::mode::Meta;
    type ME = KExpr<Meta>;
    type MU = KUniv<Meta>;

    let mut env = KEnv::<Meta>::new();
    let dup_name =
      ix_common::env::Name::str(ix_common::env::Name::anon(), "u".into());
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
        is_unsafe: true,
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
