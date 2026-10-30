//! Lean's block-wide inductive flags (`isRec`, `isReflexive`, `numNested`),
//! recomputed from the constructors.
//!
//! Ixon does not store these flags, so kernel egress and decompilation
//! reconstruct them, and compilation rejects an environment whose stored
//! flags differ from the recomputed ones (a domain restriction).
//!
//! `numNested` counts the auxiliary members of the block's nested expansion:
//! every nested occurrence in constructor syntax (e.g. the `List Tree` inside
//! `Id (List Tree)`) is replaced by an auxiliary member sharing the block's
//! parameters and levels, as the C++ kernel's `elim_nested_inductive` does.
//! The traversal walks syntax without delta-reducing definition heads.
//! Block parameters are opened as FVars; later binders retain BVars. Free
//! BVars and non-parameter FVars cannot enter a specialization.

use bignat::Nat;
use rustc_hash::{FxHashMap, FxHashSet};
use std::sync::LazyLock;
use std::time::Instant;

use crate::compile::ExprKey;
use crate::compile::nat_conv::{nat_to_u64, nat_to_usize};
use crate::compile::validation::{self, AttemptError, Cancelled, Checkpoint};
use ix_common::env::{
  BinderInfo, ConstantInfo, Env as LeanEnv, Expr as LeanExpr, ExprData, Level,
  Name,
};
use ixon::CompileError;

mod checked_expr;
#[cfg(test)]
mod expr_reference;

// =========================================================================
// FVar infrastructure
// =========================================================================

/// A local declaration: FVar name, binder metadata, and domain type.
///
/// Accumulates binder information while building expressions in FVar space.
/// The `fvar_name` is a unique identifier; `binder_name` is the cosmetic name
/// that appears in the final forall chain.
#[derive(Clone)]
struct LocalDecl {
  fvar_name: Name,
  binder_name: Name,
  domain: LeanExpr,
  info: BinderInfo,
}

/// Create a fresh FVar with a unique name derived from `prefix` and `idx`.
fn fresh_fvar(prefix: &str, idx: usize) -> (Name, LeanExpr) {
  let name = Name::str(Name::anon(), format!("_{}_{}", prefix, idx));
  let fvar = LeanExpr::fvar(name.clone());
  (name, fvar)
}

/// Decompose an application spine: `f a1 a2 ... an` -> `(f, [a1, ..., an])`.
fn decompose_apps(expr: &LeanExpr) -> (LeanExpr, Vec<LeanExpr>) {
  let mut args = Vec::new();
  let mut cur = expr.clone();
  while let ExprData::App(f, a, _) = cur.as_data() {
    args.push(a.clone());
    cur = f.clone();
  }
  args.reverse();
  (cur, args)
}

// =========================================================================
// Nested expansion
// =========================================================================

/// A mutual block whose nested inductive occurrences have been replaced with
/// auxiliary members sharing the block's parameters and levels.
struct ExpandedBlock {
  /// All members of the expanded block: originals first, then auxiliaries.
  types: Vec<ExpandedMember>,
  /// Number of original (non-auxiliary) members.
  n_originals: usize,
}

/// A member of the expanded block (original or auxiliary).
struct ExpandedMember {
  /// Inductive name: the original name for originals, `_nested.ExtInd_N`
  /// (scoped under `all[0]`) for auxiliaries.
  name: Name,
  /// Constructor types with nested occurrences replaced by applications of
  /// auxiliary members: `∀ (block_params...) (fields...) → Member ...`.
  ctors: Vec<LeanExpr>,
}

/// Mutable state for the nested expansion.
struct ExpandCtx<'a> {
  types: Vec<ExpandedMember>,
  /// Mirror of `types.iter().map(|m| m.name)` maintained incrementally, for
  /// O(1) "is this name in the block?" checks in the hot `replace_if_nested`
  /// path. Every member is pushed through `push_type`, which keeps both in
  /// sync.
  type_name_set: FxHashSet<Name>,
  /// Dedup: each detected occurrence, compared exactly, to its auxiliary.
  aux_seen: FxHashMap<ExprKey, Name>,
  next_aux_idx: usize,
  all0: Name,
  block_levels: Vec<Level>,
  block_param_fvars: Vec<LeanExpr>,
  block_param_decls: Vec<LocalDecl>,
  block_param_fvar_names: Vec<Name>,
  lean_env: &'a LeanEnv,
  control: &'a Checkpoint,
}

impl ExpandCtx<'_> {
  /// Push a new member and keep `type_name_set` in sync.
  fn push_type(&mut self, member: ExpandedMember) {
    self.type_name_set.insert(member.name.clone());
    self.types.push(member);
  }

  /// Recursively replace all nested inductive occurrences in an expression.
  ///
  /// Matches C++ `replace_all_nested` (`inductive.cpp:1031`): walks the
  /// expression top-down, calling `replace_if_nested` at each sub-expression.
  ///
  /// `cache` memoizes input-expression hashes to output rewrites for the
  /// current constructor walk only: the result depends on `as_fvars`, so the
  /// caller provides a fresh cache per constructor. Within a single
  /// constructor walk the function is deterministic (auxiliaries created
  /// while processing one subterm cannot change the rewrite of an
  /// already-processed one), so memoization is safe even though `self`
  /// mutates during the walk.
  fn replace_all_nested(
    &mut self,
    e: &LeanExpr,
    as_fvars: &[LeanExpr],
    cache: &mut FxHashMap<ExprKey, LeanExpr>,
  ) -> Result<LeanExpr, Cancelled> {
    self.control.visit()?;
    let key = ExprKey(e.clone());
    if let Some(cached) = cache.get(&key) {
      return Ok(cached.clone());
    }

    // Try top-level replacement first.
    if let Some(replaced) = self.replace_if_nested(e, as_fvars)? {
      cache.insert(key, replaced.clone());
      return Ok(replaced);
    }
    // No match — recurse into sub-expressions.
    let result = match e.as_data() {
      ExprData::App(f, a, _) => LeanExpr::app(
        self.replace_all_nested(f, as_fvars, cache)?,
        self.replace_all_nested(a, as_fvars, cache)?,
      ),
      ExprData::Lam(n, t, b, bi, _) => LeanExpr::lam(
        n.clone(),
        self.replace_all_nested(t, as_fvars, cache)?,
        self.replace_all_nested(b, as_fvars, cache)?,
        bi.clone(),
      ),
      ExprData::ForallE(n, t, b, bi, _) => LeanExpr::all(
        n.clone(),
        self.replace_all_nested(t, as_fvars, cache)?,
        self.replace_all_nested(b, as_fvars, cache)?,
        bi.clone(),
      ),
      ExprData::LetE(n, t, v, b, nd, _) => LeanExpr::letE(
        n.clone(),
        self.replace_all_nested(t, as_fvars, cache)?,
        self.replace_all_nested(v, as_fvars, cache)?,
        self.replace_all_nested(b, as_fvars, cache)?,
        *nd,
      ),
      ExprData::Proj(n, i, val, _) => LeanExpr::proj(
        n.clone(),
        i.clone(),
        self.replace_all_nested(val, as_fvars, cache)?,
      ),
      ExprData::Mdata(md, inner, _) => LeanExpr::mdata(
        md.clone(),
        self.replace_all_nested(inner, as_fvars, cache)?,
      ),
      _ => e.clone(),
    };
    let result = if result.same_raw(e) { e.clone() } else { result };
    cache.insert(key, result.clone());
    self.control.scratch(
      cache.capacity()
        * (size_of::<(ExprKey, LeanExpr)>() + size_of::<ExprData>()),
    );
    Ok(result)
  }

  /// Check if `e` is a nested inductive application and, if so, create
  /// auxiliary members and return the replacement expression.
  ///
  /// Matches C++ `replace_if_nested` (`inductive.cpp:963-1027`).
  fn replace_if_nested(
    &mut self,
    e: &LeanExpr,
    as_fvars: &[LeanExpr],
  ) -> Result<Option<LeanExpr>, Cancelled> {
    self.control.visit()?;
    let (head, args) = decompose_apps(e);
    let (head_name, head_levels) = match head.as_data() {
      ExprData::Const(name, levels, _) => (name.clone(), levels.clone()),
      _ => return Ok(None),
    };

    // Skip if head is in the block (direct recursive, not nested).
    if self.type_name_set.contains(&head_name) {
      return Ok(None);
    }

    // Verify head is an external inductive.
    let ext_ind_ref = self.lean_env.get(&head_name);
    let ext_ind = match ext_ind_ref.as_deref() {
      Some(ConstantInfo::InductInfo(v)) => v,
      _ => return Ok(None),
    };
    let ext_n_params = nat_to_usize(&ext_ind.num_params);

    if args.len() < ext_n_params {
      return Ok(None);
    }

    // Check if any parameter arg mentions a block member.
    let mut mentions = false;
    for arg in args.iter().take(ext_n_params) {
      if checked_expr::any(arg, self.control, |e, _| match e.as_data() {
        ExprData::Const(n, _, _) | ExprData::Proj(n, _, _, _) => {
          self.type_name_set.contains(n)
        },
        _ => false,
      })? {
        mentions = true;
        break;
      }
    }
    if !mentions {
      return Ok(None);
    }

    // Extract spec_params, normalizing constructor-local parameter FVars to
    // the block parameter FVars before validation. Parameterized nested
    // occurrences such as `List (Rose α)` are seen while scanning a
    // constructor telescope, so their raw spec params mention `as_fvars`; the
    // auxiliary identity must be expressed in the shared block-param space.
    let spec_params: Vec<LeanExpr> = args[..ext_n_params]
      .iter()
      .map(|sp| {
        checked_expr::replace_params(
          sp,
          as_fvars,
          &self.block_param_fvars,
          self.control,
        )
      })
      .collect::<Result<_, _>>()?;
    for sp in &spec_params {
      if checked_expr::any(sp, self.control, |e, depth| match e.as_data() {
        ExprData::Bvar(i, _) => nat_to_u64(i) >= depth,
        ExprData::Fvar(n, _) => !self.block_param_fvar_names.contains(n),
        _ => false,
      })? {
        return Ok(None);
      }
    }

    // `I.{I_lvls} spec_params`, normalized to block param FVars.
    let apply_spec = |name: &Name| {
      let mut app = LeanExpr::cnst(name.clone(), head_levels.clone());
      for sp in &spec_params {
        app = LeanExpr::app(app, sp.clone());
      }
      app
    };

    // Dedup: check if we've already created an auxiliary for this occurrence.
    if let Some(aux_name) = self.aux_seen.get(&ExprKey(apply_spec(&head_name)))
    {
      let mut result =
        LeanExpr::cnst(aux_name.clone(), self.block_levels.clone());
      for af in as_fvars {
        result = LeanExpr::app(result, af.clone());
      }
      for idx_arg in args.iter().skip(ext_n_params) {
        result = LeanExpr::app(result, idx_arg.clone());
      }
      return Ok(Some(result));
    }

    // New nested occurrence — create an auxiliary member for every member of
    // the external inductive's mutual group (Lean's `I.all`).
    let group: Vec<Name> = ext_ind.all.clone();
    let mut result: Option<LeanExpr> = None;

    for j_name in &group {
      self.control.visit()?;
      let j_info_ref = self.lean_env.get(j_name);
      let j_info = match j_info_ref.as_deref() {
        Some(ConstantInfo::InductInfo(v)) => v,
        _ => continue,
      };

      // Auxiliary name: _nested.ExtInd_N (scoped under all[0]).
      let aux_name = Name::str(
        Name::str(self.all0.clone(), "_nested".to_string()),
        format!("{}_{}", j_name.pretty().replace('.', "_"), self.next_aux_idx),
      );
      self.next_aux_idx += 1;

      // Every member `J As` of the group registers under its own occurrence
      // (Lean's `elim_nested_inductive_fn`): a later occurrence of a sibling,
      // e.g. `Forest T` inside the `Tree T` auxiliary's constructors, dedups
      // to that sibling's auxiliary instead of opening a second copy of the
      // group.
      self
        .aux_seen
        .entry(ExprKey(apply_spec(j_name)))
        .or_insert_with(|| aux_name.clone());

      // Build the auxiliary constructors.
      let mut aux_ctors: Vec<LeanExpr> = Vec::new();
      for j_ctor_name in &j_info.ctors {
        self.control.visit()?;
        let j_ctor_ref = self.lean_env.get(j_ctor_name);
        let j_ctor = match j_ctor_ref.as_deref() {
          Some(ConstantInfo::CtorInfo(c)) => c,
          _ => continue,
        };
        let ctor_type_inst = checked_expr::subst_levels(
          &j_ctor.cnst.typ,
          &j_info.cnst.level_params,
          &head_levels,
          self.control,
        )?;
        let ctor_type_peeled = checked_expr::instantiate_pi_params(
          &ctor_type_inst,
          ext_n_params,
          &spec_params,
          self.control,
        )?;
        let ctor_type_block = checked_expr::replace_params(
          &ctor_type_peeled,
          as_fvars,
          &self.block_param_fvars,
          self.control,
        )?;
        let ctor_type_block = replace_ctor_result_head_with_aux(
          &ctor_type_block,
          j_name,
          &aux_name,
          ext_n_params,
          &self.block_levels,
          &self.block_param_fvars,
          self.control,
        )?;
        aux_ctors.push(checked_expr::mk_forall(
          ctor_type_block,
          &self.block_param_decls,
          self.control,
        )?);
      }

      // If this is the head inductive, build the replacement expression.
      if *j_name == head_name {
        let mut r = LeanExpr::cnst(aux_name.clone(), self.block_levels.clone());
        for af in as_fvars {
          r = LeanExpr::app(r, af.clone());
        }
        for idx_arg in args.iter().skip(ext_n_params) {
          r = LeanExpr::app(r, idx_arg.clone());
        }
        result = Some(r);
      }

      self.push_type(ExpandedMember { name: aux_name, ctors: aux_ctors });
    }

    Ok(result)
  }
}

/// Expand the block `originals` (Lean's `all`, in source order): replace
/// nested inductive occurrences with auxiliary members that share the
/// block's parameters and universe levels.
///
/// Matches the C++ kernel's `elim_nested_inductive_fn::operator()()` at
/// `refs/lean4/src/kernel/inductive.cpp:1045-1077`.
fn expand_nested_block(
  originals: &[Name],
  lean_env: &LeanEnv,
  control: &Checkpoint,
) -> Result<ExpandedBlock, AttemptError> {
  control.visit()?;
  let first_name =
    originals.first().ok_or_else(|| CompileError::InvalidMutualBlock {
      reason: "expand_nested_block: empty originals".into(),
    })?;
  let first_ind_ref = lean_env.get(first_name);
  let first_ind = match first_ind_ref.as_deref() {
    Some(ConstantInfo::InductInfo(v)) => v,
    _ => {
      return Err(
        CompileError::MissingConstant {
          name: first_name.pretty(),
          caller: "expand_nested_block: first original not an inductive".into(),
        }
        .into(),
      );
    },
  };

  let n_params = nat_to_usize(&first_ind.num_params);
  let block_levels: Vec<Level> = first_ind
    .cnst
    .level_params
    .iter()
    .map(|lp| Level::param(lp.clone()))
    .collect();

  let (block_param_fvars, block_param_decls, _) =
    checked_expr::forall_telescope(
      &first_ind.cnst.typ,
      n_params,
      "bp",
      0,
      control,
    )?;
  let block_param_fvar_names: Vec<Name> =
    block_param_decls.iter().map(|d| d.fvar_name.clone()).collect();

  let all0 =
    first_ind.all.first().cloned().unwrap_or_else(|| originals[0].clone());

  let mut ctx = ExpandCtx {
    types: Vec::new(),
    type_name_set: FxHashSet::default(),
    aux_seen: FxHashMap::default(),
    next_aux_idx: 1,
    all0,
    block_levels,
    block_param_fvars,
    block_param_decls,
    block_param_fvar_names,
    lean_env,
    control,
  };

  // Seed with the original inductives.
  for name in originals {
    control.visit()?;
    let ind_ref = lean_env.get(name);
    let ind = match ind_ref.as_deref() {
      Some(ConstantInfo::InductInfo(v)) => v,
      _ => {
        return Err(
          CompileError::MissingConstant {
            name: name.pretty(),
            caller: "expand_nested_block: original not an inductive".into(),
          }
          .into(),
        );
      },
    };
    let ctors: Vec<LeanExpr> = ind
      .ctors
      .iter()
      .filter_map(|cn| match lean_env.get(cn).as_deref() {
        Some(ConstantInfo::CtorInfo(c)) => Some(c.cnst.typ.clone()),
        _ => None,
      })
      .collect();
    ctx.push_type(ExpandedMember { name: name.clone(), ctors });
  }

  let n_originals = ctx.types.len();

  // Queue-based scan: process each member's constructors, auxiliaries
  // included. A fresh memoization cache is allocated per constructor because
  // `replace_all_nested` closes over `as_fvars`, which differs between
  // constructors. Within a single constructor the walk is deterministic, so
  // the cache turns DAG traversal from O(shared × nodes) into O(nodes).
  let mut qi = 0;
  while qi < ctx.types.len() {
    control.visit()?;
    let n_ctors = ctx.types[qi].ctors.len();
    for ci in 0..n_ctors {
      let ctor_type = ctx.types[qi].ctors[ci].clone();

      // Peel params, re-creating FVars per constructor for binding info.
      let (as_fvars, as_decls, peeled) = checked_expr::forall_telescope(
        &ctor_type,
        n_params,
        "cp",
        qi * 100 + ci,
        control,
      )?;

      // Replace all nested occurrences in the peeled body.
      let mut walk_cache: FxHashMap<ExprKey, LeanExpr> = FxHashMap::default();
      let replaced =
        ctx.replace_all_nested(&peeled, &as_fvars, &mut walk_cache)?;

      // Re-wrap with constructor-local params.
      ctx.types[qi].ctors[ci] =
        checked_expr::mk_forall(replaced, &as_decls, control)?;
    }
    qi += 1;
  }

  Ok(ExpandedBlock { types: ctx.types, n_originals })
}

/// Rewrite the final result of an auxiliary constructor from the external
/// inductive `J spec_params indices` to the synthetic aux
/// `aux_name block_params indices`.
///
/// Lean's nested-inductive pass eventually rewrites these constructor results
/// when the queue processes the freshly-created auxiliary type. Doing it at
/// creation time avoids rediscovering the aux's own result as a second nested
/// occurrence while leaving constructor field domains available for the normal
/// queue walk.
fn replace_ctor_result_head_with_aux(
  e: &LeanExpr,
  original_ind: &Name,
  aux_name: &Name,
  original_n_params: usize,
  block_levels: &[Level],
  block_param_fvars: &[LeanExpr],
  control: &Checkpoint,
) -> Result<LeanExpr, Cancelled> {
  control.visit()?;
  Ok(match e.as_data() {
    ExprData::ForallE(n, t, b, bi, _) => LeanExpr::all(
      n.clone(),
      t.clone(),
      replace_ctor_result_head_with_aux(
        b,
        original_ind,
        aux_name,
        original_n_params,
        block_levels,
        block_param_fvars,
        control,
      )?,
      bi.clone(),
    ),
    ExprData::Mdata(md, inner, _) => LeanExpr::mdata(
      md.clone(),
      replace_ctor_result_head_with_aux(
        inner,
        original_ind,
        aux_name,
        original_n_params,
        block_levels,
        block_param_fvars,
        control,
      )?,
    ),
    _ => {
      let (head, args) = decompose_apps(e);
      let ExprData::Const(head_name, _, _) = head.as_data() else {
        return Ok(e.clone());
      };
      if head_name != original_ind || args.len() < original_n_params {
        return Ok(e.clone());
      }

      let mut result = LeanExpr::cnst(aux_name.clone(), block_levels.to_vec());
      for param in block_param_fvars {
        result = LeanExpr::app(result, param.clone());
      }
      for idx_arg in args.iter().skip(original_n_params) {
        result = LeanExpr::app(result, idx_arg.clone());
      }
      result
    },
  })
}

// =========================================================================
// Flags
// =========================================================================

/// Lean-faithful declaration flags for an original mutual block
pub struct LeanIndFlags {
  pub is_rec: bool,
  pub is_reflexive: bool,
  pub num_nested: u64,
}

/// Recompute Lean's block-wide `isRec` / `isReflexive` / `numNested` for the
/// original mutual group `all`
/// used whereever an `InductiveVal` must be reconstructed without a Lean env
/// to copy from, such as kernel egress and decompile, since Ixon doesn't store
/// these flags
pub fn compute_lean_ind_flags(
  all: &[Name],
  lean_env: &LeanEnv,
) -> Result<LeanIndFlags, CompileError> {
  compute_lean_ind_flags_checked(all, lean_env, &Checkpoint::default())
    .map_err(AttemptError::into_compile)
}

fn compute_lean_ind_flags_checked(
  all: &[Name],
  lean_env: &LeanEnv,
  control: &Checkpoint,
) -> Result<LeanIndFlags, AttemptError> {
  let expanded = expand_nested_block(all, lean_env, control)?;
  let num_nested = (expanded.types.len() - expanded.n_originals) as u64;
  let block_names: FxHashSet<&Name> =
    expanded.types.iter().map(|m| &m.name).collect();

  let mut occ_cache: FxHashMap<ExprKey, bool> = FxHashMap::default();
  let mut is_rec = false;
  let mut is_reflexive = false;
  for member in &expanded.types {
    for ctor in &member.ctors {
      let mut ty = ctor;
      while let ExprData::ForallE(_, dom, body, _, _) = ty.as_data() {
        control.visit()?;
        if has_ind_occ(dom, &block_names, &mut occ_cache, control)? {
          is_rec = true;
          if matches!(dom.as_data(), ExprData::ForallE(..)) {
            is_reflexive = true;
          }
        }
        ty = body;
      }
    }
  }
  Ok(LeanIndFlags { is_rec, is_reflexive, num_nested })
}

/// Validate that every inductive group in `lean_env` carries exactly the flags
/// `compute_lean_ind_flags` recomputes.
pub fn validate_lean_ind_flags(lean_env: &LeanEnv) -> Result<(), CompileError> {
  let mut groups: FxHashMap<Name, Vec<Name>> = FxHashMap::default();
  for (_, ci) in lean_env.iter() {
    if let ConstantInfo::InductInfo(v) = &*ci
      && let Some(first) = v.all.first()
    {
      groups.entry(first.clone()).or_insert_with(|| v.all.clone());
    }
  }
  validate_ind_groups(&groups, lean_env)
}

static LOG_IND_GROUPS: LazyLock<bool> =
  LazyLock::new(|| std::env::var_os("IX_LOG_IND_GROUPS").is_some());

/// Per-group half of [`validate_lean_ind_flags`], for callers that
/// already hold the inductive groups from a wider env pass.
/// `IX_LOG_IND_GROUPS=1` logs group entry/exit for allocation-failure diagnosis.
pub fn validate_ind_groups(
  groups: &FxHashMap<Name, Vec<Name>>,
  lean_env: &LeanEnv,
) -> Result<(), CompileError> {
  // Stable IDs make cancellations/retries identifiable in progress logs.
  let mut entries: Vec<_> = groups.iter().collect();
  entries.sort_unstable_by(|(a, _), (b, _)| {
    a.get_hash().as_bytes().cmp(b.get_hash().as_bytes())
  });
  let entries: Vec<_> = entries.into_iter().enumerate().collect();
  validation::run(&entries, |(id, (leader, all)), control| {
    let start = Instant::now();
    if *LOG_IND_GROUPS {
      eprintln!("[validate_ind_flags] BEGIN {} (group #{id})", leader.pretty());
    }
    let result = validate_one_group(all, lean_env, control);
    if *LOG_IND_GROUPS {
      let status = match &result {
        Ok(()) => "END",
        Err(AttemptError::Cancelled) => "CANCEL",
        Err(AttemptError::Compile(_)) => "ERROR",
      };
      eprintln!(
        "[validate_ind_flags] {status} {} (group #{id}, {:.2}s)",
        leader.pretty(),
        start.elapsed().as_secs_f32()
      );
    }
    result
  })
}

fn validate_one_group(
  all: &[Name],
  lean_env: &LeanEnv,
  control: &Checkpoint,
) -> Result<(), AttemptError> {
  for member in all.iter() {
    control.visit()?;
    let entry = lean_env.get(member);
    let Some(ConstantInfo::InductInfo(v)) = entry.as_deref() else {
      return Ok(());
    };
    for cn in &v.ctors {
      control.visit()?;
      if !matches!(lean_env.get(cn).as_deref(), Some(ConstantInfo::CtorInfo(_)))
      {
        return Ok(());
      }
    }
  }
  let flags = compute_lean_ind_flags_checked(all, lean_env, control)?;
  for member in all.iter() {
    let entry = lean_env.get(member);
    let Some(ConstantInfo::InductInfo(v)) = entry.as_deref() else {
      continue; // unreachable
    };
    if v.is_rec != flags.is_rec
      || v.is_reflexive != flags.is_reflexive
      || v.num_nested != Nat::from(flags.num_nested)
    {
      return Err(
        CompileError::InvalidMutualBlock {
          reason: format!(
            "non-canonical inductive flags for '{}': \
               stored isRec={} isReflexive={} numNested={}, \
               computed isRec={} isReflexive={} numNested={}",
            member.pretty(),
            v.is_rec,
            v.is_reflexive,
            v.num_nested,
            flags.is_rec,
            flags.is_reflexive,
            flags.num_nested,
          ),
        }
        .into(),
      );
    }
  }
  Ok(())
}

// does `expr` mention any block type by name anywhere?
// DAG-memoized: ctor types share subterm DAGs
fn has_ind_occ(
  expr: &LeanExpr,
  names: &FxHashSet<&Name>,
  cache: &mut FxHashMap<ExprKey, bool>,
  control: &Checkpoint,
) -> Result<bool, Cancelled> {
  control.visit()?;
  let key = ExprKey(expr.clone());
  if let Some(&cached) = cache.get(&key) {
    return Ok(cached);
  }
  let result = match expr.as_data() {
    ExprData::Const(name, _, _) => names.contains(name),
    ExprData::App(f, a, _) => {
      has_ind_occ(f, names, cache, control)?
        || has_ind_occ(a, names, cache, control)?
    },
    ExprData::Lam(_, t, b, _, _) | ExprData::ForallE(_, t, b, _, _) => {
      has_ind_occ(t, names, cache, control)?
        || has_ind_occ(b, names, cache, control)?
    },
    ExprData::LetE(_, t, v, b, _, _) => {
      has_ind_occ(t, names, cache, control)?
        || has_ind_occ(v, names, cache, control)?
        || has_ind_occ(b, names, cache, control)?
    },
    ExprData::Proj(_, _, e, _) | ExprData::Mdata(_, e, _) => {
      has_ind_occ(e, names, cache, control)?
    },
    _ => false,
  };
  cache.insert(key, result);
  control.scratch(cache.capacity() * size_of::<(ExprKey, bool)>());
  Ok(result)
}

#[cfg(test)]
mod tests {
  use super::*;
  use ix_common::env::{
    ConstantVal, ConstructorVal, InductiveVal, Level as LL,
  };

  fn mk_name_for(s: &str) -> Name {
    let mut n = Name::anon();
    for part in s.split('.') {
      n = Name::str(n, part.to_string());
    }
    n
  }

  /// Recursive single-ctor inductive `N` with a real `CtorInfo` entry.
  /// Canonical flags: isRec=true, isReflexive=false, numNested=0.
  fn flags_env(is_rec: bool, is_reflexive: bool, num_nested: u64) -> LeanEnv {
    let mut env = LeanEnv::default();
    let n = mk_name_for("N");
    env.insert(
      n.clone(),
      ConstantInfo::InductInfo(InductiveVal {
        cnst: ConstantVal {
          name: n.clone(),
          level_params: vec![],
          typ: LeanExpr::sort(LL::succ(LL::zero())),
        },
        num_params: Nat::from(0u64),
        num_indices: Nat::from(0u64),
        all: vec![n.clone()],
        ctors: vec![mk_name_for("N.mk")],
        num_nested: Nat::from(num_nested),
        is_rec,
        is_unsafe: false,
        is_reflexive,
      }),
    );
    // N.mk : N → N
    env.insert(
      mk_name_for("N.mk"),
      ConstantInfo::CtorInfo(ConstructorVal {
        cnst: ConstantVal {
          name: mk_name_for("N.mk"),
          level_params: vec![],
          typ: LeanExpr::all(
            mk_name_for("_"),
            LeanExpr::cnst(n.clone(), vec![]),
            LeanExpr::cnst(n.clone(), vec![]),
            BinderInfo::Default,
          ),
        },
        induct: n,
        cidx: Nat::from(0u64),
        num_params: Nat::from(0u64),
        num_fields: Nat::from(1u64),
        is_unsafe: false,
      }),
    );
    env
  }

  #[test]
  fn validate_lean_ind_flags_accepts_canonical() {
    assert!(validate_lean_ind_flags(&flags_env(true, false, 0)).is_ok());
  }

  #[test]
  fn validate_lean_ind_flags_rejects_bad_is_rec() {
    let r = validate_lean_ind_flags(&flags_env(false, false, 0));
    assert!(matches!(r, Err(CompileError::InvalidMutualBlock { .. })));
  }

  #[test]
  fn validate_lean_ind_flags_rejects_bad_num_nested() {
    let r = validate_lean_ind_flags(&flags_env(true, false, 1));
    assert!(matches!(r, Err(CompileError::InvalidMutualBlock { .. })));
  }

  #[test]
  fn validate_lean_ind_flags_skips_unresolvable_group() {
    // Wrong flags, but the ctor entry is removed → group unresolvable →
    // skipped (grounding owns partial envs), not rejected.
    let full = flags_env(false, false, 0);
    let env: LeanEnv = full
      .iter()
      .filter(|(n, _)| **n != mk_name_for("N.mk"))
      .map(|(n, ci)| (n.clone(), ci.cloned()))
      .collect();
    assert!(validate_lean_ind_flags(&env).is_ok());
  }

  /// `UniverseNested.{u,v}` with constructors `left : Phantom.{0,u}
  /// UniverseNested → UniverseNested` and `right : Phantom.{0,v}
  /// UniverseNested → UniverseNested`: the two occurrences differ only in
  /// the external family's second universe argument, so each opens its own
  /// auxiliary.
  fn universe_specialized_nested_env() -> LeanEnv {
    let mut env = LeanEnv::default();
    let phantom = mk_name_for("Phantom");
    let phantom_mk = mk_name_for("Phantom.mk");
    let root = mk_name_for("UniverseNested");
    let left = mk_name_for("UniverseNested.left");
    let right = mk_name_for("UniverseNested.right");
    let p = mk_name_for("p");
    let q = mk_name_for("q");
    let u = mk_name_for("u");
    let v = mk_name_for("v");
    let param = |name: &Name| LL::param(name.clone());
    let root_app = || LeanExpr::cnst(root.clone(), vec![param(&u), param(&v)]);
    let sort0 = || LeanExpr::sort(LL::zero());

    env.insert(
      phantom.clone(),
      ConstantInfo::InductInfo(InductiveVal {
        cnst: ConstantVal {
          name: phantom.clone(),
          level_params: vec![p.clone(), q.clone()],
          typ: LeanExpr::all(
            mk_name_for("alpha"),
            LeanExpr::sort(param(&p)),
            sort0(),
            BinderInfo::Default,
          ),
        },
        num_params: Nat::from(1u64),
        num_indices: Nat::from(0u64),
        all: vec![phantom.clone()],
        ctors: vec![phantom_mk.clone()],
        num_nested: Nat::from(0u64),
        is_rec: false,
        is_unsafe: false,
        is_reflexive: false,
      }),
    );
    env.insert(
      phantom_mk.clone(),
      ConstantInfo::CtorInfo(ConstructorVal {
        cnst: ConstantVal {
          name: phantom_mk,
          level_params: vec![p.clone(), q.clone()],
          typ: LeanExpr::all(
            mk_name_for("alpha"),
            LeanExpr::sort(param(&p)),
            LeanExpr::all(
              mk_name_for("beta"),
              LeanExpr::sort(param(&q)),
              LeanExpr::app(
                LeanExpr::cnst(phantom.clone(), vec![param(&p), param(&q)]),
                LeanExpr::bvar(Nat::from(1u64)),
              ),
              BinderInfo::Default,
            ),
            BinderInfo::Default,
          ),
        },
        induct: phantom.clone(),
        cidx: Nat::from(0u64),
        num_params: Nat::from(1u64),
        num_fields: Nat::from(1u64),
        is_unsafe: false,
      }),
    );

    env.insert(
      root.clone(),
      ConstantInfo::InductInfo(InductiveVal {
        cnst: ConstantVal {
          name: root.clone(),
          level_params: vec![u.clone(), v.clone()],
          typ: sort0(),
        },
        num_params: Nat::from(0u64),
        num_indices: Nat::from(0u64),
        all: vec![root.clone()],
        ctors: vec![left.clone(), right.clone()],
        num_nested: Nat::from(2u64),
        is_rec: true,
        is_unsafe: false,
        is_reflexive: false,
      }),
    );
    for (name, level, cidx) in
      [(left, param(&u), 0u64), (right, param(&v), 1u64)]
    {
      let nested = LeanExpr::app(
        LeanExpr::cnst(phantom.clone(), vec![LL::zero(), level]),
        root_app(),
      );
      env.insert(
        name.clone(),
        ConstantInfo::CtorInfo(ConstructorVal {
          cnst: ConstantVal {
            name,
            level_params: vec![u.clone(), v.clone()],
            typ: LeanExpr::all(
              mk_name_for("nested"),
              nested,
              root_app(),
              BinderInfo::Default,
            ),
          },
          induct: root.clone(),
          cidx: Nat::from(cidx),
          num_params: Nat::from(0u64),
          num_fields: Nat::from(1u64),
          is_unsafe: false,
        }),
      );
    }
    env
  }

  /// Each nested occurrence opens an auxiliary (`numNested`), and a field
  /// whose type is an auxiliary is recursive (`isRec`).
  #[test]
  fn nested_occurrences_count_as_auxiliaries_and_recursion() {
    let env = universe_specialized_nested_env();
    let flags =
      compute_lean_ind_flags(&[mk_name_for("UniverseNested")], &env).unwrap();
    assert_eq!(flags.num_nested, 2);
    assert!(flags.is_rec);
    assert!(!flags.is_reflexive);
    assert!(validate_lean_ind_flags(&env).is_ok());
  }

  /// Replace the field domain of both `UniverseNested` constructors by
  /// `domain(original domain)`.
  fn rewrite_field_domains(
    env: &mut LeanEnv,
    domain: impl Fn(&LeanExpr) -> LeanExpr,
  ) {
    for name in ["UniverseNested.left", "UniverseNested.right"] {
      let Some(ConstantInfo::CtorInfo(ctor)) = env.get_mut(&mk_name_for(name))
      else {
        panic!("missing fixture constructor");
      };
      let ExprData::ForallE(field, dom, result, info, _) =
        ctor.cnst.typ.as_data()
      else {
        panic!("missing fixture field");
      };
      ctor.cnst.typ =
        LeanExpr::all(field.clone(), domain(dom), result.clone(), info.clone());
    }
  }

  fn flags_of(env: &LeanEnv) -> (bool, bool, u64) {
    let flags =
      compute_lean_ind_flags(&[mk_name_for("UniverseNested")], env).unwrap();
    (flags.is_rec, flags.is_reflexive, flags.num_nested)
  }

  /// Nested occurrences are found beneath non-inductive heads and binders;
  /// a field whose type is a function into one is reflexive.
  #[test]
  fn nested_occurrences_under_wrappers_and_binders_are_found() {
    let mut env = universe_specialized_nested_env();
    rewrite_field_domains(&mut env, |dom| {
      let wrapped = LeanExpr::app(
        LeanExpr::cnst(mk_name_for("NonInductiveWrapper"), vec![]),
        dom.clone(),
      );
      LeanExpr::all(
        mk_name_for("local"),
        LeanExpr::sort(LL::zero()),
        wrapped,
        BinderInfo::Default,
      )
    });
    assert_eq!(flags_of(&env), (true, true, 2));
  }

  /// A specialization that mentions a field-local binder is not a nested
  /// occurrence: no auxiliary opens, though the field still mentions the
  /// block.
  #[test]
  fn field_local_specializations_open_no_auxiliary() {
    let mut env = universe_specialized_nested_env();
    rewrite_field_domains(&mut env, |dom| {
      let ExprData::App(head, root, _) = dom.as_data() else {
        panic!("missing fixture occurrence");
      };
      let dependent = LeanExpr::app(
        head.clone(),
        LeanExpr::app(LeanExpr::bvar(Nat::from(0u64)), root.clone()),
      );
      let wrapped = LeanExpr::app(
        LeanExpr::cnst(mk_name_for("NonInductiveWrapper"), vec![]),
        dependent,
      );
      let function_type = LeanExpr::all(
        mk_name_for("p"),
        LeanExpr::sort(LL::zero()),
        LeanExpr::sort(LL::zero()),
        BinderInfo::Default,
      );
      LeanExpr::all(
        mk_name_for("local"),
        function_type,
        wrapped,
        BinderInfo::Default,
      )
    });
    assert_eq!(flags_of(&env), (true, true, 0));
  }

  /// A recognized occurrence is replaced whole: an occurrence nested in its
  /// specialization is not expanded separately, and both constructors'
  /// identical occurrences share one auxiliary.
  #[test]
  fn recognized_occurrences_are_replaced_whole_and_deduplicated() {
    let mut env = universe_specialized_nested_env();
    let root = LeanExpr::cnst(
      mk_name_for("UniverseNested"),
      vec![LL::param(mk_name_for("u")), LL::param(mk_name_for("v"))],
    );
    let phantom = |level: &str, arg: LeanExpr| {
      LeanExpr::app(
        LeanExpr::cnst(
          mk_name_for("Phantom"),
          vec![LL::zero(), LL::param(mk_name_for(level))],
        ),
        arg,
      )
    };
    let outer = phantom("u", phantom("v", root));
    rewrite_field_domains(&mut env, |_| outer.clone());
    assert_eq!(flags_of(&env), (true, false, 1));
  }

  #[test]
  fn fresh_fvar_produces_unique_names() {
    let (n1, f1) = fresh_fvar("p", 0);
    let (n2, f2) = fresh_fvar("p", 1);
    assert_ne!(n1, n2);
    assert!(matches!(f1.as_data(), ExprData::Fvar(n, _) if *n == n1));
    assert!(matches!(f2.as_data(), ExprData::Fvar(n, _) if *n == n2));
  }

  #[test]
  fn fresh_fvar_prefix_changes_name() {
    let (na, _) = fresh_fvar("a", 0);
    let (nb, _) = fresh_fvar("b", 0);
    assert_ne!(na, nb);
  }

  #[test]
  fn decompose_apps_non_app() {
    let e = LeanExpr::sort(LL::zero());
    let (head, args) = decompose_apps(&e);
    assert_eq!(args.len(), 0);
    assert_eq!(head.get_hash(), e.get_hash());
  }

  #[test]
  fn decompose_apps_left_deep_order() {
    // ((f a) b) c → head=f, args=[a, b, c]
    let f = LeanExpr::cnst(mk_name_for("f"), vec![]);
    let a = LeanExpr::sort(LL::zero());
    let b = LeanExpr::sort(LL::succ(LL::zero()));
    let c = LeanExpr::bvar(Nat::from(0u64));
    let e = LeanExpr::app(
      LeanExpr::app(LeanExpr::app(f.clone(), a.clone()), b.clone()),
      c.clone(),
    );
    let (head, args) = decompose_apps(&e);
    assert_eq!(head.get_hash(), f.get_hash());
    assert_eq!(args.len(), 3);
    assert_eq!(args[0].get_hash(), a.get_hash());
    assert_eq!(args[1].get_hash(), b.get_hash());
    assert_eq!(args[2].get_hash(), c.get_hash());
  }
}
