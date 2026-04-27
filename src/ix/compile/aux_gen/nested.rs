//! Nested-inductive detection and flat block construction.
//!
//! Detects nested occurrences in constructor field types (e.g., `List Tree`)
//! and builds auxiliary entries for the flat block. Ported from the kernel's
//! `build_flat_block` + `try_detect_nested` (`src/ix/kernel/inductive.rs:364-612`),
//! adapted to use `Name`/`LeanExpr`/`Level` types from the compile-side environment.
//!
//! Key differences from the kernel implementation:
//! - No WHNF — finalized Lean env types are already normalized
//! - Uses FVar-based field processing (via `forall_telescope`) instead of manual
//!   BVar depth tracking. This eliminates `lower_vars`-style normalization —
//!   field-local dependencies are detected by checking for non-param FVars
//!   rather than BVar range arithmetic.
//! - Spec_params are built in FVar space during detection, then abstracted back
//!   to BVars for the returned `CompileFlatMember`.

use blake3::Hash;
use lean_ffi::nat::Nat;
use rustc_hash::{FxHashMap, FxHashSet};

use super::expr_utils::{
  LocalDecl, batch_abstract, decompose_apps, forall_telescope,
  instantiate_pi_params, instantiate1, mk_forall, subst_levels,
};
use crate::ix::compile::nat_conv::{nat_to_u64, nat_to_usize};
use crate::ix::env::{
  ConstantInfo, Env as LeanEnv, Expr as LeanExpr, ExprData, Level, Name,
};
use crate::ix::ixon::CompileError;

/// A member of the flat block (original inductive or nested auxiliary).
///
/// Spec_params use BVars relative to the block's parameter context:
/// `BVar(0)` = innermost (last) param, `BVar(n_params-1)` = outermost (first).
#[derive(Clone)]
pub(crate) struct CompileFlatMember {
  pub name: Name,
  pub spec_params: Vec<LeanExpr>,
  pub occurrence_level_args: Vec<Level>,
  pub own_params: usize,
  pub n_indices: usize,
}

// =========================================================================
// Expanded block (expand/restore model)
// =========================================================================

/// An expanded mutual block where nested inductive occurrences have been
/// replaced with auxiliary types sharing the block's parameters and levels.
///
/// Matches the C++ kernel's `elim_nested_inductive_result`: auxiliary types
/// like `_nested.Array_1` replace `Array (Part α β)` so that the recursor
/// generator can treat all members uniformly.
pub(crate) struct ExpandedBlock {
  /// All types in the expanded block: originals first, then auxiliaries.
  pub types: Vec<ExpandedMember>,
  /// `aux_name → nested_expr`: the original nested application with block
  /// param FVars as free variables. Used by `restore_nested` to convert
  /// auxiliary references back to original nested form.
  ///
  /// Example: `"_nested.Array_1" → Array.{max u v} (Part.{u,v} fvar_α fvar_β)`
  pub aux_to_nested: FxHashMap<Name, LeanExpr>,
  /// `aux_ctor_name → (original_ctor_name, aux_inductive_name)`.
  ///
  /// Second element is the aux inductive (e.g., `_nested.List_1`) that this
  /// ctor belongs to — used by `RestoreCtx::replace_walk` to look up the
  /// corresponding entry in `aux_to_nested` directly in O(1). Previously
  /// this stored the *original external* inductive name (e.g., `List`) and
  /// callers had to prefix-scan `aux_to_nested.keys()` to find the aux
  /// inductive; the data was wasted overhead.
  pub aux_ctor_map: FxHashMap<Name, (Name, Name)>, // (orig_ctor, aux_ind)
  /// Block parameters as FVars (shared across all members).
  pub block_param_fvars: Vec<LeanExpr>,
  /// Number of original (non-auxiliary) types.
  pub n_originals: usize,
  /// Block-level universe parameters (from the first original inductive).
  pub level_params: Vec<Name>,
}

/// A member of the expanded block (original or auxiliary).
///
/// All members share the same `level_params` and `n_params` — auxiliaries
/// have the block's parameters, not the external inductive's own parameters.
#[derive(Clone)]
pub(crate) struct ExpandedMember {
  /// Inductive name: original name for originals, `_nested.ExtInd_N` for
  /// auxiliaries (scoped under `all[0]`).
  pub name: Name,
  /// Original source member whose constructor walk first discovered this
  /// member. Auxiliaries inherit this through the nested-discovery queue.
  pub source_owner: Name,
  /// Inductive type: `∀ (block_params...) (indices...) → Sort s`
  pub typ: LeanExpr,
  /// Constructors with types already rewritten (nested refs → aux consts).
  pub ctors: Vec<ExpandedCtor>,
  /// Number of block parameters (same for all members).
  pub n_params: usize,
  /// Number of indices (from the external inductive's metadata).
  pub n_indices: usize,
}

/// A constructor in the expanded block.
#[derive(Clone)]
pub(crate) struct ExpandedCtor {
  /// Constructor name: for auxiliaries, prefixed with aux name.
  pub name: Name,
  /// Constructor type with nested refs replaced by aux const applications.
  /// Shape: `∀ (block_params...) (fields...) → Member block_params indices`
  pub typ: LeanExpr,
  /// Number of fields (constructor arguments past params).
  pub n_fields: usize,
}

// =========================================================================
// Expand: create auxiliary types for nested occurrences
// =========================================================================

/// Mutable state for the nested expansion algorithm.
struct ExpandCtx<'a> {
  types: Vec<ExpandedMember>,
  /// Mirror of `types.iter().map(|m| m.name)` maintained incrementally.
  /// Used for O(1) "is this name in the block?" checks in the hot
  /// `replace_if_nested` path. Must be updated whenever a member is pushed
  /// (seeding, nested aux creation). Invariant: `type_name_set.len() ==
  /// types.len()` and both contain the same names.
  type_name_set: FxHashSet<Name>,
  aux_to_nested: FxHashMap<Name, LeanExpr>,
  aux_ctor_map: FxHashMap<Name, (Name, Name)>,
  /// Dedup: maps nested_expr_hash → aux_name for each detected occurrence.
  /// Previously a `Vec<(Hash, Name)>` scanned linearly per subterm; swapped
  /// to a map so the lookup in `replace_if_nested` is O(1).
  aux_seen: FxHashMap<Hash, Name>,
  next_aux_idx: usize,
  all0: Name,
  block_levels: Vec<Level>,
  block_param_fvars: Vec<LeanExpr>,
  block_param_decls: Vec<LocalDecl>,
  block_param_fvar_names: Vec<Name>,
  lean_env: &'a LeanEnv,
  n_params: usize,
}

impl<'a> ExpandCtx<'a> {
  /// Push a new member and keep `type_name_set` in sync. All pushes to
  /// `types` must go through this method so the incremental name set
  /// stays consistent with the vector.
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
  /// current constructor walk only. Caller is responsible for providing a
  /// fresh cache per constructor (see `expand_nested_block`) — the result
  /// depends on `as_fvars` and `source_owner`, so cache entries from one
  /// constructor are not valid for another. On the other hand, within a
  /// single constructor walk the function is deterministic: once a subterm
  /// is rewritten, every subsequent visit of that subterm yields the same
  /// expression, so memoization is safe even though `self` mutates during
  /// the walk (new auxes created while processing subterm X cannot change
  /// the rewrite of an already-processed subterm Y).
  fn replace_all_nested(
    &mut self,
    e: &LeanExpr,
    as_fvars: &[LeanExpr],
    source_owner: &Name,
    cache: &mut FxHashMap<Hash, LeanExpr>,
  ) -> LeanExpr {
    let key = *e.get_hash();
    if let Some(cached) = cache.get(&key) {
      return cached.clone();
    }

    // Try top-level replacement first.
    if let Some(replaced) = self.replace_if_nested(e, as_fvars, source_owner) {
      cache.insert(key, replaced.clone());
      return replaced;
    }
    // No match — recurse into sub-expressions.
    let result = match e.as_data() {
      ExprData::App(f, a, _) => LeanExpr::app(
        self.replace_all_nested(f, as_fvars, source_owner, cache),
        self.replace_all_nested(a, as_fvars, source_owner, cache),
      ),
      ExprData::Lam(n, t, b, bi, _) => LeanExpr::lam(
        n.clone(),
        self.replace_all_nested(t, as_fvars, source_owner, cache),
        self.replace_all_nested(b, as_fvars, source_owner, cache),
        bi.clone(),
      ),
      ExprData::ForallE(n, t, b, bi, _) => LeanExpr::all(
        n.clone(),
        self.replace_all_nested(t, as_fvars, source_owner, cache),
        self.replace_all_nested(b, as_fvars, source_owner, cache),
        bi.clone(),
      ),
      ExprData::LetE(n, t, v, b, nd, _) => LeanExpr::letE(
        n.clone(),
        self.replace_all_nested(t, as_fvars, source_owner, cache),
        self.replace_all_nested(v, as_fvars, source_owner, cache),
        self.replace_all_nested(b, as_fvars, source_owner, cache),
        *nd,
      ),
      ExprData::Proj(n, i, val, _) => LeanExpr::proj(
        n.clone(),
        i.clone(),
        self.replace_all_nested(val, as_fvars, source_owner, cache),
      ),
      ExprData::Mdata(md, inner, _) => LeanExpr::mdata(
        md.clone(),
        self.replace_all_nested(inner, as_fvars, source_owner, cache),
      ),
      _ => e.clone(),
    };
    cache.insert(key, result.clone());
    result
  }

  /// Check if `e` is a nested inductive application and, if so, create
  /// auxiliary types and return the replacement expression.
  ///
  /// Matches C++ `replace_if_nested` (`inductive.cpp:963-1027`).
  fn replace_if_nested(
    &mut self,
    e: &LeanExpr,
    as_fvars: &[LeanExpr],
    source_owner: &Name,
  ) -> Option<LeanExpr> {
    let (head, args) = decompose_apps(e);
    let (head_name, head_levels) = match head.as_data() {
      ExprData::Const(name, levels, _) => (name.clone(), levels.clone()),
      _ => return None,
    };

    // Skip if head is in the block (direct recursive, not nested). The
    // `type_name_set` mirrors `self.types` names and is maintained
    // incrementally by `push_type`, so this is O(1) rather than O(n_types).
    if self.type_name_set.contains(&head_name) {
      return None;
    }

    // Verify head is an external inductive.
    let ext_ind_ref = self.lean_env.get(&head_name);
    let ext_ind = match ext_ind_ref {
      Some(ConstantInfo::InductInfo(v)) => v,
      _ => return None,
    };
    let ext_n_params = nat_to_usize(&ext_ind.num_params);

    if args.len() < ext_n_params {
      return None;
    }

    // Check if any parameter arg mentions a block/flat-block member.
    // `expr_mentions_any_name` takes the incremental set directly so each
    // Const check is O(1) instead of a linear Vec scan.
    if !args
      .iter()
      .take(ext_n_params)
      .any(|a| expr_mentions_any_name(a, &self.type_name_set))
    {
      return None;
    }

    // Extract spec_params, normalizing constructor-local parameter FVars to
    // the block parameter FVars before validation. Parameterized nested
    // occurrences such as `List (Rose α)` are seen while scanning a
    // constructor telescope, so their raw spec params mention `as_fvars`; the
    // auxiliary identity must be expressed in the shared block-param space.
    let spec_params: Vec<LeanExpr> = args[..ext_n_params]
      .iter()
      .map(|sp| replace_params_expr(sp, as_fvars, &self.block_param_fvars))
      .collect();
    for sp in &spec_params {
      if has_invalid_spec_ref(sp, &self.block_param_fvar_names) {
        return None;
      }
    }

    // Build `IAs = I.{I_lvls} spec_params` normalized to block param FVars.
    let i_as = {
      let mut app = LeanExpr::cnst(head_name.clone(), head_levels.clone());
      for sp in &spec_params {
        app = LeanExpr::app(app, sp.clone());
      }
      app
    };
    let i_as_hash = *i_as.get_hash();

    // Dedup: check if we've already created an auxiliary for this occurrence.
    // O(1) HashMap lookup; previously a linear scan over `Vec<(Hash, Name)>`.
    if let Some(aux_name) = self.aux_seen.get(&i_as_hash).cloned() {
      let mut result = LeanExpr::cnst(aux_name, self.block_levels.clone());
      for af in as_fvars {
        result = LeanExpr::app(result, af.clone());
      }
      for idx_arg in args.iter().skip(ext_n_params) {
        result = LeanExpr::app(result, idx_arg.clone());
      }
      return Some(result);
    }

    // New nested occurrence — create auxiliary types for all members of
    // the external inductive's mutual group.
    let ext_all = ext_ind.all.clone();
    let mut result: Option<LeanExpr> = None;

    for j_name in &ext_all {
      let j_info_ref = self.lean_env.get(j_name);
      let j_info = match j_info_ref {
        Some(ConstantInfo::InductInfo(v)) => v,
        _ => continue,
      };

      // Auxiliary name: _nested.ExtInd_N (scoped under all[0]).
      let aux_name = Name::str(
        Name::str(self.all0.clone(), "_nested".to_string()),
        format!("{}_{}", j_name.pretty().replace('.', "_"), self.next_aux_idx),
      );
      self.next_aux_idx += 1;

      // Store mapping: aux_name → J.{I_lvls} spec_params (with block param FVars).
      let j_as = {
        let mut app = LeanExpr::cnst(j_name.clone(), head_levels.clone());
        for sp in &spec_params {
          app = LeanExpr::app(app, sp.clone());
        }
        app
      };
      self.aux_to_nested.insert(aux_name.clone(), j_as);
      // Only the *first* j_name (head) registers under this nested-hash so
      // subsequent hits of the same occurrence dedup to the right aux.
      // Extra mutual-group members live in `aux_to_nested` but are reached
      // through the normal queue walk, not via `aux_seen` lookup.
      self.aux_seen.entry(i_as_hash).or_insert_with(|| aux_name.clone());

      // Build auxiliary type:
      // 1. subst_levels(J.type, J.level_params, I_lvls)
      // 2. instantiate_pi_params(result, ext_n_params, spec_params)
      // 3. mk_forall(block_params, result)
      let j_type_inst =
        subst_levels(&j_info.cnst.typ, &j_info.cnst.level_params, &head_levels);
      let j_type_peeled =
        instantiate_pi_params(&j_type_inst, ext_n_params, &spec_params);
      let j_type_block =
        replace_params_expr(&j_type_peeled, as_fvars, &self.block_param_fvars);
      let aux_type = mk_forall(j_type_block, &self.block_param_decls);

      // Build auxiliary constructors.
      let mut aux_ctors: Vec<ExpandedCtor> = Vec::new();
      for j_ctor_name in &j_info.ctors {
        let j_ctor_ref = self.lean_env.get(j_ctor_name);
        let j_ctor = match j_ctor_ref {
          Some(ConstantInfo::CtorInfo(c)) => c,
          _ => continue,
        };
        let aux_ctor_name = name_replace_prefix(j_ctor_name, j_name, &aux_name);
        let ctor_type_inst = subst_levels(
          &j_ctor.cnst.typ,
          &j_info.cnst.level_params,
          &head_levels,
        );
        let ctor_type_peeled =
          instantiate_pi_params(&ctor_type_inst, ext_n_params, &spec_params);
        let ctor_type_block = replace_params_expr(
          &ctor_type_peeled,
          as_fvars,
          &self.block_param_fvars,
        );
        let ctor_type_block = replace_ctor_result_head_with_aux(
          &ctor_type_block,
          j_name,
          &aux_name,
          ext_n_params,
          &self.block_levels,
          &self.block_param_fvars,
        );
        let aux_ctor_type = mk_forall(ctor_type_block, &self.block_param_decls);

        self.aux_ctor_map.insert(
          aux_ctor_name.clone(),
          (j_ctor_name.clone(), aux_name.clone()),
        );
        aux_ctors.push(ExpandedCtor {
          name: aux_ctor_name,
          typ: aux_ctor_type,
          n_fields: nat_to_usize(&j_ctor.num_fields),
        });
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

      self.push_type(ExpandedMember {
        name: aux_name,
        source_owner: source_owner.clone(),
        typ: aux_type,
        n_params: self.n_params,
        n_indices: nat_to_usize(&j_info.num_indices),
        ctors: aux_ctors,
      });
    }

    result
  }
}

/// Build an expanded block by replacing nested inductive occurrences with
/// auxiliary types that share the block's parameters and universe levels.
///
/// Matches the C++ kernel's `elim_nested_inductive_fn::operator()()` at
/// `refs/lean4/src/kernel/inductive.cpp:1045-1077`.
pub(crate) fn expand_nested_block(
  ordered_originals: &[Name],
  lean_env: &LeanEnv,
  alias_to_rep: &FxHashMap<Name, Name>,
) -> Result<ExpandedBlock, CompileError> {
  let first_name = ordered_originals.first().ok_or_else(|| {
    CompileError::InvalidMutualBlock {
      reason: "expand_nested_block: empty ordered_originals".into(),
    }
  })?;
  let first_ind_ref = lean_env.get(first_name);
  let first_ind = match first_ind_ref {
    Some(ConstantInfo::InductInfo(v)) => v,
    _ => {
      return Err(CompileError::MissingConstant {
        name: first_name.pretty(),
        caller: "expand_nested_block: first original not an inductive".into(),
      });
    },
  };

  let n_params = nat_to_usize(&first_ind.num_params);
  let level_params = first_ind.cnst.level_params.clone();
  let block_levels: Vec<Level> =
    level_params.iter().map(|lp| Level::param(lp.clone())).collect();

  let (block_param_fvars, block_param_decls, _) =
    forall_telescope(&first_ind.cnst.typ, n_params, "bp", 0);
  let block_param_fvar_names: Vec<Name> =
    block_param_decls.iter().map(|d| d.fvar_name.clone()).collect();

  let all0 = first_ind
    .all
    .first()
    .cloned()
    .unwrap_or_else(|| ordered_originals[0].clone());

  let mut ctx = ExpandCtx {
    types: Vec::new(),
    type_name_set: FxHashSet::default(),
    aux_to_nested: FxHashMap::default(),
    aux_ctor_map: FxHashMap::default(),
    aux_seen: FxHashMap::default(),
    next_aux_idx: 1,
    all0,
    block_levels,
    block_param_fvars: block_param_fvars.clone(),
    block_param_decls: block_param_decls.clone(),
    block_param_fvar_names,
    lean_env,
    n_params,
  };

  // Seed with original inductives.
  for name in ordered_originals {
    let ind_ref = lean_env.get(name);
    let ind = match ind_ref {
      Some(ConstantInfo::InductInfo(v)) => v,
      _ => {
        return Err(CompileError::MissingConstant {
          name: name.pretty(),
          caller: "expand_nested_block: original not an inductive".into(),
        });
      },
    };
    let ctors: Vec<ExpandedCtor> = ind
      .ctors
      .iter()
      .filter_map(|cn| match lean_env.get(cn) {
        Some(ConstantInfo::CtorInfo(c)) => Some(ExpandedCtor {
          name: c.cnst.name.clone(),
          typ: c.cnst.typ.clone(),
          n_fields: nat_to_usize(&c.num_fields),
        }),
        _ => None,
      })
      .collect();
    ctx.push_type(ExpandedMember {
      name: name.clone(),
      source_owner: name.clone(),
      typ: ind.cnst.typ.clone(),
      n_params,
      n_indices: nat_to_usize(&ind.num_indices),
      ctors,
    });
  }

  let n_originals = ctx.types.len();

  // Canonicalize constructor types: replace alias references with
  // representative names. This prevents false nested detections where
  // an alias (B) in a constructor is treated as an external inductive
  // when the block only contains the representative (A).
  //
  // One shared cache across every ctor/type in the block: all callers use
  // the same `alias_to_rep`, so DAG-shared subterms (common in Mathlib
  // inductives with repeated implicit-arg types) collapse to a single
  // rewrite instead of being re-traversed per member.
  if !alias_to_rep.is_empty() {
    let mut alias_cache: FxHashMap<Hash, LeanExpr> = FxHashMap::default();
    for member in &mut ctx.types {
      for ctor in &mut member.ctors {
        ctor.typ =
          canonicalize_const_names(&ctor.typ, alias_to_rep, &mut alias_cache);
      }
      member.typ =
        canonicalize_const_names(&member.typ, alias_to_rep, &mut alias_cache);
    }
  }

  // Queue-based scan: process each type's constructors. A fresh
  // memoization cache is allocated per constructor because `replace_all_nested`
  // closes over `as_fvars` and `source_owner`, both of which differ between
  // constructors — so cached rewrites from one constructor are not reusable
  // for another. Within a single constructor the walk is deterministic, so
  // the cache turns DAG traversal from O(shared × nodes) into O(nodes).
  let mut qi = 0;
  while qi < ctx.types.len() {
    let n_ctors = ctx.types[qi].ctors.len();
    let source_owner = ctx.types[qi].source_owner.clone();
    for ci in 0..n_ctors {
      let ctor_type = ctx.types[qi].ctors[ci].typ.clone();

      // Peel params, re-creating FVars per constructor for binding info.
      let (as_fvars, as_decls, peeled) =
        forall_telescope(&ctor_type, n_params, "cp", qi * 100 + ci);

      // Replace all nested occurrences in the peeled body.
      let mut walk_cache: FxHashMap<Hash, LeanExpr> = FxHashMap::default();
      let replaced = ctx.replace_all_nested(
        &peeled,
        &as_fvars,
        &source_owner,
        &mut walk_cache,
      );

      // Re-wrap with constructor-local params.
      let new_ctor_type = mk_forall(replaced, &as_decls);
      ctx.types[qi].ctors[ci].typ = new_ctor_type;
    }
    qi += 1;
  }

  Ok(ExpandedBlock {
    types: ctx.types,
    aux_to_nested: ctx.aux_to_nested,
    aux_ctor_map: ctx.aux_ctor_map,
    block_param_fvars,
    n_originals,
    level_params,
  })
}

// =========================================================================
// Canonical structural sort of the aux section
// =========================================================================

/// Reorder the aux section of an `ExpandedBlock` structurally so that
/// the canonical (compile-side) aux ordering is independent of Lean's
/// source-walk discovery order.
///
/// Returns `perm: Vec<usize>` mapping original aux index (0-based, where
/// 0 = first aux after the `n_originals` user members) to the new
/// canonical aux index. Callers use the permutation to:
/// - permute source-aux motives/minors at call sites (`surgery.rs`)
/// - register Lean source aux rec names (`X.rec_{source_j+1}`) at the
///   canonical DPrj/RPrj position `perm[source_j]`
///
/// Each aux member is compared using the same structural order as normal
/// mutual block constants, with original members fixed as a prefix in the
/// mutual context. The compared data includes:
/// - `aux_to_nested[name]`: the normalized nested-app with block-param
///   FVars (the unique semantic identity of this aux, independent of the
///   aux's own name or position)
/// - `member.typ`: the aux inductive's type
/// - each ctor's `typ`
///
/// Renaming is cascaded through every site that references aux names:
/// - `aux_to_nested` keys (the aux name → nested-expr map)
/// - `aux_ctor_map` keys (aux-ctor names carry the aux prefix) and their
///   aux-ind component
/// - every member's ctor types (aux inductives may reference sibling
///   auxes via `Const` nodes) and the member's own type
///
/// Aux names themselves are internal (`<all0>._nested.<Ext>_N`) and never
/// appear in user-visible env: `RestoreCtx` converts them back to
/// `ExtInd spec_params` expressions during recursor emission. So renaming
/// them by canonical index is purely an internal-labeling change.
pub(crate) fn sort_aux_by_partition_refinement(
  expanded: &mut ExpandedBlock,
  stt: &crate::ix::compile::CompileState,
) -> Result<Vec<usize>, CompileError> {
  let n_originals = expanded.n_originals;
  let n_total = expanded.types.len();
  if n_total <= n_originals {
    return Ok(Vec::new());
  }
  let n_aux = n_total - n_originals;

  // Sort aux members using the same name-insensitive structural comparison
  // used for non-expanded block members. References to source originals inside
  // aux signatures intentionally resolve by compiled address rather than by a
  // fixed positional MutRef, so alpha-equivalent originals collapse to the same
  // aux signature. If any referenced original is unresolved, compare_expr now
  // errors instead of falling back to namespace-sensitive name hashes.
  use crate::ix::compile::{BlockCache, sort_consts};
  use crate::ix::env::{ConstantVal, ConstructorVal, InductiveVal};
  use crate::ix::mutual::{Ind, MutConst};

  let level_params = expanded.level_params.clone();

  // Build MutConst::Indc for all members, then sort only the aux tail. The
  // original prefix is still needed so the aux slice can borrow stable
  // `MutConst`s from one vector; source-original references inside aux
  // expressions intentionally remain external references and compare by
  // resolved content address.
  let all_mut_consts: Vec<MutConst> = expanded
    .types
    .iter()
    .map(|mem| {
      let ctor_names: Vec<Name> =
        mem.ctors.iter().map(|c| c.name.clone()).collect();
      let ctors: Vec<ConstructorVal> = mem
        .ctors
        .iter()
        .enumerate()
        .map(|(ci, c)| ConstructorVal {
          cnst: ConstantVal {
            name: c.name.clone(),
            typ: c.typ.clone(),
            level_params: level_params.clone(),
          },
          induct: mem.name.clone(),
          cidx: Nat::from(ci as u64),
          num_params: Nat::from(mem.n_params as u64),
          num_fields: Nat::from(c.n_fields as u64),
          is_unsafe: false,
        })
        .collect();
      MutConst::Indc(Ind {
        ind: InductiveVal {
          cnst: ConstantVal {
            name: mem.name.clone(),
            typ: mem.typ.clone(),
            level_params: level_params.clone(),
          },
          num_params: Nat::from(mem.n_params as u64),
          num_indices: Nat::from(mem.n_indices as u64),
          all: vec![],
          ctors: ctor_names,
          num_nested: Nat::from(0u64),
          is_rec: false,
          is_unsafe: false,
          is_reflexive: false,
        },
        ctors,
      })
    })
    .collect();

  let aux_consts: Vec<&MutConst> =
    all_mut_consts[n_originals..].iter().collect();
  let mut cache = BlockCache::default();

  let sorted_classes = sort_consts(&aux_consts, &mut cache, stt)?;

  let n_canon = sorted_classes.len();

  // Build old_j → canonical_j. `sort_consts` returns equivalence classes, so
  // duplicate auxes intentionally map many-to-one into a single canonical slot.
  let mut perm = vec![usize::MAX; n_aux];
  let mut sorted_order: Vec<usize> = Vec::with_capacity(n_canon);
  for (canonical_j, class) in sorted_classes.iter().enumerate() {
    for (member_j, member) in class.iter().enumerate() {
      let Some(old_j) = expanded.types[n_originals..]
        .iter()
        .position(|m| m.name == member.name())
      else {
        return Err(CompileError::InvalidMutualBlock {
          reason: format!(
            "aux sort returned unknown member {}",
            member.name().pretty()
          ),
        });
      };
      perm[old_j] = canonical_j;
      if member_j == 0 {
        sorted_order.push(old_j);
      }
    }
  }
  if perm.contains(&usize::MAX) {
    return Err(CompileError::InvalidMutualBlock {
      reason: "aux sort did not assign every auxiliary member".into(),
    });
  }

  // Short-circuit if already in canonical order.
  if n_canon == n_aux && perm.iter().enumerate().all(|(i, &p)| i == p) {
    return Ok(perm);
  }

  // Compute the `<all0>._nested` prefix. Every aux name is of shape
  // `Name::str(Name::str(all0, "_nested"), "<Ext>_N")`. We'll use this
  // prefix to rebuild canonical aux names after sorting.
  let nested_prefix = {
    let first_aux_name = &expanded.types[n_originals].name;
    match first_aux_name.as_data() {
      crate::ix::env::NameData::Str(prefix, _, _) => prefix.clone(),
      _ => {
        return Err(CompileError::InvalidMutualBlock {
          reason: format!(
            "nested aux name is not a string name: {}",
            first_aux_name.pretty()
          ),
        });
      },
    }
  };

  // Build old_aux_name → new_aux_name rename map.
  //
  // New aux name: `<all0>._nested.<Ext>_<new_j+1>` where `<Ext>` is
  // recovered from the OLD name by stripping the trailing `_<old_j+1>`
  // suffix. This preserves the "Ext" identifier (e.g. `Array`, `Option`,
  // `List`) so downstream name-based diagnostics remain readable, while
  // canonicalizing the trailing index by sort position.
  let mut name_rename: FxHashMap<Name, Name> = FxHashMap::default();
  let mut new_aux_names: Vec<Name> = Vec::with_capacity(n_canon);
  for (new_j, &old_j) in sorted_order.iter().take(n_canon).enumerate() {
    let old_name = expanded.types[n_originals + old_j].name.clone();

    // Extract the "<Ext>" identifier from old suffix.
    let ext_name = match old_name.as_data() {
      crate::ix::env::NameData::Str(_, suffix, _) => {
        // Old suffix is "<Ext>_<old_j+1>" — strip the trailing "_<N>".
        let s: &str = suffix.as_ref();
        // Find the last underscore — everything before is "<Ext>".
        if let Some(ub) = s.rfind('_') {
          let (ext, _) = s.split_at(ub);
          ext.to_string()
        } else {
          s.to_string()
        }
      },
      _ => {
        return Err(CompileError::InvalidMutualBlock {
          reason: format!(
            "nested aux name is not a string name: {}",
            old_name.pretty()
          ),
        });
      },
    };

    let new_suffix = format!("{}_{}", ext_name, new_j + 1);
    let new_name = Name::str(nested_prefix.clone(), new_suffix);
    new_aux_names.push(new_name);
  }

  for (old_j, &canonical_j) in perm.iter().enumerate() {
    let old_name = expanded.types[n_originals + old_j].name.clone();
    name_rename.insert(old_name, new_aux_names[canonical_j].clone());
  }

  // Rewrite aux_ctor_map: both keys (aux-ctor names) and the
  // aux-inductive component of the value.
  //
  // Aux ctor names are produced by `name_replace_prefix(j_ctor_name,
  // j_name, &aux_name)` — i.e. the prefix of the ctor name is replaced
  // with the aux inductive name. Renaming the aux inductive therefore
  // requires a corresponding prefix-swap on every ctor name that starts
  // with the old aux name.
  let mut new_aux_ctor_map: FxHashMap<Name, (Name, Name)> =
    FxHashMap::default();
  for (old_ctor_name, (orig_ctor_name, old_aux_ind_name)) in
    std::mem::take(&mut expanded.aux_ctor_map)
  {
    let new_aux_ind_name = name_rename
      .get(&old_aux_ind_name)
      .cloned()
      .unwrap_or_else(|| old_aux_ind_name.clone());
    let new_ctor_name =
      name_replace_prefix(&old_ctor_name, &old_aux_ind_name, &new_aux_ind_name);
    new_aux_ctor_map
      .entry(new_ctor_name)
      .or_insert((orig_ctor_name, new_aux_ind_name));
  }
  expanded.aux_ctor_map = new_aux_ctor_map;

  // Rewrite aux_to_nested: keys rename; values (nested exprs) are
  // independent of aux name — they describe the nested semantic form,
  // not the aux name that represents it.
  let mut new_aux_to_nested: FxHashMap<Name, LeanExpr> = FxHashMap::default();
  for (old_name, nested_expr) in std::mem::take(&mut expanded.aux_to_nested) {
    let new_name =
      name_rename.get(&old_name).cloned().unwrap_or_else(|| old_name.clone());
    new_aux_to_nested.entry(new_name).or_insert(nested_expr);
  }
  expanded.aux_to_nested = new_aux_to_nested;

  // Rewrite every member's typ and ctor types to replace aux-name Const
  // references with the renamed names. Sibling auxes may reference each
  // other (e.g. `_nested.Array_3` containing `_nested.Option_1` fields),
  // so this sweep must cover user members too (in case user ctor types
  // got rewritten during expansion).
  //
  // Share a cache across every member/ctor: they all use the same
  // `name_rename_std`, and Mathlib types tend to share large implicit-arg
  // substructure across sibling ctors.
  let name_rename_std: std::collections::HashMap<Name, Name> =
    name_rename.iter().map(|(k, v)| (k.clone(), v.clone())).collect();
  let mut rename_cache: FxHashMap<Hash, LeanExpr> = FxHashMap::default();
  for member in &mut expanded.types {
    member.typ = super::expr_utils::replace_const_names_cached(
      &member.typ,
      &name_rename_std,
      &mut rename_cache,
    );
    for ctor in &mut member.ctors {
      ctor.typ = super::expr_utils::replace_const_names_cached(
        &ctor.typ,
        &name_rename_std,
        &mut rename_cache,
      );
    }
  }

  // Reorder the aux section of `expanded.types` and rewrite member/ctor
  // names to their canonical forms.
  //
  // For each new canonical position `new_j`, pick the aux at
  // `aux_tail[old_j]` (where `sorted_order[new_j] == old_j`) and
  // rename its own name + its ctors' prefixes from the old aux name to
  // the new one. We can't move out of `aux_tail` by index because we
  // pick in new_j order; clone instead (cheap — ctor vec is a small Vec).
  let aux_tail: Vec<ExpandedMember> = expanded.types.split_off(n_originals);
  let mut reordered: Vec<ExpandedMember> = Vec::with_capacity(n_canon);
  for new_j in 0..n_canon {
    let old_j = sorted_order[new_j];
    let mut mem = aux_tail[old_j].clone();
    let old_name = mem.name.clone();
    let new_name = new_aux_names[new_j].clone();
    mem.name = new_name.clone();
    for ctor in &mut mem.ctors {
      ctor.name = name_replace_prefix(&ctor.name, &old_name, &new_name);
    }
    reordered.push(mem);
  }
  expanded.types.extend(reordered);

  Ok(perm)
}

/// Compute the source-walk discovery order of nested auxiliaries by
/// running `expand_nested_block` on **source-order originals** (no alias
/// rewriting, no canonical aux-sort post-pass). Returns a vector of
/// `(ext_ind_name, normalized_spec_params)` entries, one per aux, in
/// the exact order Lean's C++ elaborator discovers them.
///
/// This walker structurally mirrors Lean's `inductive.cpp:1045`, so the
/// returned order matches Lean's aux-recursor numbering (`X.rec_1`,
/// `X.rec_2`, …). Used together with the canonical order (output of
/// `sort_aux_by_partition_refinement` on a second expansion) to compute a
/// permutation `perm[source_j] = canonical_i`.
///
/// `original_all` is the source-order Lean `InductiveVal.all` list —
/// not alpha-collapsed representatives, and not canonical-aux-sorted.
pub(crate) fn source_aux_order(
  original_all: &[Name],
  lean_env: &LeanEnv,
) -> Result<Vec<(Name, Vec<LeanExpr>)>, CompileError> {
  Ok(
    source_aux_order_with_owner(original_all, lean_env)?
      .into_iter()
      .map(|(_, head, args)| (head, args))
      .collect(),
  )
}

/// Like [`source_aux_order`], but also reports the source mutual-block member
/// whose constructor walk first discovered each auxiliary.
pub(crate) fn source_aux_order_with_owner(
  original_all: &[Name],
  lean_env: &LeanEnv,
) -> Result<Vec<(Name, Name, Vec<LeanExpr>)>, CompileError> {
  let alias_to_rep: FxHashMap<Name, Name> = FxHashMap::default();
  let expanded = expand_nested_block(original_all, lean_env, &alias_to_rep)?;
  Ok(source_aux_order_from_expanded(&expanded))
}

fn source_aux_order_from_expanded(
  expanded: &ExpandedBlock,
) -> Vec<(Name, Name, Vec<LeanExpr>)> {
  let n_originals = expanded.n_originals;

  let mut out: Vec<(Name, Name, Vec<LeanExpr>)> = Vec::new();
  for mem in expanded.types.iter().skip(n_originals) {
    // Each aux's `aux_to_nested` entry is `ExtInd.{lvls} spec_params`
    // with block-param FVars — decompose into (head_name, spec_params).
    let Some(nested_expr) = expanded.aux_to_nested.get(&mem.name) else {
      continue;
    };
    let (head, args) = decompose_apps(nested_expr);
    let head_name = match head.as_data() {
      ExprData::Const(n, _, _) => n.clone(),
      _ => continue,
    };
    out.push((mem.source_owner.clone(), head_name, args));
  }
  out
}

/// Sentinel value for "this source aux position has no canonical match
/// in the current SCC block". Used by `compute_aux_perm` to flag
/// source auxes whose spec_params reference inductives that belong to
/// a different SCC block — those auxes are handled by that block's
/// compilation, not ours.
pub(crate) const PERM_OUT_OF_SCC: usize = usize::MAX;

/// Compute the permutation mapping Lean-source aux-walk positions to
/// canonical aux positions. Returns `perm: Vec<usize>`
/// of length `n_source`, where:
///   - `perm[source_j] < n_canon` when source_j maps to a canonical
///     aux in the current SCC block, or
///   - `perm[source_j] == PERM_OUT_OF_SCC` when source_j's spec_params
///     reference inductives OUTSIDE the current SCC block — those
///     auxes belong to a different block's compilation and are skipped.
///
/// Many-to-one is permitted: multiple source indices can map to the
/// same canonical index. This happens under alpha-collapse where two
/// distinct source originals collapse to the same canonical
/// representative, making their respective `Array <orig>` auxes
/// alpha-equivalent (dedup'd in the canonical walk) while the source
/// walk sees them as separate.
///
/// Inputs:
/// - `expanded`: the canonical (post-`sort_aux_by_partition_refinement`) expanded
///   block. Auxes are in `expanded.types[n_originals..]`, structurally sorted.
/// - `original_all`: Lean's source-order inductive names (from any
///   `InductiveVal.all` in the block). Drives the second expansion that
///   reveals Lean's own aux-walk numbering. May be LARGER than the
///   current SCC block: Lean lists all members of the original mutual,
///   while `sort_consts` splits into SCCs.
/// - `lean_env`: Lean environment for both expansions.
/// - `orig_to_canon_names`: maps each original name in the current SCC
///   to its canonical class representative. Names NOT in this map are
///   out-of-SCC — source auxes that reference them get `PERM_OUT_OF_SCC`.
///
/// Returns an error if some canonical aux has no matching source. This
/// shouldn't happen because canonical members are always a subset (via
/// dedup) of what a full source walk would find.
pub(crate) fn compute_aux_perm(
  expanded: &ExpandedBlock,
  original_all: &[Name],
  lean_env: &LeanEnv,
  stt: &crate::ix::compile::CompileState,
  orig_to_canon_names: &std::collections::HashMap<Name, Name>,
) -> Result<Vec<usize>, CompileError> {
  let n_originals = expanded.n_originals;
  let canonical_aux = &expanded.types[n_originals..];
  let n_canon = canonical_aux.len();

  let alias_to_rep: FxHashMap<Name, Name> = FxHashMap::default();
  let source_expanded =
    expand_nested_block(original_all, lean_env, &alias_to_rep)?;
  let source_order = source_aux_order_from_expanded(&source_expanded);
  let n_source = source_order.len();
  let mut source_to_canon_fvar: FxHashMap<Name, Name> = FxHashMap::default();
  for (src, canon) in source_expanded
    .block_param_fvars
    .iter()
    .zip(expanded.block_param_fvars.iter())
  {
    if let (ExprData::Fvar(src_name, _), ExprData::Fvar(canon_name, _)) =
      (src.as_data(), canon.as_data())
    {
      source_to_canon_fvar.insert(src_name.clone(), canon_name.clone());
    }
  }

  // Precompute canonical (head_name, spec_params) for each canonical aux.
  //
  // Do not key by LeanExpr hash here. During auxiliary alpha-collapse the
  // canonical aux may be represented with a different source inductive name
  // than the source-walk occurrence (`Array B` vs `Array C`), even though
  // those names already resolve to the same content address. Raw LeanExpr
  // hashes intentionally include names, so matching must use semantic
  // comparison below.
  let canonical_signatures: Vec<(Name, Vec<LeanExpr>)> = canonical_aux
    .iter()
    .filter_map(|mem| {
      let nested_expr = expanded.aux_to_nested.get(&mem.name)?;
      let (head, args) = decompose_apps(nested_expr);
      let head_name = match head.as_data() {
        ExprData::Const(n, _, _) => n.clone(),
        _ => return None,
      };
      Some((head_name, args))
    })
    .collect();

  if canonical_signatures.len() != n_canon {
    return Err(CompileError::InvalidMutualBlock {
      reason: "compute_aux_perm: canonical aux missing nested_expr entries"
        .into(),
    });
  }

  // Index canonical signatures by their head-name so matching becomes
  // ≈O(n_source) instead of O(n_source × n_canon). For realistic blocks
  // the head-name buckets are small (one aux per distinct external
  // inductive occurrence) and `aux_spec_eq` already memoizes per-pair
  // structural comparison.
  let mut canon_by_head: FxHashMap<&Name, Vec<usize>> = FxHashMap::default();
  for (i, (head, _)) in canonical_signatures.iter().enumerate() {
    canon_by_head.entry(head).or_default().push(i);
  }

  // For each source aux, try to find a canonical match. If the source
  // references members not in the current SCC (orig_to_canon_names),
  // mark it as `PERM_OUT_OF_SCC`.
  let mut perm: Vec<usize> = vec![PERM_OUT_OF_SCC; n_source];

  let original_names: std::collections::HashSet<Name> =
    original_all.iter().cloned().collect();
  let mut spec_eq_cache: FxHashMap<(Hash, Hash), bool> = FxHashMap::default();
  let mut out_of_scc_cache: FxHashMap<Hash, bool> = FxHashMap::default();
  // Shared across every source aux's spec_param normalization: all
  // calls use the same `orig_to_canon_names`, so DAG-shared subterms
  // between source spec_params collapse to a single rewrite.
  let mut normalize_cache: FxHashMap<Hash, LeanExpr> = FxHashMap::default();

  for (j, (src_owner, src_head, src_specs)) in source_order.iter().enumerate() {
    // If any spec_param references an original mutual member that's NOT
    // in orig_to_canon_names, this source aux is out-of-SCC — skip it.
    // Other constants are ordinary external parameters (e.g. `String` in
    // `AssocList String Json`) and must remain part of the signature.
    let in_scc = src_specs.iter().all(|sp| {
      !has_out_of_scc_const(
        sp,
        orig_to_canon_names,
        &original_names,
        &mut out_of_scc_cache,
      )
    });
    if !in_scc {
      continue;
    }

    // Normalize source spec_params using orig_to_canon_names so they
    // match the canonical walk's view.
    let normalized: Vec<LeanExpr> = src_specs
      .iter()
      .map(|sp| {
        super::expr_utils::replace_const_names_cached(
          sp,
          orig_to_canon_names,
          &mut normalize_cache,
        )
      })
      .collect();
    // Consult the head-name bucket first. If no canonical aux shares
    // this head, there can't be a match.
    let canon_idx = canon_by_head.get(src_head).and_then(|candidates| {
      candidates.iter().copied().find(|&i| {
        let (_, canon_specs) = &canonical_signatures[i];
        canon_specs.len() == normalized.len()
          && canon_specs.iter().zip(normalized.iter()).all(|(canon, src)| {
            aux_spec_eq(
              canon,
              src,
              stt,
              &source_to_canon_fvar,
              &mut spec_eq_cache,
            )
          })
      })
    });

    // If this source aux was discovered while scanning a constructor from a
    // different split SCC, it belongs to the full Lean source numbering but
    // not necessarily to this canonical block. Example:
    //   Z.mk : List Z
    //   X.mk : Option Z
    // while compiling the split {Z} SCC, `Option Z` mentions only in-SCC
    // names but was discovered from `X.mk`; if {Z}'s canonical expansion
    // doesn't contain `Option Z`, skip it instead of treating it as a broken
    // in-SCC source mapping.
    let Some(canon_idx) = canon_idx else {
      if !orig_to_canon_names.contains_key(src_owner) {
        continue;
      }
      return Err(CompileError::InvalidMutualBlock {
        reason: format!(
          "compute_aux_perm: no canonical match for in-SCC source aux #{j} owned by {} (head={})",
          src_owner.pretty(),
          src_head.pretty(),
        ),
      });
    };

    perm[j] = canon_idx;
  }

  // Sanity: every canonical aux must have at least one source mapping
  // to it. Otherwise the canonical walk produced an aux that the
  // source walk never discovered — shouldn't happen since canonical
  // dedup only merges, never creates.
  let mut covered = vec![false; n_canon];
  for &p in &perm {
    if p != PERM_OUT_OF_SCC && p < n_canon {
      covered[p] = true;
    }
  }
  if let Some((i, _)) = covered.iter().enumerate().find(|(_, c)| !**c) {
    return Err(CompileError::InvalidMutualBlock {
      reason: format!(
        "compute_aux_perm: canonical aux #{i} has no source mapping (canonical produced an aux that source walk missed)",
      ),
    });
  }

  Ok(perm)
}

/// Semantic equality for nested auxiliary spec parameters.
///
/// `sort_aux_by_partition_refinement` canonicalizes aux motives by structural content,
/// not by raw Lean names. Source-walk signatures therefore need the same notion
/// of equality: constants are equal if their names are equal or if both names
/// already resolve to the same compiled address. Everything else is compared
/// structurally, ignoring mdata and level parameter names.
fn aux_spec_eq(
  canon: &LeanExpr,
  src: &LeanExpr,
  stt: &crate::ix::compile::CompileState,
  source_to_canon_fvar: &FxHashMap<Name, Name>,
  cache: &mut FxHashMap<(Hash, Hash), bool>,
) -> bool {
  let canon = crate::ix::congruence::strip_mdata(canon);
  let src = crate::ix::congruence::strip_mdata(src);

  let key = (*canon.get_hash(), *src.get_hash());
  if let Some(cached) = cache.get(&key) {
    return *cached;
  }

  let result = match (canon.as_data(), src.as_data()) {
    (ExprData::Bvar(a, _), ExprData::Bvar(b, _)) => a == b,
    (ExprData::Fvar(a, _), ExprData::Fvar(b, _)) => {
      source_to_canon_fvar.get(b).map_or(a == b, |expected| a == expected)
    },
    (ExprData::Sort(a, _), ExprData::Sort(b, _)) => {
      crate::ix::congruence::level_alpha_eq(a, b).is_ok()
    },
    (
      ExprData::Const(a_name, a_lvls, _),
      ExprData::Const(b_name, b_lvls, _),
    ) => {
      if a_lvls.len() != b_lvls.len()
        || a_lvls
          .iter()
          .zip(b_lvls.iter())
          .any(|(a, b)| crate::ix::congruence::level_alpha_eq(a, b).is_err())
      {
        return false;
      }
      if a_name == b_name {
        return true;
      }
      match (stt.resolve_addr(a_name), stt.resolve_addr(b_name)) {
        (Some(a_addr), Some(b_addr)) => a_addr == b_addr,
        _ => false,
      }
    },
    (ExprData::App(a_f, a_arg, _), ExprData::App(b_f, b_arg, _)) => {
      aux_spec_eq(a_f, b_f, stt, source_to_canon_fvar, cache)
        && aux_spec_eq(a_arg, b_arg, stt, source_to_canon_fvar, cache)
    },
    (ExprData::Lam(_, a_t, a_b, _, _), ExprData::Lam(_, b_t, b_b, _, _))
    | (
      ExprData::ForallE(_, a_t, a_b, _, _),
      ExprData::ForallE(_, b_t, b_b, _, _),
    ) => {
      aux_spec_eq(a_t, b_t, stt, source_to_canon_fvar, cache)
        && aux_spec_eq(a_b, b_b, stt, source_to_canon_fvar, cache)
    },
    (
      ExprData::LetE(_, a_t, a_v, a_b, _, _),
      ExprData::LetE(_, b_t, b_v, b_b, _, _),
    ) => {
      aux_spec_eq(a_t, b_t, stt, source_to_canon_fvar, cache)
        && aux_spec_eq(a_v, b_v, stt, source_to_canon_fvar, cache)
        && aux_spec_eq(a_b, b_b, stt, source_to_canon_fvar, cache)
    },
    (
      ExprData::Proj(a_name, a_idx, a_val, _),
      ExprData::Proj(b_name, b_idx, b_val, _),
    ) => {
      a_idx == b_idx
        && (a_name == b_name
          || matches!(
            (stt.resolve_addr(a_name), stt.resolve_addr(b_name)),
            (Some(a_addr), Some(b_addr)) if a_addr == b_addr
          ))
        && aux_spec_eq(a_val, b_val, stt, source_to_canon_fvar, cache)
    },
    (ExprData::Lit(a, _), ExprData::Lit(b, _)) => a == b,
    _ => false,
  };
  cache.insert(key, result);
  result
}

/// Check whether an expression contains any `Const(name, _)` where
/// `name` is NOT in the provided name map. Used by `compute_aux_perm`
/// to detect source auxes whose spec_params reference inductives that
/// belong to a different SCC block.
///
/// `cache` memoizes the result per subterm hash for the duration of a
/// single `compute_aux_perm` call. Without memoization this walks the
/// full DAG for every spec_param, and Mathlib expressions have heavy
/// hash-cons sharing — the realized cost becomes exponential for
/// diamond-shaped types (a `TensorProduct` with shared param subterms
/// fans out). With memoization each unique subterm is visited once.
fn has_out_of_scc_const(
  expr: &LeanExpr,
  in_scc_names: &std::collections::HashMap<Name, Name>,
  original_names: &std::collections::HashSet<Name>,
  cache: &mut FxHashMap<Hash, bool>,
) -> bool {
  let key = *expr.get_hash();
  if let Some(&cached) = cache.get(&key) {
    return cached;
  }
  let result = match expr.as_data() {
    ExprData::Const(name, _, _) => {
      original_names.contains(name) && !in_scc_names.contains_key(name)
    },
    ExprData::App(f, a, _) => {
      has_out_of_scc_const(f, in_scc_names, original_names, cache)
        || has_out_of_scc_const(a, in_scc_names, original_names, cache)
    },
    ExprData::Lam(_, t, b, _, _) | ExprData::ForallE(_, t, b, _, _) => {
      has_out_of_scc_const(t, in_scc_names, original_names, cache)
        || has_out_of_scc_const(b, in_scc_names, original_names, cache)
    },
    ExprData::LetE(_, t, v, b, _, _) => {
      has_out_of_scc_const(t, in_scc_names, original_names, cache)
        || has_out_of_scc_const(v, in_scc_names, original_names, cache)
        || has_out_of_scc_const(b, in_scc_names, original_names, cache)
    },
    ExprData::Proj(_, _, val, _) => {
      has_out_of_scc_const(val, in_scc_names, original_names, cache)
    },
    ExprData::Mdata(_, inner, _) => {
      has_out_of_scc_const(inner, in_scc_names, original_names, cache)
    },
    _ => false,
  };
  cache.insert(key, result);
  result
}

/// Rewrite Const names in an expression using a name map.
///
/// For each `Const(name, levels)` where `name` is in `name_map`, replaces
/// it with `Const(name_map[name], levels)`. Used to canonicalize alias
/// references to representative names before nested expansion.
///
/// The `cache` is a caller-owned memoization table keyed on expression
/// hash. The seed-loop caller in `expand_nested_block` rewrites every
/// ctor and inductive type in the block against the same `name_map`, so
/// a shared cache collapses DAG-shared subterms to a single rewrite.
fn canonicalize_const_names(
  expr: &LeanExpr,
  name_map: &FxHashMap<Name, Name>,
  cache: &mut FxHashMap<Hash, LeanExpr>,
) -> LeanExpr {
  let key = *expr.get_hash();
  if let Some(cached) = cache.get(&key) {
    return cached.clone();
  }
  let result = match expr.as_data() {
    ExprData::Const(name, levels, _) => {
      if let Some(new_name) = name_map.get(name) {
        LeanExpr::cnst(new_name.clone(), levels.clone())
      } else {
        expr.clone()
      }
    },
    ExprData::App(f, a, _) => LeanExpr::app(
      canonicalize_const_names(f, name_map, cache),
      canonicalize_const_names(a, name_map, cache),
    ),
    ExprData::Lam(n, t, b, bi, _) => LeanExpr::lam(
      n.clone(),
      canonicalize_const_names(t, name_map, cache),
      canonicalize_const_names(b, name_map, cache),
      bi.clone(),
    ),
    ExprData::ForallE(n, t, b, bi, _) => LeanExpr::all(
      n.clone(),
      canonicalize_const_names(t, name_map, cache),
      canonicalize_const_names(b, name_map, cache),
      bi.clone(),
    ),
    ExprData::LetE(n, t, v, b, nd, _) => LeanExpr::letE(
      n.clone(),
      canonicalize_const_names(t, name_map, cache),
      canonicalize_const_names(v, name_map, cache),
      canonicalize_const_names(b, name_map, cache),
      *nd,
    ),
    ExprData::Proj(n, i, e, _) => LeanExpr::proj(
      n.clone(),
      i.clone(),
      canonicalize_const_names(e, name_map, cache),
    ),
    ExprData::Mdata(md, e, _) => {
      LeanExpr::mdata(md.clone(), canonicalize_const_names(e, name_map, cache))
    },
    _ => expr.clone(),
  };
  cache.insert(key, result.clone());
  result
}

/// Replace `old_prefix` in a Name with `new_prefix`.
///
/// Example: `name_replace_prefix("A.B.mk", "A.B", "X.Y")` → `"X.Y.mk"`
fn name_replace_prefix(
  name: &Name,
  old_prefix: &Name,
  new_prefix: &Name,
) -> Name {
  match name.strip_prefix(old_prefix) {
    Some(suffix) => new_prefix.clone().append_components(&suffix),
    None => name.clone(),
  }
}

/// Convert an expression from constructor-local param FVars (`as_fvars`)
/// to block param FVars (`block_param_fvars`).
///
/// Matches C++ `replace_params`: abstract over `As`, then instantiate with
/// `m_params`.
fn replace_params_expr(
  e: &LeanExpr,
  as_fvars: &[LeanExpr],
  block_param_fvars: &[LeanExpr],
) -> LeanExpr {
  if as_fvars.is_empty() {
    return e.clone();
  }
  let fvar_map: FxHashMap<Name, LeanExpr> = as_fvars
    .iter()
    .zip(block_param_fvars.iter())
    .filter_map(|(local, block)| match local.as_data() {
      ExprData::Fvar(n, _) => Some((n.clone(), block.clone())),
      _ => None,
    })
    .collect();
  replace_fvars(e, &fvar_map)
}

fn replace_fvars(
  e: &LeanExpr,
  fvar_map: &FxHashMap<Name, LeanExpr>,
) -> LeanExpr {
  match e.as_data() {
    ExprData::Fvar(n, _) => {
      fvar_map.get(n).cloned().unwrap_or_else(|| e.clone())
    },
    ExprData::App(f, a, _) => {
      LeanExpr::app(replace_fvars(f, fvar_map), replace_fvars(a, fvar_map))
    },
    ExprData::Lam(n, t, b, bi, _) => LeanExpr::lam(
      n.clone(),
      replace_fvars(t, fvar_map),
      replace_fvars(b, fvar_map),
      bi.clone(),
    ),
    ExprData::ForallE(n, t, b, bi, _) => LeanExpr::all(
      n.clone(),
      replace_fvars(t, fvar_map),
      replace_fvars(b, fvar_map),
      bi.clone(),
    ),
    ExprData::LetE(n, t, v, b, nd, _) => LeanExpr::letE(
      n.clone(),
      replace_fvars(t, fvar_map),
      replace_fvars(v, fvar_map),
      replace_fvars(b, fvar_map),
      *nd,
    ),
    ExprData::Proj(n, i, e, _) => {
      LeanExpr::proj(n.clone(), i.clone(), replace_fvars(e, fvar_map))
    },
    ExprData::Mdata(md, e, _) => {
      LeanExpr::mdata(md.clone(), replace_fvars(e, fvar_map))
    },
    _ => e.clone(),
  }
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
) -> LeanExpr {
  match e.as_data() {
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
      ),
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
      ),
    ),
    _ => {
      let (head, args) = decompose_apps(e);
      let ExprData::Const(head_name, _, _) = head.as_data() else {
        return e.clone();
      };
      if head_name != original_ind || args.len() < original_n_params {
        return e.clone();
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
  }
}

// =========================================================================
// Expression helpers
// =========================================================================

/// Check if any `Const` or `Proj` name in `expr` is in `names`.
///
/// Uses an explicit stack to avoid recursion. Analogous to the kernel's
/// `expr_mentions_any_addr` (`src/ix/kernel/tc.rs:459-501`).
///
/// `names` is a hash set so each check is O(1). The hot caller
/// (`ExpandCtx::replace_if_nested`) tests this for every parameter arg of
/// every external inductive occurrence seen during a constructor walk; a
/// Vec-with-`contains` used to dominate the profile for large blocks.
pub(super) fn expr_mentions_any_name(
  expr: &LeanExpr,
  names: &FxHashSet<Name>,
) -> bool {
  if names.is_empty() {
    return false;
  }
  let mut stack: Vec<&LeanExpr> = vec![expr];
  while let Some(e) = stack.pop() {
    match e.as_data() {
      ExprData::Const(n, _, _) => {
        if names.contains(n) {
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
      ExprData::Proj(type_name, _, val, _) => {
        if names.contains(type_name) {
          return true;
        }
        stack.push(val);
      },
      ExprData::Mdata(_, inner, _) => {
        stack.push(inner);
      },
      // BVar, FVar, MVar, Sort, Lit — no constant names.
      _ => {},
    }
  }
  false
}

/// Check if an expression contains any invalid reference for a spec_param:
/// a free BVar (from domain-local foralls) or an FVar not in the block's
/// parameter set (from field-local binders).
///
/// Valid spec_params should contain only block-param FVars, constants, sorts,
/// and literals — nothing that depends on field-local or domain-local bindings.
fn has_invalid_spec_ref(expr: &LeanExpr, param_fvar_names: &[Name]) -> bool {
  let mut stack: Vec<(&LeanExpr, u64)> = vec![(expr, 0)];
  while let Some((e, depth)) = stack.pop() {
    match e.as_data() {
      ExprData::Bvar(idx, _) => {
        // Free BVar = domain-local variable leaked into spec_param.
        if nat_to_u64(idx) >= depth {
          return true;
        }
      },
      ExprData::Fvar(n, _) => {
        // FVar not in param set = field-local variable.
        if !param_fvar_names.contains(n) {
          return true;
        }
      },
      ExprData::App(f, a, _) => {
        stack.push((f, depth));
        stack.push((a, depth));
      },
      ExprData::Lam(_, t, b, _, _) | ExprData::ForallE(_, t, b, _, _) => {
        stack.push((t, depth));
        stack.push((b, depth + 1));
      },
      ExprData::LetE(_, t, v, b, _, _) => {
        stack.push((t, depth));
        stack.push((v, depth));
        stack.push((b, depth + 1));
      },
      ExprData::Proj(_, _, val, _) => stack.push((val, depth)),
      ExprData::Mdata(_, inner, _) => stack.push((inner, depth)),
      _ => {},
    }
  }
  false
}

// =========================================================================
// Flat block construction
// =========================================================================

/// Internal flat member during detection — spec_params in FVar form.
#[derive(Clone)]
struct FvarFlatMember {
  name: Name,
  /// Spec_params as FVar expressions referencing block param FVars.
  spec_params: Vec<LeanExpr>,
  occurrence_level_args: Vec<Level>,
  own_params: usize,
  n_indices: usize,
}

/// Build a flat block from an ordered list of original inductives.
///
/// Detects nested inductive occurrences in constructor fields and creates
/// auxiliary entries. The returned vector starts with the originals (in order)
/// followed by any auxiliary entries discovered during the queue-based scan.
///
/// Internally works in FVar space: block parameters are represented as FVars
/// during detection, and `forall_telescope` opens constructor field binders.
/// This avoids manual BVar depth tracking — field-local dependencies are
/// caught by checking for non-param FVars in the detected spec_params.
///
/// Ported from the kernel's `build_flat_block` (`src/ix/kernel/inductive.rs:364-475`).
pub(crate) fn build_compile_flat_block(
  ordered_originals: &[Name],
  lean_env: &LeanEnv,
) -> Result<Vec<CompileFlatMember>, CompileError> {
  build_compile_flat_block_with_overlay(ordered_originals, lean_env, None)
}

/// Like `build_compile_flat_block`, but checks an optional overlay
/// environment first for all lookups. Used by the expand/restore path
/// to scan expanded constructor types (where nested refs are already
/// replaced with auxiliary const applications).
pub(crate) fn build_compile_flat_block_with_overlay(
  ordered_originals: &[Name],
  lean_env: &LeanEnv,
  overlay: Option<&LeanEnv>,
) -> Result<Vec<CompileFlatMember>, CompileError> {
  let first_name = ordered_originals.first().ok_or_else(|| {
    CompileError::InvalidMutualBlock {
      reason: "build_compile_flat_block: empty ordered_originals".into(),
    }
  })?;
  let first_ind_ref = overlay
    .and_then(|o| o.get(first_name))
    .or_else(|| lean_env.get(first_name));
  let first_ind = match first_ind_ref {
    Some(ConstantInfo::InductInfo(v)) => v,
    _ => {
      return Err(CompileError::MissingConstant {
        name: first_name.pretty(),
        caller: "build_compile_flat_block: first original not an inductive"
          .into(),
      });
    },
  };
  let n_params = nat_to_usize(&first_ind.num_params);

  // Create canonical block-parameter FVars by opening the first inductive's
  // type. These FVars represent the shared parameters across the mutual block
  // and are used as the "param namespace" during detection.
  let (block_param_fvars, block_param_decls, _) =
    forall_telescope(&first_ind.cnst.typ, n_params, "bp", 0);
  let block_param_fvar_names: Vec<Name> =
    block_param_decls.iter().map(|d| d.fvar_name.clone()).collect();

  let mut flat: Vec<FvarFlatMember> = Vec::new();
  // Dedup tracker: (ext_ind_name, spec_param content hashes).
  let mut aux_seen: Vec<(Name, Vec<Hash>)> = Vec::new();

  // Precompute the set of block original names once. Threaded through
  // `try_detect_nested_fvar` for O(1) "is head in the block?" checks on
  // every constructor field.
  let block_name_set: FxHashSet<Name> =
    ordered_originals.iter().cloned().collect();

  // Seed with original block inductives. For originals, spec_params are
  // the block param FVars themselves (identity specialization).
  for name in ordered_originals {
    let ind_ref =
      overlay.and_then(|o| o.get(name)).or_else(|| lean_env.get(name));
    let ind = match ind_ref {
      Some(ConstantInfo::InductInfo(v)) => v,
      _ => {
        return Err(CompileError::MissingConstant {
          name: name.pretty(),
          caller: "build_compile_flat_block: original not an inductive".into(),
        });
      },
    };
    flat.push(FvarFlatMember {
      name: name.clone(),
      spec_params: block_param_fvars.clone(),
      occurrence_level_args: ind
        .cnst
        .level_params
        .iter()
        .map(|lp| Level::param(lp.clone()))
        .collect(),
      own_params: nat_to_usize(&ind.num_params),
      n_indices: nat_to_usize(&ind.num_indices),
    });
  }

  // Queue-based processing: scan each member's constructors for nested
  // occurrences. New auxiliary entries are appended to `flat` and will be
  // processed in subsequent iterations.
  let mut qi = 0;
  while qi < flat.len() {
    let member = flat[qi].clone();
    qi += 1;

    // Look up the inductive to get its constructor names and level params.
    let member_ref = overlay
      .and_then(|o| o.get(&member.name))
      .or_else(|| lean_env.get(&member.name));
    let (ctor_names, level_params) = match member_ref {
      Some(ConstantInfo::InductInfo(v)) => {
        (v.ctors.clone(), v.cnst.level_params.clone())
      },
      _ => continue,
    };

    for ctor_name in &ctor_names {
      let ctor_ref = overlay
        .and_then(|o| o.get(ctor_name))
        .or_else(|| lean_env.get(ctor_name));
      let (ctor_n_fields, ctor_typ) = match ctor_ref {
        Some(ConstantInfo::CtorInfo(c)) => {
          let fields = nat_to_usize(&c.num_fields);
          (fields, c.cnst.typ.clone())
        },
        _ => continue,
      };

      // Substitute the external inductive's level params with the concrete
      // universe args from the occurrence. For original members, this is
      // identity (Level::param(lp) for each lp). For auxiliary members,
      // these are the concrete levels extracted from the nested Const node.
      let ctor_ty_inst =
        subst_levels(&ctor_typ, &level_params, &member.occurrence_level_args);

      // Peel own_params foralls, substituting with the member's FVar-form
      // spec_params. After this, `cur` has block-param FVars where the
      // constructor originally referenced its own params.
      let mut cur = ctor_ty_inst;
      for j in 0..member.own_params {
        match cur.as_data() {
          ExprData::ForallE(_, _, body, _, _) => {
            let sp = if j < member.spec_params.len() {
              &member.spec_params[j]
            } else {
              // Shouldn't happen for well-formed types.
              continue;
            };
            cur = instantiate1(body, sp);
          },
          _ => break,
        }
      }

      // Open field foralls into FVars via forall_telescope. Each field
      // domain is now in FVar space: block-param FVars for parameters,
      // field FVars for earlier fields. No manual depth tracking needed.
      let (_, field_decls, _) = forall_telescope(&cur, ctor_n_fields, "nf", 0);

      for decl in &field_decls {
        try_detect_nested_fvar(
          &decl.domain,
          &block_name_set,
          &mut flat,
          &mut aux_seen,
          lean_env,
          overlay,
          &block_param_fvar_names,
        );
      }
    }
  }

  // Maximize occurrence levels: Lean uses a single set of levels per external
  // inductive name across ALL occurrences in the block. When `Array` appears
  // with both `Array.{u}` (containing Type u) and `Array.{max u v}` (containing
  // Type (max u v)), Lean uses `max u v` for all Array auxiliaries.
  //
  // For each external inductive name, compute the pointwise max of all
  // occurrence_level_args, then apply that to all auxiliaries with that name.
  maximize_occurrence_levels(&mut flat, ordered_originals.len());

  // Convert FVar-form spec_params back to BVar form for the output.
  // Abstract block-param FVars outermost-first: _bp_0 → BVar(n-1),
  // _bp_1 → BVar(n-2), ..., _bp_{n-1} → BVar(0).
  Ok(
    flat
      .into_iter()
      .map(|entry| {
        let spec_params =
          abstract_spec_params_to_bvars(&entry.spec_params, &block_param_decls);
        CompileFlatMember {
          name: entry.name,
          spec_params,
          // Preserve the original level structure from Const nodes in
          // constructor types. The Lean kernel's restore_nested uses these
          // exact levels, so structural congruence requires we match their
          // associativity (typically left-associated from the elaborator).
          occurrence_level_args: entry.occurrence_level_args.clone(),
          own_params: entry.own_params,
          n_indices: entry.n_indices,
        }
      })
      .collect(),
  )
}

/// Convert spec_params from FVar form (referencing block-param FVars) back to
/// BVar form using batch abstraction.
///
/// Outermost param `_bp_0` ends up at `BVar(n_params - 1)` and innermost
/// `_bp_{n-1}` at `BVar(0)`, matching the convention used by `recursor.rs`.
fn abstract_spec_params_to_bvars(
  spec_params: &[LeanExpr],
  block_param_decls: &[LocalDecl],
) -> Vec<LeanExpr> {
  let n = block_param_decls.len();
  if n == 0 {
    return spec_params.to_vec();
  }
  let fvar_map: FxHashMap<Name, usize> = block_param_decls
    .iter()
    .enumerate()
    .map(|(i, d)| (d.fvar_name.clone(), i))
    .collect();
  spec_params.iter().map(|sp| batch_abstract(sp, &fvar_map, n, 0)).collect()
}

/// Check if a field domain contains a nested inductive occurrence and, if so,
/// add an auxiliary entry to the flat block.
///
/// A nested occurrence is: after peeling foralls, the result is `ExtInd args`
/// where `ExtInd` is a previously-declared inductive (not in our block) and
/// some parameter arg mentions a block or flat-block inductive.
///
/// Field domains are in FVar space (block-param FVars + field FVars), so
/// field-local dependencies are detected by checking for non-param FVars
/// rather than BVar range arithmetic.
///
/// Ported from the kernel's `try_detect_nested` (`src/ix/kernel/inductive.rs:483-612`).
/// Maximize occurrence levels across all auxiliaries sharing the same external
/// inductive name.
///
/// Lean's kernel computes a single set of universe levels per external inductive
/// across all its nested occurrences in the block. When `Array` appears as both
/// `Array.{u}` (containing `Type u`) and `Array.{max u v}` (containing
/// `Type (max u v)`), all Array auxiliaries use `max u v`.
///
/// This function computes the pointwise max of `occurrence_level_args` across
/// all auxiliaries with the same `name`, then updates all of them.
fn maximize_occurrence_levels(flat: &mut [FvarFlatMember], n_originals: usize) {
  use crate::ix::env::LevelData;
  use rustc_hash::FxHashMap;

  // Group auxiliary members by external inductive name.
  // Key: ext_ind name, Value: (n_levels, merged_levels)
  let mut max_levels: FxHashMap<Name, Vec<Level>> = FxHashMap::default();

  for entry in flat.iter().skip(n_originals) {
    let merged = max_levels
      .entry(entry.name.clone())
      .or_insert_with(|| entry.occurrence_level_args.clone());
    // Pointwise max: for each level position, take the broader level.
    if merged.len() == entry.occurrence_level_args.len() {
      for (m, e) in merged.iter_mut().zip(entry.occurrence_level_args.iter()) {
        *m = level_max_raw(m, e);
      }
    }
  }

  // Apply the maximized levels to all auxiliaries.
  for entry in flat.iter_mut().skip(n_originals) {
    if let Some(merged) = max_levels.get(&entry.name)
      && merged.len() == entry.occurrence_level_args.len()
    {
      entry.occurrence_level_args = merged.clone();
    }
  }

  /// Raw level max: `max(a, b)` with only zero elimination.
  /// Matches Lean's `mkLevelMax` behavior.
  fn level_max_raw(a: &Level, b: &Level) -> Level {
    if a == b {
      return a.clone();
    }
    if matches!(a.as_data(), LevelData::Zero(_)) {
      return b.clone();
    }
    if matches!(b.as_data(), LevelData::Zero(_)) {
      return a.clone();
    }
    Level::max(a.clone(), b.clone())
  }
}

fn try_detect_nested_fvar(
  dom: &LeanExpr,
  block_names: &FxHashSet<Name>,
  flat: &mut Vec<FvarFlatMember>,
  aux_seen: &mut Vec<(Name, Vec<Hash>)>,
  lean_env: &LeanEnv,
  overlay: Option<&LeanEnv>,
  block_param_fvar_names: &[Name],
) {
  // Peel foralls structurally to get to the result type. No WHNF needed —
  // finalized Lean env types are already in normal form. Note: we do NOT
  // use forall_telescope here — the peeled binders introduce BVars in the
  // body, which `has_invalid_spec_ref` will flag if they leak into a
  // spec_param (domain-local dependency).
  let mut cur = dom.clone();
  while let ExprData::ForallE(_, _, body, _, _) = cur.as_data() {
    cur = body.clone();
  }

  // Decompose into head and args.
  let (head, args) = decompose_apps(&cur);
  let (head_name, head_levels) = match head.as_data() {
    ExprData::Const(name, levels, _) => (name.clone(), levels.clone()),
    _ => return,
  };

  // Skip if head is in the original block (direct recursive, not nested).
  if block_names.contains(&head_name) {
    return;
  }
  // Skip if head is already a non-auxiliary flat member.
  if flat.iter().any(|m| m.name == head_name && block_names.contains(&m.name)) {
    return;
  }

  // Verify head is an external inductive.
  let head_ref = overlay
    .and_then(|o| o.get(&head_name))
    .or_else(|| lean_env.get(&head_name));
  let (ext_n_params, ext_n_indices) = match head_ref {
    Some(ConstantInfo::InductInfo(v)) => {
      let p = nat_to_usize(&v.num_params);
      let i = nat_to_usize(&v.num_indices);
      (p, i)
    },
    _ => return,
  };

  // Must have at least ext_n_params applied args.
  if args.len() < ext_n_params {
    return;
  }

  // Check if any parameter arg mentions an *original* block inductive. This
  // is the kernel's definition of a nested occurrence (C++
  // `is_nested_inductive_app`: `m_new_types` contains unique auxiliary names
  // like `_nested.List_1` that can never appear in user-written expressions,
  // so in practice only originals ever trigger the check).
  //
  // We intentionally do NOT extend the check with `flat`-stored aux names.
  // `FvarFlatMember.name` holds the EXTERNAL inductive (`Array`, `Option`,
  // ...), so matching against it would false-positive on unrelated
  // occurrences — e.g. `Option (Array Script.LazyStep)` inside
  // `Aesop.RappData` gets flagged because `Array` sits in `flat`, even though
  // `Script.LazyStep` doesn't reference any block member. That false positive
  // creates a spurious `_nested.Option_N` aux, which then cascades into
  // phantom `.rec_{N+1}` / `.below_{N+1}` / `.brecOn_{N+1}` constants during
  // decompile (see `decompile_block_aux_gen`, which uses this function and
  // doesn't have the expand/restore scaffolding to mask the bug).
  let has_nested_ref = args
    .iter()
    .take(ext_n_params)
    .any(|a| expr_mentions_any_name(a, block_names));
  if !has_nested_ref {
    return;
  }

  // Extract spec_params (first ext_n_params args). In FVar space, these may
  // contain block-param FVars (valid), field FVars (invalid), or free BVars
  // from structurally-peeled domain foralls (invalid).
  let spec_params: Vec<LeanExpr> = args[..ext_n_params].to_vec();

  // Reject if any spec_param has invalid references: free BVars (from
  // domain-local foralls) or non-param FVars (from field-local binders).
  for sp in &spec_params {
    if has_invalid_spec_ref(sp, block_param_fvar_names) {
      return;
    }
  }

  // Dedup: check if we've already seen this (ext_ind_name, spec_params) pair.
  // Use blake3 content hashes for structural equality. Since the FVar naming
  // is deterministic (_bp_0, _bp_1, ...), hashing in FVar form is stable.
  let spec_hashes: Vec<Hash> =
    spec_params.iter().map(|e| *e.get_hash()).collect();
  if aux_seen.iter().any(|(name, hashes)| {
    *name == head_name
      && hashes.len() == spec_hashes.len()
      && hashes.iter().zip(spec_hashes.iter()).all(|(a, b)| a == b)
  }) {
    return;
  }
  aux_seen.push((head_name.clone(), spec_hashes));

  // Use the raw levels from the Const node in the constructor type.
  // These match the Lean kernel's `restore_nested` output, which
  // preserves the exact level structure from the original elaboration.
  flat.push(FvarFlatMember {
    name: head_name,
    spec_params,
    occurrence_level_args: head_levels,
    own_params: ext_n_params,
    n_indices: ext_n_indices,
  });
}

// NOTE: the kernel-level `compute_occurrence_levels` / `compute_expr_sort_level`
// / `extract_level_param_with_offset` / `peel_succ` helpers, and their
// transitive dep `super::below::get_ind_sort_level`, were removed as part
// of Round 2 dead-code cleanup. They implemented the principled universe
// recomputation per `elim_nested_inductive_fn` in the C++ kernel, but
// were never wired into the live pipeline — `try_detect_nested_fvar` uses
// raw `head_levels` and `maximize_occurrence_levels` does pointwise-max
// per external name. If we ever need the principled path (e.g., for
// heterogeneous nested args like `HashMap (List α) (Array β)`), revive
// from git history; the current live pipeline has zero observed failures
// on 25k+ constants via `validate-aux`.

#[cfg(test)]
mod tests {
  use super::*;
  use crate::ix::env::{
    AxiomVal, ConstantVal, InductiveVal, Level as LL, Name,
  };
  use lean_ffi::nat::Nat;

  fn mk_name_for(s: &str) -> Name {
    let mut n = Name::anon();
    for part in s.split('.') {
      n = Name::str(n, part.to_string());
    }
    n
  }

  fn sort0() -> LeanExpr {
    LeanExpr::sort(LL::zero())
  }

  /// Small test helper: build an `FxHashSet<Name>` from a slice of names.
  /// `expr_mentions_any_name` takes a set so the hot caller is O(1); tests
  /// use this to stay ergonomic.
  fn names_of<const N: usize>(items: [Name; N]) -> FxHashSet<Name> {
    items.into_iter().collect()
  }

  // ---- expr_mentions_any_name ----

  #[test]
  fn expr_mentions_any_name_none() {
    let e = sort0();
    assert!(!expr_mentions_any_name(&e, &names_of([mk_name_for("X")])));
  }

  #[test]
  fn expr_mentions_any_name_direct_const() {
    let e = LeanExpr::cnst(mk_name_for("List"), vec![]);
    assert!(expr_mentions_any_name(&e, &names_of([mk_name_for("List")])));
  }

  #[test]
  fn expr_mentions_any_name_in_app_spine() {
    let e = LeanExpr::app(
      LeanExpr::cnst(mk_name_for("f"), vec![]),
      LeanExpr::cnst(mk_name_for("Tree"), vec![]),
    );
    assert!(expr_mentions_any_name(&e, &names_of([mk_name_for("Tree")])));
  }

  #[test]
  fn expr_mentions_any_name_under_forall() {
    // ∀ (x : A), B where B = Const("Target")
    let e = LeanExpr::all(
      mk_name_for("x"),
      sort0(),
      LeanExpr::cnst(mk_name_for("Target"), vec![]),
      crate::ix::env::BinderInfo::Default,
    );
    assert!(expr_mentions_any_name(&e, &names_of([mk_name_for("Target")])));
  }

  #[test]
  fn expr_mentions_any_name_detects_proj_type() {
    let e = LeanExpr::proj(
      mk_name_for("MyStruct"),
      Nat::from(0u64),
      LeanExpr::bvar(Nat::from(0u64)),
    );
    assert!(expr_mentions_any_name(&e, &names_of([mk_name_for("MyStruct")])));
  }

  #[test]
  fn expr_mentions_any_name_any_of_several() {
    let e = LeanExpr::cnst(mk_name_for("B"), vec![]);
    assert!(expr_mentions_any_name(
      &e,
      &names_of([mk_name_for("A"), mk_name_for("B"), mk_name_for("C")]),
    ));
  }

  #[test]
  fn expr_mentions_any_name_through_let() {
    let e = LeanExpr::letE(
      mk_name_for("x"),
      sort0(),
      sort0(),
      LeanExpr::cnst(mk_name_for("Nested"), vec![]),
      false,
    );
    assert!(expr_mentions_any_name(&e, &names_of([mk_name_for("Nested")])));
  }

  #[test]
  fn expr_mentions_any_name_peels_mdata() {
    let inner = LeanExpr::cnst(mk_name_for("Target"), vec![]);
    let e = LeanExpr::mdata(vec![], inner);
    assert!(expr_mentions_any_name(&e, &names_of([mk_name_for("Target")])));
  }

  // ---- has_invalid_spec_ref ----

  #[test]
  fn has_invalid_spec_ref_free_bvar_is_invalid() {
    // bare BVar(0) at top level is invalid (domain-local leak)
    let e = LeanExpr::bvar(Nat::from(0u64));
    assert!(has_invalid_spec_ref(&e, &[]));
  }

  #[test]
  fn has_invalid_spec_ref_unbound_fvar_is_invalid() {
    let unknown = Name::str(Name::anon(), "field_local".into());
    let e = LeanExpr::fvar(unknown.clone());
    // Pass empty param_fvar_names → FVar is field-local, invalid.
    assert!(has_invalid_spec_ref(&e, &[]));
  }

  #[test]
  fn has_invalid_spec_ref_known_fvar_is_valid() {
    let param_name = Name::str(Name::anon(), "param_0".into());
    let e = LeanExpr::fvar(param_name.clone());
    assert!(!has_invalid_spec_ref(&e, &[param_name]));
  }

  #[test]
  fn has_invalid_spec_ref_const_only_is_valid() {
    let e = LeanExpr::cnst(mk_name_for("Nat"), vec![]);
    assert!(!has_invalid_spec_ref(&e, &[]));
  }

  #[test]
  fn has_invalid_spec_ref_sort_only_is_valid() {
    assert!(!has_invalid_spec_ref(&sort0(), &[]));
  }

  #[test]
  fn has_invalid_spec_ref_bvar_under_binder_is_valid() {
    // ∀ (x : α), BVar(0) — bvar is bound, valid.
    let e = LeanExpr::all(
      mk_name_for("x"),
      sort0(),
      LeanExpr::bvar(Nat::from(0u64)),
      crate::ix::env::BinderInfo::Default,
    );
    assert!(!has_invalid_spec_ref(&e, &[]));
  }

  #[test]
  fn has_invalid_spec_ref_field_local_inside_forall_is_invalid() {
    let unknown = Name::str(Name::anon(), "field_local".into());
    let e = LeanExpr::all(
      mk_name_for("x"),
      sort0(),
      LeanExpr::fvar(unknown),
      crate::ix::env::BinderInfo::Default,
    );
    assert!(has_invalid_spec_ref(&e, &[]));
  }

  // ---- build_compile_flat_block: non-nested happy path ----

  /// Build a minimal Nat-like inductive (no params, no indices, no nesting).
  fn minimal_nat_env() -> LeanEnv {
    let mut env = LeanEnv::default();
    let zero_ty = LL::zero();
    let nat_name = mk_name_for("Nat");
    // Inductive Nat : Sort 1 with ctors [Nat.zero, Nat.succ].
    let nat_ind = InductiveVal {
      cnst: ConstantVal {
        name: nat_name.clone(),
        level_params: vec![],
        typ: LeanExpr::sort(LL::succ(zero_ty.clone())),
      },
      num_params: Nat::from(0u64),
      num_indices: Nat::from(0u64),
      all: vec![nat_name.clone()],
      ctors: vec![mk_name_for("Nat.zero"), mk_name_for("Nat.succ")],
      num_nested: Nat::from(0u64),
      is_rec: true,
      is_unsafe: false,
      is_reflexive: false,
    };
    env.insert(nat_name.clone(), ConstantInfo::InductInfo(nat_ind));

    // Nat.zero : Nat  (as axiom for detection test — real ctor form isn't
    // exercised by the no-nesting path).
    env.insert(
      mk_name_for("Nat.zero"),
      ConstantInfo::AxiomInfo(AxiomVal {
        cnst: ConstantVal {
          name: mk_name_for("Nat.zero"),
          level_params: vec![],
          typ: LeanExpr::cnst(nat_name.clone(), vec![]),
        },
        is_unsafe: false,
      }),
    );
    // Nat.succ : Nat → Nat
    env.insert(
      mk_name_for("Nat.succ"),
      ConstantInfo::AxiomInfo(AxiomVal {
        cnst: ConstantVal {
          name: mk_name_for("Nat.succ"),
          level_params: vec![],
          typ: LeanExpr::all(
            mk_name_for("_"),
            LeanExpr::cnst(nat_name.clone(), vec![]),
            LeanExpr::cnst(nat_name.clone(), vec![]),
            crate::ix::env::BinderInfo::Default,
          ),
        },
        is_unsafe: false,
      }),
    );
    env
  }

  #[test]
  fn build_compile_flat_block_non_nested_returns_single_entry() {
    let env = minimal_nat_env();
    let flat = build_compile_flat_block(&[mk_name_for("Nat")], &env).unwrap();
    assert_eq!(flat.len(), 1, "non-nested Nat → single flat entry");
    assert_eq!(flat[0].name, mk_name_for("Nat"));
    assert_eq!(flat[0].own_params, 0);
    assert_eq!(flat[0].n_indices, 0);
    assert!(flat[0].spec_params.is_empty());
  }

  #[test]
  fn build_compile_flat_block_empty_originals_errors() {
    let env = LeanEnv::default();
    let r = build_compile_flat_block(&[], &env);
    assert!(r.is_err());
  }

  #[test]
  fn build_compile_flat_block_missing_inductive_errors() {
    let env = LeanEnv::default();
    let r = build_compile_flat_block(&[mk_name_for("Missing")], &env);
    assert!(r.is_err());
  }

  #[test]
  fn build_compile_flat_block_non_inductive_errors() {
    let mut env = LeanEnv::default();
    // Insert an axiom under the name of a supposed inductive — should
    // error out.
    env.insert(
      mk_name_for("Pretender"),
      ConstantInfo::AxiomInfo(AxiomVal {
        cnst: ConstantVal {
          name: mk_name_for("Pretender"),
          level_params: vec![],
          typ: sort0(),
        },
        is_unsafe: false,
      }),
    );
    let r = build_compile_flat_block(&[mk_name_for("Pretender")], &env);
    assert!(r.is_err());
  }
}
