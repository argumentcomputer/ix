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
use rustc_hash::FxHashMap;

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
pub(crate) struct ExpandedMember {
  /// Inductive name: original name for originals, `_nested.ExtInd_N` for
  /// auxiliaries (scoped under `all[0]`).
  pub name: Name,
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
  aux_to_nested: FxHashMap<Name, LeanExpr>,
  aux_ctor_map: FxHashMap<Name, (Name, Name)>,
  /// Dedup: stores (nested_expr_hash, aux_name) for each detected occurrence.
  aux_seen: Vec<(Hash, Name)>,
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
  /// Collect all type names currently in the expanded block.
  fn all_type_names(&self) -> Vec<Name> {
    self.types.iter().map(|m| m.name.clone()).collect()
  }

  /// Recursively replace all nested inductive occurrences in an expression.
  ///
  /// Matches C++ `replace_all_nested` (`inductive.cpp:1031`): walks the
  /// expression top-down, calling `replace_if_nested` at each sub-expression.
  fn replace_all_nested(
    &mut self,
    e: &LeanExpr,
    as_fvars: &[LeanExpr],
  ) -> LeanExpr {
    // Try top-level replacement first.
    if let Some(replaced) = self.replace_if_nested(e, as_fvars) {
      return replaced;
    }
    // No match — recurse into sub-expressions.
    match e.as_data() {
      ExprData::App(f, a, _) => LeanExpr::app(
        self.replace_all_nested(f, as_fvars),
        self.replace_all_nested(a, as_fvars),
      ),
      ExprData::Lam(n, t, b, bi, _) => LeanExpr::lam(
        n.clone(),
        self.replace_all_nested(t, as_fvars),
        self.replace_all_nested(b, as_fvars),
        bi.clone(),
      ),
      ExprData::ForallE(n, t, b, bi, _) => LeanExpr::all(
        n.clone(),
        self.replace_all_nested(t, as_fvars),
        self.replace_all_nested(b, as_fvars),
        bi.clone(),
      ),
      ExprData::LetE(n, t, v, b, nd, _) => LeanExpr::letE(
        n.clone(),
        self.replace_all_nested(t, as_fvars),
        self.replace_all_nested(v, as_fvars),
        self.replace_all_nested(b, as_fvars),
        *nd,
      ),
      ExprData::Proj(n, i, val, _) => LeanExpr::proj(
        n.clone(),
        i.clone(),
        self.replace_all_nested(val, as_fvars),
      ),
      ExprData::Mdata(md, inner, _) => {
        LeanExpr::mdata(md.clone(), self.replace_all_nested(inner, as_fvars))
      },
      _ => e.clone(),
    }
  }

  /// Check if `e` is a nested inductive application and, if so, create
  /// auxiliary types and return the replacement expression.
  ///
  /// Matches C++ `replace_if_nested` (`inductive.cpp:963-1027`).
  fn replace_if_nested(
    &mut self,
    e: &LeanExpr,
    as_fvars: &[LeanExpr],
  ) -> Option<LeanExpr> {
    let (head, args) = decompose_apps(e);
    let (head_name, head_levels) = match head.as_data() {
      ExprData::Const(name, levels, _) => (name.clone(), levels.clone()),
      _ => return None,
    };

    // Skip if head is in the block (direct recursive, not nested).
    let all_names = self.all_type_names();
    if all_names.contains(&head_name) {
      return None;
    }

    // Verify head is an external inductive.
    let ext_ind_ref = self.lean_env.get(&head_name);
    let ext_ind = match ext_ind_ref.as_deref() {
      Some(ConstantInfo::InductInfo(v)) => v,
      _ => return None,
    };
    let ext_n_params = nat_to_usize(&ext_ind.num_params);

    if args.len() < ext_n_params {
      return None;
    }

    // Check if any parameter arg mentions a block/flat-block member.
    if !args
      .iter()
      .take(ext_n_params)
      .any(|a| expr_mentions_any_name(a, &all_names))
    {
      return None;
    }

    // Extract spec_params and validate no invalid refs.
    let spec_params: Vec<LeanExpr> = args[..ext_n_params].to_vec();
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
      replace_params_expr(&app, as_fvars, &self.block_param_fvars)
    };
    let i_as_hash = *i_as.get_hash();

    // Dedup: check if we've already created an auxiliary for this occurrence.
    let existing_aux = self.aux_seen.iter().find_map(|(h, name)| {
      if *h == i_as_hash { Some(name.clone()) } else { None }
    });

    if let Some(aux_name) = existing_aux {
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

      // Store mapping: aux_name → J.{I_lvls} spec_params (with block param FVars).
      let j_as = {
        let mut app = LeanExpr::cnst(j_name.clone(), head_levels.clone());
        for sp in &spec_params {
          app = LeanExpr::app(app, sp.clone());
        }
        replace_params_expr(&app, as_fvars, &self.block_param_fvars)
      };
      self.aux_to_nested.insert(aux_name.clone(), j_as);
      self.aux_seen.push((i_as_hash, aux_name.clone()));

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
        let j_ctor = match j_ctor_ref.as_deref() {
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

      self.types.push(ExpandedMember {
        name: aux_name,
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
  let first_ind = match first_ind_ref.as_deref() {
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
    aux_to_nested: FxHashMap::default(),
    aux_ctor_map: FxHashMap::default(),
    aux_seen: Vec::new(),
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
    let ind = match ind_ref.as_deref() {
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
      .filter_map(|cn| match lean_env.get(cn).as_deref() {
        Some(ConstantInfo::CtorInfo(c)) => Some(ExpandedCtor {
          name: c.cnst.name.clone(),
          typ: c.cnst.typ.clone(),
          n_fields: nat_to_usize(&c.num_fields),
        }),
        _ => None,
      })
      .collect();
    ctx.types.push(ExpandedMember {
      name: name.clone(),
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
  if !alias_to_rep.is_empty() {
    for member in &mut ctx.types {
      for ctor in &mut member.ctors {
        ctor.typ = canonicalize_const_names(&ctor.typ, alias_to_rep);
      }
      member.typ = canonicalize_const_names(&member.typ, alias_to_rep);
    }
  }

  // Queue-based scan: process each type's constructors.
  let mut qi = 0;
  while qi < ctx.types.len() {
    let n_ctors = ctx.types[qi].ctors.len();
    for ci in 0..n_ctors {
      let ctor_type = ctx.types[qi].ctors[ci].typ.clone();

      // Peel params, re-creating FVars per constructor for binding info.
      let (as_fvars, as_decls, peeled) =
        forall_telescope(&ctor_type, n_params, "cp", qi * 100 + ci);

      // Replace all nested occurrences in the peeled body.
      let replaced = ctx.replace_all_nested(&peeled, &as_fvars);

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

/// Rewrite Const names in an expression using a name map.
///
/// For each `Const(name, levels)` where `name` is in `name_map`, replaces
/// it with `Const(name_map[name], levels)`. Used to canonicalize alias
/// references to representative names before nested expansion.
fn canonicalize_const_names(
  expr: &LeanExpr,
  name_map: &FxHashMap<Name, Name>,
) -> LeanExpr {
  match expr.as_data() {
    ExprData::Const(name, levels, _) => {
      if let Some(new_name) = name_map.get(name) {
        LeanExpr::cnst(new_name.clone(), levels.clone())
      } else {
        expr.clone()
      }
    },
    ExprData::App(f, a, _) => LeanExpr::app(
      canonicalize_const_names(f, name_map),
      canonicalize_const_names(a, name_map),
    ),
    ExprData::Lam(n, t, b, bi, _) => LeanExpr::lam(
      n.clone(),
      canonicalize_const_names(t, name_map),
      canonicalize_const_names(b, name_map),
      bi.clone(),
    ),
    ExprData::ForallE(n, t, b, bi, _) => LeanExpr::all(
      n.clone(),
      canonicalize_const_names(t, name_map),
      canonicalize_const_names(b, name_map),
      bi.clone(),
    ),
    ExprData::LetE(n, t, v, b, nd, _) => LeanExpr::letE(
      n.clone(),
      canonicalize_const_names(t, name_map),
      canonicalize_const_names(v, name_map),
      canonicalize_const_names(b, name_map),
      *nd,
    ),
    ExprData::Proj(n, i, e, _) => LeanExpr::proj(
      n.clone(),
      i.clone(),
      canonicalize_const_names(e, name_map),
    ),
    ExprData::Mdata(md, e, _) => {
      LeanExpr::mdata(md.clone(), canonicalize_const_names(e, name_map))
    },
    _ => expr.clone(),
  }
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
  let fvar_map: FxHashMap<Name, usize> = as_fvars
    .iter()
    .enumerate()
    .filter_map(|(i, fv)| match fv.as_data() {
      ExprData::Fvar(n, _) => Some((n.clone(), i)),
      _ => None,
    })
    .collect();
  let n = as_fvars.len();
  let abstracted = batch_abstract(e, &fvar_map, n, 0);
  super::expr_utils::instantiate_rev(&abstracted, block_param_fvars)
}

// =========================================================================
// Expression helpers
// =========================================================================

/// Check if any `Const` or `Proj` name in `expr` is in `names`.
///
/// Uses an explicit stack to avoid recursion. Analogous to the kernel's
/// `expr_mentions_any_addr` (`src/ix/kernel/tc.rs:459-501`).
pub(super) fn expr_mentions_any_name(expr: &LeanExpr, names: &[Name]) -> bool {
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
  let first_ind = match first_ind_ref.as_deref() {
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

  // Seed with original block inductives. For originals, spec_params are
  // the block param FVars themselves (identity specialization).
  for name in ordered_originals {
    let ind_ref =
      overlay.and_then(|o| o.get(name)).or_else(|| lean_env.get(name));
    let ind = match ind_ref.as_deref() {
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
    let (ctor_names, level_params) = match member_ref.as_deref() {
      Some(ConstantInfo::InductInfo(v)) => {
        (v.ctors.clone(), v.cnst.level_params.clone())
      },
      _ => continue,
    };

    for ctor_name in &ctor_names {
      let ctor_ref = overlay
        .and_then(|o| o.get(ctor_name))
        .or_else(|| lean_env.get(ctor_name));
      let (ctor_n_fields, ctor_typ) = match ctor_ref.as_deref() {
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
          ordered_originals,
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
  let fvar_map: rustc_hash::FxHashMap<crate::ix::env::Name, usize> =
    block_param_decls
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
    if let Some(merged) = max_levels.get(&entry.name) {
      if merged.len() == entry.occurrence_level_args.len() {
        entry.occurrence_level_args = merged.clone();
      }
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
  block_names: &[Name],
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
  let (ext_n_params, ext_n_indices) = match head_ref.as_deref() {
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
