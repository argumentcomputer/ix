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

use super::expr_utils::{
  LocalDecl, batch_abstract, decompose_apps, forall_telescope, instantiate1,
  subst_levels,
};
use crate::ix::env::{
  ConstantInfo, Env as LeanEnv, Expr as LeanExpr, ExprData, Level, Name,
};

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
// Expression helpers
// =========================================================================

/// Check if any `Const` or `Proj` name in `expr` is in `names`.
///
/// Uses an explicit stack to avoid recursion. Analogous to the kernel's
/// `expr_mentions_any_addr` (`src/ix/kernel/tc.rs:459-501`).
fn expr_mentions_any_name(expr: &LeanExpr, names: &[Name]) -> bool {
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
        if idx.to_u64().unwrap_or(0) >= depth {
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
) -> Vec<CompileFlatMember> {
  let first_ind = match ordered_originals.first() {
    Some(name) => match lean_env.get(name) {
      Some(ConstantInfo::InductInfo(v)) => v,
      _ => return vec![],
    },
    None => return vec![],
  };
  let n_params = first_ind.num_params.to_u64().unwrap_or(0) as usize;

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
    let ind = match lean_env.get(name) {
      Some(ConstantInfo::InductInfo(v)) => v,
      _ => continue,
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
      own_params: ind.num_params.to_u64().unwrap_or(0) as usize,
      n_indices: ind.num_indices.to_u64().unwrap_or(0) as usize,
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
    let (ctor_names, level_params) = match lean_env.get(&member.name) {
      Some(ConstantInfo::InductInfo(v)) => {
        (v.ctors.clone(), v.cnst.level_params.clone())
      },
      _ => continue,
    };

    for ctor_name in &ctor_names {
      let (ctor_n_fields, ctor_typ) = match lean_env.get(ctor_name) {
        Some(ConstantInfo::CtorInfo(c)) => {
          let fields = c.num_fields.to_u64().unwrap_or(0) as usize;
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
          &block_param_fvar_names,
        );
      }
    }
  }

  // Convert FVar-form spec_params back to BVar form for the output.
  // Abstract block-param FVars outermost-first: _bp_0 → BVar(n-1),
  // _bp_1 → BVar(n-2), ..., _bp_{n-1} → BVar(0).
  flat
    .into_iter()
    .map(|entry| {
      let spec_params =
        abstract_spec_params_to_bvars(&entry.spec_params, &block_param_decls);
      CompileFlatMember {
        name: entry.name,
        spec_params,
        // Normalize occurrence levels to right-associated form to match
        // Lean's inferType normalization. The raw levels from Const nodes
        // in constructor expressions may be left-associated.
        occurrence_level_args: entry
          .occurrence_level_args
          .iter()
          .map(|l| super::below::normalize_level(l))
          .collect(),
        own_params: entry.own_params,
        n_indices: entry.n_indices,
      }
    })
    .collect()
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
fn try_detect_nested_fvar(
  dom: &LeanExpr,
  block_names: &[Name],
  flat: &mut Vec<FvarFlatMember>,
  aux_seen: &mut Vec<(Name, Vec<Hash>)>,
  lean_env: &LeanEnv,
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
  let (ext_n_params, ext_n_indices) = match lean_env.get(&head_name) {
    Some(ConstantInfo::InductInfo(v)) => {
      let p = v.num_params.to_u64().unwrap_or(0) as usize;
      let i = v.num_indices.to_u64().unwrap_or(0) as usize;
      (p, i)
    },
    _ => return,
  };

  // Must have at least ext_n_params applied args.
  if args.len() < ext_n_params {
    return;
  }

  // Check if any parameter arg mentions a block inductive or existing flat
  // member. This is what makes it "nested" — e.g., `List Tree` has param
  // arg `Tree` which is in the block.
  let all_flat_names: Vec<Name> = flat.iter().map(|m| m.name.clone()).collect();
  let combined: Vec<Name> =
    block_names.iter().chain(all_flat_names.iter()).cloned().collect();
  let has_nested_ref = args
    .iter()
    .take(ext_n_params)
    .any(|a| expr_mentions_any_name(a, &combined));
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

  flat.push(FvarFlatMember {
    name: head_name,
    spec_params,
    occurrence_level_args: head_levels,
    own_params: ext_n_params,
    n_indices: ext_n_indices,
  });
}
