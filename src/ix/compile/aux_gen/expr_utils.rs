//! Shared expression manipulation utilities for auxiliary generation.
//!
//! Provides FVar-based expression construction: create fresh free variables,
//! open forall telescopes, build expressions using FVar references, then
//! abstract back into de Bruijn binder chains with `mk_forall`/`mk_lambda`.
//!
//! Also includes substitution, shifting, and universe manipulation helpers
//! used across `recursor.rs`, `below.rs`, and `brecon.rs`.

use rustc_hash::{FxHashMap, FxHashSet};

use crate::ix::address::Address;
use crate::ix::compile::nat_conv::{nat_to_u64, nat_to_usize};
use crate::ix::env::{
  BinderInfo, Expr as LeanExpr, ExprData, Level, LevelData, Name,
};
use crate::ix::kernel::ingress::{lean_level_to_kuniv, resolve_lean_name_addr};
use crate::ix::kernel::mode::Meta;
use lean_ffi::nat::Nat;

// =========================================================================
// FVar infrastructure
// =========================================================================

/// A local declaration: FVar name, binder metadata, and domain type.
///
/// Used to accumulate binder information while building expressions in
/// FVar space. The `fvar_name` is a unique identifier; `binder_name` is
/// the cosmetic name that appears in the final forall/lambda chain.
#[derive(Clone)]
pub(crate) struct LocalDecl {
  pub fvar_name: Name,
  pub binder_name: Name,
  pub domain: LeanExpr,
  pub info: BinderInfo,
}

/// Create a fresh FVar with a unique name derived from `prefix` and `idx`.
pub(crate) fn fresh_fvar(prefix: &str, idx: usize) -> (Name, LeanExpr) {
  let name = Name::str(Name::anon(), format!("_{}_{}", prefix, idx));
  let fvar = LeanExpr::fvar(name.clone());
  (name, fvar)
}

// =========================================================================
// Inductive recursor-structural decomposition
// =========================================================================

/// Per-inductive recursor-structural info, derived from the stored type by
/// WHNF-peeling params and indices.
///
/// Mirrors `rec_info` in `refs/lean4/src/kernel/inductive.cpp:150-158` — the
/// C++ kernel's bookkeeping for `m_indices` / `m_major` / `m_C`. We don't
/// bind the motive here (that's created at a caller-specific position in
/// the rec type's binder chain), but everything needed to build it in one
/// line is on this struct.
///
/// Binders use FVars (via [`LocalDecl`]) so the result can be embedded in
/// any outer binder chain without de-Bruijn shifting — matching Lean's
/// MetaM-style where `forallTelescopeReducing` introduces fresh fvars
/// into an ambient local context.
#[derive(Clone)]
pub(super) struct IndRecInfo {
  /// Index binders after WHNF-peeling. For inductives whose target is a
  /// reducible alias (e.g. `Set σ := σ → Prop`), `indices.len()` may equal
  /// `InductiveVal.num_indices` even when the stored type has no
  /// syntactic `Pi` at the index position — WHNF exposes the hidden
  /// arrow. Source of truth for "how many indices does this inductive
  /// actually have in its recursor binder chain."
  pub indices: Vec<LocalDecl>,

  /// Major premise `(t : I params indices)` — domain is the inductive
  /// head applied to all params (supplied via `param_fvars`) and indices
  /// as FVars.
  pub major: LocalDecl,
}

/// Decompose an inductive's stored type into its recursor-structural
/// pieces, peeling params (using the caller-supplied `param_fvars`) then
/// all remaining leading `Pi`s as indices, with kernel WHNF between
/// every step.
///
/// Mirrors `mk_rec_infos` in `refs/lean4/src/kernel/inductive.cpp:588-618`:
///
/// ```cpp
/// t = whnf(t);
/// while (is_pi(t)) {
///     if (i < m_nparams) { t = instantiate(binding_body(t), m_params[i]); }
///     else {
///         expr idx = mk_local_decl_for(t);
///         info.m_indices.push_back(idx);
///         t = instantiate(binding_body(t), idx);
///     }
///     i++;
///     t = whnf(t);
/// }
/// ```
///
/// `ind_univs` are the universe levels to substitute for the inductive's
/// stored `level_params` — typically the canonical rec's level params
/// (for the main case) or concrete occurrence levels (for nested aux).
///
/// `param_fvars` are the caller-supplied parameter `LocalDecl`s; this
/// helper instantiates them into the type rather than creating fresh
/// ones, so that downstream consumers (`build_motive_type`,
/// `build_rec_type`) can reference the same FVars throughout the
/// recursor's binder chain.
///
/// # Errors
///
/// - `InvalidMutualBlock` if the type has fewer Pi binders than
///   `param_fvars.len()` (even after WHNF).
/// - `InvalidMutualBlock` if the final body isn't a `Sort` after peeling
///   every leading Pi.
///
/// Per-step WHNF failures from the kernel fall through to
/// `TcScope::whnf_lean`'s graceful degradation (returns the original
/// expression); a stuck type at that point surfaces as a non-`Pi` in the
/// loop body and terminates peeling, potentially yielding a shorter
/// `indices` vec than Lean's stored `num_indices`.
pub(super) fn decompose_inductive_type(
  ind: &crate::ix::env::InductiveVal,
  ind_univs: &[Level],
  param_fvars: &[LocalDecl],
  stt: &crate::ix::compile::CompileState,
  kctx: &mut crate::ix::compile::KernelCtx,
) -> Result<IndRecInfo, crate::ix::ixon::CompileError> {
  use crate::ix::ixon::CompileError;

  let n_params = param_fvars.len();
  let ty = subst_levels(&ind.cnst.typ, &ind.cnst.level_params, ind_univs);

  // TcScope pre-populated with the caller's param FVars. As we peel
  // indices, we push each into the scope so subsequent `whnf_lean` calls
  // see them as locals (required for correctness when index domains
  // reference earlier indices, or when WHNF needs to look through a
  // `Var` bound to a `let` binding — rare but possible in principle).
  let mut scope = TcScope::new(param_fvars, &ind.cnst.level_params, stt, kctx);

  // Initial WHNF — the stored type may start with a reducible head
  // (unusual for Lean-generated types, but cheap insurance matching the
  // `whnf(t);` before the main loop in `mk_rec_infos`).
  let mut cur = scope.whnf_lean(&ty);

  // Instantiate `n_params` leading Pi's with the caller's param FVars.
  // WHNF after each substitution to expose any alias introduced by the
  // substitution (e.g., a param whose domain mentions a reducible def).
  for (p, param_fvar) in param_fvars.iter().take(n_params).enumerate() {
    match cur.as_data() {
      ExprData::ForallE(_, _, body, _, _) => {
        let param_fv = LeanExpr::fvar(param_fvar.fvar_name.clone());
        cur = instantiate1(body, &param_fv);
        cur = scope.whnf_lean(&cur);
      },
      _ => {
        return Err(CompileError::InvalidMutualBlock {
          reason: format!(
            "decompose_inductive_type({}): fewer than {n_params} param \
             foralls in stored type (peeled {p} before hitting non-Pi)",
            ind.cnst.name.pretty(),
          ),
        });
      },
    }
  }

  // Peel all remaining leading Pi's as indices. Matches Lean's
  // `while (is_pi(t)) { ... }` — we don't impose a count; the stored
  // `num_indices` is informational, but authoritative count comes from
  // actual post-WHNF binders. This is what handles the `Set σ`-style
  // reducible-alias target case.
  let mut indices: Vec<LocalDecl> = Vec::new();
  let mut idx_i = 0usize;
  while let ExprData::ForallE(name, dom, body, bi, _) = cur.as_data() {
    let (fv_name, fv) = fresh_fvar("idx", idx_i);
    let decl = LocalDecl {
      fvar_name: fv_name,
      binder_name: name.clone(),
      domain: dom.clone(),
      info: bi.clone(),
    };
    scope.push_locals(std::slice::from_ref(&decl));
    indices.push(decl);
    cur = instantiate1(body, &fv);
    cur = scope.whnf_lean(&cur);
    idx_i += 1;
  }

  // Target sort.
  if !matches!(cur.as_data(), ExprData::Sort(_, _)) {
    return Err(CompileError::InvalidMutualBlock {
      reason: format!(
        "decompose_inductive_type({}): peeled {n_params} params + {} \
         indices; expected remaining body to be a Sort, got something \
         else",
        ind.cnst.name.pretty(),
        indices.len(),
      ),
    });
  }

  // Major domain: `I params indices`, all FVars.
  let mut major_dom = mk_const(&ind.cnst.name, ind_univs);
  for p in param_fvars {
    major_dom = LeanExpr::app(major_dom, LeanExpr::fvar(p.fvar_name.clone()));
  }
  for ix in &indices {
    major_dom = LeanExpr::app(major_dom, LeanExpr::fvar(ix.fvar_name.clone()));
  }

  let (major_fv_name, _) = fresh_fvar("major", n_params + indices.len());
  let major = LocalDecl {
    fvar_name: major_fv_name,
    binder_name: Name::str(Name::anon(), "t".to_string()),
    domain: major_dom,
    info: BinderInfo::Default,
  };

  Ok(IndRecInfo { indices, major })
}

/// Open N leading foralls of `expr`, replacing each BVar(0) with a fresh
/// FVar. Returns the FVars, their declarations, and the remaining body.
///
/// This is the Rust equivalent of Lean's `forallTelescope`: it converts
/// a de Bruijn binder chain into FVar-based form so that expression
/// construction can use named references instead of manual index arithmetic.
///
/// The declarations are returned in outermost-first order, suitable for
/// passing directly to `mk_forall` or `mk_lambda`.
///
/// `Mdata` wrappers on the forall spine are transparently peeled — Lean
/// stores annotations (reducibility hints, pretty-printing info, etc.) as
/// `Mdata` around otherwise-forall expressions, and Lean's own
/// `forallTelescope` looks through them via WHNF. Every other transformer
/// in this file already treats `Mdata` as a structural no-op; doing the
/// same here avoids spurious short telescopes on recursors whose types
/// happen to carry metadata (observed in Mathlib).
///
/// If the expression has fewer than `n` leading foralls (even after
/// peeling `Mdata`), the returned `decls` is short. Callers indexing by
/// position MUST verify `decls.len() == n` before indexing — otherwise
/// a surprising input shape becomes a panic. Prefer
/// [`forall_telescope_exact`] when a precise arity is required.
pub(crate) fn forall_telescope(
  expr: &LeanExpr,
  n: usize,
  prefix: &str,
  start_idx: usize,
) -> (Vec<LeanExpr>, Vec<LocalDecl>, LeanExpr) {
  let mut fvars = Vec::with_capacity(n);
  let mut decls = Vec::with_capacity(n);
  let mut cur = expr.clone();
  for i in 0..n {
    // Peel any Mdata wrappers before matching — they're structural no-ops.
    while let ExprData::Mdata(_, inner, _) = cur.as_data() {
      cur = inner.clone();
    }
    match cur.as_data() {
      ExprData::ForallE(name, dom, body, bi, _) => {
        let (fv_name, fv) = fresh_fvar(prefix, start_idx + i);
        decls.push(LocalDecl {
          fvar_name: fv_name,
          binder_name: name.clone(),
          domain: dom.clone(),
          info: bi.clone(),
        });
        fvars.push(fv.clone());
        cur = instantiate1(body, &fv);
      },
      _ => break,
    }
  }
  (fvars, decls, cur)
}

/// Like [`forall_telescope`], but errors if fewer than `n` foralls are
/// peeled. Use this when the caller is about to index into the returned
/// `decls` or `fvars` at position `n - 1` (or by explicit offset) — a
/// short telescope otherwise becomes an `index out of bounds` panic deep
/// in aux_gen with no context about which constant triggered it.
///
/// `context` is a short human-readable tag (e.g., `"build_below_def"`)
/// included in the error message. `what` describes what arity `n` was
/// expected to count (e.g., `"params + motives + minors + indices + 1"`).
pub(super) fn forall_telescope_exact(
  expr: &LeanExpr,
  n: usize,
  prefix: &str,
  start_idx: usize,
  context: &str,
  what: &str,
) -> Result<
  (Vec<LeanExpr>, Vec<LocalDecl>, LeanExpr),
  crate::ix::ixon::CompileError,
> {
  let (fvars, decls, body) = forall_telescope(expr, n, prefix, start_idx);
  if decls.len() != n {
    // Include enough context to pinpoint the shape problem: every peeled
    // binder name plus the kind of node that blocked further peeling. The
    // caller already prefixed this with the recursor name via `context`.
    let binder_list: Vec<String> = decls
      .iter()
      .map(|d| {
        format!("{}:{}", d.binder_name.pretty(), describe_expr_head(&d.domain))
      })
      .collect();
    return Err(crate::ix::ixon::CompileError::UnsupportedExpr {
      desc: format!(
        "{context}: expected {n} leading foralls ({what}), got {actual}. \
         Peeled binders (name:domain_kind): [{binders}]. \
         Stopped at body kind: {body_kind}. \
         This is either a mismatch between the recursor's structural \
         metadata and its actual type, or an unexpected binder shape \
         (let/mdata/etc.) that forall_telescope doesn't peel through.",
        actual = decls.len(),
        binders = binder_list.join(", "),
        body_kind = describe_expr_head(&body),
      ),
    });
  }
  Ok((fvars, decls, body))
}

/// Short tag describing the head of an expression, for use in diagnostic
/// messages. Includes enough detail to distinguish forall/lambda/app from
/// let/mdata/const/literal — the distinctions that matter for diagnosing
/// a short telescope.
fn describe_expr_head(e: &LeanExpr) -> String {
  match e.as_data() {
    ExprData::Bvar(i, _) => format!("Bvar({})", nat_to_u64(i)),
    ExprData::Fvar(n, _) => format!("Fvar({})", n.pretty()),
    ExprData::Mvar(n, _) => format!("Mvar({})", n.pretty()),
    ExprData::Sort(l, _) => format!("Sort({})", l.pretty()),
    ExprData::Const(n, _, _) => format!("Const({})", n.pretty()),
    ExprData::App(..) => "App".into(),
    ExprData::Lam(..) => "Lam".into(),
    ExprData::ForallE(..) => "ForallE".into(),
    ExprData::LetE(..) => "LetE".into(),
    ExprData::Proj(..) => "Proj".into(),
    ExprData::Mdata(..) => "Mdata".into(),
    ExprData::Lit(..) => "Lit".into(),
  }
}

// =========================================================================
// Abstraction: FVar -> BVar
// =========================================================================

/// Abstract a single FVar: replace all occurrences of `Fvar(fvar_name)` with
/// `BVar(depth)`, and increment all existing BVars >= depth.
/// This is the inverse of `instantiate1`.
///
/// Prefer `batch_abstract` or `mk_forall`/`mk_lambda` which abstract all
/// FVars in a single pass. This function is retained for cases that need
/// to abstract a single FVar outside of a binder-chain context.
#[allow(dead_code)]
pub(super) fn abstract_fvar(
  expr: &LeanExpr,
  fvar_name: &Name,
  depth: u64,
) -> LeanExpr {
  match expr.as_data() {
    ExprData::Fvar(n, _) if n == fvar_name => LeanExpr::bvar(Nat::from(depth)),
    ExprData::Bvar(idx, _) => {
      let i = nat_to_u64(idx);
      if i >= depth { LeanExpr::bvar(Nat::from(i + 1)) } else { expr.clone() }
    },
    ExprData::App(f, a, _) => LeanExpr::app(
      abstract_fvar(f, fvar_name, depth),
      abstract_fvar(a, fvar_name, depth),
    ),
    ExprData::Lam(n, t, b, bi, _) => LeanExpr::lam(
      n.clone(),
      abstract_fvar(t, fvar_name, depth),
      abstract_fvar(b, fvar_name, depth + 1),
      bi.clone(),
    ),
    ExprData::ForallE(n, t, b, bi, _) => LeanExpr::all(
      n.clone(),
      abstract_fvar(t, fvar_name, depth),
      abstract_fvar(b, fvar_name, depth + 1),
      bi.clone(),
    ),
    ExprData::LetE(n, t, v, b, nd, _) => LeanExpr::letE(
      n.clone(),
      abstract_fvar(t, fvar_name, depth),
      abstract_fvar(v, fvar_name, depth),
      abstract_fvar(b, fvar_name, depth + 1),
      *nd,
    ),
    ExprData::Proj(n, i, e, _) => {
      LeanExpr::proj(n.clone(), i.clone(), abstract_fvar(e, fvar_name, depth))
    },
    ExprData::Mdata(kvs, e, _) => {
      LeanExpr::mdata(kvs.clone(), abstract_fvar(e, fvar_name, depth))
    },
    _ => expr.clone(),
  }
}

/// Build a forall chain by batch-abstracting all FVars in a single pass
/// per sub-expression.
///
/// `binders` is outermost-first. Each domain and the body are walked
/// exactly once by `batch_abstract`, replacing all FVar references with
/// the correct BVar indices simultaneously.
///
/// Complexity: O(|body| + sum(|D_j|)) — one walk per expression.
/// The previous per-binder approach was O(k * (|body| + sum(|D_j|))).
pub(super) fn mk_forall(body: LeanExpr, binders: &[LocalDecl]) -> LeanExpr {
  mk_binder_chain(body, binders, BinderKind::Forall)
}

/// Build a lambda chain by batch-abstracting all FVars in a single pass.
///
/// Same semantics as `mk_forall` but produces `λ (x : T), body`.
pub(crate) fn mk_lambda(body: LeanExpr, binders: &[LocalDecl]) -> LeanExpr {
  mk_binder_chain(body, binders, BinderKind::Lambda)
}

/// Whether to build forall or lambda binders.
#[derive(Clone, Copy)]
enum BinderKind {
  Forall,
  Lambda,
}

/// Shared implementation for `mk_forall` and `mk_lambda`.
fn mk_binder_chain(
  body: LeanExpr,
  binders: &[LocalDecl],
  kind: BinderKind,
) -> LeanExpr {
  let k = binders.len();
  if k == 0 {
    return body;
  }

  // Build FVar name → binder position map (0 = outermost).
  let fvar_map: FxHashMap<Name, usize> =
    binders.iter().enumerate().map(|(i, d)| (d.fvar_name.clone(), i)).collect();

  // Abstract body: all k binders in scope.
  let mut result = batch_abstract(&body, &fvar_map, k, 0);

  // Build binder chain from innermost to outermost.
  for j in (0..k).rev() {
    let decl = &binders[j];
    // Domain D_j: only binders 0..j-1 are in scope (scope_depth = j).
    // Binder j's domain is NOT under binder j itself — only the body is.
    let domain = batch_abstract(&decl.domain, &fvar_map, j, 0);
    result = match kind {
      BinderKind::Forall => LeanExpr::all(
        decl.binder_name.clone(),
        domain,
        result,
        decl.info.clone(),
      ),
      BinderKind::Lambda => LeanExpr::lam(
        decl.binder_name.clone(),
        domain,
        result,
        decl.info.clone(),
      ),
    };
  }
  result
}

/// Single-pass FVar→BVar abstraction for an entire binder telescope.
///
/// Replaces all FVars (identified by `fvar_map`) with the correct BVar
/// indices in one expression walk, and shifts existing free BVars to
/// account for the new binders.
///
/// # Parameters
/// - `fvar_map`: FVar name → binder position (0 = outermost binder)
/// - `scope_depth`: how many of our binders are in scope at this point.
///   For the body, this is `k` (all binders). For domain `D_j`, this is `j`.
/// - `internal_depth`: expression-internal binder depth (forall/lambda/let
///   bodies entered during the walk). Starts at 0.
///
/// # BVar index computation
/// - FVar at binder position `i`, scope depth `s`, internal depth `d`:
///   `BVar((s - 1 - i) + d)`
/// - Free BVar(n) where `n >= d`: shifted to `BVar(n + s)`
/// - Bound BVar(n) where `n < d`: unchanged
pub(super) fn batch_abstract(
  expr: &LeanExpr,
  fvar_map: &FxHashMap<Name, usize>,
  scope_depth: usize,
  internal_depth: u64,
) -> LeanExpr {
  // Fast path: no binders to abstract.
  if scope_depth == 0 {
    return expr.clone();
  }
  match expr.as_data() {
    ExprData::Fvar(name, _) => {
      if let Some(&pos) = fvar_map.get(name) {
        if pos < scope_depth {
          let idx = (scope_depth - 1 - pos) as u64 + internal_depth;
          LeanExpr::bvar(Nat::from(idx))
        } else {
          // FVar not yet in scope (e.g., a forward reference in a domain
          // to a binder declared later). Leave as-is.
          expr.clone()
        }
      } else {
        // FVar not in our telescope — leave as-is.
        expr.clone()
      }
    },
    ExprData::Bvar(idx, _) => {
      let i = nat_to_u64(idx);
      if i >= internal_depth {
        // Free BVar: shift up by scope_depth to make room for our binders.
        LeanExpr::bvar(Nat::from(i + scope_depth as u64))
      } else {
        // Bound by an expression-internal binder — unchanged.
        expr.clone()
      }
    },
    ExprData::App(f, a, _) => LeanExpr::app(
      batch_abstract(f, fvar_map, scope_depth, internal_depth),
      batch_abstract(a, fvar_map, scope_depth, internal_depth),
    ),
    ExprData::Lam(n, t, b, bi, _) => LeanExpr::lam(
      n.clone(),
      batch_abstract(t, fvar_map, scope_depth, internal_depth),
      batch_abstract(b, fvar_map, scope_depth, internal_depth + 1),
      bi.clone(),
    ),
    ExprData::ForallE(n, t, b, bi, _) => LeanExpr::all(
      n.clone(),
      batch_abstract(t, fvar_map, scope_depth, internal_depth),
      batch_abstract(b, fvar_map, scope_depth, internal_depth + 1),
      bi.clone(),
    ),
    ExprData::LetE(n, t, v, b, nd, _) => LeanExpr::letE(
      n.clone(),
      batch_abstract(t, fvar_map, scope_depth, internal_depth),
      batch_abstract(v, fvar_map, scope_depth, internal_depth),
      batch_abstract(b, fvar_map, scope_depth, internal_depth + 1),
      *nd,
    ),
    ExprData::Proj(n, i, e, _) => LeanExpr::proj(
      n.clone(),
      i.clone(),
      batch_abstract(e, fvar_map, scope_depth, internal_depth),
    ),
    ExprData::Mdata(kvs, e, _) => LeanExpr::mdata(
      kvs.clone(),
      batch_abstract(e, fvar_map, scope_depth, internal_depth),
    ),
    // Sort, Const, MVar, Lit — no FVars or BVars to process.
    _ => expr.clone(),
  }
}

// =========================================================================
// Instantiation: BVar -> replacement
// =========================================================================

/// Lean's `instantiate1`: replace BVar(0) with `replacement`, decrement
/// BVar(i>0) by 1 (removing a binder level). The replacement is NOT
/// shifted — it's inserted as-is at the substitution depth.
///
/// `instantiate1` is used when peeling forall binders during recursor
/// construction (matching Lean C++ and lean4lean).
pub(crate) fn instantiate1(
  body: &LeanExpr,
  replacement: &LeanExpr,
) -> LeanExpr {
  instantiate1_at(body, replacement, 0)
}

pub(super) fn instantiate1_at(
  body: &LeanExpr,
  replacement: &LeanExpr,
  depth: u64,
) -> LeanExpr {
  match body.as_data() {
    ExprData::Bvar(idx, _) => {
      let i = nat_to_u64(idx);
      if i == depth {
        replacement.clone()
      } else if i > depth {
        LeanExpr::bvar(Nat::from(i - 1))
      } else {
        body.clone()
      }
    },
    ExprData::App(f, a, _) => LeanExpr::app(
      instantiate1_at(f, replacement, depth),
      instantiate1_at(a, replacement, depth),
    ),
    ExprData::Lam(n, t, b, bi, _) => LeanExpr::lam(
      n.clone(),
      instantiate1_at(t, replacement, depth),
      instantiate1_at(b, replacement, depth + 1),
      bi.clone(),
    ),
    ExprData::ForallE(n, t, b, bi, _) => LeanExpr::all(
      n.clone(),
      instantiate1_at(t, replacement, depth),
      instantiate1_at(b, replacement, depth + 1),
      bi.clone(),
    ),
    ExprData::LetE(n, t, v, b, nd, _) => LeanExpr::letE(
      n.clone(),
      instantiate1_at(t, replacement, depth),
      instantiate1_at(v, replacement, depth),
      instantiate1_at(b, replacement, depth + 1),
      *nd,
    ),
    ExprData::Proj(n, i, e, _) => LeanExpr::proj(
      n.clone(),
      i.clone(),
      instantiate1_at(e, replacement, depth),
    ),
    ExprData::Mdata(kvs, e, _) => {
      LeanExpr::mdata(kvs.clone(), instantiate1_at(e, replacement, depth))
    },
    _ => body.clone(),
  }
}

/// Multi-argument reverse instantiation: replace BVar(0)..BVar(n-1) with
/// `args[0]..args[n-1]` simultaneously, and decrement BVar(i >= n) by n.
///
/// Matches Lean C++ `instantiate_rev(e, n, subst)`. At binder depth `d`,
/// BVar(d + i) for i < n becomes `shift_vars(args[i], d, 0)`, and
/// BVar(d + i) for i >= n becomes BVar(d + i - n).
pub(super) fn instantiate_rev(body: &LeanExpr, args: &[LeanExpr]) -> LeanExpr {
  if args.is_empty() {
    return body.clone();
  }
  instantiate_rev_at(body, args, 0)
}

fn instantiate_rev_at(
  body: &LeanExpr,
  args: &[LeanExpr],
  depth: u64,
) -> LeanExpr {
  let n = args.len() as u64;
  match body.as_data() {
    ExprData::Bvar(idx, _) => {
      let i = nat_to_u64(idx);
      if i >= depth {
        let ridx = i - depth;
        if ridx < n {
          // Replace with args[ridx], shifted up by depth for the binders we're under.
          shift_vars(&args[ridx as usize], depth as usize, 0)
        } else {
          // Free BVar past our substitution range: decrement by n.
          LeanExpr::bvar(Nat::from(i - n))
        }
      } else {
        // Bound by an expression-internal binder — unchanged.
        body.clone()
      }
    },
    ExprData::App(f, a, _) => LeanExpr::app(
      instantiate_rev_at(f, args, depth),
      instantiate_rev_at(a, args, depth),
    ),
    ExprData::Lam(name, t, b, bi, _) => LeanExpr::lam(
      name.clone(),
      instantiate_rev_at(t, args, depth),
      instantiate_rev_at(b, args, depth + 1),
      bi.clone(),
    ),
    ExprData::ForallE(name, t, b, bi, _) => LeanExpr::all(
      name.clone(),
      instantiate_rev_at(t, args, depth),
      instantiate_rev_at(b, args, depth + 1),
      bi.clone(),
    ),
    ExprData::LetE(name, t, v, b, nd, _) => LeanExpr::letE(
      name.clone(),
      instantiate_rev_at(t, args, depth),
      instantiate_rev_at(v, args, depth),
      instantiate_rev_at(b, args, depth + 1),
      *nd,
    ),
    ExprData::Proj(name, i, e, _) => LeanExpr::proj(
      name.clone(),
      i.clone(),
      instantiate_rev_at(e, args, depth),
    ),
    ExprData::Mdata(kvs, e, _) => {
      LeanExpr::mdata(kvs.clone(), instantiate_rev_at(e, args, depth))
    },
    // Sort, Const, Lit, FVar, MVar — no BVars to substitute.
    _ => body.clone(),
  }
}

/// Peel `n` forall binders and substitute their variables with `args`.
///
/// Matches Lean C++ `instantiate_pi_params` (`inductive.cpp:954-960`):
/// peel n foralls (taking just the body), then substitute all at once.
///
/// Equivalent to calling `instantiate1(body, args[i])` iteratively
/// for each peeled forall, which is what our recursor builder does
/// inline. This function packages that pattern for the expand phase.
pub(super) fn instantiate_pi_params(
  typ: &LeanExpr,
  n: usize,
  args: &[LeanExpr],
) -> LeanExpr {
  debug_assert!(
    args.len() >= n,
    "instantiate_pi_params: args.len()={} < n={}",
    args.len(),
    n
  );
  let mut cur = typ.clone();
  for arg in args.iter().take(n) {
    match cur.as_data() {
      ExprData::ForallE(_, _, body, _, _) => {
        cur = instantiate1(body, arg);
      },
      _ => break,
    }
  }
  cur
}

// NOTE: `subst_at` / `subst_bvar0` (shift-and-substitute-BVar-0 helpers)
// were removed in Round 4 cleanup. They were marked `#[allow(dead_code)]`
// and have zero callers. `instantiate1` and `instantiate_rev` cover the
// substitution shapes the live pipeline actually uses — if a
// shift-preserving substitution is ever needed, resurrect from git.

/// Convert spec_params from BVar form to FVar form.
///
/// Spec_params use BVars relative to the param context: BVar(0) is the
/// last (innermost) param, BVar(n_params-1) is the first. We want
/// `BVar(i) → param_fvars[n_params - 1 - i]` for i < n_params, and
/// `BVar(i) → BVar(i - n_params)` for i >= n_params (a free BVar past
/// the param context, e.g., an outer binder that's still in scope).
///
/// Implemented as a single `instantiate_rev` call with a reversed
/// param vector. Earlier versions iterated `instantiate1` n times,
/// which produced the same result for this call site's inputs (because
/// `param_fvars` are fresh closed FVars, so the repeated decrement
/// cascade is benign) but at `O(n · |body|)` per spec_param. The
/// single-pass `instantiate_rev` is `O(|body|)` and clearer — it's
/// the exact Lean idiom for this substitution shape
/// (matches `instantiate_rev(e, n, subst)` in the C++ kernel).
///
/// Safety note: this relies on `param_fvars` being closed (no BVars
/// inside). If that invariant is ever violated, per-step substitution
/// and single-pass substitution would diverge — but `forall_telescope`
/// guarantees fresh FVars, and FVars are by construction closed.
pub(super) fn instantiate_spec_with_fvars(
  spec_params: &[LeanExpr],
  param_fvars: &[LeanExpr],
) -> Vec<LeanExpr> {
  // Reverse once; `instantiate_rev` expects `args[i]` to replace `BVar(i)`,
  // but our convention is `BVar(0) = innermost = param_fvars[n-1]`.
  let reversed: Vec<LeanExpr> = param_fvars.iter().rev().cloned().collect();
  spec_params.iter().map(|sp| instantiate_rev(sp, &reversed)).collect()
}

// =========================================================================
// BVar shifting
// =========================================================================

/// Shift BVars UP by `amount` for BVars >= cutoff.
///
/// Used internally by `instantiate_rev_at` when substituting args under
/// inner binders (each args element is re-shifted by the current depth).
pub(super) fn shift_vars(
  expr: &LeanExpr,
  amount: usize,
  cutoff: usize,
) -> LeanExpr {
  if amount == 0 {
    return expr.clone();
  }
  match expr.as_data() {
    ExprData::Bvar(idx, _) => {
      let i = nat_to_usize(idx);
      if i >= cutoff {
        LeanExpr::bvar(Nat::from((i + amount) as u64))
      } else {
        expr.clone()
      }
    },
    ExprData::App(f, a, _) => LeanExpr::app(
      shift_vars(f, amount, cutoff),
      shift_vars(a, amount, cutoff),
    ),
    ExprData::Lam(n, t, b, bi, _) => LeanExpr::lam(
      n.clone(),
      shift_vars(t, amount, cutoff),
      shift_vars(b, amount, cutoff + 1),
      bi.clone(),
    ),
    ExprData::ForallE(n, t, b, bi, _) => LeanExpr::all(
      n.clone(),
      shift_vars(t, amount, cutoff),
      shift_vars(b, amount, cutoff + 1),
      bi.clone(),
    ),
    ExprData::LetE(n, t, v, b, nd, _) => LeanExpr::letE(
      n.clone(),
      shift_vars(t, amount, cutoff),
      shift_vars(v, amount, cutoff),
      shift_vars(b, amount, cutoff + 1),
      *nd,
    ),
    ExprData::Proj(n, i, e, _) => {
      LeanExpr::proj(n.clone(), i.clone(), shift_vars(e, amount, cutoff))
    },
    ExprData::Mdata(kvs, e, _) => {
      LeanExpr::mdata(kvs.clone(), shift_vars(e, amount, cutoff))
    },
    _ => expr.clone(),
  }
}

// =========================================================================
// Universe substitution
// =========================================================================

/// Substitute universe parameters in expressions.
pub(crate) fn subst_levels(
  expr: &LeanExpr,
  params: &[Name],
  univs: &[Level],
) -> LeanExpr {
  if params.is_empty() || univs.is_empty() {
    return expr.clone();
  }
  match expr.as_data() {
    ExprData::Sort(lvl, _) => LeanExpr::sort(subst_level(lvl, params, univs)),
    ExprData::Const(name, us, _) => LeanExpr::cnst(
      name.clone(),
      us.iter().map(|u| subst_level(u, params, univs)).collect(),
    ),
    ExprData::App(f, a, _) => LeanExpr::app(
      subst_levels(f, params, univs),
      subst_levels(a, params, univs),
    ),
    ExprData::Lam(n, t, b, bi, _) => LeanExpr::lam(
      n.clone(),
      subst_levels(t, params, univs),
      subst_levels(b, params, univs),
      bi.clone(),
    ),
    ExprData::ForallE(n, t, b, bi, _) => LeanExpr::all(
      n.clone(),
      subst_levels(t, params, univs),
      subst_levels(b, params, univs),
      bi.clone(),
    ),
    ExprData::LetE(n, t, v, b, nd, _) => LeanExpr::letE(
      n.clone(),
      subst_levels(t, params, univs),
      subst_levels(v, params, univs),
      subst_levels(b, params, univs),
      *nd,
    ),
    ExprData::Proj(n, i, e, _) => {
      LeanExpr::proj(n.clone(), i.clone(), subst_levels(e, params, univs))
    },
    ExprData::Mdata(md, e, _) => {
      LeanExpr::mdata(md.clone(), subst_levels(e, params, univs))
    },
    _ => expr.clone(),
  }
}

/// Substitute universe parameters in a level.
///
/// Uses the smart constructors `Level::max_smart` and `Level::imax_smart` so
/// that substituting away parameters produces the same canonical form the
/// kernel sees post-ingress (`KUniv::max` does the same simplifications at
/// kernel-side construction time). Without this normalization, `Max(Succ Param u,
/// Succ Param v)` substituted to `Max(Succ Zero, Succ Zero)` stays as a `Max`
/// node compile-side while the kernel collapses it to `Succ Zero` —
/// `sort_aux_by_partition_refinement` would then disagree with the kernel's
/// `canonical_aux_order` on whether two structurally-different aux types
/// (e.g. `Sort 1` vs `Sort (max 1 1)`) are equivalent.
pub(super) fn subst_level(
  lvl: &Level,
  params: &[Name],
  univs: &[Level],
) -> Level {
  match lvl.as_data() {
    LevelData::Zero(_) | LevelData::Mvar(_, _) => lvl.clone(),
    LevelData::Succ(l, _) => Level::succ(subst_level(l, params, univs)),
    LevelData::Max(a, b, _) => Level::max_smart(
      subst_level(a, params, univs),
      subst_level(b, params, univs),
    ),
    LevelData::Imax(a, b, _) => Level::imax_smart(
      subst_level(a, params, univs),
      subst_level(b, params, univs),
    ),
    LevelData::Param(name, _) => {
      for (i, p) in params.iter().enumerate() {
        if p == name && i < univs.len() {
          return univs[i].clone();
        }
      }
      lvl.clone()
    },
  }
}

// =========================================================================
// Restore: replace auxiliary const refs with original nested expressions
// =========================================================================

/// Context for restoring auxiliary const references back to original nested
/// inductive applications.
///
/// Produced by `expand_nested_block` and consumed after all auxiliary constants
/// (rec, casesOn, below, brecOn, etc.) have been generated.
pub(super) struct RestoreCtx {
  /// `aux_name → nested_expr`: the original nested application with block
  /// param FVars. Example: `"_nested.Array_1" → Array.{max u v}(Part.{u,v} fvar_α fvar_β)`
  pub aux_to_nested: FxHashMap<Name, LeanExpr>,
  /// `aux_ctor_name → (original_ctor_name, original_ind_name)`: maps auxiliary
  /// constructor names back to originals for prefix replacement.
  pub aux_ctor_map: FxHashMap<Name, (Name, Name)>,
  /// `aux_rec_name → canonical_rec_name`: maps auxiliary recursor names
  /// (e.g., `_nested.Array_1.rec`) to their canonical names (e.g., `Part.rec_1`).
  pub aux_rec_map: FxHashMap<Name, Name>,
  /// Block-param FVars used during expansion. These are the free variables
  /// in the `aux_to_nested` expressions.
  pub block_param_fvars: Vec<LeanExpr>,
  /// Number of block parameters.
  pub n_params: usize,
  /// Block-scoped cache initialised on the first `restore()` call and
  /// reused by every subsequent call on this context.
  ///
  /// Why this is safe to share across calls: `forall_telescope` /
  /// `lambda_telescope` allocate FVars via the deterministic
  /// `fresh_fvar("rp", i)` scheme (see `fresh_fvar` in this file), so
  /// `subst_fvars` is identical for every `restore()` call — any
  /// per-aux precomputation (`batch_abstract` + `instantiate_rev`)
  /// yields the same result, and `walk_cache` entries keyed on an
  /// expression hash remain valid regardless of which restored
  /// expression first populated them.
  cached: std::cell::RefCell<Option<RestoreStateCache>>,
}

/// The block-scoped cached state referenced by `RestoreCtx::cached`.
/// Populated lazily on the first `restore()` call.
struct RestoreStateCache {
  /// `aux_name → nested instantiated with the per-call subst_fvars`.
  ///
  /// Previously `replace_walk` recomputed `batch_abstract` +
  /// `instantiate_rev` on every encounter of an aux, even though the
  /// inputs were identical across the entire block; now materialised
  /// once.
  aux_restored: FxHashMap<Name, LeanExpr>,
  /// `aux_ind name → (orig_head_levels, orig_ind_args)` derived from
  /// decomposing the restored nested expression. Used for the aux-ctor
  /// restoration path where we need to rebuild
  /// `orig_ctor.{I_lvls} spec_params`.
  aux_decomp: FxHashMap<Name, (Vec<Level>, Vec<LeanExpr>)>,
  /// Walk memoization shared across every `restore()` call on this
  /// context. DAG-shared subterms between recursor rules collapse to a
  /// single rewrite.
  walk_cache: FxHashMap<blake3::Hash, LeanExpr>,
}

/// Per-call borrow of the cached state. The lifetime ties the state's
/// `RefCell` borrow to the `replace_walk` call chain.
struct RestoreState<'a> {
  ctx: &'a RestoreCtx,
  cache: std::cell::RefMut<'a, RestoreStateCache>,
}

impl RestoreCtx {
  /// Build a context with an empty cache. The cache is populated lazily
  /// on the first `restore()` call.
  pub(super) fn new(
    aux_to_nested: FxHashMap<Name, LeanExpr>,
    aux_ctor_map: FxHashMap<Name, (Name, Name)>,
    aux_rec_map: FxHashMap<Name, Name>,
    block_param_fvars: Vec<LeanExpr>,
    n_params: usize,
  ) -> Self {
    Self {
      aux_to_nested,
      aux_ctor_map,
      aux_rec_map,
      block_param_fvars,
      n_params,
      cached: std::cell::RefCell::new(None),
    }
  }

  /// Lazily initialise the cached per-aux substitution + walk cache.
  ///
  /// Called at the top of every `restore()` invocation. The cache is
  /// keyed implicitly on `(self.n_params, self.aux_to_nested,
  /// self.block_param_fvars)` — all inherent to the `RestoreCtx` —
  /// which means entries populated by one call remain valid for every
  /// subsequent call on the same context.
  fn ensure_cache(&self) {
    if self.cached.borrow().is_some() {
      return;
    }

    // Canonical telescope FVars: every real `restore()` call uses
    // `forall_telescope`/`lambda_telescope` which in turn allocate via
    // `fresh_fvar("rp", i)` — deterministic on the index — so these
    // are the exact FVars every call sees after peeling.
    let as_fvars: Vec<LeanExpr> = (0..self.n_params)
      .map(|i| {
        let (_, fv) = fresh_fvar("rp", i);
        fv
      })
      .collect();
    let subst_fvars: Vec<LeanExpr> = as_fvars.iter().rev().cloned().collect();

    let bp_fvar_map: FxHashMap<Name, usize> = self
      .block_param_fvars
      .iter()
      .enumerate()
      .filter_map(|(i, fv)| match fv.as_data() {
        ExprData::Fvar(n, _) => Some((n.clone(), i)),
        _ => None,
      })
      .collect();

    let mut aux_restored: FxHashMap<Name, LeanExpr> =
      FxHashMap::with_capacity_and_hasher(
        self.aux_to_nested.len(),
        Default::default(),
      );
    let mut aux_decomp: FxHashMap<Name, (Vec<Level>, Vec<LeanExpr>)> =
      FxHashMap::default();
    for (aux_name, nested) in &self.aux_to_nested {
      let abstracted = batch_abstract(nested, &bp_fvar_map, self.n_params, 0);
      let restored = instantiate_rev(&abstracted, &subst_fvars);
      let (orig_head, orig_args) = decompose_apps(&restored);
      if let ExprData::Const(_, orig_levels, _) = orig_head.as_data() {
        aux_decomp.insert(aux_name.clone(), (orig_levels.clone(), orig_args));
      }
      aux_restored.insert(aux_name.clone(), restored);
    }

    *self.cached.borrow_mut() = Some(RestoreStateCache {
      aux_restored,
      aux_decomp,
      walk_cache: FxHashMap::default(),
    });
  }

  /// Restore a complete expression (type or value) by peeling params,
  /// walking the body to replace aux references, and re-wrapping.
  ///
  /// Matches C++ `restore_nested` (`inductive.cpp:828-872`).
  pub(super) fn restore(&self, expr: &LeanExpr) -> LeanExpr {
    if self.aux_to_nested.is_empty()
      && self.aux_ctor_map.is_empty()
      && self.aux_rec_map.is_empty()
    {
      return expr.clone();
    }

    self.ensure_cache();

    // Peel n_params Pi or Lambda binders, creating fresh locals. These
    // coincide with the FVars used by `ensure_cache` to precompute
    // `aux_restored`.
    let is_pi = matches!(expr.as_data(), ExprData::ForallE(..));
    let (_as_fvars, as_decls, body) = if is_pi {
      forall_telescope(expr, self.n_params, "rp", 0)
    } else {
      lambda_telescope(expr, self.n_params, "rp", 0)
    };

    let cache_borrow = self.cached.borrow_mut();
    let cache_ref = std::cell::RefMut::map(cache_borrow, |c| {
      c.as_mut().expect("RestoreStateCache must be initialised")
    });
    let mut state = RestoreState { ctx: self, cache: cache_ref };

    let restored_body = state.replace_walk(&body);

    if is_pi {
      mk_forall(restored_body, &as_decls)
    } else {
      mk_lambda(restored_body, &as_decls)
    }
  }
}

impl<'a> RestoreState<'a> {
  /// Walk an expression and replace auxiliary const references.
  ///
  /// Memoizes on `e`'s structural hash. DAG-shared subterms are visited
  /// once regardless of how many times they appear in the walked tree.
  fn replace_walk(&mut self, e: &LeanExpr) -> LeanExpr {
    let key = *e.get_hash();
    if let Some(cached) = self.cache.walk_cache.get(&key) {
      return cached.clone();
    }
    let result = self.replace_walk_uncached(e);
    self.cache.walk_cache.insert(key, result.clone());
    result
  }

  fn replace_walk_uncached(&mut self, e: &LeanExpr) -> LeanExpr {
    // Check for bare Const matching aux_rec_map (recursor rename).
    if let ExprData::Const(name, levels, _) = e.as_data()
      && let Some(new_name) = self.ctx.aux_rec_map.get(name)
    {
      return LeanExpr::cnst(new_name.clone(), levels.clone());
    }

    // Check for application whose head is an aux type or aux constructor.
    let (head, args) = decompose_apps(e);
    if let ExprData::Const(name, levels, _) = head.as_data() {
      // Case 1: aux type reference → replace with original nested app.
      if let Some(restored) = self.cache.aux_restored.get(name).cloned() {
        let n = self.ctx.n_params;
        debug_assert!(
          args.len() >= n,
          "restore: aux {} has {} args but n_params={}",
          name.pretty(),
          args.len(),
          n,
        );
        // Apply remaining args (indices past params).
        let mut result = restored;
        for idx_arg in args.iter().skip(n) {
          result = LeanExpr::app(result, self.replace_walk(idx_arg));
        }
        return result;
      }

      // Case 2: aux constructor reference → rename and restore.
      // Matches C++ restore_nested lines 852-866: look up the nested
      // expression for the constructor's aux inductive, decompose it to
      // get the original ind's Const (with levels), then rename the
      // constructor and apply the original ind's params + remaining args.
      //
      // `aux_ctor_map` stores `(orig_ctor, aux_ind)`, so we can look up the
      // aux inductive's nested expression in `aux_to_nested` directly — no
      // prefix scan needed.
      if let Some((orig_ctor, aux_ind)) = self.ctx.aux_ctor_map.get(name) {
        if let Some((orig_levels, orig_ind_args)) =
          self.cache.aux_decomp.get(aux_ind).cloned()
        {
          // Build: orig_ctor.{I_lvls} spec_params remaining_args
          let new_fn = LeanExpr::cnst(orig_ctor.clone(), orig_levels);
          let mut result = new_fn;
          for a in orig_ind_args {
            result = LeanExpr::app(result, a);
          }
          for idx_arg in args.iter().skip(self.ctx.n_params) {
            result = LeanExpr::app(result, self.replace_walk(idx_arg));
          }
          return result;
        }

        // Fallback: just rename the const and recurse args. Hit when the
        // aux's nested expression doesn't decompose to a Const head — in
        // practice never, but kept for defensive parity with the original
        // implementation.
        let new_head = LeanExpr::cnst(orig_ctor.clone(), levels.clone());
        let mut result = new_head;
        for a in &args {
          result = LeanExpr::app(result, self.replace_walk(a));
        }
        return result;
      }

      // Case 3: aux rec name in application position.
      if let Some(new_name) = self.ctx.aux_rec_map.get(name) {
        let new_head = LeanExpr::cnst(new_name.clone(), levels.clone());
        let mut result = new_head;
        for a in &args {
          result = LeanExpr::app(result, self.replace_walk(a));
        }
        return result;
      }
    }

    // No match — recurse into sub-expressions.
    match e.as_data() {
      ExprData::App(f, a, _) => {
        LeanExpr::app(self.replace_walk(f), self.replace_walk(a))
      },
      ExprData::Lam(n, t, b, bi, _) => LeanExpr::lam(
        n.clone(),
        self.replace_walk(t),
        self.replace_walk(b),
        bi.clone(),
      ),
      ExprData::ForallE(n, t, b, bi, _) => LeanExpr::all(
        n.clone(),
        self.replace_walk(t),
        self.replace_walk(b),
        bi.clone(),
      ),
      ExprData::LetE(n, t, v, b, nd, _) => LeanExpr::letE(
        n.clone(),
        self.replace_walk(t),
        self.replace_walk(v),
        self.replace_walk(b),
        *nd,
      ),
      ExprData::Proj(n, i, val, _) => {
        LeanExpr::proj(n.clone(), i.clone(), self.replace_walk(val))
      },
      ExprData::Mdata(md, inner, _) => {
        LeanExpr::mdata(md.clone(), self.replace_walk(inner))
      },
      _ => e.clone(),
    }
  }
}

/// Open lambda binders into FVars (matching forall_telescope but for lambdas).
pub(crate) fn lambda_telescope(
  expr: &LeanExpr,
  n: usize,
  prefix: &str,
  offset: usize,
) -> (Vec<LeanExpr>, Vec<LocalDecl>, LeanExpr) {
  let mut fvars = Vec::new();
  let mut decls = Vec::new();
  let mut cur = expr.clone();
  for i in 0..n {
    match cur.as_data() {
      ExprData::Lam(name, dom, body, bi, _) => {
        let (fv_name, fv) = fresh_fvar(prefix, offset + i);
        let clean_dom = instantiate_fvars_in_domain(dom, &fvars, &decls);
        decls.push(LocalDecl {
          fvar_name: fv_name,
          binder_name: name.clone(),
          domain: clean_dom,
          info: bi.clone(),
        });
        fvars.push(fv.clone());
        cur = instantiate1(body, &fv);
      },
      _ => break,
    }
  }
  (fvars, decls, cur)
}

/// Instantiate FVars in a domain expression (for dependent binder domains).
fn instantiate_fvars_in_domain(
  dom: &LeanExpr,
  _fvars: &[LeanExpr],
  _decls: &[LocalDecl],
) -> LeanExpr {
  // Domain is already in FVar form from instantiate1 calls.
  dom.clone()
}

// =========================================================================
// Beta-reduction
// =========================================================================

/// Reduce all beta-redexes in an expression.
///
/// `App(Lam(_, _, body, _), arg)` → `instantiate1(body, arg)` (then recurse).
///
/// Lean's elaborator auto-reduces beta-redexes during `inferType`/`whnf`.
/// Our FVar-based construction can leave unreduced redexes when lambda-valued
/// spec_params (e.g., `λ _ => String` for function-typed inductive parameters)
/// are substituted into forall bodies and later applied.
pub(super) fn beta_reduce(expr: &LeanExpr) -> LeanExpr {
  // Head-only beta reduction.
  //
  // Reduces redexes on the outer application spine only; does NOT recurse
  // into lambda/forall/let bodies, projections, or non-head subexpressions.
  //
  // Lean's kernel follows the same policy when constructing recursor types
  // for nested inductives (see `elim_nested_inductive_fn::replace_if_nested`
  // and `restore_nested` in `refs/lean4/src/kernel/inductive.cpp`): it calls
  // `instantiate_rev` / `mk_app` to substitute lambda-valued parameters but
  // never beta-reduces the substituted term. The result can contain
  // `(λ_. T) arg` in field-type positions (e.g. the `v : β k` field of
  // `Internal.Impl.inner` when `β := λ_. PrefixTreeNode α β cmp`), and Lean
  // preserves that shape in the stored recursor.
  //
  // Our earlier implementation was a full recursive walk, which eliminated
  // those redexes and broke alpha-congruence with Lean's original recursor.
  // Head-only reduction is sufficient for the call sites in recursor.rs —
  // they only need to expose a top-level `ForallE` after param substitution.
  match expr.as_data() {
    ExprData::App(..) => {
      // Collect the application spine, reducing redexes as they surface.
      let mut head = expr.clone();
      let mut args: Vec<LeanExpr> = Vec::new();
      while let ExprData::App(f, a, _) = head.as_data() {
        args.push(a.clone());
        head = f.clone();
      }
      args.reverse();
      // Now `head` is a non-App; try to reduce `head args[0]` into head.
      let mut i = 0;
      while i < args.len()
        && let ExprData::Lam(_, _, body, _, _) = head.as_data()
      {
        head = instantiate1(body, &args[i]);
        i += 1;
      }
      // Re-apply remaining args.
      let mut result = head;
      for a in &args[i..] {
        result = LeanExpr::app(result, a.clone());
      }
      result
    },
    // Non-App: no top-level redex to reduce.
    _ => expr.clone(),
  }
}

// =========================================================================
// Nested universe rewriting
// =========================================================================

/// Targeted rewrite of nested type universe levels in constructor fields.
///
/// Lean's kernel recomputes nested type universes from the element's sort
/// (via `elim_nested_inductive_fn`), but the elaborator stores the original
/// universe. For example, a constructor field `Array (Part α β)` stores
/// `Array.{u}`, but the recursor needs `Array.{max u v}` since Part lives
/// in `Sort (max u v)`.
///
/// This function walks the expression and for each application
/// `Const(aux_name, levels) args...` where `aux_name` is an auxiliary flat
/// member AND at least one of the first `n_params` args references a block
/// member, rewrites the Const's levels to `occurrence_level_args`.
///
/// Non-nested occurrences (like `Array Nat`) are left unchanged.
/// Rewrite nested-aux `Const` level args with a caller-managed cache.
///
/// Use a shared cache when rewriting multiple expressions against the
/// SAME `aux_info` and `block_names` — every constructor type in a
/// block, every recursor rule, etc. — so DAG-shared subterms (common in
/// Mathlib ctor types with shared implicit-arg prefixes) collapse to a
/// single traversal per unique subterm.
///
/// The cache must only be reused across calls whose `aux_info` and
/// `block_names` are identical; mixing keys between maps would return
/// stale rewrites.
pub(super) fn rewrite_nested_const_levels_cached(
  expr: &LeanExpr,
  aux_info: &std::collections::HashMap<Name, (usize, Vec<Level>)>,
  block_names: &rustc_hash::FxHashSet<Name>,
  cache: &mut FxHashMap<blake3::Hash, LeanExpr>,
) -> LeanExpr {
  let key = *expr.get_hash();
  if let Some(cached) = cache.get(&key) {
    return cached.clone();
  }
  let result =
    rewrite_nested_const_levels_walk(expr, aux_info, block_names, cache);
  cache.insert(key, result.clone());
  result
}

fn rewrite_nested_const_levels_walk(
  expr: &LeanExpr,
  aux_info: &std::collections::HashMap<Name, (usize, Vec<Level>)>,
  block_names: &rustc_hash::FxHashSet<Name>,
  cache: &mut FxHashMap<blake3::Hash, LeanExpr>,
) -> LeanExpr {
  // Try to decompose as an application of an auxiliary Const.
  let (head, args) = decompose_apps(expr);
  if let ExprData::Const(name, levels, _) = head.as_data()
    && let Some((n_params, new_levels)) = aux_info.get(name)
  {
    let has_nested_ref = args
      .iter()
      .take(*n_params)
      .any(|a| super::nested::expr_mentions_any_name(a, block_names));
    if has_nested_ref && new_levels.len() == levels.len() {
      // Rewrite head levels and recurse into args.
      let new_head = LeanExpr::cnst(name.clone(), new_levels.clone());
      let mut result = new_head;
      for a in &args {
        result = LeanExpr::app(
          result,
          rewrite_nested_const_levels_cached(a, aux_info, block_names, cache),
        );
      }
      return result;
    }
  }

  // Not a rewritable app — recurse into sub-expressions.
  match expr.as_data() {
    ExprData::App(f, a, _) => LeanExpr::app(
      rewrite_nested_const_levels_cached(f, aux_info, block_names, cache),
      rewrite_nested_const_levels_cached(a, aux_info, block_names, cache),
    ),
    ExprData::Lam(n, t, b, bi, _) => LeanExpr::lam(
      n.clone(),
      rewrite_nested_const_levels_cached(t, aux_info, block_names, cache),
      rewrite_nested_const_levels_cached(b, aux_info, block_names, cache),
      bi.clone(),
    ),
    ExprData::ForallE(n, t, b, bi, _) => LeanExpr::all(
      n.clone(),
      rewrite_nested_const_levels_cached(t, aux_info, block_names, cache),
      rewrite_nested_const_levels_cached(b, aux_info, block_names, cache),
      bi.clone(),
    ),
    ExprData::LetE(n, t, v, b, nd, _) => LeanExpr::letE(
      n.clone(),
      rewrite_nested_const_levels_cached(t, aux_info, block_names, cache),
      rewrite_nested_const_levels_cached(v, aux_info, block_names, cache),
      rewrite_nested_const_levels_cached(b, aux_info, block_names, cache),
      *nd,
    ),
    ExprData::Proj(n, i, e, _) => LeanExpr::proj(
      n.clone(),
      i.clone(),
      rewrite_nested_const_levels_cached(e, aux_info, block_names, cache),
    ),
    ExprData::Mdata(md, e, _) => LeanExpr::mdata(
      md.clone(),
      rewrite_nested_const_levels_cached(e, aux_info, block_names, cache),
    ),
    _ => expr.clone(),
  }
}

// =========================================================================
// Expression utilities
// =========================================================================

/// Create a `Const` expression with the given name and universe levels.
pub(super) fn mk_const(name: &Name, univs: &[Level]) -> LeanExpr {
  LeanExpr::cnst(name.clone(), univs.to_vec())
}

/// Strip type annotation wrappers from a type expression.
///
/// Matches Lean's `Expr.consumeTypeAnnotations` (Expr.lean:1721-1727):
/// - `outParam α` → recurse on `α`
/// - `semiOutParam α` → recurse on `α`
/// - `optParam α default` → recurse on `α`
/// - `autoParam α tactic` → recurse on `α`
///
/// Called by the kernel's `mk_local_decl` during inductive processing
/// to ensure parameter/field types are clean before entering the local context.
pub(crate) fn consume_type_annotations(e: &LeanExpr) -> LeanExpr {
  let (head, args) = decompose_apps(e);
  if let ExprData::Const(name, _, _) = head.as_data() {
    let n = name.pretty();
    if (n == "outParam" || n == "semiOutParam") && args.len() == 1 {
      // outParam.{u} (α : Sort u) := α — strip and recurse
      return consume_type_annotations(&args[0]);
    }
    if (n == "optParam" || n == "autoParam") && args.len() == 2 {
      // optParam.{u} (α : Sort u) (default : α) := α — strip to first arg
      return consume_type_annotations(&args[0]);
    }
  }
  e.clone()
}

/// Decompose an application spine: `f a1 a2 ... an` -> `(f, [a1, ..., an])`.
pub(crate) fn decompose_apps(expr: &LeanExpr) -> (LeanExpr, Vec<LeanExpr>) {
  let mut args = Vec::new();
  let mut cur = expr.clone();
  while let ExprData::App(f, a, _) = cur.as_data() {
    args.push(a.clone());
    cur = f.clone();
  }
  args.reverse();
  (cur, args)
}

/// Count the number of leading forall binders in an expression.
pub(super) fn count_foralls(expr: &LeanExpr) -> usize {
  let mut n = 0;
  let mut cur = expr.clone();
  loop {
    match cur.as_data() {
      ExprData::ForallE(_, _, body, _, _) => {
        n += 1;
        cur = body.clone();
      },
      _ => return n,
    }
  }
}

/// Apply an expression to a sequence of arguments: `f a1 a2 ... an`.
pub(super) fn mk_app_n(f: LeanExpr, args: &[LeanExpr]) -> LeanExpr {
  let mut result = f;
  for a in args {
    result = LeanExpr::app(result, a.clone());
  }
  result
}

/// Check if the head of `dom` (after peeling foralls) is one of the
/// given `motive_fvars`. Returns `Some(class_index)` if matched.
///
/// Substitute all occurrences of `Fvar(fvar_name)` with `replacement`.
///
/// Unlike `abstract_fvar` (which replaces FVar with BVar), this replaces
/// FVar with an arbitrary expression. Used when eliminating free FVars
/// that shouldn't appear in the final output.
pub(super) fn subst_fvar(
  expr: &LeanExpr,
  fvar_name: &Name,
  replacement: &LeanExpr,
) -> LeanExpr {
  match expr.as_data() {
    ExprData::Fvar(n, _) if n == fvar_name => replacement.clone(),
    ExprData::App(f, a, _) => LeanExpr::app(
      subst_fvar(f, fvar_name, replacement),
      subst_fvar(a, fvar_name, replacement),
    ),
    ExprData::Lam(n, t, b, bi, _) => LeanExpr::lam(
      n.clone(),
      subst_fvar(t, fvar_name, replacement),
      subst_fvar(b, fvar_name, replacement),
      bi.clone(),
    ),
    ExprData::ForallE(n, t, b, bi, _) => LeanExpr::all(
      n.clone(),
      subst_fvar(t, fvar_name, replacement),
      subst_fvar(b, fvar_name, replacement),
      bi.clone(),
    ),
    ExprData::LetE(n, t, v, b, nd, _) => LeanExpr::letE(
      n.clone(),
      subst_fvar(t, fvar_name, replacement),
      subst_fvar(v, fvar_name, replacement),
      subst_fvar(b, fvar_name, replacement),
      *nd,
    ),
    ExprData::Proj(n, i, e, _) => LeanExpr::proj(
      n.clone(),
      i.clone(),
      subst_fvar(e, fvar_name, replacement),
    ),
    ExprData::Mdata(kvs, e, _) => {
      LeanExpr::mdata(kvs.clone(), subst_fvar(e, fvar_name, replacement))
    },
    _ => expr.clone(),
  }
}

/// Replace constant names throughout an expression according to a name map.
///
/// Recursively traverses the expression tree, substituting `Const` names
/// and `Proj` type names that appear as keys in `map` with their
/// corresponding values. All other expression structure is preserved.
///
/// Used by `rename_below_indc` to fix up constructor types when creating
/// alpha-collapsed aliases: the canonical `.below` constructor types
/// reference the canonical parent inductive and its constructors, which
/// must be rewritten to reference the alias target.
pub(super) fn replace_const_names(
  expr: &LeanExpr,
  map: &std::collections::HashMap<Name, Name>,
) -> LeanExpr {
  if map.is_empty() {
    return expr.clone();
  }
  let mut cache: FxHashMap<blake3::Hash, LeanExpr> = FxHashMap::default();
  replace_const_names_cached(expr, map, &mut cache)
}

/// Like [`replace_const_names`] but accepts a caller-managed memoization
/// cache. Use this when calling the rewriter many times with the SAME
/// `map` in a tight loop — typical for `expand_nested_block`'s alias
/// pass and `compute_aux_perm`'s spec-param normalization, where
/// multiple expressions share large DAG substructure. The cache must
/// only be reused for calls with identical `map`; using one cache
/// across different maps would return stale results.
pub(super) fn replace_const_names_cached(
  expr: &LeanExpr,
  map: &std::collections::HashMap<Name, Name>,
  cache: &mut FxHashMap<blake3::Hash, LeanExpr>,
) -> LeanExpr {
  if map.is_empty() {
    return expr.clone();
  }
  let key = *expr.get_hash();
  if let Some(cached) = cache.get(&key) {
    return cached.clone();
  }
  let result = match expr.as_data() {
    ExprData::Const(name, lvls, _) => {
      let new_name = map.get(name).cloned().unwrap_or_else(|| name.clone());
      LeanExpr::cnst(new_name, lvls.clone())
    },
    ExprData::App(f, a, _) => LeanExpr::app(
      replace_const_names_cached(f, map, cache),
      replace_const_names_cached(a, map, cache),
    ),
    ExprData::ForallE(n, d, b, bi, _) => LeanExpr::all(
      n.clone(),
      replace_const_names_cached(d, map, cache),
      replace_const_names_cached(b, map, cache),
      bi.clone(),
    ),
    ExprData::Lam(n, d, b, bi, _) => LeanExpr::lam(
      n.clone(),
      replace_const_names_cached(d, map, cache),
      replace_const_names_cached(b, map, cache),
      bi.clone(),
    ),
    ExprData::LetE(n, t, v, b, nd, _) => LeanExpr::letE(
      n.clone(),
      replace_const_names_cached(t, map, cache),
      replace_const_names_cached(v, map, cache),
      replace_const_names_cached(b, map, cache),
      *nd,
    ),
    ExprData::Proj(type_name, idx, e, _) => {
      let new_type_name =
        map.get(type_name).cloned().unwrap_or_else(|| type_name.clone());
      LeanExpr::proj(
        new_type_name,
        idx.clone(),
        replace_const_names_cached(e, map, cache),
      )
    },
    ExprData::Mdata(kvs, e, _) => {
      LeanExpr::mdata(kvs.clone(), replace_const_names_cached(e, map, cache))
    },
    // BVar, FVar, MVar, Sort, Lit — no constant names to replace.
    _ => expr.clone(),
  };
  cache.insert(key, result.clone());
  result
}

/// This replaces the BVar-range-based `is_motive_application` and
/// `find_motive_class` with a simple structural FVar comparison.
pub(super) fn find_motive_fvar(
  dom: &LeanExpr,
  motive_fvars: &[LeanExpr],
) -> Option<usize> {
  let mut ty = dom.clone();
  loop {
    match ty.as_data() {
      ExprData::ForallE(_, _, body, _, _) => ty = body.clone(),
      _ => {
        let (head, _) = decompose_apps(&ty);
        if let ExprData::Fvar(name, _) = head.as_data() {
          for (j, mfv) in motive_fvars.iter().enumerate() {
            if let ExprData::Fvar(mn, _) = mfv.as_data()
              && name == mn
            {
              return Some(j);
            }
          }
        }
        return None;
      },
    }
  }
}

// =========================================================================
// Kernel-backed sort level inference
// =========================================================================

/// Ensure PUnit and PProd are in `stt.kenv` for kernel type inference.
///
/// These are prelude constants with fixed definitions that brecOn's
/// `get_level` needs to resolve. Hardcoded so they're available even
/// without a Lean environment (e.g. during decompile roundtrip).
///
/// ```text
/// inductive PUnit : Sort u where | unit : PUnit
/// structure PProd (α : Sort u) (β : Sort v) : Sort (max 1 u v) where
///   mk :: (fst : α) (snd : β)
/// ```
/// Ensure PUnit and PProd are in the given kenv for kernel type inference.
/// Accepts `kctx` so callers can choose which KernelCtx to populate.
pub(crate) fn ensure_prelude_in_kenv_of(
  stt: &crate::ix::compile::CompileState,
  kctx: &mut crate::ix::compile::KernelCtx,
) {
  use crate::ix::kernel::constant::KConst;
  use crate::ix::kernel::expr::KExpr;
  use crate::ix::kernel::id::KId;
  use crate::ix::kernel::level::KUniv;

  let n2a = Some(&stt.name_to_addr);
  let aux_n2a = Some(&stt.aux_name_to_addr);

  // --- PUnit.{u} : Sort u ---
  // Always insert (unconditional) so the hardcoded Indc definitions are
  // authoritative. ingress_field_deps may have already inserted PUnit/PProd
  // as bare Axio stubs with potentially wrong types; overwriting is safe.
  let punit_name = Name::str(Name::anon(), "PUnit".to_string());
  let punit_addr = resolve_lean_name_addr(&punit_name, n2a, aux_n2a);
  let punit_id = KId::new(punit_addr, punit_name.clone());

  // Fast path: if PUnit is already registered as an Indc (not an Axio stub),
  // assume PProd is too and skip redundant construction.
  if let Some(kconst) = kctx.kenv.get(&punit_id)
    && matches!(kconst, KConst::Indc { .. })
  {
    return;
  }

  let u_name = Name::str(Name::anon(), "u".to_string());
  {
    // PUnit.{u} : Sort u
    let u0 = KUniv::param(0, u_name.clone());
    let punit_ty = KExpr::sort(u0);
    // PUnit.unit.{u} : PUnit.{u}
    let unit_name = Name::str(punit_name.clone(), "unit".to_string());
    let unit_addr = resolve_lean_name_addr(&unit_name, n2a, aux_n2a);
    let unit_id = KId::new(unit_addr, unit_name.clone());
    let unit_ty = KExpr::cnst(
      punit_id.clone(),
      vec![KUniv::param(0, u_name.clone())].into_boxed_slice(),
    );
    kctx.kenv.insert(
      unit_id.clone(),
      KConst::Ctor {
        name: unit_name,
        level_params: vec![u_name.clone()],
        is_unsafe: false,
        lvls: 1,
        induct: punit_id.clone(),
        cidx: 0,
        params: 0,
        fields: 0,
        ty: unit_ty,
      },
    );
    kctx.kenv.insert(
      punit_id.clone(),
      KConst::Indc {
        name: punit_name.clone(),
        level_params: vec![u_name.clone()],
        lvls: 1,
        params: 0,
        indices: 0,
        is_rec: false,
        is_refl: false,
        is_unsafe: false,
        ctors: vec![unit_id],
        ty: punit_ty,
        block: punit_id,
        nested: 0,
        member_idx: 0,
        lean_all: vec![],
      },
    );
  }

  // --- PProd.{u, v} (α : Sort u) (β : Sort v) : Sort (max 1 u v) ---
  let pprod_name = Name::str(Name::anon(), "PProd".to_string());
  let pprod_addr = resolve_lean_name_addr(&pprod_name, n2a, aux_n2a);
  let pprod_id = KId::new(pprod_addr, pprod_name.clone());
  let v_name = Name::str(Name::anon(), "v".to_string());
  let alpha_name = Name::str(Name::anon(), "\u{03B1}".to_string());
  let beta_name = Name::str(Name::anon(), "\u{03B2}".to_string());
  let fst_name = Name::str(Name::anon(), "fst".to_string());
  let snd_name = Name::str(Name::anon(), "snd".to_string());
  {
    let u0 = KUniv::param(0, u_name.clone());
    let u1 = KUniv::param(1, v_name.clone());
    let sort_u = KExpr::sort(u0.clone());
    let sort_v = KExpr::sort(u1.clone());
    // Lean stores `max 1 u v` left-associated: max(max(1, u), v).
    // Matching this structure is essential: after level substitution and
    // the normalizing `Level::max` constructor (which collapses
    // `max(a, max(b, a))` to `max(b, a)`), a right-associated
    // `max(1, max(u, v))` produces a different tree than Lean's form.
    let max_1_u_v = KUniv::max(
      KUniv::max(KUniv::succ(KUniv::zero()), u0.clone()),
      u1.clone(),
    );

    // PProd.{u,v} : Sort u → Sort v → Sort (max 1 u v)
    let pprod_ty = KExpr::all(
      alpha_name.clone(),
      BinderInfo::Default,
      sort_u.clone(),
      KExpr::all(
        beta_name.clone(),
        BinderInfo::Default,
        sort_v.clone(),
        KExpr::sort(max_1_u_v),
      ),
    );

    // PProd.mk.{u,v} : {α : Sort u} → {β : Sort v} → α → β → PProd α β
    let mk_name = Name::str(pprod_name.clone(), "mk".to_string());
    let mk_addr = resolve_lean_name_addr(&mk_name, n2a, aux_n2a);
    let mk_id = KId::new(mk_addr, mk_name.clone());
    // Body: ∀ {α : Sort u} {β : Sort v} (fst : α) (snd : β), PProd.{u,v} α β
    // In de Bruijn: ∀ Sort(u) . ∀ Sort(v) . ∀ Var(1) . ∀ Var(1) . PProd Var(3) Var(2)
    let pprod_app = KExpr::app(
      KExpr::app(
        KExpr::cnst(
          pprod_id.clone(),
          vec![u0.clone(), u1.clone()].into_boxed_slice(),
        ),
        KExpr::var(3, Name::anon()),
      ),
      KExpr::var(2, Name::anon()),
    );
    let mk_ty = KExpr::all(
      alpha_name.clone(),
      BinderInfo::Implicit,
      sort_u, // {α : Sort u}
      KExpr::all(
        beta_name.clone(),
        BinderInfo::Implicit,
        sort_v, // {β : Sort v}
        KExpr::all(
          fst_name,
          BinderInfo::Default,
          KExpr::var(1, Name::anon()), // (fst : α)
          KExpr::all(
            snd_name,
            BinderInfo::Default,
            KExpr::var(1, Name::anon()), // (snd : β)
            pprod_app,
          ),
        ),
      ),
    );
    kctx.kenv.insert(
      mk_id.clone(),
      KConst::Ctor {
        name: mk_name,
        level_params: vec![u_name.clone(), v_name.clone()],
        is_unsafe: false,
        lvls: 2,
        induct: pprod_id.clone(),
        cidx: 0,
        params: 2,
        fields: 2,
        ty: mk_ty,
      },
    );
    kctx.kenv.insert(
      pprod_id.clone(),
      KConst::Indc {
        name: pprod_name,
        level_params: vec![u_name, v_name],
        lvls: 2,
        params: 2,
        indices: 0,
        is_rec: false,
        is_refl: false,
        is_unsafe: false,
        ctors: vec![mk_id],
        ty: pprod_ty,
        block: pprod_id,
        nested: 0,
        member_idx: 0,
        lean_all: vec![],
      },
    );
  }
}

/// Ingress a **single** Lean constant into the given kenv so the kernel
/// type checker can resolve it during inference. Handles all constant
/// types: inductives (with their constructors, via the parent→ctor
/// redirect), definitions, theorems, axioms, quotients, and recursors.
///
/// # Contract — IMPORTANT
///
/// **This function does not walk the constant's dependencies.** It
/// converts the constant's type/value expressions to `KExpr` via
/// `to_z` and inserts the resulting `KConst` entry into `kctx.kenv`,
/// but does not ingress constants referenced *inside* those expressions.
///
/// If `A` depends on `B` and you call `ensure_in_kenv_of(&"A", ...)`,
/// then `A`'s KConst is registered but `B`'s is not — a subsequent
/// `TypeChecker::infer` on a KExpr that references `B` will fail with
/// "kenv\[B\]: NOT FOUND". Callers are responsible for loading the
/// full dependency closure before invoking the type checker.
///
/// A transitive variant (BFS over the KExpr to ingress all referenced
/// `Const` names) was considered in CR5 of the adversarial review but
/// not adopted — most callers either (a) use a separately-loaded full
/// env (compile.rs, mutual.rs) or (b) are limited to aux_gen contexts
/// where the closure is small and explicit (below.rs, brecon.rs). If
/// you find yourself calling this on a constant whose deps aren't
/// already loaded, consider wiring in a real transitive walk rather
/// than papering over the missing deps with another helper call.
///
/// # Behavior
///
/// - **Idempotent**: skips if `zid` is already present in `kctx.kenv`.
/// - **Silent on missing source**: if `lean_env` has no entry for
///   `name`, this function returns without doing anything. Combined
///   with the non-transitive semantics above, missing deps manifest
///   as TC failures at use sites — not as errors here.
/// - **Ctor → parent redirect**: for `CtorInfo`, we also insert the
///   parent inductive and its sibling constructors, which is the one
///   place we *do* walk downstream (because kernel TC for a ctor use
///   requires the parent).
fn ensure_in_kenv_of_inner_env(
  name: &Name,
  lean_env: &crate::ix::env::Env,
  stt: &crate::ix::compile::CompileState,
  kenv: &mut crate::ix::kernel::env::KEnv<Meta>,
  replace_axio_stub: bool,
) {
  use crate::ix::env::{ConstantInfo as LCI, DefinitionSafety};
  use crate::ix::kernel::constant::KConst;
  use crate::ix::kernel::id::KId;
  use crate::ix::kernel::ingress::{
    lean_expr_to_zexpr_cached, param_names_hash,
  };

  let n2a = Some(&stt.name_to_addr);
  let aux_n2a = Some(&stt.aux_name_to_addr);

  let addr = resolve_lean_name_addr(name, n2a, aux_n2a);
  let zid: KId<Meta> = KId::new(addr, name.clone());

  if let Some(existing) = kenv.get(&zid) {
    // Most aux_gen ingress paths only need type-only stubs. When a later
    // WHNF path needs a real definition/inductive, allow replacing those
    // stubs; never overwrite already-real entries such as the current
    // canonical mutual block.
    if !replace_axio_stub || !matches!(existing, KConst::Axio { .. }) {
      return; // Already loaded.
    }
  }

  let Some(ci) = lean_env.get(name).cloned() else { return };
  // Helper: convert a LeanExpr to KExpr with the given level param names,
  // using the KEnv's persistent ingress cache. Callers are top-level, so
  // we start with an empty binder-name stack.
  let to_z = |expr: &crate::ix::env::Expr,
              lp: &[Name],
              kenv: &mut crate::ix::kernel::env::KEnv<Meta>|
   -> crate::ix::kernel::expr::KExpr<Meta> {
    let pn_h = param_names_hash(lp);
    let mut binder_names: Vec<Name> = Vec::new();
    lean_expr_to_zexpr_cached(
      expr,
      lp,
      &mut binder_names,
      &mut kenv.intern,
      n2a,
      aux_n2a,
      Some(&mut kenv.ingress_cache),
      Some(&pn_h),
    )
  };

  match &ci {
    LCI::InductInfo(ind) => {
      let lp = &ind.cnst.level_params;
      let n_lvls = lp.len() as u64;
      let ty_z = to_z(&ind.cnst.typ, lp, kenv);
      let mut ctor_zids = Vec::new();
      for ctor_name in &ind.ctors {
        if let Some(LCI::CtorInfo(ctor)) = lean_env.get(ctor_name) {
          let ctor_zid = KId::new(
            resolve_lean_name_addr(ctor_name, n2a, aux_n2a),
            ctor_name.clone(),
          );
          let ty = to_z(&ctor.cnst.typ, lp, kenv);
          kenv.insert(
            ctor_zid.clone(),
            KConst::Ctor {
              name: ctor_name.clone(),
              level_params: lp.clone(),
              is_unsafe: ctor.is_unsafe,
              lvls: n_lvls,
              induct: zid.clone(),
              cidx: ctor_zids.len() as u64,
              params: nat_to_u64(&ctor.num_params),
              fields: nat_to_u64(&ctor.num_fields),
              ty,
            },
          );
          ctor_zids.push(ctor_zid);
        }
      }
      kenv.insert(
        zid.clone(),
        KConst::Indc {
          name: name.clone(),
          level_params: lp.clone(),
          lvls: n_lvls,
          params: nat_to_u64(&ind.num_params),
          indices: nat_to_u64(&ind.num_indices),
          is_rec: ind.is_rec,
          is_refl: ind.is_reflexive,
          is_unsafe: ind.is_unsafe,
          ctors: ctor_zids,
          ty: ty_z,
          block: zid,
          nested: nat_to_u64(&ind.num_nested),
          member_idx: 0,
          lean_all: vec![],
        },
      );
    },
    LCI::DefnInfo(d) => {
      let lp = &d.cnst.level_params;
      let ty = to_z(&d.cnst.typ, lp, kenv);
      let val = to_z(&d.value, lp, kenv);
      kenv.insert(
        zid.clone(),
        KConst::Defn {
          name: name.clone(),
          level_params: lp.clone(),
          kind: crate::ix::ixon::constant::DefKind::Definition,
          safety: d.safety,
          hints: d.hints,
          lvls: lp.len() as u64,
          ty,
          val,
          lean_all: vec![],
          block: zid,
        },
      );
    },
    LCI::ThmInfo(d) => {
      let lp = &d.cnst.level_params;
      let ty = to_z(&d.cnst.typ, lp, kenv);
      let val = to_z(&d.value, lp, kenv);
      kenv.insert(
        zid.clone(),
        KConst::Defn {
          name: name.clone(),
          level_params: lp.clone(),
          kind: crate::ix::ixon::constant::DefKind::Theorem,
          safety: DefinitionSafety::Safe,
          hints: crate::ix::env::ReducibilityHints::Opaque,
          lvls: lp.len() as u64,
          ty,
          val,
          lean_all: vec![],
          block: zid,
        },
      );
    },
    LCI::OpaqueInfo(d) => {
      let lp = &d.cnst.level_params;
      let ty = to_z(&d.cnst.typ, lp, kenv);
      let val = to_z(&d.value, lp, kenv);
      kenv.insert(
        zid.clone(),
        KConst::Defn {
          name: name.clone(),
          level_params: lp.clone(),
          kind: crate::ix::ixon::constant::DefKind::Opaque,
          safety: DefinitionSafety::Safe,
          hints: crate::ix::env::ReducibilityHints::Opaque,
          lvls: lp.len() as u64,
          ty,
          val,
          lean_all: vec![],
          block: zid,
        },
      );
    },
    LCI::AxiomInfo(a) => {
      let lp = &a.cnst.level_params;
      let ty = to_z(&a.cnst.typ, lp, kenv);
      kenv.insert(
        zid.clone(),
        KConst::Axio {
          name: name.clone(),
          level_params: lp.clone(),
          is_unsafe: a.is_unsafe,
          lvls: lp.len() as u64,
          ty,
        },
      );
    },
    LCI::QuotInfo(q) => {
      let lp = &q.cnst.level_params;
      let ty = to_z(&q.cnst.typ, lp, kenv);
      kenv.insert(
        zid.clone(),
        KConst::Quot {
          name: name.clone(),
          level_params: lp.clone(),
          kind: q.kind,
          lvls: lp.len() as u64,
          ty,
        },
      );
    },
    LCI::CtorInfo(ctor) => {
      // Constructors are ingressed as part of their parent inductive.
      ensure_in_kenv_of_inner_env(
        &ctor.induct,
        lean_env,
        stt,
        kenv,
        replace_axio_stub,
      );
    },
    LCI::RecInfo(_) => {
      // Recursors are generated by the kernel, not ingressed from Lean.
      // They'll be created when check_inductive runs on the parent.
    },
  }
}

fn ensure_in_kenv_of_inner(
  name: &Name,
  lean_env: &crate::ix::env::Env,
  stt: &crate::ix::compile::CompileState,
  kctx: &mut crate::ix::compile::KernelCtx,
  replace_axio_stub: bool,
) {
  ensure_in_kenv_of_inner_env(
    name,
    lean_env,
    stt,
    &mut kctx.kenv,
    replace_axio_stub,
  );
}

pub(crate) fn ensure_in_kenv_of(
  name: &Name,
  lean_env: &crate::ix::env::Env,
  stt: &crate::ix::compile::CompileState,
  kctx: &mut crate::ix::compile::KernelCtx,
) {
  ensure_in_kenv_of_inner(name, lean_env, stt, kctx, false);
}

/// Like [`ensure_in_kenv_of`], but upgrades an existing type-only `Axio`
/// stub into the real constant. This is required before WHNF paths that must
/// unfold reducible definitions or inspect inductive/ctor metadata.
pub(crate) fn ensure_full_in_kenv_of(
  name: &Name,
  lean_env: &crate::ix::env::Env,
  stt: &crate::ix::compile::CompileState,
  kctx: &mut crate::ix::compile::KernelCtx,
) {
  ensure_in_kenv_of_inner(name, lean_env, stt, kctx, true);
}

fn ensure_full_in_tc_env(
  name: &Name,
  lean_env: &crate::ix::env::Env,
  stt: &crate::ix::compile::CompileState,
  kenv: &mut crate::ix::kernel::env::KEnv<Meta>,
) {
  ensure_in_kenv_of_inner_env(name, lean_env, stt, kenv, true);
}

/// Convenience wrapper: ingress into the **original** kenv (`stt.kctx`).
pub(crate) fn ensure_in_kenv(
  name: &Name,
  lean_env: &crate::ix::env::Env,
  stt: &crate::ix::compile::CompileState,
  kctx: &mut crate::ix::compile::KernelCtx,
) {
  ensure_in_kenv_of(name, lean_env, stt, kctx);
}

// =========================================================================
// Scoped access to the global TypeChecker
// =========================================================================

/// RAII scope for using a TypeChecker with an FVar context.
///
/// Locks `kctx.tc` for its lifetime. Callers push/pop locals via
/// `push_locals` / `pop_locals` and infer sort levels via `get_level`.
/// All locals pushed must be popped before the scope is dropped.
pub(super) struct TcScope<'a> {
  fvar_levels: FxHashMap<Name, usize>,
  base_depth: usize,
  param_names: &'a [Name],
  stt: &'a crate::ix::compile::CompileState,
  tc: crate::ix::kernel::tc::TypeChecker<'a, Meta>,
  /// How many extra locals are currently pushed above base_depth.
  extra_locals: usize,
}

impl<'a> TcScope<'a> {
  /// Lock the TC (`kctx.tc`) and push the outer FVar context.
  pub(super) fn new(
    outer_fvar_ctx: &[LocalDecl],
    param_names: &'a [Name],
    stt: &'a crate::ix::compile::CompileState,
    kctx: &'a mut crate::ix::compile::KernelCtx,
  ) -> Self {
    let fvar_levels: FxHashMap<Name, usize> = outer_fvar_ctx
      .iter()
      .enumerate()
      .map(|(i, decl)| (decl.fvar_name.clone(), i))
      .collect();

    let mut tc = crate::ix::kernel::tc::TypeChecker::new(&mut kctx.kenv);
    tc.infer_only = true;

    // Push outer FVar types once.
    for (i, decl) in outer_fvar_ctx.iter().enumerate() {
      let kty =
        to_kexpr_static(&decl.domain, &fvar_levels, i, param_names, stt);
      tc.push_local(kty);
    }

    TcScope {
      fvar_levels,
      base_depth: outer_fvar_ctx.len(),
      param_names,
      stt,
      tc,
      extra_locals: 0,
    }
  }

  /// Push additional locals (e.g. minor premise lambda binders).
  /// Must be balanced by a later `pop_locals` call.
  pub(super) fn push_locals(&mut self, decls: &[LocalDecl]) {
    let depth = self.base_depth + self.extra_locals;
    for (i, decl) in decls.iter().enumerate() {
      self.fvar_levels.insert(decl.fvar_name.clone(), depth + i);
      let kty = to_kexpr_static(
        &decl.domain,
        &self.fvar_levels,
        depth + i,
        self.param_names,
        self.stt,
      );
      self.tc.push_local(kty);
    }
    self.extra_locals += decls.len();
  }

  /// Pop locals pushed by `push_locals`.
  pub(super) fn pop_locals(&mut self, decls: &[LocalDecl]) {
    for decl in decls.iter().rev() {
      self.tc.pop_local();
      self.fvar_levels.remove(&decl.fvar_name);
    }
    self.extra_locals -= decls.len();
  }

  fn fault_in_direct_expr_consts(&mut self, expr: &LeanExpr) {
    let mut refs = FxHashSet::default();
    collect_lean_const_refs(expr, &mut refs);
    for name in refs {
      self.fault_in_name(&name);
    }
  }

  fn fault_in_name(&mut self, name: &Name) -> bool {
    let Some(lean_env) = self.stt.lean_env.as_deref() else {
      return false;
    };
    ensure_full_in_tc_env(name, lean_env, self.stt, self.tc.env);
    let addr = resolve_lean_name_addr(
      name,
      Some(&self.stt.name_to_addr),
      Some(&self.stt.aux_name_to_addr),
    );
    self.addr_present(&addr)
  }

  fn fault_in_addr(&mut self, addr: &Address) -> bool {
    if self.addr_present(addr) {
      return true;
    }
    let Some(name) = self.name_for_addr(addr) else {
      return false;
    };
    self.fault_in_name(&name) && self.addr_present(addr)
  }

  fn addr_present(&self, addr: &Address) -> bool {
    self.tc.env.consts.keys().any(|id| &id.addr == addr)
  }

  fn name_for_addr(&self, addr: &Address) -> Option<Name> {
    for entry in self.stt.name_to_addr.iter() {
      if entry.value() == addr {
        return Some(entry.key().clone());
      }
    }
    for entry in self.stt.aux_name_to_addr.iter() {
      if entry.value() == addr {
        return Some(entry.key().clone());
      }
    }
    let lean_env = self.stt.lean_env.as_deref()?;
    lean_env.keys().find_map(|name| {
      let name_addr = Address::from_blake3_hash(*name.get_hash());
      if &name_addr == addr { Some(name.clone()) } else { None }
    })
  }

  fn get_level_error(
    &self,
    ty: &LeanExpr,
    kexpr: &crate::ix::kernel::expr::KExpr<Meta>,
    e: &crate::ix::kernel::error::TcError<Meta>,
  ) -> crate::ix::ixon::CompileError {
    eprintln!("[TcScope::get_level] FAILED");
    eprintln!("  lean_expr: {}", ty.pretty());
    eprintln!("  kexpr:     {kexpr}");
    eprintln!("  error:     {e}");
    eprintln!(
      "  ctx depth: {} (base={}, extra={})",
      self.tc.ctx.len(),
      self.base_depth,
      self.extra_locals
    );
    // Dump kenv entries for constants referenced in the expression.
    let mut stack: Vec<&crate::ix::kernel::expr::KExpr<Meta>> = vec![kexpr];
    let mut seen_ids = std::collections::HashSet::new();
    while let Some(expr) = stack.pop() {
      use crate::ix::kernel::expr::ExprData as ZED;
      match expr.data() {
        ZED::Const(id, us, _) => {
          if seen_ids.insert(id.clone()) {
            match self.tc.env.get(id) {
              Some(c) => {
                eprintln!("  kenv[{}]: lvls={}, ty={}", id, c.lvls(), c.ty())
              },
              None => eprintln!("  kenv[{}]: NOT FOUND", id),
            }
            eprintln!(
              "    level_args: [{}]",
              us.iter().map(|u| format!("{u}")).collect::<Vec<_>>().join(", ")
            );
          }
        },
        ZED::App(f, a, _) => {
          stack.push(f);
          stack.push(a);
        },
        ZED::All(_, _, d, b, _) | ZED::Lam(_, _, d, b, _) => {
          stack.push(d);
          stack.push(b);
        },
        _ => {},
      }
    }
    crate::ix::ixon::CompileError::UnsupportedExpr {
      desc: format!(
        "TcScope::get_level({}): tc.infer failed: {e}",
        ty.pretty()
      ),
    }
  }

  /// Infer the sort level of a type expression in the current context.
  ///
  /// Uses a fast path matching Lean's `inferAppType` (InferType.lean:79-91):
  /// for fully-applied constants whose stored type telescopes to a `Sort`,
  /// reads the level directly from the type after level-param instantiation.
  /// This avoids kernel-level normalization artifacts that can produce
  /// structurally different level trees.
  ///
  /// Falls back to the kernel TC for non-constant expressions, partially-
  /// applied constants, or types that don't end in Sort.
  pub(super) fn get_level(
    &mut self,
    ty: &LeanExpr,
  ) -> Result<Level, crate::ix::ixon::CompileError> {
    // Fast path: read Sort level from stored type (matching Lean's
    // inferAppType which peels foralls without substituting term args).
    // Sort levels use level params, not BVars, so the level is correct
    // without term substitution.
    if let Some(lvl) = self.try_infer_app_sort_level(ty) {
      return Ok(lvl);
    }

    let depth = self.base_depth + self.extra_locals;
    let kexpr =
      to_kexpr_static(ty, &self.fvar_levels, depth, self.param_names, self.stt);

    // Lazy on-demand ingress: load only constants demanded by this specific
    // aux_gen inference, then retry one missing upstream constant at a time.
    self.fault_in_direct_expr_consts(ty);
    let mut faulted_addrs = FxHashSet::default();
    let inferred = loop {
      match self.tc.infer(&kexpr) {
        Ok(inferred) => break inferred,
        Err(crate::ix::kernel::error::TcError::UnknownConst(addr))
          if faulted_addrs.insert(addr.clone())
            && self.fault_in_addr(&addr) =>
        {
          continue;
        },
        Err(e) => return Err(self.get_level_error(ty, &kexpr, &e)),
      }
    };
    let ku = self.tc.ensure_sort(&inferred).map_err(|e| {
      crate::ix::ixon::CompileError::UnsupportedExpr {
        desc: format!("TcScope::get_level: ensure_sort failed: {e}"),
      }
    })?;
    let raw = super::below::kuniv_to_level(&ku, self.param_names);
    // When `ty` is a forall, mirror Lean's `inferForallType`
    // (`refs/lean4/src/Lean/Meta/InferType.lean:160`): apply
    // `Level.normalize` before returning. Without this, the imax chain
    // built by our kernel's `KUniv::imax` (cheap-simp only) stays in a
    // structurally different max-tree than the Lean-stored form, and
    // downstream PProd/PProd.mk uses of this level as a universe arg
    // produce aux_gen output that's alpha-equivalent but not hash-equal
    // to Lean's — e.g. `SetTheory.PGame.brecOn.go` d=9 PProd.mk.lvl[1].
    // For non-forall `ty`, match Lean exactly and leave the level as-is.
    let lvl = if matches!(ty.as_data(), ExprData::ForallE(..)) {
      super::below::level_normalize(&raw)
    } else {
      raw
    };
    Ok(lvl)
  }
  /// Check if a Level is guaranteed non-zero. Matches Lean's `is_not_zero`:
  /// true for Succ(_), Param, Max(a,b) where either is not-zero.
  fn is_not_zero_level(l: &Level) -> bool {
    use crate::ix::env::LevelData;
    match l.as_data() {
      LevelData::Succ(_, _) => true,
      LevelData::Max(a, b, _) => {
        Self::is_not_zero_level(a) || Self::is_not_zero_level(b)
      },
      LevelData::Imax(_, b, _) => Self::is_not_zero_level(b),
      // Param could be zero; everything else (Zero, Mvar) is treated as
      // potentially zero too.
      _ => false,
    }
  }

  /// Fast path for `get_level`: if `ty` is a fully-applied constant whose
  /// stored type telescopes to `Sort l`, return `l` with level params
  /// substituted. Matches Lean's `inferAppType` optimization.
  ///
  /// Returns `None` if the fast path doesn't apply (not a constant
  /// application, not enough foralls, result isn't Sort, or the constant
  /// isn't found in the kernel env).
  fn try_infer_app_sort_level(&self, ty: &LeanExpr) -> Option<Level> {
    use crate::ix::env::ExprData;
    use crate::ix::kernel::expr::ExprData as ZED;

    // Decompose into head constant + args.
    let (head, args) = decompose_apps(ty);
    let (name, levels) = match head.as_data() {
      ExprData::Const(name, levels, _) => (name, levels),
      _ => return None,
    };

    // Look up the constant in the kernel env to get its stored type.
    let n2a = Some(&self.stt.name_to_addr);
    let aux_n2a = Some(&self.stt.aux_name_to_addr);
    let addr = resolve_lean_name_addr(name, n2a, aux_n2a);
    let kid = crate::ix::kernel::id::KId::new(addr, name.clone());
    let kconst = self.tc.env.get(&kid)?;
    let kty = kconst.ty();

    // Peel foralls from the stored type — one per applied arg.
    // Don't substitute term args (Sort levels have no BVars).
    let mut cur = kty.clone();
    for _ in 0..args.len() {
      match cur.data() {
        ZED::All(_, _, _, body, _) => cur = body.clone(),
        _ => return None,
      }
    }

    // Check if the result is Sort and extract the level.
    let ku = match cur.data() {
      ZED::Sort(u, _) => u,
      _ => {
        // Not a Sort — the type might have dependent binders where
        // term args matter. Fall through to kernel TC.
        return None;
      },
    };

    // The level uses de Bruijn indices for level params (Param(i)).
    // The constant's level args give the concrete levels for each param.
    // Substitute: Param(i) → levels[i] (converted from LeanExpr Level).
    //
    // Convert the KUniv to a Level, substituting level params with the
    // concrete level args from the Const node.
    Some(self.kuniv_to_level_with_const_levels(ku, levels))
  }

  /// Convert a `KUniv` to `Level`, substituting level param indices with
  /// the concrete levels from a Const's level args.
  fn kuniv_to_level_with_const_levels(
    &self,
    u: &crate::ix::kernel::level::KUniv<Meta>,
    const_levels: &[Level],
  ) -> Level {
    use crate::ix::kernel::level::UnivData;
    match u.data() {
      UnivData::Zero(_) => Level::zero(),
      UnivData::Succ(inner, _) => {
        Level::succ(self.kuniv_to_level_with_const_levels(inner, const_levels))
      },
      UnivData::Max(a, b, _) => {
        // Use level_max (matching Lean's mk_max: zero/equality/subsumption
        // checks) to simplify after substitution.
        super::below::level_max(
          &self.kuniv_to_level_with_const_levels(a, const_levels),
          &self.kuniv_to_level_with_const_levels(b, const_levels),
        )
      },
      UnivData::IMax(a, b, _) => {
        let la = self.kuniv_to_level_with_const_levels(a, const_levels);
        let lb = self.kuniv_to_level_with_const_levels(b, const_levels);
        // Match Lean's mk_imax: simplify when the second argument's
        // zero/nonzero status is known.
        if Self::is_not_zero_level(&lb) {
          super::below::level_max(&la, &lb)
        } else if matches!(lb.as_data(), LevelData::Zero(_))
          || matches!(la.as_data(), LevelData::Zero(_))
          || matches!(la.as_data(), LevelData::Succ(inner, _) if matches!(inner.as_data(), LevelData::Zero(_)))
        {
          // Lean's mk_imax: imax(_, 0) = 0, imax(0, _) = b, imax(1, b) = b.
          lb
        } else if la == lb {
          la
        } else {
          Level::imax(la, lb)
        }
      },
      UnivData::Param(idx, _, _) => {
        // Substitute with the concrete level from the Const's level args.
        const_levels.get(*idx as usize).cloned().unwrap_or_else(|| {
          // Fallback: use the TcScope's param names.
          let name = self
            .param_names
            .get(*idx as usize)
            .cloned()
            .unwrap_or_else(|| Name::str(Name::anon(), format!("u_{idx}")));
          Level::param(name)
        })
      },
    }
  }
}

impl<'a> TcScope<'a> {
  /// Weak-head-normalize a `LeanExpr` in the current FVar context, using
  /// our Rust kernel's `whnf`. Matches Lean's `Meta.whnf` behavior:
  /// unfolds reducible definitions, beta-reduces, applies iota/zeta.
  ///
  /// Crucial for decomposing types whose target is a reducible alias.
  /// E.g. when the inductive `εClosure (S : Set α) : Set α` is declared,
  /// Lean's kernel `mk_rec_infos` WHNFs the target type to expose the
  /// `Pi (a : α), Prop` hiding inside `Set α := α → Prop`. Without this
  /// step, a syntactic match on `Set α` (an `App(Const, FVar)`) fails
  /// to find the index binder.
  pub(super) fn whnf_lean(&mut self, ty: &LeanExpr) -> LeanExpr {
    let depth = self.base_depth + self.extra_locals;
    let kexpr =
      to_kexpr_static(ty, &self.fvar_levels, depth, self.param_names, self.stt);
    let whnfed = match self.tc.whnf(&kexpr) {
      Ok(k) => k,
      Err(_) => return ty.clone(),
    };
    kexpr_to_lean(&whnfed, depth, &self.fvar_levels, 0, self.param_names)
  }

  /// Check whether two `LeanExpr` types are definitionally equal in the
  /// current FVar context, via the Rust kernel's `is_def_eq`. Matches
  /// Lean's `Meta.isDefEq` used throughout the cases/subst machinery —
  /// e.g. `mkEqAndProof` in `refs/lean4/src/Lean/Meta/Tactic/Cases.lean:30-37`
  /// uses `isDefEq lhsType rhsType` to decide between `Eq` and `HEq`.
  ///
  /// Returns `false` on kernel errors (conservative: treat as not defEq).
  pub(super) fn is_def_eq(&mut self, a: &LeanExpr, b: &LeanExpr) -> bool {
    let depth = self.base_depth + self.extra_locals;
    let ka =
      to_kexpr_static(a, &self.fvar_levels, depth, self.param_names, self.stt);
    let kb =
      to_kexpr_static(b, &self.fvar_levels, depth, self.param_names, self.stt);
    self.tc.is_def_eq(&ka, &kb).unwrap_or(false)
  }
}

// No Drop impl needed — the TC is owned and discarded with the scope.
// Context cleanup (pop_local) is unnecessary since the TC dies here.

/// Convert a `KExpr<Meta>` back to `LeanExpr`, reconstructing FVar
/// references from de-Bruijn `Var` indices.
///
/// Parallels `egress_expr` in `src/ix/kernel/egress.rs`, which handles
/// the closed-expression case (Var → Bvar unconditionally). This version
/// is for expressions that live inside an ambient FVar context — the
/// shape we produce mid-pipeline when working in LeanExpr+FVar with a
/// kernel `TypeChecker` tracking the FVar types as locals.
///
/// `outer_depth` is the FVar context depth that was used to convert the
/// source `LeanExpr` to `KExpr` (via [`to_kexpr_static`]). Kernel `Var`
/// indices below `local_depth` are bound by the KExpr itself (become
/// `Bvar`s); indices at or above `local_depth` refer to the outer FVar
/// context, and get mapped back to their corresponding `Fvar` name via
/// `fvar_levels`. The encoding and its inverse are symmetric: an FVar at
/// level L is encoded as `Var(outer_depth - L - 1)` from the top, so the
/// inverse at descent depth `d` is `L = outer_depth - (i - d) - 1`.
///
/// `local_depth` is incremented by `All`, `Lam`, `Let` arms.
///
/// `Mdata` layers carried by the kernel expression are re-wrapped around
/// the result in original order — matching `egress_expr`.
pub(super) fn kexpr_to_lean(
  expr: &crate::ix::kernel::expr::KExpr<Meta>,
  outer_depth: usize,
  fvar_levels: &FxHashMap<Name, usize>,
  local_depth: usize,
  param_names: &[Name],
) -> LeanExpr {
  use crate::ix::kernel::expr::ExprData as KED;

  // Reverse `fvar_levels` lazily via linear search — the FVar context is
  // small in practice (a handful of param/motive/minor/index binders),
  // so an O(n) scan per Var hit is cheaper than maintaining an inverse
  // map alongside `TcScope`.
  let lookup_fvar = |level: usize| -> Option<Name> {
    fvar_levels.iter().find_map(|(name, &lvl)| {
      if lvl == level { Some(name.clone()) } else { None }
    })
  };

  let inner = match expr.data() {
    KED::Var(i, _, _) => {
      let i = *i as usize;
      if i < local_depth {
        LeanExpr::bvar(Nat::from(i as u64))
      } else {
        let fvar_idx_from_top = i - local_depth;
        let level = outer_depth
          .checked_sub(fvar_idx_from_top + 1)
          .expect("kexpr_to_lean: Var index out of range of outer context");
        let name = lookup_fvar(level).unwrap_or_else(|| {
          // Unregistered FVar — indicates mismatched `fvar_levels` vs.
          // the expression's Var indices. Use a synthetic placeholder
          // rather than panic so diagnostics can surface the issue.
          Name::str(Name::anon(), format!("_dangling_fvar_{level}"))
        });
        LeanExpr::fvar(name)
      }
    },
    KED::Sort(u, _) => {
      LeanExpr::sort(super::below::kuniv_to_level(u, param_names))
    },
    KED::Const(kid, us, _) => {
      let levels: Vec<Level> = us
        .iter()
        .map(|u| super::below::kuniv_to_level(u, param_names))
        .collect();
      LeanExpr::cnst(kid.name.clone(), levels)
    },
    KED::App(f, a, _) => LeanExpr::app(
      kexpr_to_lean(f, outer_depth, fvar_levels, local_depth, param_names),
      kexpr_to_lean(a, outer_depth, fvar_levels, local_depth, param_names),
    ),
    KED::All(name, bi, d, b, _) => LeanExpr::all(
      name.clone(),
      kexpr_to_lean(d, outer_depth, fvar_levels, local_depth, param_names),
      kexpr_to_lean(b, outer_depth, fvar_levels, local_depth + 1, param_names),
      bi.clone(),
    ),
    KED::Lam(name, bi, d, b, _) => LeanExpr::lam(
      name.clone(),
      kexpr_to_lean(d, outer_depth, fvar_levels, local_depth, param_names),
      kexpr_to_lean(b, outer_depth, fvar_levels, local_depth + 1, param_names),
      bi.clone(),
    ),
    KED::Let(name, ty, val, body, nd, _) => LeanExpr::letE(
      name.clone(),
      kexpr_to_lean(ty, outer_depth, fvar_levels, local_depth, param_names),
      kexpr_to_lean(val, outer_depth, fvar_levels, local_depth, param_names),
      kexpr_to_lean(
        body,
        outer_depth,
        fvar_levels,
        local_depth + 1,
        param_names,
      ),
      *nd,
    ),
    KED::Prj(kid, field, val, _) => LeanExpr::proj(
      kid.name.clone(),
      Nat::from(*field),
      kexpr_to_lean(val, outer_depth, fvar_levels, local_depth, param_names),
    ),
    KED::Nat(n, _, _) => {
      use crate::ix::env::Literal;
      LeanExpr::lit(Literal::NatVal(n.clone()))
    },
    KED::Str(s, _, _) => {
      use crate::ix::env::Literal;
      LeanExpr::lit(Literal::StrVal(s.clone()))
    },
  };

  // Re-wrap mdata layers, outermost first (matching egress_expr's order).
  expr
    .mdata()
    .iter()
    .rev()
    .fold(inner, |acc, kvs| LeanExpr::mdata(kvs.clone(), acc))
}

/// Static version of `to_kexpr` that takes borrowed references.
///
/// Identical to the closure-based `to_kexpr` in `get_level`, but as a
/// standalone function so it can be called from both `PreparedTC::new`
/// and `get_level_with_tc`.
fn to_kexpr_static(
  expr: &LeanExpr,
  fvar_levels: &FxHashMap<Name, usize>,
  ctx_depth: usize,
  param_names: &[Name],
  stt: &crate::ix::compile::CompileState,
) -> crate::ix::kernel::expr::KExpr<Meta> {
  let n2a = Some(&stt.name_to_addr);
  let aux_n2a = Some(&stt.aux_name_to_addr);
  use crate::ix::kernel::expr::KExpr;
  use crate::ix::kernel::id::KId;
  use crate::ix::kernel::level::KUniv;

  match expr.as_data() {
    ExprData::Fvar(fname, _) => {
      if let Some(&level) = fvar_levels.get(fname) {
        KExpr::var((ctx_depth - level - 1) as u64, Name::anon())
      } else {
        KExpr::sort(KUniv::zero())
      }
    },
    ExprData::Bvar(idx, _) => KExpr::var(nat_to_u64(idx), Name::anon()),
    ExprData::Sort(lvl, _) => {
      KExpr::sort(lean_level_to_kuniv(lvl, param_names))
    },
    ExprData::Const(cname, us, _) => {
      let addr = resolve_lean_name_addr(cname, n2a, aux_n2a);
      let zid = KId::new(addr, cname.clone());
      let zus: Box<[KUniv<Meta>]> =
        us.iter().map(|u| lean_level_to_kuniv(u, param_names)).collect();
      KExpr::cnst(zid, zus)
    },
    ExprData::App(f, a, _) => {
      let kf = to_kexpr_static(f, fvar_levels, ctx_depth, param_names, stt);
      let ka = to_kexpr_static(a, fvar_levels, ctx_depth, param_names, stt);
      KExpr::app(kf, ka)
    },
    ExprData::ForallE(binder_name, dom, body, bi, _) => {
      let kd = to_kexpr_static(dom, fvar_levels, ctx_depth, param_names, stt);
      let kb =
        to_kexpr_static(body, fvar_levels, ctx_depth + 1, param_names, stt);
      KExpr::all(binder_name.clone(), bi.clone(), kd, kb)
    },
    ExprData::Lam(binder_name, dom, body, bi, _) => {
      let kd = to_kexpr_static(dom, fvar_levels, ctx_depth, param_names, stt);
      let kb =
        to_kexpr_static(body, fvar_levels, ctx_depth + 1, param_names, stt);
      KExpr::lam(binder_name.clone(), bi.clone(), kd, kb)
    },
    ExprData::LetE(binder_name, ty, val, body, nd, _) => {
      let kt = to_kexpr_static(ty, fvar_levels, ctx_depth, param_names, stt);
      let kv = to_kexpr_static(val, fvar_levels, ctx_depth, param_names, stt);
      let kb =
        to_kexpr_static(body, fvar_levels, ctx_depth + 1, param_names, stt);
      KExpr::let_(binder_name.clone(), kt, kv, kb, *nd)
    },
    ExprData::Proj(pname, idx, e, _) => {
      let addr = resolve_lean_name_addr(pname, n2a, aux_n2a);
      let zid = KId::new(addr, pname.clone());
      let ke = to_kexpr_static(e, fvar_levels, ctx_depth, param_names, stt);
      KExpr::prj(zid, nat_to_u64(idx), ke)
    },
    ExprData::Lit(lit, _) => {
      use crate::ix::env::Literal;
      match lit {
        Literal::NatVal(n) => {
          let addr = Address::hash(&nat_to_u64(n).to_le_bytes());
          KExpr::nat(n.clone(), addr)
        },
        Literal::StrVal(s) => {
          let addr = Address::hash(s.as_bytes());
          KExpr::str(s.clone(), addr)
        },
      }
    },
    ExprData::Mdata(_, inner, _) => {
      to_kexpr_static(inner, fvar_levels, ctx_depth, param_names, stt)
    },
    _ => KExpr::sort(KUniv::zero()),
  }
}

fn collect_lean_const_refs(expr: &LeanExpr, out: &mut FxHashSet<Name>) {
  let mut stack = vec![expr];
  while let Some(expr) = stack.pop() {
    match expr.as_data() {
      ExprData::Const(name, _, _) => {
        out.insert(name.clone());
      },
      ExprData::App(f, a, _) => {
        stack.push(f);
        stack.push(a);
      },
      ExprData::ForallE(_, d, b, _, _) | ExprData::Lam(_, d, b, _, _) => {
        stack.push(d);
        stack.push(b);
      },
      ExprData::LetE(_, t, v, b, _, _) => {
        stack.push(t);
        stack.push(v);
        stack.push(b);
      },
      ExprData::Proj(type_name, _, e, _) => {
        out.insert(type_name.clone());
        stack.push(e);
      },
      ExprData::Mdata(_, e, _) => stack.push(e),
      _ => {},
    }
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::ix::env::BinderInfo;

  fn mk_name_for(s: &str) -> Name {
    let mut n = Name::anon();
    for part in s.split('.') {
      n = Name::str(n, part.to_string());
    }
    n
  }

  fn sort0() -> LeanExpr {
    LeanExpr::sort(Level::zero())
  }

  fn bvar_at(i: u64) -> LeanExpr {
    LeanExpr::bvar(Nat::from(i))
  }

  /// `∀ (a : α) (b : β) (c : γ), body`
  fn mk_triple_forall(
    a: LeanExpr,
    b: LeanExpr,
    c: LeanExpr,
    body: LeanExpr,
  ) -> LeanExpr {
    LeanExpr::all(
      mk_name_for("a"),
      a,
      LeanExpr::all(
        mk_name_for("b"),
        b,
        LeanExpr::all(mk_name_for("c"), c, body, BinderInfo::Default),
        BinderInfo::Default,
      ),
      BinderInfo::Default,
    )
  }

  fn is_fvar_with_name(e: &LeanExpr, expected: &Name) -> bool {
    matches!(e.as_data(), ExprData::Fvar(n, _) if n == expected)
  }

  // ---- fresh_fvar ----

  #[test]
  fn fresh_fvar_produces_unique_names() {
    let (n1, f1) = fresh_fvar("p", 0);
    let (n2, f2) = fresh_fvar("p", 1);
    assert_ne!(n1, n2);
    assert!(is_fvar_with_name(&f1, &n1));
    assert!(is_fvar_with_name(&f2, &n2));
  }

  #[test]
  fn fresh_fvar_prefix_changes_name() {
    let (na, _) = fresh_fvar("a", 0);
    let (nb, _) = fresh_fvar("b", 0);
    assert_ne!(na, nb);
  }

  // ---- forall_telescope ----

  #[test]
  fn forall_telescope_opens_exactly_n_binders() {
    let e = mk_triple_forall(sort0(), sort0(), sort0(), bvar_at(0));
    let (fvars, decls, body) = forall_telescope(&e, 3, "p", 0);
    assert_eq!(fvars.len(), 3);
    assert_eq!(decls.len(), 3);
    // After instantiating all three foralls, body BVar(0) became the
    // innermost FVar.
    match body.as_data() {
      ExprData::Fvar(n, _) => assert_eq!(n, &decls[2].fvar_name),
      other => panic!("expected innermost FVar in body, got {other:?}"),
    }
  }

  #[test]
  fn forall_telescope_partial_with_too_small_n() {
    let e = mk_triple_forall(sort0(), sort0(), sort0(), bvar_at(0));
    let (fvars, decls, body) = forall_telescope(&e, 2, "p", 0);
    assert_eq!(fvars.len(), 2);
    assert_eq!(decls.len(), 2);
    // Body is still a forall because we didn't peel the innermost.
    assert!(matches!(body.as_data(), ExprData::ForallE(..)));
  }

  #[test]
  fn forall_telescope_requests_more_than_available_stops_early() {
    // Body is not a forall; telescope caps at 1.
    let e =
      LeanExpr::all(mk_name_for("x"), sort0(), bvar_at(0), BinderInfo::Default);
    let (fvars, decls, _body) = forall_telescope(&e, 5, "p", 0);
    assert_eq!(fvars.len(), 1);
    assert_eq!(decls.len(), 1);
  }

  #[test]
  fn forall_telescope_peels_mdata() {
    // ∀ (x : α), Mdata(_, ∀ (y : β), body)
    let inner_forall =
      LeanExpr::all(mk_name_for("y"), sort0(), bvar_at(0), BinderInfo::Default);
    let with_mdata = LeanExpr::mdata(vec![], inner_forall);
    let outer =
      LeanExpr::all(mk_name_for("x"), sort0(), with_mdata, BinderInfo::Default);
    let (_, decls, _) = forall_telescope(&outer, 2, "p", 0);
    assert_eq!(decls.len(), 2, "mdata should be transparent");
  }

  #[test]
  fn forall_telescope_uses_start_idx_offset() {
    let e = mk_triple_forall(sort0(), sort0(), sort0(), bvar_at(0));
    let (_, decls1, _) = forall_telescope(&e, 1, "p", 0);
    let (_, decls2, _) = forall_telescope(&e, 1, "p", 10);
    assert_ne!(decls1[0].fvar_name, decls2[0].fvar_name);
  }

  #[test]
  fn forall_telescope_exact_errors_on_short() {
    let e =
      LeanExpr::all(mk_name_for("x"), sort0(), sort0(), BinderInfo::Default);
    let r = forall_telescope_exact(&e, 5, "p", 0, "test", "binders");
    assert!(r.is_err());
  }

  // ---- decompose_apps ----

  #[test]
  fn decompose_apps_non_app() {
    let e = sort0();
    let (head, args) = decompose_apps(&e);
    assert_eq!(args.len(), 0);
    assert_eq!(head.get_hash(), e.get_hash());
  }

  #[test]
  fn decompose_apps_left_deep_order() {
    // ((f a) b) c → head=f, args=[a, b, c]
    let f = LeanExpr::cnst(mk_name_for("f"), vec![]);
    let a = sort0();
    let b = LeanExpr::sort(Level::succ(Level::zero()));
    let c = bvar_at(0);
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

  // ---- count_foralls ----

  #[test]
  fn count_foralls_counts_leading_only() {
    let e = mk_triple_forall(sort0(), sort0(), sort0(), bvar_at(0));
    assert_eq!(count_foralls(&e), 3);
  }

  #[test]
  fn count_foralls_zero_on_non_forall() {
    assert_eq!(count_foralls(&sort0()), 0);
    assert_eq!(count_foralls(&bvar_at(7)), 0);
  }

  #[test]
  fn count_foralls_does_not_enter_domain() {
    // Forall with another forall in its domain — only one leading forall.
    let e = LeanExpr::all(
      mk_name_for("x"),
      mk_triple_forall(sort0(), sort0(), sort0(), bvar_at(0)),
      sort0(),
      BinderInfo::Default,
    );
    assert_eq!(count_foralls(&e), 1);
  }

  // ---- mk_app_n ----

  #[test]
  fn mk_app_n_builds_left_deep_spine() {
    let f = LeanExpr::cnst(mk_name_for("f"), vec![]);
    let args = vec![sort0(), bvar_at(0), bvar_at(1)];
    let e = mk_app_n(f.clone(), &args);
    let (head, got_args) = decompose_apps(&e);
    assert_eq!(head.get_hash(), f.get_hash());
    assert_eq!(got_args.len(), args.len());
  }

  #[test]
  fn mk_app_n_with_no_args_returns_head() {
    let f = LeanExpr::cnst(mk_name_for("f"), vec![]);
    let e = mk_app_n(f.clone(), &[]);
    assert_eq!(e.get_hash(), f.get_hash());
  }

  // ---- mk_const ----

  #[test]
  fn mk_const_embeds_universes() {
    let u = Level::param(mk_name_for("u"));
    let e = mk_const(&mk_name_for("List"), std::slice::from_ref(&u));
    match e.as_data() {
      ExprData::Const(n, us, _) => {
        assert_eq!(n, &mk_name_for("List"));
        assert_eq!(us.len(), 1);
      },
      other => panic!("expected Const, got {other:?}"),
    }
  }

  // ---- instantiate1 / instantiate1_at ----

  #[test]
  fn instantiate1_substitutes_bvar_0() {
    // body = BVar(0), replacement = sort0 → sort0
    let e = instantiate1(&bvar_at(0), &sort0());
    assert_eq!(e.get_hash(), sort0().get_hash());
  }

  #[test]
  fn instantiate1_shifts_bvar_above_depth_down() {
    // body = BVar(3), replacement = sort0; BVar(3) -> BVar(2) (shifted down).
    let e = instantiate1(&bvar_at(3), &sort0());
    match e.as_data() {
      ExprData::Bvar(n, _) => assert_eq!(nat_to_u64(n), 2),
      other => panic!("expected Bvar, got {other:?}"),
    }
  }

  #[test]
  fn instantiate1_no_bvar_unchanged() {
    let e = sort0();
    let r = instantiate1(&e, &bvar_at(5));
    assert_eq!(r.get_hash(), e.get_hash());
  }

  #[test]
  fn instantiate1_at_non_zero_depth() {
    // body = BVar(2), depth = 2, replacement = sort0.
    let r = instantiate1_at(&bvar_at(2), &sort0(), 2);
    assert_eq!(r.get_hash(), sort0().get_hash());
  }

  // ---- instantiate_rev ----

  #[test]
  fn instantiate_rev_empty_args_is_identity() {
    let e = bvar_at(5);
    let r = instantiate_rev(&e, &[]);
    assert_eq!(r.get_hash(), e.get_hash());
  }

  #[test]
  fn instantiate_rev_substitutes_multiple() {
    // body = App(BVar(0), BVar(1)); args = [a, b]
    // BVar(0) → a, BVar(1) → b
    let a = LeanExpr::cnst(mk_name_for("a"), vec![]);
    let b = LeanExpr::cnst(mk_name_for("b"), vec![]);
    let body = LeanExpr::app(bvar_at(0), bvar_at(1));
    let r = instantiate_rev(&body, &[a.clone(), b.clone()]);
    let (f, args) = decompose_apps(&r);
    assert_eq!(f.get_hash(), a.get_hash());
    assert_eq!(args.len(), 1);
    assert_eq!(args[0].get_hash(), b.get_hash());
  }

  // ---- subst_fvar ----

  #[test]
  fn subst_fvar_replaces_matching_fvar() {
    let (nm, fv) = fresh_fvar("x", 0);
    let r = subst_fvar(&fv, &nm, &sort0());
    assert_eq!(r.get_hash(), sort0().get_hash());
  }

  #[test]
  fn subst_fvar_leaves_unrelated_alone() {
    let (_nm1, _fv1) = fresh_fvar("x", 0);
    let (nm2, _fv2) = fresh_fvar("x", 1);
    let e = sort0();
    let r = subst_fvar(&e, &nm2, &bvar_at(99));
    assert_eq!(r.get_hash(), e.get_hash());
  }

  #[test]
  fn subst_fvar_goes_under_binders() {
    let (nm, fv) = fresh_fvar("p", 0);
    // λ (z : α), fv
    let body =
      LeanExpr::lam(mk_name_for("z"), sort0(), fv.clone(), BinderInfo::Default);
    let r = subst_fvar(&body, &nm, &sort0());
    match r.as_data() {
      ExprData::Lam(_, _, inner, _, _) => {
        assert_eq!(inner.get_hash(), sort0().get_hash());
      },
      other => panic!("expected Lam, got {other:?}"),
    }
  }

  // ---- replace_const_names ----

  #[test]
  fn replace_const_names_empty_map_is_identity() {
    let e = LeanExpr::cnst(mk_name_for("A"), vec![]);
    let r = replace_const_names(&e, &std::collections::HashMap::new());
    assert_eq!(r.get_hash(), e.get_hash());
  }

  #[test]
  fn replace_const_names_renames_const() {
    let mut map = std::collections::HashMap::new();
    map.insert(mk_name_for("A"), mk_name_for("B"));
    let e = LeanExpr::cnst(mk_name_for("A"), vec![]);
    let r = replace_const_names(&e, &map);
    match r.as_data() {
      ExprData::Const(n, _, _) => assert_eq!(n, &mk_name_for("B")),
      other => panic!("expected Const, got {other:?}"),
    }
  }

  #[test]
  fn replace_const_names_preserves_universes() {
    let mut map = std::collections::HashMap::new();
    map.insert(mk_name_for("List"), mk_name_for("Vec"));
    let u = Level::param(mk_name_for("u"));
    let e = LeanExpr::cnst(mk_name_for("List"), vec![u.clone()]);
    let r = replace_const_names(&e, &map);
    match r.as_data() {
      ExprData::Const(n, us, _) => {
        assert_eq!(n, &mk_name_for("Vec"));
        assert_eq!(us.len(), 1);
      },
      other => panic!("expected Const, got {other:?}"),
    }
  }

  #[test]
  fn replace_const_names_renames_proj_type() {
    let mut map = std::collections::HashMap::new();
    map.insert(mk_name_for("Old"), mk_name_for("New"));
    let e = LeanExpr::proj(mk_name_for("Old"), Nat::from(0u64), bvar_at(0));
    let r = replace_const_names(&e, &map);
    match r.as_data() {
      ExprData::Proj(name, _, _, _) => assert_eq!(name, &mk_name_for("New")),
      other => panic!("expected Proj, got {other:?}"),
    }
  }

  #[test]
  fn replace_const_names_nested_in_app_spine() {
    let mut map = std::collections::HashMap::new();
    map.insert(mk_name_for("A"), mk_name_for("B"));
    let e = LeanExpr::app(
      LeanExpr::cnst(mk_name_for("A"), vec![]),
      LeanExpr::cnst(mk_name_for("A"), vec![]),
    );
    let r = replace_const_names(&e, &map);
    let (head, args) = decompose_apps(&r);
    match head.as_data() {
      ExprData::Const(n, _, _) => assert_eq!(n, &mk_name_for("B")),
      other => panic!("expected Const, got {other:?}"),
    }
    match args[0].as_data() {
      ExprData::Const(n, _, _) => assert_eq!(n, &mk_name_for("B")),
      other => panic!("expected Const, got {other:?}"),
    }
  }

  // ---- consume_type_annotations ----

  #[test]
  fn consume_type_annotations_strips_known_wrappers() {
    // `outParam α` reduces to `α`. We use a stub inductive name that the
    // function recognizes.
    use crate::ix::env::BinderInfo;
    let inner = sort0();
    let wrapped = LeanExpr::app(
      LeanExpr::cnst(mk_name_for("outParam"), vec![]),
      inner.clone(),
    );
    let r = consume_type_annotations(&wrapped);
    assert_eq!(r.get_hash(), inner.get_hash());
    // Use BinderInfo to suppress unused-import lint in this module.
    let _ = BinderInfo::Default;
  }

  #[test]
  fn consume_type_annotations_non_wrapper_unchanged() {
    let e = sort0();
    let r = consume_type_annotations(&e);
    assert_eq!(r.get_hash(), e.get_hash());
  }

  // ---- mk_forall / mk_lambda + batch_abstract roundtrip ----

  #[test]
  fn mk_forall_roundtrips_with_forall_telescope() {
    // Open a forall telescope, then reclose with mk_forall. Should match
    // the original up to binder names (which are preserved via LocalDecl).
    let orig = mk_triple_forall(sort0(), sort0(), sort0(), bvar_at(0));
    let (_, decls, body) = forall_telescope(&orig, 3, "p", 0);
    let rebuilt = mk_forall(body, &decls);
    assert_eq!(rebuilt.get_hash(), orig.get_hash());
  }

  #[test]
  fn mk_lambda_produces_lambda_not_forall() {
    let (fv_name, fv) = fresh_fvar("p", 0);
    let decl = LocalDecl {
      fvar_name: fv_name,
      binder_name: mk_name_for("x"),
      domain: sort0(),
      info: BinderInfo::Default,
    };
    let body = fv.clone();
    let e = mk_lambda(body, &[decl]);
    assert!(matches!(e.as_data(), ExprData::Lam(..)));
  }

  #[test]
  fn mk_forall_empty_binders_returns_body_unchanged() {
    let body = sort0();
    let r = mk_forall(body.clone(), &[]);
    assert_eq!(r.get_hash(), body.get_hash());
  }

  // ---- find_motive_fvar ----

  #[test]
  fn find_motive_fvar_direct_match() {
    let (_, motive) = fresh_fvar("motive", 0);
    let motives = vec![motive.clone()];
    // dom = motive applied to some arg
    let dom = LeanExpr::app(motive.clone(), bvar_at(0));
    assert_eq!(find_motive_fvar(&dom, &motives), Some(0));
  }

  #[test]
  fn find_motive_fvar_peels_foralls_then_matches() {
    let (_, motive) = fresh_fvar("motive", 0);
    let motives = vec![motive.clone()];
    // ∀ (x : α), motive x
    let dom = LeanExpr::all(
      mk_name_for("x"),
      sort0(),
      LeanExpr::app(motive.clone(), bvar_at(0)),
      BinderInfo::Default,
    );
    assert_eq!(find_motive_fvar(&dom, &motives), Some(0));
  }

  #[test]
  fn find_motive_fvar_returns_correct_index() {
    let (_, m1) = fresh_fvar("motive", 0);
    let (_, m2) = fresh_fvar("motive", 1);
    let motives = vec![m1.clone(), m2.clone()];
    let dom = LeanExpr::app(m2.clone(), bvar_at(0));
    assert_eq!(find_motive_fvar(&dom, &motives), Some(1));
  }

  #[test]
  fn find_motive_fvar_no_match_returns_none() {
    let (_, motive) = fresh_fvar("motive", 0);
    let motives = vec![motive];
    let dom = sort0();
    assert_eq!(find_motive_fvar(&dom, &motives), None);
  }
}
