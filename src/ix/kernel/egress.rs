//! Egress: convert zero kernel types (`Meta` mode) to `src/ix/env.rs` Lean types.
//!
//! Only works for `Meta` mode since it needs actual names and binder info.

use rayon::iter::{IntoParallelIterator, IntoParallelRefIterator, ParallelIterator};
use rustc_hash::FxHashMap;

use crate::ix::env::{
  self, AxiomVal, ConstantInfo as LeanCI, ConstantVal, ConstructorVal,
  DefinitionVal, InductiveVal, Name, OpaqueVal, QuotVal,
  RecursorRule as LeanRecRule, RecursorVal, TheoremVal,
};
use crate::ix::ixon::constant::DefKind;
use lean_ffi::nat::Nat;

use super::constant::KConst;
use super::env::KEnv;
use super::expr::{ExprData, KExpr, MData};
use super::id::KId;
use super::level::{KUniv, UnivData};
use super::mode::Meta;

/// Convert a zero kernel universe to a Lean level.
fn egress_level(u: &KUniv<Meta>, level_params: &[Name]) -> env::Level {
  match u.data() {
    UnivData::Zero(_) => env::Level::zero(),
    UnivData::Succ(inner, _) => {
      env::Level::succ(egress_level(inner, level_params))
    },
    UnivData::Max(a, b, _) => env::Level::max(
      egress_level(a, level_params),
      egress_level(b, level_params),
    ),
    UnivData::IMax(a, b, _) => env::Level::imax(
      egress_level(a, level_params),
      egress_level(b, level_params),
    ),
    UnivData::Param(idx, _, _) => {
      let pos = usize::try_from(*idx).expect("level param index exceeds usize");
      let name = level_params.get(pos).cloned().unwrap_or_else(Name::anon);
      env::Level::param(name)
    },
  }
}

fn egress_levels(
  levels: &[KUniv<Meta>],
  level_params: &[Name],
) -> Vec<env::Level> {
  levels.iter().map(|l| egress_level(l, level_params)).collect()
}

/// Expression egress cache, keyed by content hash.
type Cache = FxHashMap<super::env::Addr, env::Expr>;

/// Convert a zero kernel expression to a Lean expression.
fn egress_expr(
  expr: &KExpr<Meta>,
  level_params: &[Name],
  cache: &mut Cache,
) -> env::Expr {
  let hk = expr.hash_key();
  if let Some(cached) = cache.get(&hk) {
    return cached.clone();
  }

  let mdata: &Vec<MData> = expr.mdata();

  let inner = match expr.data() {
    ExprData::Var(idx, _, _) => env::Expr::bvar(Nat::from(*idx)),
    ExprData::Sort(u, _) => env::Expr::sort(egress_level(u, level_params)),
    ExprData::Const(id, levels, _) => {
      let lvls = egress_levels(levels, level_params);
      env::Expr::cnst(id.name.clone(), lvls)
    },
    ExprData::App(f, a, _) => {
      let ef = egress_expr(f, level_params, cache);
      let ea = egress_expr(a, level_params, cache);
      env::Expr::app(ef, ea)
    },
    ExprData::Lam(name, bi, ty, body, _) => {
      let ety = egress_expr(ty, level_params, cache);
      let ebody = egress_expr(body, level_params, cache);
      env::Expr::lam(name.clone(), ety, ebody, bi.clone())
    },
    ExprData::All(name, bi, ty, body, _) => {
      let ety = egress_expr(ty, level_params, cache);
      let ebody = egress_expr(body, level_params, cache);
      env::Expr::all(name.clone(), ety, ebody, bi.clone())
    },
    ExprData::Let(name, ty, val, body, nd, _) => {
      let ety = egress_expr(ty, level_params, cache);
      let eval = egress_expr(val, level_params, cache);
      let ebody = egress_expr(body, level_params, cache);
      env::Expr::letE(name.clone(), ety, eval, ebody, *nd)
    },
    ExprData::Prj(id, field, val, _) => {
      let eval = egress_expr(val, level_params, cache);
      env::Expr::proj(id.name.clone(), Nat::from(*field), eval)
    },
    ExprData::Nat(n, _, _) => env::Expr::lit(env::Literal::NatVal(n.clone())),
    ExprData::Str(s, _, _) => env::Expr::lit(env::Literal::StrVal(s.clone())),
  };

  // Re-wrap with mdata layers (innermost first via reverse iteration).
  let result = mdata
    .iter()
    .rev()
    .fold(inner, |acc, kvs| env::Expr::mdata(kvs.clone(), acc));

  cache.insert(hk, result.clone());
  result
}

fn zids_to_names(ids: &[KId<Meta>]) -> Vec<Name> {
  ids.iter().map(|id| id.name.clone()).collect()
}

/// Convert a zero kernel constant to a Lean `ConstantInfo`.
pub fn egress_constant(zc: &KConst<Meta>) -> LeanCI {
  let mut cache = Cache::default();

  match zc {
    KConst::Defn {
      name,
      level_params,
      kind,
      safety,
      hints,
      ty,
      val,
      lean_all,
      ..
    } => {
      let lp: &Vec<Name> = level_params;
      let cnst = ConstantVal {
        name: name.clone(),
        level_params: lp.clone(),
        typ: egress_expr(ty, lp, &mut cache),
      };
      let value = egress_expr(val, lp, &mut cache);
      let all = zids_to_names(lean_all);
      match kind {
        DefKind::Definition => LeanCI::DefnInfo(DefinitionVal {
          cnst,
          value,
          hints: *hints,
          safety: *safety,
          all,
        }),
        DefKind::Theorem => LeanCI::ThmInfo(TheoremVal { cnst, value, all }),
        DefKind::Opaque => LeanCI::OpaqueInfo(OpaqueVal {
          cnst,
          value,
          is_unsafe: *safety == env::DefinitionSafety::Unsafe,
          all,
        }),
      }
    },

    KConst::Axio { name, level_params, is_unsafe, ty, .. } => {
      let lp: &Vec<Name> = level_params;
      LeanCI::AxiomInfo(AxiomVal {
        cnst: ConstantVal {
          name: name.clone(),
          level_params: lp.clone(),
          typ: egress_expr(ty, lp, &mut cache),
        },
        is_unsafe: *is_unsafe,
      })
    },

    KConst::Quot { name, level_params, kind, ty, .. } => {
      let lp: &Vec<Name> = level_params;
      LeanCI::QuotInfo(QuotVal {
        cnst: ConstantVal {
          name: name.clone(),
          level_params: lp.clone(),
          typ: egress_expr(ty, lp, &mut cache),
        },
        kind: *kind,
      })
    },

    KConst::Indc {
      name,
      level_params,
      params,
      indices,
      is_rec,
      is_refl,
      is_unsafe,
      nested,
      ty,
      ctors,
      lean_all,
      ..
    } => {
      let lp: &Vec<Name> = level_params;
      LeanCI::InductInfo(InductiveVal {
        cnst: ConstantVal {
          name: name.clone(),
          level_params: lp.clone(),
          typ: egress_expr(ty, lp, &mut cache),
        },
        num_params: Nat::from(*params),
        num_indices: Nat::from(*indices),
        all: zids_to_names(lean_all),
        ctors: zids_to_names(ctors),
        num_nested: Nat::from(*nested),
        is_rec: *is_rec,
        is_unsafe: *is_unsafe,
        is_reflexive: *is_refl,
      })
    },

    KConst::Ctor {
      name,
      level_params,
      induct,
      cidx,
      params,
      fields,
      is_unsafe,
      ty,
      ..
    } => {
      let lp: &Vec<Name> = level_params;
      LeanCI::CtorInfo(ConstructorVal {
        cnst: ConstantVal {
          name: name.clone(),
          level_params: lp.clone(),
          typ: egress_expr(ty, lp, &mut cache),
        },
        induct: induct.name.clone(),
        cidx: Nat::from(*cidx),
        num_params: Nat::from(*params),
        num_fields: Nat::from(*fields),
        is_unsafe: *is_unsafe,
      })
    },

    KConst::Recr {
      name,
      level_params,
      params,
      indices,
      motives,
      minors,
      ty,
      rules,
      k,
      is_unsafe,
      lean_all,
      ..
    } => {
      let lp: &Vec<Name> = level_params;
      // `RecRule<Meta>` carries the Lean ctor name as an `MField<Name>`
      // purely for LEON roundtrip. The kernel doesn't consult it during
      // type checking — dispatch is positional via the ctor's `cidx` —
      // so we just echo it out verbatim.
      let lean_rules: Vec<LeanRecRule> = rules
        .iter()
        .map(|r| LeanRecRule {
          ctor: r.ctor.clone(),
          n_fields: Nat::from(r.fields),
          rhs: egress_expr(&r.rhs, lp, &mut cache),
        })
        .collect();
      let typ = egress_expr(ty, lp, &mut cache);
      // Surgery permutation is deferred — no source_motive_perm / source_minor_groups
      LeanCI::RecInfo(RecursorVal {
        cnst: ConstantVal { name: name.clone(), level_params: lp.clone(), typ },
        all: zids_to_names(lean_all),
        num_params: Nat::from(*params),
        num_indices: Nat::from(*indices),
        num_motives: Nat::from(*motives),
        num_minors: Nat::from(*minors),
        rules: lean_rules,
        k: *k,
        is_unsafe: *is_unsafe,
      })
    },
  }
}

/// Convert the entire zero kernel environment to a Lean environment.
pub fn lean_egress(zenv: &KEnv<Meta>) -> env::Env {
  let entries: Vec<_> = zenv.iter().collect();

  let results: Vec<(Name, LeanCI)> = entries
    .into_par_iter()
    .map(|(id, zc)| (id.name.clone(), egress_constant(&zc)))
    .collect();

  let mut lean_env = env::Env::default();
  for (name, ci) in results {
    lean_env.insert(name, ci);
  }
  lean_env
}

// ===========================================================================
// Ixon egress: KEnv<Meta> → IxonEnv
// ===========================================================================
//
// This is the inverse of `ixon_ingress`. We walk each constant in the kernel
// env, produce the corresponding Ixon `Constant` payload, and pair it with
// the original `ConstantMeta` (arena + extension tables) so the output env
// is a well-formed input for `decompile_env`.
//
// Why we reuse the original meta: the kernel does not track per-expression
// metadata like binder names, mdata KV-maps, or call-site surgery — those
// live in `ConstantMeta.arena` + `meta_sharing` / `meta_refs` / `meta_univs`.
// Regenerating them from kenv alone would be equivalent to re-running
// compile's call-site surgery pass (hundreds of LOC, and any divergence
// would reintroduce the "second decompiler" problem we're trying to solve).
// Instead we take the original `Named.meta` as-is.
//
// Consequence: `ixon_egress` is only meaningful after a prior `compile_env`
// produced the original `IxonEnv`. For the diagnostic roundtrip test that's
// fine — the test path is `compile_env → ixon_ingress → kenv → ixon_egress
// → decompile_env`. Callers without a pre-existing compile state would need
// to regenerate metadata themselves (out of scope here).
//
// Meta-only: we only need this for the Meta-mode roundtrip diagnostic.
// Generalizing to `<M: KernelMode>` requires address-keyed lookups (in
// Anon mode `kid.name` is `()`, so we can't look up `original_env.named`
// by name). Left as future work.

use std::sync::Arc;

use indexmap::IndexSet;

use crate::ix::address::Address;
use crate::ix::compile::{
  apply_sharing_to_axiom_with_stats, apply_sharing_to_definition_with_stats,
  apply_sharing_to_mutual_block, apply_sharing_to_quotient_with_stats,
  apply_sharing_to_recursor_with_stats,
};
use crate::ix::ixon::constant::{
  Axiom as IxonAxiom, Constant as IxonConstant, ConstantInfo as IxonCI,
  Constructor as IxonConstructor, ConstructorProj, Definition as IxonDefinition,
  DefinitionProj, Inductive as IxonInductive, InductiveProj,
  MutConst as IxonMutConst, Quotient as IxonQuotient, Recursor as IxonRecursor,
  RecursorProj, RecursorRule as IxonRecursorRule,
};
use crate::ix::ixon::env::{Env as IxonEnv, Named};
use crate::ix::ixon::expr::Expr as IxonExpr;
use crate::ix::ixon::metadata::ConstantMetaInfo;
use crate::ix::ixon::univ::Univ as IxonUniv;

/// Per-constant (or per-block) working context accumulated while converting
/// kernel expressions back to Ixon. Mirrors `BlockCache.refs` / `univs` on
/// the compile side: every distinct address gets one slot in `refs`, every
/// distinct universe term gets one slot in `univs`, and expressions refer to
/// entries by positional index.
///
/// Also carries the block's `mut_ctx` as a `FxHashMap` (for O(1) per-Const
/// lookup when discriminating `Rec` from `Ref`) and a memoization cache
/// keyed by `KExpr::addr()` so DAG-shared subexpressions are converted
/// only once.
struct EgressCtx {
  /// External constant references, in insertion order.
  refs: IndexSet<Address>,
  /// Universe terms, in insertion order (dedup by structural equality
  /// via `Arc<Univ>`'s derived `Eq`/`Hash`).
  univs: IndexSet<Arc<IxonUniv>>,
  /// Mutual block sibling lookup: KId of a sibling → its position in the
  /// block. Used to decide `Rec(idx, _)` vs. `Ref(idx, _)` for Const nodes.
  /// Empty for non-Muts (standalone) constants.
  mut_ctx: FxHashMap<KId<Meta>, u64>,
  /// Memoized expression conversion. Keyed by `KExpr::addr()` (content
  /// hash); same hash → same Ixon expression (within a single block's
  /// tables).
  expr_cache: FxHashMap<blake3::Hash, Arc<IxonExpr>>,
  /// Memoized universe conversion.
  univ_cache: FxHashMap<blake3::Hash, Arc<IxonUniv>>,
}

impl EgressCtx {
  fn new() -> Self {
    Self {
      refs: IndexSet::new(),
      univs: IndexSet::new(),
      mut_ctx: FxHashMap::default(),
      expr_cache: FxHashMap::default(),
      univ_cache: FxHashMap::default(),
    }
  }

  fn with_mut_ctx(mut_ctx: Vec<KId<Meta>>) -> Self {
    let mut out = Self::new();
    for (i, kid) in mut_ctx.into_iter().enumerate() {
      out.mut_ctx.insert(kid, i as u64);
    }
    out
  }

  fn intern_ref(&mut self, addr: Address) -> u64 {
    let (idx, _) = self.refs.insert_full(addr);
    idx as u64
  }

  fn intern_univ(&mut self, u: Arc<IxonUniv>) -> u64 {
    let (idx, _) = self.univs.insert_full(u);
    idx as u64
  }

  fn into_vecs(self) -> (Vec<Address>, Vec<Arc<IxonUniv>>) {
    (self.refs.into_iter().collect(), self.univs.into_iter().collect())
  }
}

/// Convert a kernel universe to an Ixon universe (memoized by content hash).
fn kuniv_to_ixon(u: &KUniv<Meta>, ctx: &mut EgressCtx) -> Arc<IxonUniv> {
  let key = **u.addr();
  if let Some(hit) = ctx.univ_cache.get(&key) {
    return hit.clone();
  }
  let out = match u.data() {
    UnivData::Zero(_) => IxonUniv::zero(),
    UnivData::Succ(inner, _) => IxonUniv::succ(kuniv_to_ixon(inner, ctx)),
    UnivData::Max(a, b, _) => {
      let a = kuniv_to_ixon(a, ctx);
      let b = kuniv_to_ixon(b, ctx);
      IxonUniv::max(a, b)
    },
    UnivData::IMax(a, b, _) => {
      let a = kuniv_to_ixon(a, ctx);
      let b = kuniv_to_ixon(b, ctx);
      IxonUniv::imax(a, b)
    },
    UnivData::Param(idx, _, _) => IxonUniv::var(*idx),
  };
  ctx.univ_cache.insert(key, out.clone());
  out
}

/// Intern a universe into the block's `univs` table and return its index.
fn kuniv_idx(u: &KUniv<Meta>, ctx: &mut EgressCtx) -> u64 {
  let u = kuniv_to_ixon(u, ctx);
  ctx.intern_univ(u)
}

/// Convert a list of kernel universes to a `Vec<u64>` of indices into the
/// block's `univs` table. Used for `IxonExpr::Ref` / `Rec` universe args.
fn kunivs_to_idxs(us: &[KUniv<Meta>], ctx: &mut EgressCtx) -> Vec<u64> {
  us.iter().map(|u| kuniv_idx(u, ctx)).collect()
}

/// Convert a kernel expression to an Ixon expression, accumulating any
/// referenced addresses and universes into `ctx`. Memoized on
/// `expr.addr()` (content hash) so DAG-shared subtrees convert once.
///
/// `ctx.mut_ctx` is the block's list of sibling `KId`s (for mutual
/// blocks): if an `ExprData::Const` node's `KId` matches one of these,
/// it is emitted as an `IxonExpr::Rec(idx, univs)` rather than a
/// `Ref(idx, univs)`. This is the inverse of `ingress_expr`'s
/// `IxonExpr::Rec → KExpr::Const(mut_ctx[i])` case.
///
/// Note on `Share`: we never emit `IxonExpr::Share(_)` here; sharing is
/// discovered fresh by the `apply_sharing_*` pass that wraps our output.
fn kexpr_to_ixon(expr: &KExpr<Meta>, ctx: &mut EgressCtx) -> Arc<IxonExpr> {
  let key = **expr.addr();
  if let Some(hit) = ctx.expr_cache.get(&key) {
    return hit.clone();
  }
  let out = match expr.data() {
    ExprData::Var(idx, _, _) => IxonExpr::var(*idx),
    ExprData::Sort(u, _) => {
      let u_idx = kuniv_idx(u, ctx);
      IxonExpr::sort(u_idx)
    },
    ExprData::Const(id, univs, _) => {
      let u_idxs = kunivs_to_idxs(univs, ctx);
      // Look up in mut_ctx first — a match means this is a mutual
      // self-reference and must be emitted as `Rec`, not `Ref`.
      if let Some(&rec_idx) = ctx.mut_ctx.get(id) {
        IxonExpr::rec(rec_idx, u_idxs)
      } else {
        let r_idx = ctx.intern_ref(id.addr.clone());
        IxonExpr::reference(r_idx, u_idxs)
      }
    },
    ExprData::App(f, a, _) => {
      let f = kexpr_to_ixon(f, ctx);
      let a = kexpr_to_ixon(a, ctx);
      IxonExpr::app(f, a)
    },
    ExprData::Lam(_, _, ty, body, _) => {
      let ty = kexpr_to_ixon(ty, ctx);
      let body = kexpr_to_ixon(body, ctx);
      IxonExpr::lam(ty, body)
    },
    ExprData::All(_, _, ty, body, _) => {
      let ty = kexpr_to_ixon(ty, ctx);
      let body = kexpr_to_ixon(body, ctx);
      IxonExpr::all(ty, body)
    },
    ExprData::Let(_, ty, val, body, nd, _) => {
      let ty = kexpr_to_ixon(ty, ctx);
      let val = kexpr_to_ixon(val, ctx);
      let body = kexpr_to_ixon(body, ctx);
      IxonExpr::let_(*nd, ty, val, body)
    },
    ExprData::Prj(id, field, val, _) => {
      let val = kexpr_to_ixon(val, ctx);
      let r_idx = ctx.intern_ref(id.addr.clone());
      IxonExpr::prj(r_idx, *field, val)
    },
    ExprData::Nat(_, addr, _) => {
      let r_idx = ctx.intern_ref(addr.clone());
      IxonExpr::nat(r_idx)
    },
    ExprData::Str(_, addr, _) => {
      let r_idx = ctx.intern_ref(addr.clone());
      IxonExpr::str(r_idx)
    },
  };
  ctx.expr_cache.insert(key, out.clone());
  out
}

/// Build an `IxonDefinition` body (type + value) from a `KConst::Defn`.
fn kdefn_to_ixon(
  kc: &KConst<Meta>,
  ctx: &mut EgressCtx,
) -> Result<IxonDefinition, String> {
  match kc {
    KConst::Defn { kind, safety, lvls, ty, val, .. } => {
      let typ = kexpr_to_ixon(ty, ctx);
      let value = kexpr_to_ixon(val, ctx);
      Ok(IxonDefinition {
        kind: *kind,
        safety: *safety,
        lvls: *lvls,
        typ,
        value,
      })
    },
    _ => Err(format!("kdefn_to_ixon: expected Defn, got {}", kc_kind(kc))),
  }
}

/// Build an `IxonRecursor` body from a `KConst::Recr`.
fn krecr_to_ixon(
  kc: &KConst<Meta>,
  ctx: &mut EgressCtx,
) -> Result<IxonRecursor, String> {
  match kc {
    KConst::Recr {
      k,
      is_unsafe,
      lvls,
      params,
      indices,
      motives,
      minors,
      ty,
      rules,
      ..
    } => {
      let typ = kexpr_to_ixon(ty, ctx);
      let rules: Vec<IxonRecursorRule> = rules
        .iter()
        .map(|r| IxonRecursorRule {
          fields: r.fields,
          rhs: kexpr_to_ixon(&r.rhs, ctx),
        })
        .collect();
      Ok(IxonRecursor {
        k: *k,
        is_unsafe: *is_unsafe,
        lvls: *lvls,
        params: *params,
        indices: *indices,
        motives: *motives,
        minors: *minors,
        typ,
        rules,
      })
    },
    _ => Err(format!("krecr_to_ixon: expected Recr, got {}", kc_kind(kc))),
  }
}

/// Build an `IxonAxiom` body from a `KConst::Axio`.
fn kaxio_to_ixon(
  kc: &KConst<Meta>,
  ctx: &mut EgressCtx,
) -> Result<IxonAxiom, String> {
  match kc {
    KConst::Axio { is_unsafe, lvls, ty, .. } => {
      let typ = kexpr_to_ixon(ty, ctx);
      Ok(IxonAxiom { is_unsafe: *is_unsafe, lvls: *lvls, typ })
    },
    _ => Err(format!("kaxio_to_ixon: expected Axio, got {}", kc_kind(kc))),
  }
}

/// Build an `IxonQuotient` body from a `KConst::Quot`.
fn kquot_to_ixon(
  kc: &KConst<Meta>,
  ctx: &mut EgressCtx,
) -> Result<IxonQuotient, String> {
  match kc {
    KConst::Quot { kind, lvls, ty, .. } => {
      let typ = kexpr_to_ixon(ty, ctx);
      Ok(IxonQuotient { kind: *kind, lvls: *lvls, typ })
    },
    _ => Err(format!("kquot_to_ixon: expected Quot, got {}", kc_kind(kc))),
  }
}

/// Short name for the kernel constant kind — for error messages only.
fn kc_kind(kc: &KConst<Meta>) -> &'static str {
  match kc {
    KConst::Defn { .. } => "Defn",
    KConst::Recr { .. } => "Recr",
    KConst::Axio { .. } => "Axio",
    KConst::Quot { .. } => "Quot",
    KConst::Indc { .. } => "Indc",
    KConst::Ctor { .. } => "Ctor",
  }
}

/// Build an `IxonInductive` body from a `KConst::Indc` plus all of its
/// constructor `KConst::Ctor` entries.
///
/// `ctor_kconsts` must be in cidx order (0, 1, 2, ...) — we rely on this to
/// mirror the compile-side layout. (`egress_muts_block` sorts by cidx
/// before calling.)
fn kind_to_ixon(
  ind_kc: &KConst<Meta>,
  ctor_kconsts: &[&KConst<Meta>],
  ctx: &mut EgressCtx,
) -> Result<IxonInductive, String> {
  let KConst::Indc {
    lvls,
    params,
    indices,
    is_rec,
    is_refl,
    is_unsafe,
    nested,
    ty,
    ..
  } = ind_kc
  else {
    return Err(format!(
      "kind_to_ixon: expected Indc, got {}",
      kc_kind(ind_kc)
    ));
  };

  let typ = kexpr_to_ixon(ty, ctx);
  let ctors: Vec<IxonConstructor> = ctor_kconsts
    .iter()
    .map(|cc| match cc {
      KConst::Ctor { is_unsafe, lvls, cidx, params, fields, ty, .. } => {
        let typ = kexpr_to_ixon(ty, ctx);
        Ok(IxonConstructor {
          is_unsafe: *is_unsafe,
          lvls: *lvls,
          cidx: *cidx,
          params: *params,
          fields: *fields,
          typ,
        })
      },
      other => Err(format!(
        "kind_to_ixon: expected Ctor under Indc, got {}",
        kc_kind(other)
      )),
    })
    .collect::<Result<_, _>>()?;

  Ok(IxonInductive {
    recr: *is_rec,
    refl: *is_refl,
    is_unsafe: *is_unsafe,
    lvls: *lvls,
    params: *params,
    indices: *indices,
    nested: *nested,
    typ,
    ctors,
  })
}

/// Compute content address of an Ixon `Constant` by serializing and hashing.
fn content_address_of(c: &IxonConstant) -> Address {
  let mut bytes = Vec::new();
  c.put(&mut bytes);
  Address::hash(&bytes)
}

/// Build a `FxHashMap<Name, (KId, KConst)>` for fast lookup by Lean name.
/// Call once per `ixon_egress` invocation and share.
fn build_name_index(
  kenv: &KEnv<Meta>,
) -> FxHashMap<Name, (KId<Meta>, KConst<Meta>)> {
  let mut out: FxHashMap<Name, (KId<Meta>, KConst<Meta>)> = FxHashMap::default();
  for (kid, kc) in kenv.iter() {
    out.insert(kid.name.clone(), (kid, kc));
  }
  out
}

/// Build the `mut_ctx` KId slice for a Muts block, taking one canonical name
/// from each equivalence class in `all`. This must mirror the compile-side
/// ctx — the ingress constructed mut_ctx entries via `resolve_all(ctx, names,
/// name_to_addr)` which looks up each class-representative name's stored
/// projection/block address. Here we replicate that lookup against our
/// `name_index` (Meta-mode) rather than against the Ixon `named` table, so
/// the resulting KIds are byte-for-byte identical to those `ingress_expr`
/// emitted for `IxonExpr::Rec` nodes inside this block.
fn build_block_mut_ctx(
  all: &[Vec<Address>],
  names: &FxHashMap<Address, Name>,
  name_index: &FxHashMap<Name, (KId<Meta>, KConst<Meta>)>,
) -> Result<Vec<KId<Meta>>, String> {
  let mut ctx: Vec<KId<Meta>> = Vec::with_capacity(all.len());
  for (i, cls) in all.iter().enumerate() {
    let name_addr = cls.first().ok_or_else(|| {
      format!("build_block_mut_ctx: class {i} has no canonical name")
    })?;
    let name = names.get(name_addr).cloned().ok_or_else(|| {
      format!(
        "build_block_mut_ctx: name_addr {} not in names map",
        &name_addr.hex()[..8]
      )
    })?;
    let (kid, _) = name_index.get(&name).ok_or_else(|| {
      format!("build_block_mut_ctx: '{name}' not in kenv")
    })?;
    ctx.push(kid.clone());
  }
  Ok(ctx)
}

/// Build an `IxonMutConst` for one member of a Muts block.
///
/// For `Indc` members we also need the constructor `KConst`s; caller passes
/// them pre-sorted by cidx.
fn build_mut_const(
  member: &KConst<Meta>,
  ctor_kconsts: &[&KConst<Meta>],
  ctx: &mut EgressCtx,
) -> Result<IxonMutConst, String> {
  match member {
    KConst::Defn { .. } => Ok(IxonMutConst::Defn(kdefn_to_ixon(member, ctx)?)),
    KConst::Recr { .. } => Ok(IxonMutConst::Recr(krecr_to_ixon(member, ctx)?)),
    KConst::Indc { .. } => {
      Ok(IxonMutConst::Indc(kind_to_ixon(member, ctor_kconsts, ctx)?))
    },
    other => Err(format!(
      "build_mut_const: invalid member kind {} in Muts block",
      kc_kind(other)
    )),
  }
}

/// Build a fresh `Named` entry for a reconstructed constant, preserving
/// the original's `meta` and `original` (aux_gen regeneration hint) fields
/// but with an updated `addr`.
///
/// Decompile's Pass 2 relies on `named.original.is_some()` to decide which
/// entries are aux_gen-regenerated — we MUST copy that field over, or
/// otherwise every `.brecOn*` / `.below` / `.brecOn_N.eq` gets dropped.
fn rebuild_named(addr: Address, original: &Named) -> Named {
  Named {
    addr,
    meta: original.meta.clone(),
    original: original.original.clone(),
  }
}

/// Register a member `Named` pointing at the appropriate address:
/// - If `is_singleton_class`, the member lives directly at `block_addr`
///   (no projection: compile/mutual.rs singleton-class branch).
/// - Otherwise emit the appropriate projection (`IPrj` / `CPrj` / `RPrj`
///   / `DPrj`), store it, and register the name with the projection addr.
#[allow(clippy::too_many_arguments)]
fn register_muts_member(
  out: &IxonEnv,
  member_name: &Name,
  original: &Named,
  block_addr: &Address,
  member_kind: MutConstKind,
  member_idx: u64,
  ctor_idx: Option<u64>,
  is_singleton_class: bool,
) -> Result<(), String> {
  if is_singleton_class {
    // Singleton non-inductive class: Named.addr = block_addr directly.
    out.register_name(
      member_name.clone(),
      rebuild_named(block_addr.clone(), original),
    );
    return Ok(());
  }
  // Multi-class / inductive block: build the projection wrapper.
  let proj_constant = match (member_kind, ctor_idx) {
    (MutConstKind::Indc, None) => IxonConstant::new(IxonCI::IPrj(InductiveProj {
      idx: member_idx,
      block: block_addr.clone(),
    })),
    (MutConstKind::Indc, Some(ci)) => {
      IxonConstant::new(IxonCI::CPrj(ConstructorProj {
        idx: member_idx,
        cidx: ci,
        block: block_addr.clone(),
      }))
    },
    (MutConstKind::Recr, None) => IxonConstant::new(IxonCI::RPrj(RecursorProj {
      idx: member_idx,
      block: block_addr.clone(),
    })),
    (MutConstKind::Defn, None) => IxonConstant::new(IxonCI::DPrj(DefinitionProj {
      idx: member_idx,
      block: block_addr.clone(),
    })),
    (k, Some(_)) => {
      return Err(format!(
        "register_muts_member: ctor_idx is only valid for Indc (got {k:?})"
      ));
    },
  };
  let proj_addr = content_address_of(&proj_constant);
  out.store_const(proj_addr.clone(), proj_constant);
  out.register_name(member_name.clone(), rebuild_named(proj_addr, original));
  Ok(())
}

#[derive(Clone, Copy, Debug)]
enum MutConstKind {
  Defn,
  Indc,
  Recr,
}

impl MutConstKind {
  fn of(kc: &KConst<Meta>) -> Option<Self> {
    match kc {
      KConst::Defn { .. } => Some(Self::Defn),
      KConst::Indc { .. } => Some(Self::Indc),
      KConst::Recr { .. } => Some(Self::Recr),
      _ => None,
    }
  }
}

/// Reconstruct one Muts block from the kenv.
///
/// `muts_name` is the synthetic `Ix.<hash>.<first>` name under which the
/// block was registered by compile.  `muts_named` is its `Named` entry (with
/// `meta.info == ConstantMetaInfo::Muts { all }`).  `all` is the
/// class-equivalence structure.
#[allow(clippy::too_many_arguments)]
fn egress_muts_block(
  muts_name: &Name,
  muts_named: &Named,
  all: &[Vec<Address>],
  original_env: &IxonEnv,
  names: &FxHashMap<Address, Name>,
  name_index: &FxHashMap<Name, (KId<Meta>, KConst<Meta>)>,
  out: &IxonEnv,
) -> Result<(), String> {
  let mut_ctx_vec = build_block_mut_ctx(all, names, name_index)?;
  let mut ctx = EgressCtx::with_mut_ctx(mut_ctx_vec);

  // Determine per-class representative KConst: this is the kernel's
  // canonical member for the class.  Alpha-equivalent siblings share a
  // KConst; the `all[i][0]` choice matches the compile-side canonical pick.
  let mut mut_consts: Vec<IxonMutConst> = Vec::with_capacity(all.len());
  // Track whether any class is inductive. An Indc anywhere forces the
  // block into the "multi-class-or-inductive" register-as-projection
  // branch below (mirroring compile/mutual.rs::mutual's logic).
  let mut has_indc = false;
  for (i, cls) in all.iter().enumerate() {
    let name_addr = cls.first().ok_or_else(|| {
      format!("egress_muts_block: class {i} has no canonical name")
    })?;
    let rep_name = names.get(name_addr).cloned().ok_or_else(|| {
      format!(
        "egress_muts_block: canonical name addr {} not in names map",
        &name_addr.hex()[..8]
      )
    })?;
    let (_, rep_kc) = name_index.get(&rep_name).ok_or_else(|| {
      format!(
        "egress_muts_block: canonical name '{rep_name}' (class {i}) not in kenv"
      )
    })?;

    // For Indc, collect constructor KConsts in cidx order.
    let ctor_ks: Vec<&KConst<Meta>> = match rep_kc {
      KConst::Indc { ctors, .. } => {
        has_indc = true;
        let mut sorted: Vec<(u64, &KConst<Meta>)> =
          Vec::with_capacity(ctors.len());
        for ctor_id in ctors {
          let (_, c) = name_index.get(&ctor_id.name).ok_or_else(|| {
            format!(
              "egress_muts_block: ctor '{}' (of '{rep_name}') not in kenv",
              ctor_id.name
            )
          })?;
          let cidx = match c {
            KConst::Ctor { cidx, .. } => *cidx,
            other => {
              return Err(format!(
                "egress_muts_block: expected Ctor for '{}', got {}",
                ctor_id.name,
                kc_kind(other)
              ));
            },
          };
          sorted.push((cidx, c));
        }
        sorted.sort_by_key(|(cidx, _)| *cidx);
        sorted.into_iter().map(|(_, c)| c).collect()
      },
      _ => Vec::new(),
    };

    mut_consts.push(build_mut_const(rep_kc, &ctor_ks, &mut ctx)?);
  }

  let (refs, univs) = ctx.into_vecs();
  let first_name = names
    .get(all.first().and_then(|c| c.first()).ok_or("empty Muts")?)
    .cloned()
    .ok_or("first name missing")?;
  let block_name_str = first_name.pretty();
  let result = apply_sharing_to_mutual_block(
    mut_consts,
    refs,
    univs,
    Some(&block_name_str),
  );
  let block_addr = content_address_of(&result.constant);
  out.store_const(block_addr.clone(), result.constant);

  // Register the synthetic Muts Named entry at the new block_addr. Preserve
  // the original `meta` / `original` fields — decompile's Pass 2 keys off
  // `named.original.is_some()` to identify aux_gen entries.
  out.register_name(muts_name.clone(), rebuild_named(block_addr.clone(), muts_named));

  // Register all member names. Singleton case: no projections.
  let is_singleton = all.len() == 1 && !has_indc;

  for (i, cls) in all.iter().enumerate() {
    let i_u64 = i as u64;
    let rep_name_addr = cls.first().expect("class non-empty");
    let rep_name = names.get(rep_name_addr).cloned().expect("rep present");
    let (_, rep_kc) =
      name_index.get(&rep_name).expect("rep in name_index above");
    let rep_kind = MutConstKind::of(rep_kc).ok_or_else(|| {
      format!(
        "egress_muts_block: class {i} canonical '{rep_name}' is {}, expected Defn/Indc/Recr",
        kc_kind(rep_kc)
      )
    })?;

    // Every equivalent member gets its own Named, all pointing at the same
    // projection/block addr (alpha-collapsed members share their post-
    // compile representation).
    for member_name_addr in cls {
      let member_name = names.get(member_name_addr).cloned().ok_or_else(|| {
        format!(
          "egress_muts_block: member name addr {} not in names map",
          &member_name_addr.hex()[..8]
        )
      })?;
      let orig_named = original_env.lookup_name(&member_name).ok_or_else(
        || {
          format!(
            "egress_muts_block: original Named for '{member_name}' missing \
             — can't preserve meta"
          )
        },
      )?;
      register_muts_member(
        out,
        &member_name,
        &orig_named,
        &block_addr,
        rep_kind,
        i_u64,
        None,
        is_singleton,
      )?;
    }

    // For Indc: also register each constructor name at its own CPrj.
    if let KConst::Indc { ctors, .. } = rep_kc {
      // Collect (cidx, ctor_name) pairs so we register with the right cidx
      // regardless of the `ctors` order.
      let mut sorted: Vec<(u64, Name)> = Vec::with_capacity(ctors.len());
      for cid in ctors {
        let (_, c) = name_index
          .get(&cid.name)
          .ok_or_else(|| format!("ctor '{}' not in kenv", cid.name))?;
        let cidx = match c {
          KConst::Ctor { cidx, .. } => *cidx,
          other => {
            return Err(format!(
              "expected Ctor for '{}' got {}",
              cid.name,
              kc_kind(other)
            ));
          },
        };
        sorted.push((cidx, cid.name.clone()));
      }
      sorted.sort_by_key(|(cidx, _)| *cidx);
      for (cidx, ctor_name) in sorted {
        let orig_named =
          original_env.lookup_name(&ctor_name).ok_or_else(|| {
            format!(
              "egress_muts_block: original Named for ctor '{ctor_name}' missing"
            )
          })?;
        register_muts_member(
          out,
          &ctor_name,
          &orig_named,
          &block_addr,
          MutConstKind::Indc,
          i_u64,
          Some(cidx),
          // Ctors are never singleton-class (an Indc class forces
          // projection emission even when there's only one class).
          false,
        )?;
      }
    }
  }

  Ok(())
}

/// Reconstruct a single standalone constant from the kenv.
fn egress_standalone(
  name: &Name,
  original_named: &Named,
  name_index: &FxHashMap<Name, (KId<Meta>, KConst<Meta>)>,
  out: &IxonEnv,
) -> Result<(), String> {
  let (_, kc) = name_index.get(name).ok_or_else(|| {
    format!("egress_standalone: '{name}' not in kenv")
  })?;
  let mut ctx = EgressCtx::new();
  let (constant, addr) = match kc {
    KConst::Defn { .. } => {
      let def = kdefn_to_ixon(kc, &mut ctx)?;
      let (refs, univs) = ctx.into_vecs();
      let result = apply_sharing_to_definition_with_stats(
        def,
        refs,
        univs,
        Some(&name.pretty()),
      );
      let addr = content_address_of(&result.constant);
      (result.constant, addr)
    },
    KConst::Recr { .. } => {
      let rec = krecr_to_ixon(kc, &mut ctx)?;
      let (refs, univs) = ctx.into_vecs();
      let result = apply_sharing_to_recursor_with_stats(rec, refs, univs);
      let addr = content_address_of(&result.constant);
      (result.constant, addr)
    },
    KConst::Axio { .. } => {
      let ax = kaxio_to_ixon(kc, &mut ctx)?;
      let (refs, univs) = ctx.into_vecs();
      let result = apply_sharing_to_axiom_with_stats(ax, refs, univs);
      let addr = content_address_of(&result.constant);
      (result.constant, addr)
    },
    KConst::Quot { .. } => {
      let q = kquot_to_ixon(kc, &mut ctx)?;
      let (refs, univs) = ctx.into_vecs();
      let result = apply_sharing_to_quotient_with_stats(q, refs, univs);
      let addr = content_address_of(&result.constant);
      (result.constant, addr)
    },
    other => {
      return Err(format!(
        "egress_standalone: '{name}' is {} (should have been handled by Muts path)",
        kc_kind(other)
      ));
    },
  };
  out.store_const(addr.clone(), constant);
  out.register_name(name.clone(), rebuild_named(addr, original_named));
  Ok(())
}

/// Top-level Ixon egress.
///
/// Traverses `kenv`, emits Ixon `Constant`s paired with the original metadata
/// sourced from `original_env.named`, and returns a new `IxonEnv` whose
/// `named[name]` entries preserve every per-constant meta the decompiler
/// needs. Blobs, names, and commitments are cloned from `original_env`
/// unchanged (they're content-addressed so any address referenced by an
/// expression resolves without needing regeneration).
///
/// Partitions original Named entries into Muts-block drivers and standalone
/// constants, then processes each partition in parallel via rayon. Storing
/// into the output `IxonEnv` is thread-safe because the env uses DashMaps.
pub fn ixon_egress(
  kenv: &KEnv<Meta>,
  original_env: &IxonEnv,
) -> Result<IxonEnv, String> {
  let t_start = std::time::Instant::now();
  let out = IxonEnv::new();

  // Copy immutable content tables.
  for entry in original_env.blobs.iter() {
    out.blobs.insert(entry.key().clone(), entry.value().clone());
  }
  for entry in original_env.names.iter() {
    out.names.insert(entry.key().clone(), entry.value().clone());
  }
  for entry in original_env.comms.iter() {
    out.comms.insert(entry.key().clone(), entry.value().clone());
  }
  eprintln!(
    "[ixon_egress] copy content tables: {:.2?} (blobs={}, names={}, comms={})",
    t_start.elapsed(),
    out.blobs.len(),
    out.names.len(),
    out.comms.len()
  );

  // Build name_index for fast lookups (Meta mode only — KId.name is the Lean name).
  let t_idx = std::time::Instant::now();
  let name_index = build_name_index(kenv);
  eprintln!(
    "[ixon_egress] build name_index:    {:.2?} ({} entries)",
    t_idx.elapsed(),
    name_index.len()
  );

  // Build address → name map for resolving class canonical names.
  let mut names: FxHashMap<Address, Name> = FxHashMap::default();
  for entry in original_env.names.iter() {
    names.insert(entry.key().clone(), entry.value().clone());
  }

  // Partition original Named entries:
  // - Muts-synthetic entries drive block reconstruction.
  // - Standalone entries (Def/Axio/Quot/Rec pointing at a non-projection
  //   body) get their own rebuild.
  // - Everything else (members of Muts blocks — meta is Indc/Ctor/Rec/Def
  //   pointing at IPrj/CPrj/RPrj/DPrj/Muts) is skipped here; the Muts
  //   block's reconstruction registers them.
  let t_partition = std::time::Instant::now();
  let mut muts_entries: Vec<(Name, Named)> = Vec::new();
  let mut standalone_entries: Vec<(Name, Named)> = Vec::new();
  for entry in original_env.named.iter() {
    let name = entry.key().clone();
    let named = entry.value().clone();
    match &named.meta.info {
      ConstantMetaInfo::Muts { .. } => muts_entries.push((name, named)),
      _ => {
        let orig_const = original_env.get_const(&named.addr);
        let is_muts_member = matches!(
          orig_const.as_ref().map(|c| &c.info),
          Some(
            IxonCI::IPrj(_)
              | IxonCI::CPrj(_)
              | IxonCI::RPrj(_)
              | IxonCI::DPrj(_)
              | IxonCI::Muts(_)
          )
        );
        if !is_muts_member {
          standalone_entries.push((name, named));
        }
      },
    }
  }
  eprintln!(
    "[ixon_egress] partition:           {:.2?} (muts={}, standalone={})",
    t_partition.elapsed(),
    muts_entries.len(),
    standalone_entries.len()
  );

  // Process Muts blocks in parallel.
  let t_muts = std::time::Instant::now();
  muts_entries.par_iter().try_for_each(
    |(muts_name, muts_named)| -> Result<(), String> {
      let all: &[Vec<Address>] = match &muts_named.meta.info {
        ConstantMetaInfo::Muts { all } => all.as_slice(),
        _ => unreachable!("partitioned above"),
      };
      egress_muts_block(
        muts_name,
        muts_named,
        all,
        original_env,
        &names,
        &name_index,
        &out,
      )
    },
  )?;
  eprintln!(
    "[ixon_egress] muts blocks:         {:.2?}",
    t_muts.elapsed()
  );

  // Process standalone constants in parallel.
  let t_solo = std::time::Instant::now();
  standalone_entries.par_iter().try_for_each(
    |(name, named)| -> Result<(), String> {
      egress_standalone(name, named, &name_index, &out)
    },
  )?;
  eprintln!(
    "[ixon_egress] standalone consts:   {:.2?}",
    t_solo.elapsed()
  );
  eprintln!("[ixon_egress] total:               {:.2?}", t_start.elapsed());

  Ok(out)
}
