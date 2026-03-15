//! Conversion from Ixon (compiled) types to kernel types.
//!
//! Converts Ixon `Constant`/`ConstantInfo`/`Expr`/`Univ` (alpha-invariant,
//! content-addressed) to `KExpr`/`KLevel`/`KConstantInfo` (kernel types
//! with positional universe params).
//!
//! This is the canonical path for type-checking: Lean env → Ixon compilation
//! (SCC + partition refinement) → this converter → kernel type-checker.
//! The direct `convert_env` path bypasses Ixon and leaves `canonical_block`
//! empty; this converter populates it from the Ixon mutual block structure.

use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};

use rayon::iter::{IntoParallelIterator, ParallelIterator};
use rustc_hash::FxHashMap;

use crate::ix::address::Address;
use crate::ix::compile::CompileState;
use crate::ix::env::{
  DefinitionSafety, Literal, Name, ReducibilityHints,
};
use crate::ix::ixon::constant::{
  Constant, ConstantInfo as IxonConstantInfo, DefKind,
  MutConst as IxonMutConst,
};
use crate::ix::ixon::expr::Expr;
use crate::ix::ixon::metadata::{
  ConstantMeta, DataValue as IxonDataValue, ExprMeta, ExprMetaData,
};
use crate::ix::ixon::univ::Univ;
use crate::lean::nat::Nat;

use super::convert::build_primitives_from_kenv;
use super::types::{MetaMode, *};

// ============================================================================
// Conversion context (per-constant, read-only during expression conversion)
// ============================================================================

/// Expression conversion cache, keyed on (expr pointer, arena_idx).
/// Same strategy as Lean's ConvertState.exprCache.
type ExprConvertCache<M> = FxHashMap<(usize, u64), KExpr<M>>;

/// Read-only context for converting a single Ixon constant's expressions.
struct IxonCtx<'a> {
  /// Shared subexpressions from `Constant.sharing`.
  sharing: &'a [Arc<Expr>],
  /// Reference table from `Constant.refs` (addresses for Ref, Prj, Str, Nat).
  refs: &'a [Address],
  /// Universe table from `Constant.univs`.
  univs: &'a [Arc<Univ>],
  /// Addresses of mutual block members (for resolving `Expr::Rec`).
  recur_addrs: Vec<Address>,
  /// Metadata arena for this constant.
  arena: &'a ExprMeta,
  /// Names map: address → Name (from IxonEnv.names).
  names: &'a FxHashMap<Address, Name>,
  /// Level parameter names (resolved from metadata).
  level_param_names: Vec<Name>,
}

// ============================================================================
// Universe conversion
// ============================================================================

fn convert_univ<M: MetaMode>(
  univ: &Univ,
  ctx: &IxonCtx<'_>,
) -> KLevel<M> {
  match univ {
    Univ::Zero => KLevel::zero(),
    Univ::Succ(inner) => KLevel::succ(convert_univ(inner, ctx)),
    Univ::Max(a, b) => {
      KLevel::max(convert_univ(a, ctx), convert_univ(b, ctx))
    }
    Univ::IMax(a, b) => {
      KLevel::imax(convert_univ(a, ctx), convert_univ(b, ctx))
    }
    Univ::Var(idx) => {
      let name = ctx
        .level_param_names
        .get(*idx as usize)
        .cloned()
        .unwrap_or_else(Name::anon);
      KLevel::param(*idx as usize, M::mk_field(name))
    }
  }
}

/// Convert a list of universe indices (into the constant's univs table)
/// to kernel levels.
fn convert_univ_args<M: MetaMode>(
  univ_idxs: &[u64],
  ctx: &IxonCtx<'_>,
) -> Vec<KLevel<M>> {
  univ_idxs
    .iter()
    .map(|&idx| {
      let u = &ctx.univs[idx as usize];
      convert_univ(u, ctx)
    })
    .collect()
}

// ============================================================================
// Expression conversion
// ============================================================================

/// Resolve a name from a metadata Address using the names table.
fn resolve_meta_name(addr: &Address, names: &FxHashMap<Address, Name>) -> Name {
  names.get(addr).cloned().unwrap_or_else(Name::anon)
}

// ============================================================================
// Constant conversion helpers
// ============================================================================

/// Build a KConstantVal from Ixon metadata.
fn make_cv<M: MetaMode>(
  num_levels: usize,
  typ: KExpr<M>,
  name: Name,
  level_param_names: &[Name],
) -> KConstantVal<M> {
  KConstantVal {
    num_levels,
    typ,
    name: M::mk_field(name),
    level_params: M::mk_field(level_param_names.to_vec()),
  }
}

/// Resolve level param names from ConstantMeta.lvls addresses.
fn resolve_level_params(
  lvl_addrs: &[Address],
  names: &FxHashMap<Address, Name>,
) -> Vec<Name> {
  lvl_addrs
    .iter()
    .map(|addr| resolve_meta_name(addr, names))
    .collect()
}

/// Resolve a ConstantMeta `all` field (Vec<Address>) to Vec<MetaId<M>>.
fn resolve_all<M: MetaMode>(
  all_addrs: &[Address],
  names: &FxHashMap<Address, Name>,
  name_to_addr: &FxHashMap<Name, Address>,
) -> Vec<MetaId<M>> {
  all_addrs
    .iter()
    .map(|name_addr| {
      let name = resolve_meta_name(name_addr, names);
      let addr = name_to_addr
        .get(&name)
        .cloned()
        .unwrap_or_else(|| Address::from_blake3_hash(*name.get_hash()));
      MetaId::new(addr, M::mk_field(name))
    })
    .collect()
}

/// Pre-computed canonical block membership: block_addr → Vec<(proj_addr, name)>.
/// Built once in O(n), then looked up in O(1) per constant.
type CanonicalBlockMap = FxHashMap<Address, Vec<(Address, Name)>>;

/// Build the canonical block map by scanning all named constants once.
fn build_canonical_block_map(stt: &CompileState) -> CanonicalBlockMap {
  let mut map: CanonicalBlockMap = FxHashMap::default();
  for entry in stt.env.named.iter() {
    let member_name = entry.key().clone();
    let member_addr = entry.value().addr.clone();
    if let Some(member_const) = stt.env.get_const(&member_addr) {
      let block_addr = match &member_const.info {
        IxonConstantInfo::IPrj(p) => Some(p.block.clone()),
        IxonConstantInfo::DPrj(p) => Some(p.block.clone()),
        IxonConstantInfo::RPrj(p) => Some(p.block.clone()),
        IxonConstantInfo::CPrj(p) => Some(p.block.clone()),
        _ => None,
      };
      if let Some(ba) = block_addr {
        map.entry(ba).or_default().push((member_addr, member_name));
      }
    }
  }
  map
}

/// Look up canonical_block for a constant from the pre-computed map.
fn get_canonical_block<M: MetaMode>(
  self_addr: &Address,
  self_name: &Name,
  constant: &IxonConstantInfo,
  block_map: &CanonicalBlockMap,
) -> Vec<MetaId<M>> {
  let block_addr = match constant {
    IxonConstantInfo::IPrj(p) => Some(&p.block),
    IxonConstantInfo::DPrj(p) => Some(&p.block),
    IxonConstantInfo::RPrj(p) => Some(&p.block),
    IxonConstantInfo::CPrj(p) => Some(&p.block),
    _ => None,
  };

  match block_addr.and_then(|ba| block_map.get(ba)) {
    Some(members) => members
      .iter()
      .map(|(addr, name)| MetaId::new(addr.clone(), M::mk_field(name.clone())))
      .collect(),
    None => vec![MetaId::new(
      self_addr.clone(),
      M::mk_field(self_name.clone()),
    )],
  }
}

/// Build `induct_block` for a recursor: the set of inductives in the
/// mutual block associated with this recursor's major inductive.
fn build_induct_block<M: MetaMode>(
  rec_all_addrs: &[Address],
  names: &FxHashMap<Address, Name>,
  name_to_addr: &FxHashMap<Name, Address>,
) -> Vec<MetaId<M>> {
  resolve_all(rec_all_addrs, names, name_to_addr)
}

// ============================================================================
// Per-constant conversion
// ============================================================================

/// Context for looking up blobs (strings, nats) from the IxonEnv.
struct BlobCtx<'a> {
  env: &'a crate::ix::ixon::env::Env,
}

/// Convert an Ixon expression with blob lookups for Str/Nat literals.
fn convert_expr_with_blobs<M: MetaMode>(
  expr: &Arc<Expr>,
  arena_idx: u64,
  ctx: &IxonCtx<'_>,
  blobs: &BlobCtx<'_>,
  cache: &mut ExprConvertCache<M>,
) -> Result<KExpr<M>, String> {
  // Follow mdata chain in arena, collecting layers
  let mut current_idx = arena_idx;
  let mut mdata_layers: Vec<KMData> = Vec::new();
  loop {
    match ctx.arena.nodes.get(current_idx as usize) {
      Some(ExprMetaData::Mdata { mdata, child }) => {
        for kvm in mdata {
          let resolved: KMData = kvm
            .iter()
            .filter_map(|(addr, dv)| {
              let name = resolve_meta_name(addr, ctx.names);
              resolve_ixon_data_value(dv, blobs).map(|v| (name, v))
            })
            .collect();
          mdata_layers.push(resolved);
        }
        current_idx = *child;
      }
      _ => break,
    }
  }

  // Transparently expand Share, passing the SAME arena_idx through (same as decompiler)
  if let Expr::Share(share_idx) = expr.as_ref() {
    let shared = ctx
      .sharing
      .get(*share_idx as usize)
      .ok_or_else(|| format!("invalid Share index {share_idx}"))?;
    return convert_expr_with_blobs(shared, arena_idx, ctx, blobs, cache);
  }

  // Handle bvars early (no cache needed, but DO apply mdata)
  if let Expr::Var(idx) = expr.as_ref() {
    let bv = KExpr::bvar(*idx as usize, M::Field::<Name>::default());
    if mdata_layers.is_empty() {
      return Ok(bv);
    } else {
      return Ok(bv.add_mdata(mdata_layers));
    }
  }

  // Check cache (keyed on expr pointer + ORIGINAL arena index, same as decompiler).
  // Cache stores the mdata-wrapped result.
  let cache_key = (Arc::as_ptr(expr) as usize, arena_idx);
  if let Some(cached) = cache.get(&cache_key) {
    return Ok(cached.clone());
  }

  let node = ctx
    .arena
    .nodes
    .get(current_idx as usize)
    .unwrap_or(&ExprMetaData::Leaf);

  let result = match expr.as_ref() {
    Expr::Sort(idx) => {
      let u = ctx
        .univs
        .get(*idx as usize)
        .ok_or_else(|| format!("invalid Sort univ index {idx}"))?;
      Ok::<KExpr<M>, String>(KExpr::sort(convert_univ(u, ctx)))
    }

    Expr::Var(idx) => {
      // For Var, the binder name comes from the enclosing Lam/All/Let,
      // not from the Var node itself. Use a default name.
      Ok(KExpr::bvar(*idx as usize, M::Field::<Name>::default()))
    }

    Expr::Ref(ref_idx, univ_idxs) => {
      let addr = ctx
        .refs
        .get(*ref_idx as usize)
        .ok_or_else(|| format!("invalid Ref index {ref_idx}"))?
        .clone();
      let name = match node {
        ExprMetaData::Ref { name: name_addr } => {
          resolve_meta_name(name_addr, ctx.names)
        }
        _ => Name::anon(),
      };
      let levels = convert_univ_args(univ_idxs, ctx);
      Ok(KExpr::cnst(MetaId::new(addr, M::mk_field(name)), levels))
    }

    Expr::Rec(rec_idx, univ_idxs) => {
      let addr = ctx
        .recur_addrs
        .get(*rec_idx as usize)
        .ok_or_else(|| format!("invalid Rec index {rec_idx}"))?
        .clone();
      let name = match node {
        ExprMetaData::Ref { name: name_addr } => {
          resolve_meta_name(name_addr, ctx.names)
        }
        _ => Name::anon(),
      };
      let levels = convert_univ_args(univ_idxs, ctx);
      Ok(KExpr::cnst(MetaId::new(addr, M::mk_field(name)), levels))
    }

    Expr::App(f, a) => {
      let (f_idx, a_idx) = match node {
        ExprMetaData::App { children } => (children[0], children[1]),
        _ => (current_idx, current_idx),
      };
      let kf = convert_expr_with_blobs(f, f_idx, ctx, blobs, cache)?;
      let ka = convert_expr_with_blobs(a, a_idx, ctx, blobs, cache)?;
      Ok(KExpr::app(kf, ka))
    }

    Expr::Lam(ty, body) => {
      let (name, bi, ty_idx, body_idx) = match node {
        ExprMetaData::Binder {
          name: addr,
          info,
          children,
        } => (
          resolve_meta_name(addr, ctx.names),
          info.clone(),
          children[0],
          children[1],
        ),
        _ => (Name::anon(), BinderInfo::Default, current_idx, current_idx),
      };
      let kty = convert_expr_with_blobs(ty, ty_idx, ctx, blobs, cache)?;
      let kbody = convert_expr_with_blobs(body, body_idx, ctx, blobs, cache)?;
      Ok(KExpr::lam(kty, kbody, M::mk_field(name), M::mk_field(bi)))
    }

    Expr::All(ty, body) => {
      let (name, bi, ty_idx, body_idx) = match node {
        ExprMetaData::Binder {
          name: addr,
          info,
          children,
        } => (
          resolve_meta_name(addr, ctx.names),
          info.clone(),
          children[0],
          children[1],
        ),
        _ => (Name::anon(), BinderInfo::Default, current_idx, current_idx),
      };
      let kty = convert_expr_with_blobs(ty, ty_idx, ctx, blobs, cache)?;
      let kbody = convert_expr_with_blobs(body, body_idx, ctx, blobs, cache)?;
      Ok(KExpr::forall_e(
        kty,
        kbody,
        M::mk_field(name),
        M::mk_field(bi),
      ))
    }

    Expr::Let(nd, ty, val, body) => {
      let (name, ty_idx, val_idx, body_idx) = match node {
        ExprMetaData::LetBinder { name: addr, children } => (
          resolve_meta_name(addr, ctx.names),
          children[0],
          children[1],
          children[2],
        ),
        _ => (
          Name::anon(),
          current_idx,
          current_idx,
          current_idx,
        ),
      };
      let kty = convert_expr_with_blobs(ty, ty_idx, ctx, blobs, cache)?;
      let kval = convert_expr_with_blobs(val, val_idx, ctx, blobs, cache)?;
      let kbody = convert_expr_with_blobs(body, body_idx, ctx, blobs, cache)?;
      Ok(KExpr::let_e_nd(kty, kval, kbody, M::mk_field(name), *nd))
    }

    Expr::Prj(type_ref_idx, field_idx, s) => {
      let type_addr = ctx
        .refs
        .get(*type_ref_idx as usize)
        .ok_or_else(|| format!("invalid Prj type ref index {type_ref_idx}"))?
        .clone();
      let (struct_name, child_idx) = match node {
        ExprMetaData::Prj {
          struct_name: addr,
          child,
        } => (resolve_meta_name(addr, ctx.names), *child),
        _ => (Name::anon(), current_idx),
      };
      let ks = convert_expr_with_blobs(s, child_idx, ctx, blobs, cache)?;
      Ok(KExpr::proj(
        MetaId::new(type_addr, M::mk_field(struct_name)),
        *field_idx as usize,
        ks,
      ))
    }

    Expr::Str(ref_idx) => {
      let addr = ctx
        .refs
        .get(*ref_idx as usize)
        .ok_or_else(|| format!("invalid Str ref index {ref_idx}"))?;
      let s = blobs
        .env
        .get_blob(addr)
        .and_then(|bytes| String::from_utf8(bytes).ok())
        .unwrap_or_default();
      Ok(KExpr::lit(Literal::StrVal(s)))
    }

    Expr::Nat(ref_idx) => {
      let addr = ctx
        .refs
        .get(*ref_idx as usize)
        .ok_or_else(|| format!("invalid Nat ref index {ref_idx}"))?;
      let n = blobs
        .env
        .get_blob(addr)
        .map(|bytes| Nat::from_le_bytes(&bytes))
        .unwrap_or_else(|| Nat::from(0u64));
      Ok(KExpr::lit(Literal::NatVal(n)))
    }

    Expr::Share(_) => unreachable!("Share handled above"),
  }?;

  // Attach mdata layers if any were collected
  let result = if mdata_layers.is_empty() {
    result
  } else {
    result.add_mdata(mdata_layers)
  };

  // Cache the mdata-wrapped result (same as decompiler)
  cache.insert(cache_key, result.clone());
  Ok(result)
}

// ============================================================================
// Top-level conversion: Ixon CompileState → KEnv
// ============================================================================

/// Convert an Ixon `CompileState` to a kernel `(KEnv, Primitives, quot_init)`.
///
/// This is the canonical conversion path that populates `canonical_block`
/// from the Ixon mutual block structure (SCC + partition refinement).
pub fn ixon_to_kenv<M: MetaMode>(
  stt: &CompileState,
) -> Result<(KEnv<M>, Primitives<M>, bool), String> {
  // Build names lookup: Address → Name
  let mut names: FxHashMap<Address, Name> = FxHashMap::default();
  for entry in stt.env.names.iter() {
    names.insert(entry.key().clone(), entry.value().clone());
  }

  // Build name_to_addr: Name → Address (from CompileState)
  let mut name_to_addr: FxHashMap<Name, Address> = FxHashMap::default();
  for entry in stt.name_to_addr.iter() {
    name_to_addr.insert(entry.key().clone(), entry.value().clone());
  }

  // Pre-compute canonical block membership (O(n) instead of O(n²))
  let block_map = build_canonical_block_map(stt);

  let blobs = BlobCtx { env: &stt.env };
  let quot_init_flag = AtomicBool::new(false);

  // Collect named entries for parallel processing
  let named_entries: Vec<_> = stt.env.named.iter()
    .map(|entry| (entry.key().clone(), entry.value().clone()))
    .collect();

  // Parallel conversion
  let results: Result<Vec<Vec<(MetaId<M>, KConstantInfo<M>)>>, String> = named_entries
    .into_par_iter()
    .map(|(const_name, named)| {
      let const_addr = &named.addr;
      let constant = stt
        .env
        .get_const(const_addr)
        .ok_or_else(|| {
          format!(
            "missing constant at {} for {}",
            const_addr.hex(),
            const_name.pretty()
          )
        })?;

      let mut qi = false;
      let entries = convert_named_constant(
        &const_name,
        const_addr,
        &constant,
        &named.meta,
        &names,
        &name_to_addr,
        &blobs,
        stt,
        &mut qi,
        &block_map,
      )
      .map_err(|e| format!("{}: {e}", const_name.pretty()))?;

      if qi {
        quot_init_flag.store(true, Ordering::Relaxed);
      }
      Ok(entries)
    })
    .collect();

  let mut kenv: KEnv<M> = KEnv::default();
  for entries in results? {
    for (id, kci) in entries {
      kenv.insert(id, kci);
    }
  }
  let quot_init = quot_init_flag.load(Ordering::Relaxed);

  // Build primitives from KEnv
  let prims = build_primitives_from_kenv(&kenv);

  Ok((kenv, prims, quot_init))
}

/// Convert a single named Ixon constant to kernel entries.
///
/// Returns empty vec for CPrj (constructors emitted by IPrj) and Muts blocks.
/// Extract ctx addresses from ConstantMeta (mirrors decompile.rs get_ctx_from_meta).
fn get_ctx_from_meta(meta: &ConstantMeta) -> &[Address] {
  match meta {
    ConstantMeta::Def { ctx, .. } => ctx,
    ConstantMeta::Indc { ctx, .. } => ctx,
    ConstantMeta::Rec { ctx, .. } => ctx,
    _ => &[],
  }
}

/// Build recurAddrs from a constant's metadata ctx field.
/// Resolves name-hash addresses → names → projection addresses.
fn build_recur_addrs_from_meta(
  meta: &ConstantMeta,
  names: &FxHashMap<Address, Name>,
  name_to_addr: &FxHashMap<Name, Address>,
) -> Vec<Address> {
  resolve_recur_addrs(get_ctx_from_meta(meta), names, name_to_addr)
}

#[allow(clippy::too_many_arguments)]
fn convert_named_constant<M: MetaMode>(
  name: &Name,
  addr: &Address,
  constant: &Constant,
  meta: &ConstantMeta,
  names: &FxHashMap<Address, Name>,
  name_to_addr: &FxHashMap<Name, Address>,
  blobs: &BlobCtx<'_>,
  stt: &CompileState,
  quot_init: &mut bool,
  block_map: &CanonicalBlockMap,
) -> Result<Vec<(MetaId<M>, KConstantInfo<M>)>, String> {
  let self_id: MetaId<M> = MetaId::new(addr.clone(), M::mk_field(name.clone()));

  match &constant.info {
    // ----------------------------------------------------------------
    // Simple (non-mutual) constants
    // ----------------------------------------------------------------
    IxonConstantInfo::Defn(def) => {
      let mut expr_cache: ExprConvertCache<M> = FxHashMap::default();
      let (level_params, arena, type_root, value_root, hints, safety, all_addrs, ctx_addrs) =
        match meta {
          ConstantMeta::Def {
            lvls,
            arena,
            type_root,
            value_root,
            hints,
            all,
            ctx,
            ..
          } => (
            resolve_level_params(lvls, names),
            arena,
            *type_root,
            *value_root,
            *hints,
            def.safety,
            all.clone(),
            ctx.clone(),
          ),
          _ => {
            // Fallback: no metadata
            let arena = &DEFAULT_ARENA;
            (
              vec![],
              arena,
              0,
              0,
              match def.kind {
                DefKind::Opaque => ReducibilityHints::Opaque,
                _ => ReducibilityHints::Regular(0),
              },
              def.safety,
              vec![],
              vec![],
            )
          }
        };

      let recur_addrs = resolve_recur_addrs(&ctx_addrs, names, name_to_addr);

      let ctx_obj = IxonCtx {
        sharing: &constant.sharing,
        refs: &constant.refs,
        univs: &constant.univs,
        recur_addrs,
        arena,
        names,
        level_param_names: level_params.clone(),
      };

      let typ = convert_expr_with_blobs(&def.typ, type_root, &ctx_obj, blobs, &mut expr_cache)?;
      let value = convert_expr_with_blobs(&def.value, value_root, &ctx_obj, blobs, &mut expr_cache)?;

      let lean_all = resolve_all(&all_addrs, names, name_to_addr);
      let canonical_block = get_canonical_block(addr, name, &constant.info, block_map);

      let cv = make_cv(def.lvls as usize, typ, name.clone(), &level_params);

      match def.kind {
        DefKind::Definition => Ok(vec![(self_id.clone(), KConstantInfo::Definition(KDefinitionVal {
          cv,
          value,
          hints,
          safety,
          lean_all: M::mk_field(lean_all),
          canonical_block,
        }))]),
        DefKind::Theorem => Ok(vec![(self_id.clone(), KConstantInfo::Theorem(KTheoremVal {
          cv,
          value,
          lean_all: M::mk_field(lean_all),
          canonical_block,
        }))]),
        DefKind::Opaque => Ok(vec![(self_id.clone(), KConstantInfo::Opaque(KOpaqueVal {
          cv,
          value,
          is_unsafe: safety == DefinitionSafety::Unsafe,
          lean_all: M::mk_field(lean_all),
          canonical_block,
        }))]),
      }
    }

    IxonConstantInfo::Axio(ax) => {
      let mut expr_cache: ExprConvertCache<M> = FxHashMap::default();
      let (level_params, arena, type_root) = match meta {
        ConstantMeta::Axio {
          lvls,
          arena,
          type_root,
          ..
        } => (resolve_level_params(lvls, names), arena, *type_root),
        _ => (vec![], &DEFAULT_ARENA, 0),
      };

      let ctx_obj = IxonCtx {
        sharing: &constant.sharing,
        refs: &constant.refs,
        univs: &constant.univs,
        recur_addrs: vec![],
        arena,
        names,
        level_param_names: level_params.clone(),
      };

      let typ = convert_expr_with_blobs(&ax.typ, type_root, &ctx_obj, blobs, &mut expr_cache)?;
      let cv = make_cv(ax.lvls as usize, typ, name.clone(), &level_params);

      Ok(vec![(self_id.clone(), KConstantInfo::Axiom(KAxiomVal {
        cv,
        is_unsafe: ax.is_unsafe,
      }))])
    }

    IxonConstantInfo::Quot(q) => {
      let mut expr_cache: ExprConvertCache<M> = FxHashMap::default();
      *quot_init = true;
      let (level_params, arena, type_root) = match meta {
        ConstantMeta::Quot {
          lvls,
          arena,
          type_root,
          ..
        } => (resolve_level_params(lvls, names), arena, *type_root),
        _ => (vec![], &DEFAULT_ARENA, 0),
      };

      let ctx_obj = IxonCtx {
        sharing: &constant.sharing,
        refs: &constant.refs,
        univs: &constant.univs,
        recur_addrs: vec![],
        arena,
        names,
        level_param_names: level_params.clone(),
      };

      let typ = convert_expr_with_blobs(&q.typ, type_root, &ctx_obj, blobs, &mut expr_cache)?;
      let cv = make_cv(q.lvls as usize, typ, name.clone(), &level_params);

      Ok(vec![(self_id.clone(), KConstantInfo::Quotient(KQuotVal {
        cv,
        kind: q.kind,
      }))])
    }

    IxonConstantInfo::Recr(rec) => {
      let mut expr_cache: ExprConvertCache<M> = FxHashMap::default();
      let (level_params, arena, type_root, rule_roots, all_addrs, ctx_addrs, rule_ctor_addrs) =
        match meta {
          ConstantMeta::Rec {
            lvls,
            arena,
            type_root,
            rule_roots,
            all,
            ctx,
            rules,
            ..
          } => (
            resolve_level_params(lvls, names),
            arena,
            *type_root,
            rule_roots.clone(),
            all.clone(),
            ctx.clone(),
            rules.clone(),
          ),
          _ => (vec![], &DEFAULT_ARENA, 0, vec![], vec![], vec![], vec![]),
        };

      let recur_addrs = resolve_recur_addrs(&ctx_addrs, names, name_to_addr);

      let ctx_obj = IxonCtx {
        sharing: &constant.sharing,
        refs: &constant.refs,
        univs: &constant.univs,
        recur_addrs,
        arena,
        names,
        level_param_names: level_params.clone(),
      };

      let typ = convert_expr_with_blobs(&rec.typ, type_root, &ctx_obj, blobs, &mut expr_cache)?;

      // Convert rules
      let rules: Result<Vec<KRecursorRule<M>>, String> = rec
        .rules
        .iter()
        .enumerate()
        .map(|(i, rule)| {
          let rhs_root = rule_roots.get(i).copied().unwrap_or(0);
          let rhs = convert_expr_with_blobs(&rule.rhs, rhs_root, &ctx_obj, blobs, &mut expr_cache)?;
          let ctor_id = if let Some(ctor_name_addr) = rule_ctor_addrs.get(i) {
            let ctor_name = resolve_meta_name(ctor_name_addr, names);
            let ctor_addr = name_to_addr
              .get(&ctor_name)
              .cloned()
              .unwrap_or_else(|| Address::from_blake3_hash(*ctor_name.get_hash()));
            MetaId::new(ctor_addr, M::mk_field(ctor_name))
          } else {
            MetaId::from_addr(Address::hash(b"unknown_ctor"))
          };
          Ok(KRecursorRule {
            ctor: ctor_id,
            nfields: rule.fields as usize,
            rhs,
          })
        })
        .collect();

      let lean_all: Vec<MetaId<M>> = resolve_all(&all_addrs, names, name_to_addr);
      let canonical_block = get_canonical_block(addr, name, &constant.info, block_map);
      let induct_block = build_induct_block(&all_addrs, names, name_to_addr);

      let cv = make_cv(rec.lvls as usize, typ, name.clone(), &level_params);

      Ok(vec![(self_id.clone(), KConstantInfo::Recursor(KRecursorVal {
        cv,
        lean_all: M::mk_field(lean_all),
        canonical_block,
        induct_block,
        num_params: rec.params as usize,
        num_indices: rec.indices as usize,
        num_motives: rec.motives as usize,
        num_minors: rec.minors as usize,
        rules: rules?,
        k: rec.k,
        is_unsafe: rec.is_unsafe,
      }))])
    }

    // ----------------------------------------------------------------
    // Projection constants (mutual block members)
    // Uses ctx from metadata for recurAddrs (same as decompiler).
    // CPrj is skipped — constructors are emitted when their parent
    // IPrj is processed (same as decompiler pattern).
    // ----------------------------------------------------------------
    IxonConstantInfo::IPrj(proj) => {
      let mut expr_cache: ExprConvertCache<M> = FxHashMap::default();
      let block = load_block(stt, &proj.block)?;
      let members = get_muts(&block, &proj.block)?;
      let member = members
        .get(proj.idx as usize)
        .ok_or_else(|| format!("IPrj index {} out of bounds", proj.idx))?;
      let ind = match member {
        IxonMutConst::Indc(ind) => ind,
        _ => return Err(format!("IPrj at index {} is not Indc", proj.idx)),
      };

      let recur_addrs = build_recur_addrs_from_meta(meta, names, name_to_addr);
      let canonical_block = get_canonical_block(addr, name, &constant.info, block_map);

      let (level_params, arena, type_root, all_addrs, ctor_addrs) =
        match meta {
          ConstantMeta::Indc { lvls, arena, type_root, all, ctors, .. } => (
            resolve_level_params(lvls, names),
            arena,
            *type_root,
            all.clone(),
            ctors.clone(),
          ),
          _ => (vec![], &DEFAULT_ARENA, 0, vec![], vec![]),
        };

      let ixon_ctx = IxonCtx {
        sharing: &block.sharing,
        refs: &block.refs,
        univs: &block.univs,
        recur_addrs,
        arena,
        names,
        level_param_names: level_params.clone(),
      };

      let typ = convert_expr_with_blobs(&ind.typ, type_root, &ixon_ctx, blobs, &mut expr_cache)?;
      let cv = make_cv(ind.lvls as usize, typ, name.clone(), &level_params);
      let lean_all = resolve_all(&all_addrs, names, name_to_addr);
      let ctors_ids: Vec<MetaId<M>> = ctor_addrs
        .iter()
        .map(|a| {
          let n = resolve_meta_name(a, names);
          let ca = name_to_addr.get(&n).cloned()
            .unwrap_or_else(|| Address::from_blake3_hash(*n.get_hash()));
          MetaId::new(ca, M::mk_field(n))
        })
        .collect();

      let mut results = vec![(self_id.clone(), KConstantInfo::Inductive(KInductiveVal {
        cv,
        num_params: ind.params as usize,
        num_indices: ind.indices as usize,
        lean_all: M::mk_field(lean_all),
        canonical_block: canonical_block.clone(),
        ctors: ctors_ids.clone(),
        num_nested: ind.nested as usize,
        is_rec: ind.recr,
        is_unsafe: ind.is_unsafe,
        is_reflexive: ind.refl,
      }))];

      // Also emit constructors (same as decompiler's IPrj handling)
      for (cidx, ctor) in ind.ctors.iter().enumerate() {
        // Clear expr cache: each constructor has its own arena, so cached
        // entries from the inductive (or a previous ctor) would be stale.
        expr_cache.clear();
        let ctor_id = ctors_ids.get(cidx).cloned()
          .unwrap_or_else(|| MetaId::from_addr(Address::hash(b"unknown_ctor")));

        // Constructor metadata
        let ctor_meta_name = ctor_id.name.clone();
        let ctor_name = M::field_ref(&ctor_meta_name)
          .cloned()
          .unwrap_or_else(Name::anon);
        let ctor_named = stt.env.lookup_name(&ctor_name);
        let ctor_meta = ctor_named.as_ref().map(|n| &n.meta);

        let (ctor_lvl_params, ctor_arena, ctor_type_root) = match ctor_meta {
          Some(ConstantMeta::Ctor { lvls, arena, type_root, .. }) => (
            resolve_level_params(lvls, names),
            arena,
            *type_root,
          ),
          _ => (level_params.clone(), &DEFAULT_ARENA, 0),
        };

        let ctor_ixon_ctx = IxonCtx {
          sharing: &block.sharing,
          refs: &block.refs,
          univs: &block.univs,
          recur_addrs: ixon_ctx.recur_addrs.clone(),
          arena: ctor_arena,
          names,
          level_param_names: ctor_lvl_params.clone(),
        };

        let ctor_typ = convert_expr_with_blobs(&ctor.typ, ctor_type_root, &ctor_ixon_ctx, blobs, &mut expr_cache)?;
        let ctor_cv = make_cv(ctor.lvls as usize, ctor_typ, ctor_name, &ctor_lvl_params);

        results.push((ctor_id, KConstantInfo::Constructor(KConstructorVal {
          cv: ctor_cv,
          induct: self_id.clone(),
          cidx: ctor.cidx as usize,
          num_params: ctor.params as usize,
          num_fields: ctor.fields as usize,
          is_unsafe: ctor.is_unsafe,
        })));
      }

      Ok(results)
    }

    // Constructors handled by IPrj above
    IxonConstantInfo::CPrj(_) => Ok(vec![]),

    IxonConstantInfo::RPrj(proj) => {
      let mut expr_cache: ExprConvertCache<M> = FxHashMap::default();
      let block = load_block(stt, &proj.block)?;
      let members = get_muts(&block, &proj.block)?;
      let member = members
        .get(proj.idx as usize)
        .ok_or_else(|| format!("RPrj index {} out of bounds", proj.idx))?;
      let rec = match member {
        IxonMutConst::Recr(r) => r,
        _ => return Err(format!("RPrj at index {} is not Recr", proj.idx)),
      };

      let recur_addrs = build_recur_addrs_from_meta(meta, names, name_to_addr);
      let canonical_block = get_canonical_block(addr, name, &constant.info, block_map);

      let (level_params, arena, type_root, rule_roots, all_addrs, rule_ctor_addrs) =
        match meta {
          ConstantMeta::Rec { lvls, arena, type_root, rule_roots, all, rules, .. } => (
            resolve_level_params(lvls, names),
            arena, *type_root, rule_roots.clone(), all.clone(), rules.clone(),
          ),
          _ => (vec![], &DEFAULT_ARENA, 0, vec![], vec![], vec![]),
        };

      let ixon_ctx = IxonCtx {
        sharing: &block.sharing,
        refs: &block.refs,
        univs: &block.univs,
        recur_addrs,
        arena,
        names,
        level_param_names: level_params.clone(),
      };

      let typ = convert_expr_with_blobs(&rec.typ, type_root, &ixon_ctx, blobs, &mut expr_cache)?;
      let rules: Result<Vec<KRecursorRule<M>>, String> = rec.rules.iter().enumerate()
        .map(|(i, rule)| {
          let rhs_root = rule_roots.get(i).copied().unwrap_or(0);
          let rhs = convert_expr_with_blobs(&rule.rhs, rhs_root, &ixon_ctx, blobs, &mut expr_cache)?;
          let ctor_id = if let Some(a) = rule_ctor_addrs.get(i) {
            let n = resolve_meta_name(a, names);
            let ca = name_to_addr.get(&n).cloned()
              .unwrap_or_else(|| Address::from_blake3_hash(*n.get_hash()));
            MetaId::new(ca, M::mk_field(n))
          } else {
            MetaId::from_addr(Address::hash(b"unknown_ctor"))
          };
          Ok(KRecursorRule { ctor: ctor_id, nfields: rule.fields as usize, rhs })
        })
        .collect();

      let lean_all = resolve_all(&all_addrs, names, name_to_addr);
      let induct_block = build_induct_block(&all_addrs, names, name_to_addr);
      let cv = make_cv(rec.lvls as usize, typ, name.clone(), &level_params);

      Ok(vec![(self_id.clone(), KConstantInfo::Recursor(KRecursorVal {
        cv,
        lean_all: M::mk_field(lean_all),
        canonical_block,
        induct_block,
        num_params: rec.params as usize,
        num_indices: rec.indices as usize,
        num_motives: rec.motives as usize,
        num_minors: rec.minors as usize,
        rules: rules?,
        k: rec.k,
        is_unsafe: rec.is_unsafe,
      }))])
    }

    IxonConstantInfo::DPrj(proj) => {
      let mut expr_cache: ExprConvertCache<M> = FxHashMap::default();
      let block = load_block(stt, &proj.block)?;
      let members = get_muts(&block, &proj.block)?;
      let member = members
        .get(proj.idx as usize)
        .ok_or_else(|| format!("DPrj index {} out of bounds", proj.idx))?;
      let def = match member {
        IxonMutConst::Defn(d) => d,
        _ => return Err(format!("DPrj at index {} is not Defn", proj.idx)),
      };

      let recur_addrs = build_recur_addrs_from_meta(meta, names, name_to_addr);
      let canonical_block = get_canonical_block(addr, name, &constant.info, block_map);

      let (level_params, arena, type_root, value_root, hints, all_addrs) =
        match meta {
          ConstantMeta::Def { lvls, arena, type_root, value_root, hints, all, .. } => (
            resolve_level_params(lvls, names),
            arena, *type_root, *value_root, *hints, all.clone(),
          ),
          _ => (vec![], &DEFAULT_ARENA, 0, 0, ReducibilityHints::Regular(0), vec![]),
        };

      let ixon_ctx = IxonCtx {
        sharing: &block.sharing,
        refs: &block.refs,
        univs: &block.univs,
        recur_addrs,
        arena,
        names,
        level_param_names: level_params.clone(),
      };

      let typ = convert_expr_with_blobs(&def.typ, type_root, &ixon_ctx, blobs, &mut expr_cache)?;
      let value = convert_expr_with_blobs(&def.value, value_root, &ixon_ctx, blobs, &mut expr_cache)?;
      let lean_all = resolve_all(&all_addrs, names, name_to_addr);
      let cv = make_cv(def.lvls as usize, typ, name.clone(), &level_params);

      let kci = match def.kind {
        DefKind::Definition => KConstantInfo::Definition(KDefinitionVal {
          cv, value, hints, safety: def.safety,
          lean_all: M::mk_field(lean_all), canonical_block,
        }),
        DefKind::Theorem => KConstantInfo::Theorem(KTheoremVal {
          cv, value,
          lean_all: M::mk_field(lean_all), canonical_block,
        }),
        DefKind::Opaque => KConstantInfo::Opaque(KOpaqueVal {
          cv, value, is_unsafe: def.safety == DefinitionSafety::Unsafe,
          lean_all: M::mk_field(lean_all), canonical_block,
        }),
      };
      Ok(vec![(self_id.clone(), kci)])
    }

    IxonConstantInfo::Muts(_) => Ok(vec![]),
  }
}

/// Load a Muts block constant from the Ixon env.
fn load_block(stt: &CompileState, block_addr: &Address) -> Result<Constant, String> {
  stt.env.get_const(block_addr)
    .ok_or_else(|| format!("missing Muts block {}", block_addr.hex()))
}

/// Extract the MutConst members from a block constant.
fn get_muts<'a>(block: &'a Constant, block_addr: &Address) -> Result<&'a [IxonMutConst], String> {
  match &block.info {
    IxonConstantInfo::Muts(m) => Ok(m),
    _ => Err(format!("block at {} is not Muts", block_addr.hex())),
  }
}

// ============================================================================
// Helpers
// ============================================================================

/// Resolve mutual context addresses to actual constant addresses.
fn resolve_recur_addrs(
  ctx_addrs: &[Address],
  names: &FxHashMap<Address, Name>,
  name_to_addr: &FxHashMap<Name, Address>,
) -> Vec<Address> {
  ctx_addrs
    .iter()
    .map(|name_addr| {
      let name = resolve_meta_name(name_addr, names);
      name_to_addr
        .get(&name)
        .cloned()
        .unwrap_or_else(|| Address::from_blake3_hash(*name.get_hash()))
    })
    .collect()
}

/// Resolve an Ixon DataValue (Address-based) to an env DataValue (value-based).
fn resolve_ixon_data_value(
  dv: &IxonDataValue,
  blobs: &BlobCtx<'_>,
) -> Option<DataValue> {
  use crate::ix::env::Int;
  match dv {
    IxonDataValue::OfString(addr) => {
      let bytes = blobs.env.get_blob(addr)?;
      Some(DataValue::OfString(String::from_utf8(bytes).ok()?))
    }
    IxonDataValue::OfBool(b) => Some(DataValue::OfBool(*b)),
    IxonDataValue::OfName(addr) => {
      Some(DataValue::OfName(blobs.env.get_name(addr)?))
    }
    IxonDataValue::OfNat(addr) => {
      let bytes = blobs.env.get_blob(addr)?;
      Some(DataValue::OfNat(Nat::from_le_bytes(&bytes)))
    }
    IxonDataValue::OfInt(addr) => {
      let bytes = blobs.env.get_blob(addr)?;
      if bytes.is_empty() { return None; }
      match bytes[0] {
        0 => Some(DataValue::OfInt(Int::OfNat(Nat::from_le_bytes(&bytes[1..])))),
        1 => Some(DataValue::OfInt(Int::NegSucc(Nat::from_le_bytes(&bytes[1..])))),
        _ => None,
      }
    }
    IxonDataValue::OfSyntax(addr) => {
      let bytes = blobs.env.get_blob(addr)?;
      let mut buf = bytes.as_slice();
      let syn = deser_syntax(&mut buf, blobs)?;
      Some(DataValue::OfSyntax(Box::new(syn)))
    }
  }
}

// ---------------------------------------------------------------------------
// Syntax deserialization helpers
// ---------------------------------------------------------------------------

fn deser_tag0(buf: &mut &[u8]) -> Option<u64> {
  use crate::ix::ixon::tag::Tag0;
  Tag0::get(buf).ok().map(|t| t.size)
}

fn deser_addr(buf: &mut &[u8]) -> Option<Address> {
  if buf.len() < 32 { return None; }
  let (bytes, rest) = buf.split_at(32);
  *buf = rest;
  Address::from_slice(bytes).ok()
}

fn deser_string(addr: &Address, blobs: &BlobCtx<'_>) -> Option<String> {
  let bytes = blobs.env.get_blob(addr)?;
  String::from_utf8(bytes).ok()
}

fn deser_name(addr: &Address, blobs: &BlobCtx<'_>) -> Option<Name> {
  blobs.env.get_name(addr)
}

fn deser_substring(buf: &mut &[u8], blobs: &BlobCtx<'_>) -> Option<crate::ix::env::Substring> {
  let str_addr = deser_addr(buf)?;
  let s = deser_string(&str_addr, blobs)?;
  let start_pos = Nat::from(deser_tag0(buf)?);
  let stop_pos = Nat::from(deser_tag0(buf)?);
  Some(crate::ix::env::Substring { str: s, start_pos, stop_pos })
}

fn deser_source_info(buf: &mut &[u8], blobs: &BlobCtx<'_>) -> Option<crate::ix::env::SourceInfo> {
  use crate::ix::env::SourceInfo;
  if buf.is_empty() { return None; }
  let tag = buf[0];
  *buf = &buf[1..];
  match tag {
    0 => {
      let leading = deser_substring(buf, blobs)?;
      let leading_pos = Nat::from(deser_tag0(buf)?);
      let trailing = deser_substring(buf, blobs)?;
      let trailing_pos = Nat::from(deser_tag0(buf)?);
      Some(SourceInfo::Original(leading, leading_pos, trailing, trailing_pos))
    }
    1 => {
      let start = Nat::from(deser_tag0(buf)?);
      let end = Nat::from(deser_tag0(buf)?);
      if buf.is_empty() { return None; }
      let canonical = buf[0] != 0;
      *buf = &buf[1..];
      Some(SourceInfo::Synthetic(start, end, canonical))
    }
    2 => Some(SourceInfo::None),
    _ => None,
  }
}

fn deser_preresolved(buf: &mut &[u8], blobs: &BlobCtx<'_>) -> Option<crate::ix::env::SyntaxPreresolved> {
  use crate::ix::env::SyntaxPreresolved;
  if buf.is_empty() { return None; }
  let tag = buf[0];
  *buf = &buf[1..];
  match tag {
    0 => {
      let name_addr = deser_addr(buf)?;
      let name = deser_name(&name_addr, blobs)?;
      Some(SyntaxPreresolved::Namespace(name))
    }
    1 => {
      let name_addr = deser_addr(buf)?;
      let name = deser_name(&name_addr, blobs)?;
      let count = deser_tag0(buf)? as usize;
      let mut fields = Vec::with_capacity(count);
      for _ in 0..count {
        let field_addr = deser_addr(buf)?;
        fields.push(deser_string(&field_addr, blobs)?);
      }
      Some(SyntaxPreresolved::Decl(name, fields))
    }
    _ => None,
  }
}

fn deser_syntax(buf: &mut &[u8], blobs: &BlobCtx<'_>) -> Option<crate::ix::env::Syntax> {
  use crate::ix::env::Syntax;
  if buf.is_empty() { return None; }
  let tag = buf[0];
  *buf = &buf[1..];
  match tag {
    0 => Some(Syntax::Missing),
    1 => {
      let info = deser_source_info(buf, blobs)?;
      let kind_addr = deser_addr(buf)?;
      let kind = deser_name(&kind_addr, blobs)?;
      let arg_count = deser_tag0(buf)? as usize;
      let mut args = Vec::with_capacity(arg_count);
      for _ in 0..arg_count {
        args.push(deser_syntax(buf, blobs)?);
      }
      Some(Syntax::Node(info, kind, args))
    }
    2 => {
      let info = deser_source_info(buf, blobs)?;
      let val_addr = deser_addr(buf)?;
      let val = deser_string(&val_addr, blobs)?;
      Some(Syntax::Atom(info, val))
    }
    3 => {
      let info = deser_source_info(buf, blobs)?;
      let raw_val = deser_substring(buf, blobs)?;
      let val_addr = deser_addr(buf)?;
      let val = deser_name(&val_addr, blobs)?;
      let pr_count = deser_tag0(buf)? as usize;
      let mut preresolved = Vec::with_capacity(pr_count);
      for _ in 0..pr_count {
        preresolved.push(deser_preresolved(buf, blobs)?);
      }
      Some(Syntax::Ident(info, raw_val, val, preresolved))
    }
    _ => None,
  }
}

/// Default empty arena for fallback when metadata is missing.
static DEFAULT_ARENA: ExprMeta = ExprMeta { nodes: Vec::new() };
