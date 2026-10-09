//! Compilation from Lean environment to Ixon format.
//!
//! This module compiles Lean constants to alpha-invariant Ixon representations
//! with sharing analysis for deduplication within constants

#![allow(clippy::cast_possible_truncation)]
#![allow(clippy::cast_precision_loss)]

use dashmap::{DashMap, DashSet};
use rustc_hash::{FxHashMap, FxHashSet};
use std::{cmp::Ordering, sync::Arc};

use bignat::Nat;

use ix_common::address::Address;
use ix_common::env::{
  AxiomVal, BinderInfo, ConstantInfo as LeanConstantInfo, ConstructorVal,
  DataValue as LeanDataValue, Env as LeanEnv, Expr as LeanExpr, ExprData,
  InductiveVal, Level, LevelData, Literal, Name, NameData, QuotVal,
  RecursorRule as LeanRecursorRule, ReducibilityHints,
  SourceInfo as LeanSourceInfo, Substring as LeanSubstring,
  Syntax as LeanSyntax, SyntaxPreresolved,
};
use ix_common::strong_ordering::SOrd;

use ixon::{
  CompileError, TagN,
  canon_univ::canon_univ,
  constant::{
    Axiom, Constant, ConstantInfo, Constructor, Definition, Inductive,
    MutConst as IxonMutConst, Quotient, Recursor, RecursorRule,
    ctor_proj_constant, defn_proj_constant, indc_proj_constant,
    recr_proj_constant,
  },
  env::{Env as IxonEnv, Named},
  expr::Expr,
  metadata::{
    ConstantMeta, ConstantMetaInfo, DataValue, ExprMeta, ExprMetaData, KVMap,
    UnivPatch,
  },
  sharing_exact::{
    ExactSharingLimits, ShareLayout, SharingError, canonical_sharing_tiered,
  },
  univ::Univ,
};

use crate::{
  graph::NameSet,
  mutual::{Def, Ind, MutConst, MutCtx, Rec, ctx_to_all},
};

/// Whether to output timing diagnostics for slow blocks and aux_gen phases.
/// Set via IX_TIMING=1 environment variable.
pub static IX_TIMING: std::sync::LazyLock<bool> =
  std::sync::LazyLock::new(|| std::env::var("IX_TIMING").is_ok());

/// Log every aux-name claim: alias insertions, canonical patch name
/// registrations, evaporation decisions, and call-site-plan
/// registrations — with full addresses and block context. The
/// cross-SCC ownership of `all[0].rec_N`-style names is invisible in
/// normal logs; this flag exists to attribute both claimants when a
/// name is contested (see the ownership checks in `compile/mutual.rs`
/// and `compile/aux_gen.rs`).
/// Set via IX_LOG_AUX_NAMES=1.
pub static IX_LOG_AUX_NAMES: std::sync::LazyLock<bool> =
  std::sync::LazyLock::new(|| std::env::var("IX_LOG_AUX_NAMES").is_ok());

/// Options controlling whole-environment compilation.
#[derive(Clone, Copy, Debug, Default)]
pub struct CompileOptions {
  /// Override the scheduler worker ceiling. `None` uses available parallelism
  /// or `IX_COMPILE_WORKERS`; adaptive admission may run fewer active blocks.
  pub max_workers: Option<usize>,
}

/// Worker-local kernel context for aux_gen sort-level inference.
pub struct KernelCtx {
  /// Worker-local **canonical** kernel environment. Populated incrementally by
  /// aux_gen's Phase 1+ (`compute_is_large_and_k`, `ingress_field_deps`,
  /// etc.) with aux-substituted types at `resolve_lean_name_addr`-derived
  /// addresses that may shift as alpha-collapse reassigns addresses over
  /// the course of compilation.
  pub kenv: ix_kernel::env::KEnv<ix_kernel::mode::Meta>,
  /// Ids whose `ingress_aux_gen_dep` dispatch has already run against
  /// `kenv`. The dispatch is a deterministic function of the constant's
  /// kind, so once an id is here its kenv entry is at final fidelity and
  /// the walkers skip re-expanding its whole reference closure (that
  /// re-expansion was Θ(blocks × closure) when the set lived per call).
  /// Keyed by resolved `KId` — not bare `Name` — so an address shifted
  /// by later aux registration reads as unseen and re-ingresses under
  /// the new id, exactly as the per-call sets healed it. Must be cleared
  /// together with `kenv` (the entries it vouches for die with it).
  pub aux_ingress_seen: FxHashSet<ix_kernel::id::KId<ix_kernel::mode::Meta>>,
}

impl Default for KernelCtx {
  fn default() -> Self {
    Self::new()
  }
}

impl KernelCtx {
  pub fn new() -> Self {
    KernelCtx {
      kenv: ix_kernel::env::KEnv::new(),
      aux_ingress_seen: FxHashSet::default(),
    }
  }
}

/// Compile state for building the Ixon environment.
pub struct CompileState {
  /// Ixon environment being built
  pub env: IxonEnv,
  /// Map from Lean constant name to Ixon address
  pub name_to_addr: DashMap<Name, Address>,
  /// Mutual block canonical class ordering, keyed by any inductive name in the
  /// block. Each entry is the list of equivalence classes (in `sort_consts` order),
  /// where each class is a list of names.
  pub blocks: DashMap<Name, Vec<Vec<Name>>>,
  /// Constants that couldn't be compiled (name -> error description).
  ///
  /// Populated in two phases:
  /// 1. Pre-compile grounding: `ground_consts` identifies constants unreachable
  ///    from axioms/primitives.
  /// 2. During scheduling: per-block compile failures (e.g. `compute_is_large_and_k`
  ///    rejecting an ill-formed inductive) are recorded here instead of
  ///    aborting the scheduler, so the rest of the env still compiles and
  ///    callers can report each failure per-constant.
  ///
  /// `DashMap` (rather than `FxHashMap`) because scheduler workers insert
  /// concurrently on per-block failure paths.
  pub ungrounded: DashMap<Name, String>,
  /// Persistent set of names compiled by aux_gen. Used for membership
  /// checks (e.g., "is this name aux_gen-rewritten?") throughout compilation.
  /// Never drained — callers rely on `.contains()` long after insertion.
  pub aux_gen_extra_names: DashSet<Name>,
  /// Pending aux_gen names awaiting scheduler dependency resolution.
  /// Drained after each block completion. Separated from the persistent
  /// `aux_gen_extra_names` to avoid O(N×M) re-iteration of the full set
  /// on every block completion.
  pub aux_gen_pending: std::sync::Mutex<Vec<Name>>,
  /// Fallback name->addr map for constants compiled by aux_gen or pre-compiled
  /// during a parent inductive's compilation. Visible to later compilations
  /// so expressions referencing them resolve.
  pub aux_name_to_addr: DashMap<Name, Address>,
  /// Original Lean environment, if available. Used by the decompiler for
  /// aux_gen comparison (verifying regenerated constants match originals).
  pub lean_env: Option<Arc<LeanEnv>>,
  /// Per-block nested-auxiliary layout (permutation + source ctor
  /// counts) for each source `InductiveVal.all[0]` name. Used by
  /// `compile_aux_block` (via `generate_and_compile_aux_recursors`) to
  ///    register Lean-source aux-rec/below/brecOn names at the canonical
  ///    DPrj/RPrj position.
  ///
  /// Computed once per block in `generate_and_compile_aux_recursors`
  /// right after `aux_gen::generate_aux_patches`. Blocks without nested
  /// auxiliaries simply aren't inserted.
  pub aux_perms: DashMap<Name, ixon::env::AuxLayout>,
  /// Reducibility hints per definition NAME, recorded by
  /// `compile_definition` (the only place the Lean-side hints are in
  /// scope — hints are not part of `ConstantMeta`). The constant
  /// address a name resolves to isn't final until its `Named` entry is
  /// registered, so [`Self::finalize_hints`] resolves this map through
  /// `env.named` into `env.anon_hints` once compilation completes.
  pub def_hints: DashMap<Name, ReducibilityHints>,
  /// Resource limits of every canonical sharing construction run against
  /// this state: compilation, and the decompiler's recompile check.
  /// `compile_env` sets them once, from [`SHARING_LIMITS_ENV`], before it
  /// schedules any block; an entry point that builds a state from a
  /// deserialized environment sets them with [`compiler_sharing_limits`].
  /// The default is [`ExactSharingLimits::default`].
  pub sharing_limits: ExactSharingLimits,
  /// The driver prepared Pass 3's state (the faithful rewrite, the only
  /// mode since M6R slice 6, which deleted the legacy call-site surgery):
  /// set by every whole-environment compile (`compile_env_with_options`).
  /// A hand-built state (the decompiler's recompile check, unit tests)
  /// leaves it false and runs none of Pass 3's hooks; such a state compiles
  /// single blocks, and the aux tail of a changed block is refused there
  /// (`compile_mutual`). Lean: `CompileEnv.pass3`.
  pub pass3: bool,
  /// Pass 3's records carried from block to block.
  pub p3: pass3::Pass3State,
}

/// Cached compiled expression with arena root index.
///
/// On cache hit: O(1) — just push the cached expr and arena_root.
/// The subtree's metadata nodes are already in the arena (append-only).
#[derive(Clone, Debug)]
pub struct CachedExpr {
  pub expr: Arc<Expr>,
  pub arena_root: u64,
}

/// Per-block compilation cache.
#[derive(Default)]
pub struct BlockCache {
  /// Cache for compiled expressions (keyed by Lean hash address)
  pub exprs: FxHashMap<Address, CachedExpr>,
  /// Cache for compiled universes (Level -> Univ conversion)
  /// Keyed by `(level, univ_params_key)`, NOT by `level` alone. A
  /// `Level::Param` compiles to `Univ::Var(i)` where `i` is the
  /// parameter's POSITION in `univ_params`, so the result depends on the
  /// context. This cache lives for a whole block (unlike the expression
  /// cache, which is cleared per constant) and `compile_definition`
  /// compiles each member under its own `level_params`, so a shared key
  /// would hand the second member the first member's index — a silently
  /// wrong constant under a correct-looking name, with no abort.
  /// `collect_expr_tables` keys its `seen_exprs` the same way.
  pub univ_cache: FxHashMap<(Level, Address), Arc<Univ>>,
  /// Cache for expression comparisons
  pub cmps: FxHashMap<(Name, Name), Ordering>,
  /// Arena for expression metadata (append-only within a constant)
  pub arena: ExprMeta,
  /// Arena root indices parallel to the results stack
  pub arena_roots: Vec<u64>,
  /// Reference table: unique addresses of constants referenced by Expr::Ref
  pub refs: indexmap::IndexSet<Address>,
  /// Universe table: unique universes referenced by expressions.
  /// Canonicity §10.6: every entry is `canon_univ`-fixed —
  /// `compile_univ_idx` interns only canonical forms and
  /// `preseed_expr_tables` canonicalizes before sorting.
  pub univs: indexmap::IndexSet<Arc<Univ>>,
  /// `canon_univ` memo (positional trees — context-free, so the cache is
  /// sound across constants and univ contexts).
  pub canon_cache: FxHashMap<Arc<Univ>, Arc<Univ>>,
  /// Set by `preseed_expr_tables` once the primary `univs` table is
  /// final. From then on any on-the-fly intern of a canonical form must
  /// HIT a preseeded entry — a miss would silently shift the virtual
  /// indices in `univ_patches` (which are `univs.len() + slot`), so
  /// `compile_univ_idx` debug-asserts against it.
  pub univs_final: bool,
  /// Extension univs of the CURRENT constant: original (non-canonical)
  /// spellings referenced by `univ_patches`, in first-use order.
  /// Canonicity §10.6 — drained into `ConstantMeta.meta_univs` alongside
  /// the arena.
  pub meta_univs: indexmap::IndexSet<Arc<Univ>>,
  /// Level-spelling patches of the CURRENT constant, keyed by the arena
  /// root of each affected `sort`/`const` occurrence — drained into
  /// `ConstantMeta.univ_patches` alongside the arena.
  pub univ_patches: Vec<UnivPatch>,
  /// Name of the constant currently being compiled (for error context).
  pub compiling: Option<Name>,
  /// The current constant's `ConstantMeta.meta_sharing` accumulator: the
  /// compiled source occurrences of its Pass 3 decompile records
  /// (`pass3_compile_records`), drained after compilation completes. Until
  /// M6R slice 6 it was `surgery_sharing`, which also held the legacy
  /// surgery's collapsed call-site arguments. Lean: `BlockState.metaSharing`.
  pub meta_sharing: Vec<Arc<Expr>>,
  /// Pass 3: the block's members rewritten by the call-site rewrite
  /// (`Ix.Compile.Pass.prepareBlock`'s overlay), read instead of the input.
  pub p3_overlay: FxHashMap<Name, LeanConstantInfo>,
  /// Pass 3: the source occurrence of each rewritten call site, by
  /// placeholder index.
  pub p3_sources: FxHashMap<usize, LeanExpr>,
  /// Pass 3: placeholder index to (`meta_sharing` index, arena root) of the
  /// current constant's compiled decompile records.
  pub p3_records: FxHashMap<usize, (u64, u64)>,
  /// Pass 3: compiling a decompile record; references and universes outside
  /// the primary tables go to the extension tables.
  pub p3_meta_mode: bool,
  /// Pass 3: the current constant's extension refs (`meta_refs`).
  pub p3_meta_refs: indexmap::IndexSet<Address>,
  /// Pass 3: the recorded declines of the block's rewrite, merged into the
  /// non-canonical set when the block compiles (`BlockState.p3NonCanonical`).
  pub p3_declines: Vec<(Name, String)>,
}

#[derive(Debug)]
pub struct CompileStateStats {
  pub consts: usize,
  pub names: usize,
  pub blobs: usize,
  pub blocks: usize,
}

impl Default for CompileState {
  fn default() -> Self {
    CompileState {
      env: Default::default(),
      name_to_addr: Default::default(),
      blocks: Default::default(),
      ungrounded: Default::default(),
      aux_gen_extra_names: Default::default(),
      aux_gen_pending: std::sync::Mutex::new(Vec::new()),
      aux_name_to_addr: Default::default(),
      lean_env: None,
      aux_perms: Default::default(),
      def_hints: Default::default(),
      sharing_limits: ExactSharingLimits::default(),
      pass3: false,
      p3: Default::default(),
    }
  }
}

impl CompileState {
  /// Create an empty compile state for testing (no environment).
  pub fn new_empty() -> Self {
    Self::default()
  }

  pub fn stats(&self) -> CompileStateStats {
    CompileStateStats {
      consts: self.env.const_count(),
      names: self.env.name_count(),
      blobs: self.env.blob_count(),
      blocks: self.blocks.len(),
    }
  }

  /// Claim `name` for an aux_gen product at `addr` (A0: single ownership).
  ///
  /// Insert-once: the first claim wins and an identical re-claim is a no-op,
  /// but a claim at a different address — by another aux block, or on a
  /// name a non-aux block has already compiled — is a hard error instead of
  /// a schedule-dependent overwrite (the `FieldBelowRace` shape, WB-C1).
  pub fn claim_aux_name(
    &self,
    name: &Name,
    addr: &Address,
  ) -> Result<(), CompileError> {
    if let Some(existing) = self.name_to_addr.get(name)
      && *existing.value() != *addr
    {
      return Err(name_claim_conflict(name, existing.value(), addr));
    }
    match self.aux_name_to_addr.entry(name.clone()) {
      dashmap::mapref::entry::Entry::Occupied(e) => {
        if e.get() != addr {
          return Err(name_claim_conflict(name, e.get(), addr));
        }
      },
      dashmap::mapref::entry::Entry::Vacant(e) => {
        e.insert(addr.clone());
        block_txn::log_aux(name);
      },
    }
    self.aux_gen_extra_names.insert(name.clone());
    pass3::journal_claim(name);
    Ok(())
  }

  /// Claim `name` for the block that compiles it (aux mode) at `addr`.
  /// A name aux_gen has claimed at another address is a hard error: two
  /// producers would otherwise race for it.
  pub fn claim_compiled_name(
    &self,
    name: &Name,
    addr: &Address,
  ) -> Result<(), CompileError> {
    if let Some(existing) = self.aux_name_to_addr.get(name)
      && *existing.value() != *addr
    {
      return Err(name_claim_conflict(name, existing.value(), addr));
    }
    // A7 (a7s §6.2): a second compiled claim at another address is the same
    // conflict (design document §6.2: a name assigned twice is an error
    // unless both assignments are equal). It was an overwrite, so the address
    // a name kept depended on which block claimed last; an identical
    // re-claim stays a no-op, so valid input registers the same values.
    match self.name_to_addr.entry(name.clone()) {
      dashmap::mapref::entry::Entry::Occupied(e) => {
        if e.get() != addr {
          return Err(name_claim_conflict(name, e.get(), addr));
        }
      },
      dashmap::mapref::entry::Entry::Vacant(e) => {
        e.insert(addr.clone());
        block_txn::log_compiled(name);
      },
    }
    Ok(())
  }

  /// Register `name`'s `Named` entry, logging it for the failed-block
  /// rollback when the entry is new (`block_txn`).
  pub fn register_named(&self, name: Name, named: Named) {
    let fresh = !self.env.named.contains_key(&name);
    if fresh {
      block_txn::log_named(&name);
    }
    self.env.register_name(name, named);
  }

  /// Look up a compiled constant's address by name.
  /// Checks `name_to_addr` first, then `aux_name_to_addr` when `aux` is true.
  pub fn resolve_addr_aux(&self, name: &Name, aux: bool) -> Option<Address> {
    if let Some(r) = self.name_to_addr.get(name) {
      return Some(r.value().clone());
    }
    if aux && let Some(r) = self.aux_name_to_addr.get(name) {
      return Some(r.value().clone());
    }
    None
  }

  /// Look up a compiled constant's address (with `aux_name_to_addr` fallback).
  pub fn resolve_addr(&self, name: &Name) -> Option<Address> {
    self.resolve_addr_aux(name, true)
  }

  /// Scheduled blocks publish hints only after all compilation/promotion
  /// checks succeed. Direct callers retain the immediate-write behaviour.
  pub fn record_hint(&self, name: &Name, hint: Option<ReducibilityHints>) {
    if block_txn::defer_hint(name, hint) {
      return;
    }
    match hint {
      Some(h) => {
        self.def_hints.insert(name.clone(), h);
      },
      None => {
        self.def_hints.remove(name);
      },
    }
  }

  pub fn recorded_hint(&self, name: &Name) -> Option<ReducibilityHints> {
    block_txn::hint(name)
      .unwrap_or_else(|| self.def_hints.get(name).map(|r| *r))
  }

  /// Resolve the per-name hints recorded by `compile_definition` into
  /// the env. Runs once after the scheduler drains: addresses aren't
  /// final until the `Named` entries are registered. Two channels:
  ///
  /// - `Named.hints` (exact, per name): alpha-identical definitions
  ///   under different names share one constant address but may carry
  ///   different hints; decompile reconstructs `DefinitionVal.hints`
  ///   from here, so no merge may touch it.
  /// - `env.anon_hints` (advisory, per constant address — `Named.addr`,
  ///   the projection address for mutual-block members, i.e. exactly
  ///   the address the anon-mode kernel looks hints up under). Alias
  ///   collisions resolve through `Env::register_hint`'s
  ///   order-independent merge.
  pub fn finalize_hints(&self) {
    for entry in self.def_hints.iter() {
      if let Some(mut named) = self.env.named.get_mut(entry.key()) {
        named.set_hints(Some(*entry.value()));
        self.env.register_hint(named.addr.clone(), *entry.value());
      }
    }
  }

  /// Promote a constant from `aux_name_to_addr` to `name_to_addr`, setting
  /// `Named.original` to the given `(orig_addr, orig_meta)` from the
  /// ephemeral no-aux compilation. The existing aux_gen `Named` entry keeps
  /// its canonical `addr`/`meta`; `original` captures the Lean-native form.
  /// During a scheduled block the metadata and address claims are deferred
  /// until the whole block has succeeded (`block_txn::commit`).
  ///
  /// Errors with `CompileError::InvalidMutualBlock` if the metadata's
  /// self-name address does not match `name`'s compiled address — that
  /// mismatch is structural corruption (the address map and the name
  /// table disagree about which constant this `meta` describes) and
  /// silently continuing would splice foreign metadata into `name`'s
  /// Named entry.
  pub fn promote_aux(
    &self,
    name: &Name,
    orig_addr: Address,
    orig_meta: ConstantMeta,
  ) -> Result<(), CompileError> {
    // Verify that the metadata's own name address matches the constant
    // being promoted. A mismatch means we're about to attach metadata
    // that describes some other constant.
    let meta_name_addr = match &orig_meta.info {
      ConstantMetaInfo::Def { name: a, .. }
      | ConstantMetaInfo::Axio { name: a, .. }
      | ConstantMetaInfo::Quot { name: a, .. }
      | ConstantMetaInfo::Indc { name: a, .. }
      | ConstantMetaInfo::Ctor { name: a, .. }
      | ConstantMetaInfo::Rec { name: a, .. } => Some(a),
      _ => None,
    };
    if let Some(meta_addr) = meta_name_addr {
      let expected_addr = compile_name(name, self);
      if *meta_addr != expected_addr {
        return Err(CompileError::InvalidMutualBlock {
          reason: format!(
            "promote_aux: name mismatch for '{}' — compile_name address \
             is {:.12} but meta name address is {:.12}",
            name.pretty(),
            expected_addr.hex(),
            meta_addr.hex(),
          ),
        });
      }
    }

    let Some((orig_addr, orig_meta)) =
      block_txn::defer_promotion(name, orig_addr, orig_meta)
    else {
      return Ok(());
    };
    let aux_addr = self.aux_name_to_addr.get(name).map(|r| r.value().clone());
    if let Some(aux_addr) = aux_addr {
      self.claim_compiled_name(name, &aux_addr)?;
    }
    if let Some(mut entry) = self.env.named.get_mut(name) {
      entry.value_mut().set_original(orig_addr, orig_meta);
    }
    Ok(())
  }
}

// ===========================================================================
// Helper functions
// ===========================================================================

/// Two producers claim one name at different addresses.
pub fn name_claim_conflict(
  name: &Name,
  existing: &Address,
  claimed: &Address,
) -> CompileError {
  CompileError::InvalidMutualBlock {
    reason: format!(
      "conflicting claims for name '{}': already registered at {:.12}, \
       claimed again at {:.12}",
      name.pretty(),
      existing.hex(),
      claimed.hex(),
    ),
  }
}

/// Convert a Nat to u64, returning an error if the value is too large.
fn nat_to_u64(n: &Nat, context: &'static str) -> Result<u64, CompileError> {
  n.to_u64().ok_or(CompileError::UnsupportedExpr { desc: context.into() })
}

// ===========================================================================
// Name compilation
// ===========================================================================

/// Store a string as a blob and return its address.
pub fn store_string(s: &str, stt: &CompileState) -> Address {
  stt.env.store_blob(s.as_bytes().to_vec())
}

/// Store a Nat as a blob and return its address.
pub fn store_nat(n: &Nat, stt: &CompileState) -> Address {
  stt.env.store_blob(n.to_le_bytes())
}

/// Compile a Lean Name to an address (stored in env.names).
/// Uses the Name's internal hash as the address.
/// String components are stored in blobs.
pub fn compile_name(name: &Name, stt: &CompileState) -> Address {
  // Use the Name's internal hash as the address
  let addr = Address::from_blake3_hash(*name.get_hash());

  // Check if already stored
  if stt.env.names.contains_key(&addr) {
    return addr;
  }

  // Recurse on parent first (ensures parent is stored)
  match name.as_data() {
    NameData::Anonymous(_) => {},
    NameData::Str(parent, s, _) => {
      compile_name(parent, stt);
      store_string(s, stt); // string data in blobs
    },
    NameData::Num(parent, _, _) => {
      compile_name(parent, stt);
      // Nat is inline in Name, no blob needed
    },
  }

  // Store Name struct directly in env.names
  stt.env.names.insert(addr.clone(), name.clone());
  addr
}

// ===========================================================================
// Universe compilation
// ===========================================================================

/// Compile a Lean Level to an Ixon Univ.
pub fn compile_univ(
  level: &Level,
  univ_params: &[Name],
  cache: &mut BlockCache,
) -> Result<Arc<Univ>, CompileError> {
  let ctx_key = univ_params_key(univ_params);
  if let Some(cached) = cache.univ_cache.get(&(level.clone(), ctx_key.clone()))
  {
    return Ok(cached.clone());
  }

  let univ = match level.as_data() {
    LevelData::Zero(_) => Univ::zero(),
    LevelData::Succ(inner, _) => {
      let inner_univ = compile_univ(inner, univ_params, cache)?;
      Univ::succ(inner_univ)
    },
    LevelData::Max(a, b, _) => {
      let a_univ = compile_univ(a, univ_params, cache)?;
      let b_univ = compile_univ(b, univ_params, cache)?;
      Univ::max(a_univ, b_univ)
    },
    LevelData::Imax(a, b, _) => {
      let a_univ = compile_univ(a, univ_params, cache)?;
      let b_univ = compile_univ(b, univ_params, cache)?;
      Univ::imax(a_univ, b_univ)
    },
    LevelData::Param(name, _) => {
      let idx =
        univ_params.iter().position(|n| n == name).ok_or_else(|| {
          CompileError::UnknownUnivParam {
            curr: String::new(),
            param: name.pretty(),
          }
        })?;
      Univ::var(idx as u64)
    },
    LevelData::Mvar(_name, _) => {
      return Err(CompileError::UnsupportedExpr {
        desc: "level metavariable".into(),
      });
    },
  };

  cache.univ_cache.insert((level.clone(), ctx_key), univ.clone());
  Ok(univ)
}

/// `canon_univ` through the block memo.
fn canon_univ_cached(u: &Arc<Univ>, cache: &mut BlockCache) -> Arc<Univ> {
  if let Some(c) = cache.canon_cache.get(u) {
    return c.clone();
  }
  let c = canon_univ(u);
  cache.canon_cache.insert(u.clone(), c.clone());
  c
}

/// Compile a universe and intern its CANONICAL form into the primary
/// univs table (canonicity §10.6). Returns the canonical index plus,
/// when the source spelling differs, the VIRTUAL index of the original
/// spelling in the per-constant `meta_univs` extension
/// (`univs.len() + slot` — stable because the primary table is
/// preseed-final by the time expressions compile).
fn compile_univ_idx(
  level: &Level,
  univ_params: &[Name],
  cache: &mut BlockCache,
) -> Result<(u64, Option<u64>), CompileError> {
  let univ = compile_univ(level, univ_params, cache)?;
  let canon = canon_univ_cached(&univ, cache);
  // Pass 3 decompile record: a universe outside the primary table goes to
  // the extension (virtual index), never into the primary table.
  if cache.p3_meta_mode && !cache.univs.contains(&canon) {
    let (slot, _) = cache.meta_univs.insert_full(canon.clone());
    let cidx = (cache.univs.len() + slot) as u64;
    if canon == univ {
      return Ok((cidx, None));
    }
    let (slot2, _) = cache.meta_univs.insert_full(univ);
    return Ok((cidx, Some((cache.univs.len() + slot2) as u64)));
  }
  let (idx, fresh) = cache.univs.insert_full(canon.clone());
  debug_assert!(
    !(fresh && cache.univs_final),
    "compile_univ_idx: preseed missed canonical form {canon:?} while \
     compiling {:?} — primary univ table grew after preseeding, which \
     shifts univ_patches virtual indices (canonicity §10.6 V3)",
    cache.compiling
  );
  if canon == univ {
    return Ok((idx as u64, None));
  }
  let (slot, _) = cache.meta_univs.insert_full(univ);
  Ok((idx as u64, Some((cache.univs.len() + slot) as u64)))
}

/// Compile a list of universes and add their canonical forms to the
/// univs table, returning `(canonical_idx, Option<virtual original
/// idx>)` pairs (see [`compile_univ_idx`]).
fn compile_univ_indices(
  levels: &[Level],
  univ_params: &[Name],
  cache: &mut BlockCache,
) -> Result<Vec<(u64, Option<u64>)>, CompileError> {
  levels.iter().map(|l| compile_univ_idx(l, univ_params, cache)).collect()
}

fn univ_sort_key(univ: &Arc<Univ>) -> Vec<u8> {
  let mut buf = Vec::new();
  ixon::univ::put_univ(univ, &mut buf);
  buf
}

fn univ_params_key(univ_params: &[Name]) -> Address {
  let mut hasher = blake3::Hasher::new();
  for name in univ_params {
    hasher.update(name.get_hash().as_bytes());
  }
  Address::from_blake3_hash(hasher.finalize())
}

fn collect_expr_tables(
  expr: &LeanExpr,
  univ_params: &[Name],
  mut_ctx: &MutCtx,
  cache: &mut BlockCache,
  stt: &CompileState,
  refs: &mut Vec<Address>,
  univs: &mut Vec<Arc<Univ>>,
  seen_exprs: &mut FxHashMap<(Address, Address), ()>,
  caller: &str,
) -> Result<(), CompileError> {
  let ctx_key = univ_params_key(univ_params);
  let mut stack = vec![expr];
  while let Some(e) = stack.pop() {
    let key = Address::from_blake3_hash(*e.get_hash());
    if seen_exprs.insert((key, ctx_key.clone()), ()).is_some() {
      continue;
    }

    match e.as_data() {
      ExprData::Bvar(..) => {},
      ExprData::Sort(level, _) => {
        univs.push(compile_univ(level, univ_params, cache)?);
      },
      ExprData::Const(name, levels, _) => {
        for level in levels {
          univs.push(compile_univ(level, univ_params, cache)?);
        }
        if !mut_ctx.contains_key(name) {
          let const_addr = stt.resolve_addr(name).ok_or_else(|| {
            CompileError::MissingConstant {
              name: name.pretty(),
              caller: format!("{caller} @ preseed(Const)"),
            }
          })?;
          refs.push(const_addr);
        }
      },
      ExprData::App(fun, arg, _) => {
        stack.push(arg);
        stack.push(fun);
      },
      ExprData::Lam(_, ty, body, _, _)
      | ExprData::ForallE(_, ty, body, _, _) => {
        stack.push(body);
        stack.push(ty);
      },
      ExprData::LetE(_, ty, value, body, _, _) => {
        stack.push(body);
        stack.push(value);
        stack.push(ty);
      },
      ExprData::Lit(Literal::NatVal(n), _) => {
        refs.push(store_nat(n, stt));
      },
      ExprData::Lit(Literal::StrVal(s), _) => {
        refs.push(store_string(s, stt));
      },
      ExprData::Proj(type_name, _, struct_val, _) => {
        let type_addr = stt.resolve_addr(type_name).ok_or_else(|| {
          CompileError::MissingConstant {
            name: type_name.pretty(),
            caller: format!("{caller} @ preseed(Proj)"),
          }
        })?;
        refs.push(type_addr);
        stack.push(struct_val);
      },
      ExprData::Mdata(_, inner, _) => {
        stack.push(inner);
      },
      ExprData::Fvar(..) => {
        return Err(CompileError::UnsupportedExpr {
          desc: "free variable".into(),
        });
      },
      ExprData::Mvar(..) => {
        return Err(CompileError::UnsupportedExpr {
          desc: "metavariable".into(),
        });
      },
    }
  }
  Ok(())
}

pub fn preseed_expr_tables(
  exprs: &[(&LeanExpr, &[Name])],
  mut_ctx: &MutCtx,
  cache: &mut BlockCache,
  stt: &CompileState,
  caller: &str,
) -> Result<(), CompileError> {
  let mut refs = Vec::new();
  let mut univs = Vec::new();
  let mut seen_exprs = FxHashMap::default();

  for (expr, univ_params) in exprs {
    collect_expr_tables(
      expr,
      univ_params,
      mut_ctx,
      cache,
      stt,
      &mut refs,
      &mut univs,
      &mut seen_exprs,
      caller,
    )?;
  }

  refs.sort();
  refs.dedup();
  for addr in refs {
    cache.refs.insert_full(addr);
  }

  // Canonicalize before sorting (canonicity §10.6): the primary table
  // holds only `canon_univ`-fixed forms; the on-the-fly
  // `compile_univ_idx` then always finds the preseeded canonical entry.
  let mut canon_univs: Vec<Arc<Univ>> = Vec::with_capacity(univs.len());
  for u in univs {
    canon_univs.push(canon_univ_cached(&u, cache));
  }
  let mut keyed_univs: Vec<_> =
    canon_univs.into_iter().map(|u| (univ_sort_key(&u), u)).collect();
  keyed_univs.sort_by(|(ak, _), (bk, _)| ak.cmp(bk));
  keyed_univs.dedup_by(|(ak, _), (bk, _)| ak == bk);
  for (_, univ) in keyed_univs {
    cache.univs.insert_full(univ);
  }
  cache.univs_final = true;

  Ok(())
}

pub fn collect_mut_const_exprs<'a>(
  cnst: &'a MutConst,
  exprs: &mut Vec<(&'a LeanExpr, &'a [Name])>,
) {
  match cnst {
    MutConst::Defn(def) => {
      let lvls = def.level_params.as_slice();
      exprs.push((&def.typ, lvls));
      exprs.push((&def.value, lvls));
    },
    MutConst::Indc(ind) => {
      exprs.push((&ind.ind.cnst.typ, ind.ind.cnst.level_params.as_slice()));
      for ctor in &ind.ctors {
        exprs.push((&ctor.cnst.typ, ctor.cnst.level_params.as_slice()));
      }
    },
    MutConst::Recr(rec) => {
      let lvls = rec.cnst.level_params.as_slice();
      exprs.push((&rec.cnst.typ, lvls));
      for rule in &rec.rules {
        exprs.push((&rule.rhs, lvls));
      }
    },
  }
}

// ===========================================================================
// Expression compilation
// ===========================================================================

/// Intern an address into the block's refs table, returning its index. While
/// compiling a Pass 3 decompile record, an address outside the primary table
/// goes to the constant's extension table (`meta_refs`, virtual index
/// `refs.len() + j`) instead (Lean `internRefMeta`).
fn intern_ref(cache: &mut BlockCache, addr: Address) -> usize {
  if cache.p3_meta_mode {
    if let Some(i) = cache.refs.get_index_of(&addr) {
      return i;
    }
    let (j, _) = cache.p3_meta_refs.insert_full(addr);
    return cache.refs.len() + j;
  }
  cache.refs.insert_full(addr).0
}

/// Pass 3: the placeholder indices of the rewritten call sites in `e`, in
/// first-occurrence order, each once (Lean `pass3Placeholders`).
fn pass3_placeholders(e: &LeanExpr) -> Vec<usize> {
  let key = pass3::names::inline_key();
  let mut seen: FxHashSet<Address> = FxHashSet::default();
  let mut out: Vec<usize> = Vec::new();
  let mut stack = vec![e.clone()];
  while let Some(x) = stack.pop() {
    if !seen.insert(Address::from_blake3_hash(*x.get_hash())) {
      continue;
    }
    match x.as_data() {
      ExprData::Mdata(kvs, inner, _) => {
        if let [(k, LeanDataValue::OfNat(n))] = kvs.as_slice()
          && *k == key
        {
          let n = pass3::expr::nat_usize(n);
          if !out.contains(&n) {
            out.push(n);
          }
        }
        stack.push(inner.clone());
      },
      ExprData::App(f, a, _) => {
        stack.push(a.clone());
        stack.push(f.clone());
      },
      ExprData::Lam(_, t, b, _, _) | ExprData::ForallE(_, t, b, _, _) => {
        stack.push(b.clone());
        stack.push(t.clone());
      },
      ExprData::LetE(_, t, v, b, _, _) => {
        stack.push(b.clone());
        stack.push(v.clone());
        stack.push(t.clone());
      },
      ExprData::Proj(_, _, s, _) => stack.push(s.clone()),
      _ => {},
    }
  }
  out
}

/// Pass 3: compile the decompile record of every rewritten call site of `e`
/// the current constant has not compiled yet: its source occurrence, into
/// `meta_sharing`, in meta mode; the expression cache is saved and restored
/// around it (Lean `pass3CompileRecords`).
fn pass3_compile_records(
  e: &LeanExpr,
  univ_params: &[Name],
  mut_ctx: &MutCtx,
  cache: &mut BlockCache,
  stt: &CompileState,
) -> Result<(), CompileError> {
  for n in pass3_placeholders(e) {
    if cache.p3_records.contains_key(&n) {
      continue;
    }
    let src = cache.p3_sources.get(&n).cloned().ok_or_else(|| {
      CompileError::InvalidMutualBlock {
        reason: format!(
          "Pass 3: no source occurrence for call-site record {n}"
        ),
      }
    })?;
    let saved = cache.exprs.clone();
    cache.p3_meta_mode = true;
    let res = compile_expr(&src, univ_params, mut_ctx, cache, stt);
    cache.p3_meta_mode = false;
    cache.exprs = saved;
    let ix = res?;
    let root = cache.arena_roots.pop().ok_or_else(|| {
      CompileError::InvalidMutualBlock {
        reason: "Pass 3: call-site record without an arena root".into(),
      }
    })?;
    cache.p3_records.insert(n, (cache.meta_sharing.len() as u64, root));
    cache.meta_sharing.push(ix);
  }
  Ok(())
}

fn compile_const_expr_raw(
  name: &Name,
  levels: &[Level],
  univ_params: &[Name],
  mut_ctx: &MutCtx,
  cache: &mut BlockCache,
  stt: &CompileState,
) -> Result<(Arc<Expr>, u64), CompileError> {
  let compiled = compile_univ_indices(levels, univ_params, cache)?;
  let univ_indices: Vec<u64> = compiled.iter().map(|(c, _)| *c).collect();
  let patch_idxs: Option<Vec<u64>> =
    if compiled.iter().any(|(_, o)| o.is_some()) {
      Some(compiled.iter().map(|(c, o)| o.unwrap_or(*c)).collect())
    } else {
      None
    };
  let name_addr = compile_name(name, stt);
  let expr = if let Some(idx) = mut_ctx.get(name) {
    let idx_u64 = nat_to_u64(idx, "mutual index too large")?;
    Expr::rec(idx_u64, univ_indices)
  } else {
    let const_addr = stt.resolve_addr(name).ok_or_else(|| {
      let who =
        cache.compiling.as_ref().map_or_else(|| "?".into(), |n| n.pretty());
      CompileError::MissingConstant {
        name: name.pretty(),
        caller: format!("{who} @ compile_expr(Const)"),
      }
    })?;
    let ref_idx = intern_ref(cache, const_addr.clone());
    Expr::reference(ref_idx as u64, univ_indices)
  };
  let root = cache.arena.alloc(ExprMetaData::Ref { name: name_addr });
  if let Some(univ_idxs) = patch_idxs {
    cache.univ_patches.push(UnivPatch { arena_idx: root, univ_idxs });
  }
  Ok((expr, root))
}

/// Compile a Lean expression to an Ixon expression.
/// Builds arena-based metadata in cache.arena with bottom-up allocation.
pub fn compile_expr(
  expr: &LeanExpr,
  univ_params: &[Name],
  mut_ctx: &MutCtx,
  cache: &mut BlockCache,
  stt: &CompileState,
) -> Result<Arc<Expr>, CompileError> {
  // Stack-based iterative compilation to avoid stack overflow
  enum Frame {
    Compile(LeanExpr),
    BuildApp,
    BuildLam(Address, BinderInfo),
    BuildAll(Address, BinderInfo),
    BuildLet(Address, bool),
    BuildProj(u64, u64, Address), // type_ref_idx, field_idx, struct_name_addr
    WrapMdata(Vec<KVMap>),
    ApplyContract(crate::semantic_contract::Contract, LeanExpr),
    Cache(LeanExpr),
  }

  // Pass 3: the decompile records of the rewritten call sites in `expr`
  // first (Lean `compileExpr` runs `pass3CompileRecords` before the term).
  if stt.pass3 && !cache.p3_meta_mode && !cache.p3_sources.is_empty() {
    pass3_compile_records(expr, univ_params, mut_ctx, cache, stt)?;
  }

  // Top-level cache check (O(1) with arena)
  let expr_key = Address::from_blake3_hash(*expr.get_hash());
  if let Some(cached) = cache.exprs.get(&expr_key).cloned() {
    cache.arena_roots.push(cached.arena_root);
    return Ok(cached.expr);
  }

  let mut stack: Vec<Frame> = vec![Frame::Compile(expr.clone())];
  let mut results: Vec<Arc<Expr>> = Vec::new();

  while let Some(frame) = stack.pop() {
    match frame {
      Frame::Compile(e) => {
        let e_key = Address::from_blake3_hash(*e.get_hash());
        if let Some(cached) = cache.exprs.get(&e_key).cloned() {
          // O(1) cache hit: arena root already valid
          results.push(cached.expr);
          cache.arena_roots.push(cached.arena_root);
          continue;
        }

        stack.push(Frame::Cache(e.clone()));

        match e.as_data() {
          ExprData::Bvar(idx, _) => {
            let idx_u64 = nat_to_u64(idx, "bvar index too large")?;
            results.push(Expr::var(idx_u64));
            cache.arena_roots.push(cache.arena.alloc(ExprMetaData::Leaf));
          },

          ExprData::Sort(level, _) => {
            let (univ_idx, orig) = compile_univ_idx(level, univ_params, cache)?;
            results.push(Expr::sort(univ_idx));
            let root = cache.arena.alloc(ExprMetaData::Leaf);
            cache.arena_roots.push(root);
            // Canonicity §10.6: a spelling the canonicalization changed
            // is restorable from the patch keyed by this occurrence's
            // arena root. Cache hits on repeated subtrees reuse the same
            // root, so the patch covers every occurrence.
            if let Some(vidx) = orig {
              cache
                .univ_patches
                .push(UnivPatch { arena_idx: root, univ_idxs: vec![vidx] });
            }
          },

          ExprData::Const(name, levels, _) => {
            let (raw, root) = compile_const_expr_raw(
              name,
              levels,
              univ_params,
              mut_ctx,
              cache,
              stt,
            )?;
            results.push(raw);
            cache.arena_roots.push(root);
          },

          ExprData::App(_, _, _) => {
            // Collect the full App telescope in one pass (O(depth) pointer chase).
            let (head_expr, args) = aux_source::collect_lean_telescope(&e);

            // Telescope path: interleave BuildApp + Compile(arg) for
            // each arg (right to left), then Compile(head).
            // This compiles the same result as the recursive one-App-at-a-time
            // approach, but avoids re-entering the App branch for inner nodes.
            for &arg in args.iter().rev() {
              stack.push(Frame::BuildApp);
              stack.push(Frame::Compile(arg.clone()));
            }
            stack.push(Frame::Compile(head_expr.clone()));
          },

          ExprData::Lam(name, ty, body, info, _) => {
            let name_addr = compile_name(name, stt);
            stack.push(Frame::BuildLam(name_addr, info.clone()));
            stack.push(Frame::Compile(body.clone()));
            stack.push(Frame::Compile(ty.clone()));
          },

          ExprData::ForallE(name, ty, body, info, _) => {
            let name_addr = compile_name(name, stt);
            stack.push(Frame::BuildAll(name_addr, info.clone()));
            stack.push(Frame::Compile(body.clone()));
            stack.push(Frame::Compile(ty.clone()));
          },

          ExprData::LetE(name, ty, val, body, non_dep, _) => {
            let name_addr = compile_name(name, stt);
            stack.push(Frame::BuildLet(name_addr, *non_dep));
            stack.push(Frame::Compile(body.clone()));
            stack.push(Frame::Compile(val.clone()));
            stack.push(Frame::Compile(ty.clone()));
          },

          ExprData::Lit(Literal::NatVal(n), _) => {
            let addr = store_nat(n, stt);
            let ref_idx = intern_ref(cache, addr);
            results.push(Expr::nat(ref_idx as u64));
            cache.arena_roots.push(cache.arena.alloc(ExprMetaData::Leaf));
          },

          ExprData::Lit(Literal::StrVal(s), _) => {
            let addr = store_string(s, stt);
            let ref_idx = intern_ref(cache, addr);
            results.push(Expr::str(ref_idx as u64));
            cache.arena_roots.push(cache.arena.alloc(ExprMetaData::Leaf));
          },

          ExprData::Proj(type_name, idx, struct_val, _) => {
            let idx_u64 = nat_to_u64(idx, "proj index too large")?;

            let type_addr = stt.resolve_addr(type_name).ok_or_else(|| {
              let who = cache
                .compiling
                .as_ref()
                .map_or_else(|| "?".into(), |n| n.pretty());
              CompileError::MissingConstant {
                name: type_name.pretty(),
                caller: format!("{who} @ compile_expr(Proj)"),
              }
            })?;

            let ref_idx = intern_ref(cache, type_addr.clone());
            let name_addr = compile_name(type_name, stt);

            stack.push(Frame::BuildProj(ref_idx as u64, idx_u64, name_addr));
            stack.push(Frame::Compile(struct_val.clone()));
          },

          ExprData::Mdata(kv, inner, _) => {
            if crate::semantic_contract::has_metadata(kv) {
              let contract = crate::semantic_contract::read(kv)?;
              stack.push(Frame::ApplyContract(contract, inner.clone()));
              stack.push(Frame::Compile(inner.clone()));
              continue;
            }
            // Compile KV map. Pass 3: the placeholder `[(_ix.inline, n)]`
            // becomes the decompile record `[(_ix.inline, s),
            // (_ix.inline_meta, m)]` (Lean `compileKVMap`).
            let mut kv_owned: Option<Vec<(Name, LeanDataValue)>> = None;
            if stt.pass3
              && let [(k, LeanDataValue::OfNat(n))] = kv.as_slice()
              && *k == pass3::names::inline_key()
            {
              let n = pass3::expr::nat_usize(n);
              let (s, m) =
                cache.p3_records.get(&n).copied().ok_or_else(|| {
                  CompileError::InvalidMutualBlock {
                    reason: format!(
                      "Pass 3: call-site record {n} was not compiled"
                    ),
                  }
                })?;
              kv_owned = Some(vec![
                (
                  pass3::names::inline_key(),
                  LeanDataValue::OfNat(Nat::from(s)),
                ),
                (
                  pass3::names::inline_meta_key(),
                  LeanDataValue::OfNat(Nat::from(m)),
                ),
              ]);
            }
            let kv = kv_owned.as_ref().unwrap_or(kv);
            let mut pairs = Vec::new();
            for (k, v) in kv {
              let k_addr = compile_name(k, stt);
              let v_data = compile_data_value(v, stt);
              pairs.push((k_addr, v_data));
            }
            // Mdata becomes a separate arena node wrapping inner
            stack.push(Frame::WrapMdata(vec![pairs]));
            stack.push(Frame::Compile(inner.clone()));
          },

          ExprData::Fvar(n, _) => {
            return Err(CompileError::UnsupportedExpr {
              desc: format!("free variable '{}'", n.pretty()),
            });
          },

          ExprData::Mvar(..) => {
            return Err(CompileError::UnsupportedExpr {
              desc: "metavariable".into(),
            });
          },
        }
      },

      Frame::BuildApp => {
        let a_root =
          cache.arena_roots.pop().expect("BuildApp missing arg root");
        let f_root =
          cache.arena_roots.pop().expect("BuildApp missing fun root");
        let arg = results.pop().expect("BuildApp missing arg");
        let fun = results.pop().expect("BuildApp missing fun");
        results.push(Expr::app(fun, arg));
        cache.arena_roots.push(
          cache.arena.alloc(ExprMetaData::App { children: [f_root, a_root] }),
        );
      },

      Frame::BuildLam(name_addr, info) => {
        let body_root =
          cache.arena_roots.pop().expect("BuildLam missing body root");
        let ty_root =
          cache.arena_roots.pop().expect("BuildLam missing ty root");
        let body = results.pop().expect("BuildLam missing body");
        let ty = results.pop().expect("BuildLam missing ty");
        results.push(Expr::lam(ty, body));
        cache.arena_roots.push(cache.arena.alloc(ExprMetaData::Binder {
          name: name_addr,
          info,
          children: [ty_root, body_root],
        }));
      },

      Frame::BuildAll(name_addr, info) => {
        let body_root =
          cache.arena_roots.pop().expect("BuildAll missing body root");
        let ty_root =
          cache.arena_roots.pop().expect("BuildAll missing ty root");
        let body = results.pop().expect("BuildAll missing body");
        let ty = results.pop().expect("BuildAll missing ty");
        results.push(Expr::all(ty, body));
        cache.arena_roots.push(cache.arena.alloc(ExprMetaData::Binder {
          name: name_addr,
          info,
          children: [ty_root, body_root],
        }));
      },

      Frame::BuildLet(name_addr, non_dep) => {
        let body_root =
          cache.arena_roots.pop().expect("BuildLet missing body root");
        let val_root =
          cache.arena_roots.pop().expect("BuildLet missing val root");
        let ty_root =
          cache.arena_roots.pop().expect("BuildLet missing ty root");
        let body = results.pop().expect("BuildLet missing body");
        let val = results.pop().expect("BuildLet missing val");
        let ty = results.pop().expect("BuildLet missing ty");
        results.push(Expr::let_(non_dep, ty, val, body));
        cache.arena_roots.push(cache.arena.alloc(ExprMetaData::LetBinder {
          name: name_addr,
          children: [ty_root, val_root, body_root],
        }));
      },

      Frame::BuildProj(type_ref_idx, field_idx, struct_name_addr) => {
        let child_root =
          cache.arena_roots.pop().expect("BuildProj missing child root");
        let struct_val = results.pop().expect("BuildProj missing struct_val");
        results.push(Expr::prj(type_ref_idx, field_idx, struct_val));
        cache.arena_roots.push(cache.arena.alloc(ExprMetaData::Prj {
          struct_name: struct_name_addr,
          child: child_root,
        }));
      },

      Frame::ApplyContract(contract, source) => {
        let inner = results.pop().expect("ApplyContract missing expression");
        results.push(contract.lower(&source, &inner)?);
      },

      Frame::WrapMdata(mdata) => {
        // Mdata doesn't change the Ixon expression — only wraps the arena node
        let inner_root =
          cache.arena_roots.pop().expect("WrapMdata missing inner root");
        cache.arena_roots.push(
          cache.arena.alloc(ExprMetaData::Mdata { mdata, child: inner_root }),
        );
      },

      Frame::Cache(e) => {
        let e_key = Address::from_blake3_hash(*e.get_hash());
        if let Some(result) = results.last() {
          let arena_root =
            *cache.arena_roots.last().expect("Cache missing arena root");
          cache
            .exprs
            .insert(e_key, CachedExpr { expr: result.clone(), arena_root });
        }
      },
    }
  }

  results
    .pop()
    .ok_or(CompileError::UnsupportedExpr { desc: "empty result".into() })
}

/// Compile a Lean DataValue to Ixon DataValue.
fn compile_data_value(dv: &LeanDataValue, stt: &CompileState) -> DataValue {
  match dv {
    LeanDataValue::OfString(s) => DataValue::OfString(store_string(s, stt)),
    LeanDataValue::OfBool(b) => DataValue::OfBool(*b),
    LeanDataValue::OfName(n) => DataValue::OfName(compile_name(n, stt)),
    LeanDataValue::OfNat(n) => DataValue::OfNat(store_nat(n, stt)),
    LeanDataValue::OfInt(i) => {
      // Serialize Int and store as blob
      let mut bytes = Vec::new();
      match i {
        ix_common::env::Int::OfNat(n) => {
          bytes.push(0);
          bytes.extend_from_slice(&n.to_le_bytes());
        },
        ix_common::env::Int::NegSucc(n) => {
          bytes.push(1);
          bytes.extend_from_slice(&n.to_le_bytes());
        },
      }
      DataValue::OfInt(stt.env.store_blob(bytes))
    },
    LeanDataValue::OfSyntax(syn) => {
      // Serialize syntax and store as blob
      let bytes = serialize_syntax(syn, stt);
      DataValue::OfSyntax(stt.env.store_blob(bytes))
    },
  }
}

/// Serialize a Lean Syntax to bytes.
fn serialize_syntax(syn: &LeanSyntax, stt: &CompileState) -> Vec<u8> {
  let mut bytes = Vec::new();
  serialize_syntax_inner(syn, stt, &mut bytes);
  bytes
}

fn serialize_syntax_inner(
  syn: &LeanSyntax,
  stt: &CompileState,
  bytes: &mut Vec<u8>,
) {
  match syn {
    LeanSyntax::Missing => bytes.push(0),
    LeanSyntax::Node(info, kind, args) => {
      bytes.push(1);
      serialize_source_info(info, stt, bytes);
      bytes.extend_from_slice(compile_name(kind, stt).as_bytes());
      TagN::put(0, 0, args.len() as u64, bytes);
      for arg in args {
        serialize_syntax_inner(arg, stt, bytes);
      }
    },
    LeanSyntax::Atom(info, val) => {
      bytes.push(2);
      serialize_source_info(info, stt, bytes);
      bytes.extend_from_slice(store_string(val, stt).as_bytes());
    },
    LeanSyntax::Ident(info, raw_val, val, preresolved) => {
      bytes.push(3);
      serialize_source_info(info, stt, bytes);
      serialize_substring(raw_val, stt, bytes);
      bytes.extend_from_slice(compile_name(val, stt).as_bytes());
      TagN::put(0, 0, preresolved.len() as u64, bytes);
      for pr in preresolved {
        serialize_preresolved(pr, stt, bytes);
      }
    },
  }
}

fn serialize_source_info(
  info: &LeanSourceInfo,
  stt: &CompileState,
  bytes: &mut Vec<u8>,
) {
  match info {
    LeanSourceInfo::Original(leading, leading_pos, trailing, trailing_pos) => {
      bytes.push(0);
      serialize_substring(leading, stt, bytes);
      // u64::MAX sentinel for positions that overflow u64 (should never happen in practice)
      TagN::put(0, 0, leading_pos.to_u64().unwrap_or(u64::MAX), bytes);
      serialize_substring(trailing, stt, bytes);
      TagN::put(0, 0, trailing_pos.to_u64().unwrap_or(u64::MAX), bytes);
    },
    LeanSourceInfo::Synthetic(start, end, canonical) => {
      bytes.push(1);
      TagN::put(0, 0, start.to_u64().unwrap_or(u64::MAX), bytes);
      TagN::put(0, 0, end.to_u64().unwrap_or(u64::MAX), bytes);
      bytes.push(if *canonical { 1 } else { 0 });
    },
    LeanSourceInfo::None => bytes.push(2),
  }
}

fn serialize_substring(
  ss: &LeanSubstring,
  stt: &CompileState,
  bytes: &mut Vec<u8>,
) {
  bytes.extend_from_slice(store_string(&ss.str, stt).as_bytes());
  TagN::put(0, 0, ss.start_pos.to_u64().unwrap_or(u64::MAX), bytes);
  TagN::put(0, 0, ss.stop_pos.to_u64().unwrap_or(u64::MAX), bytes);
}

fn serialize_preresolved(
  pr: &SyntaxPreresolved,
  stt: &CompileState,
  bytes: &mut Vec<u8>,
) {
  match pr {
    SyntaxPreresolved::Namespace(n) => {
      bytes.push(0);
      bytes.extend_from_slice(compile_name(n, stt).as_bytes());
    },
    SyntaxPreresolved::Decl(n, fields) => {
      bytes.push(1);
      bytes.extend_from_slice(compile_name(n, stt).as_bytes());
      TagN::put(0, 0, fields.len() as u64, bytes);
      for f in fields {
        bytes.extend_from_slice(store_string(f, stt).as_bytes());
      }
    },
  }
}

// ===========================================================================
// Canonical sharing
// ===========================================================================

// The compiler shares every block with the canonical tiered construction
// (`canonical_sharing_tiered`, TagN layout). Every construction error,
// resource exhaustion included, is a compile error: there is no fallback.
// Mirrors `Ix.CompileM.buildConstantWithSharing`.

/// Environment variable carrying a sharing-limit override in the format of
/// [`ExactSharingLimits::with_overrides`] (for example
/// `states=2^44,height=2^34` or `unbounded`). `ix compile --sharing-limits`
/// and `ix compile-lean --sharing-limits` set it. Mirrors Lean
/// `Ix.CompileM.sharingLimitsEnvVar`.
pub const SHARING_LIMITS_ENV: &str = "IX_SHARING_LIMITS";

/// The [`ExactSharingLimits`] defaults with the override `spec` applied.
pub fn compiler_sharing_limits_with(
  spec: Option<&str>,
) -> Result<ExactSharingLimits, String> {
  let limits = ExactSharingLimits::default();
  match spec {
    None => Ok(limits),
    Some(spec) => limits
      .with_overrides(spec)
      .map_err(|e| format!("{SHARING_LIMITS_ENV}: {e}")),
  }
}

/// Resource limits of the compiler's canonical sharing construction: the
/// [`ExactSharingLimits`] defaults (a safety net far above every corpus
/// maximum) with the [`SHARING_LIMITS_ENV`] override. Each entry point reads
/// it once and carries the result ([`CompileState::sharing_limits`]), so an
/// invalid override fails the run once, before any block is shared. Mirrors
/// `Ix.CompileM.compilerSharingLimitsFromEnv`.
pub fn compiler_sharing_limits() -> Result<ExactSharingLimits, String> {
  compiler_sharing_limits_with(
    std::env::var(SHARING_LIMITS_ENV).ok().as_deref(),
  )
}

/// A sharing-construction failure as a compile error: resource exhaustion is
/// `ResourceLimit` (naming the limit and how to raise it), every other kind
/// `SharingConstruction`. Mirrors `Ix.CompileM.sharingCompileError`.
fn sharing_compile_error(e: SharingError) -> CompileError {
  match e {
    SharingError::ResourceExhausted(r) => CompileError::ResourceLimit {
      reason: format!(
        "canonical sharing: {e}; raise it with --sharing-limits {}=N \
         ({SHARING_LIMITS_ENV})",
        r.resource.key()
      ),
    },
    other => CompileError::SharingConstruction {
      reason: format!("canonical sharing: {other}"),
    },
  }
}

/// Share the ordered roots of one block: the rewritten roots (same order and
/// count) and the sharing table.
fn share_roots(
  limits: &ExactSharingLimits,
  exprs: &[Arc<Expr>],
) -> Result<(Vec<Arc<Expr>>, Vec<Arc<Expr>>), CompileError> {
  let res = canonical_sharing_tiered(ShareLayout::TagN, exprs, limits)
    .map_err(sharing_compile_error)?;
  if res.roots.len() != exprs.len() {
    return Err(CompileError::SharingConstruction {
      reason: format!(
        "canonical sharing returned {} roots for {}",
        res.roots.len(),
        exprs.len()
      ),
    });
  }
  Ok((res.roots, res.sharing))
}

/// Apply the compiler's sharing under `limits` (a compile passes
/// [`CompileState::sharing_limits`]) to a definition payload.
#[allow(clippy::needless_pass_by_value)]
pub fn apply_sharing_to_definition_with_limits(
  limits: &ExactSharingLimits,
  def: Definition,
  refs: Vec<Address>,
  univs: Vec<Arc<Univ>>,
) -> Result<Constant, CompileError> {
  let (roots, sharing) =
    share_roots(limits, &[def.typ.clone(), def.value.clone()])?;
  let def = Definition {
    kind: def.kind,
    safety: def.safety,
    lvls: def.lvls,
    typ: roots[0].clone(),
    value: roots[1].clone(),
  };
  let constant =
    Constant::with_tables(ConstantInfo::Defn(def), sharing, refs, univs);
  Ok(constant)
}

/// Apply the compiler's sharing under `limits` to an axiom payload.
#[allow(clippy::needless_pass_by_value)]
pub fn apply_sharing_to_axiom_with_limits(
  limits: &ExactSharingLimits,
  ax: Axiom,
  refs: Vec<Address>,
  univs: Vec<Arc<Univ>>,
) -> Result<Constant, CompileError> {
  let (roots, sharing) = share_roots(limits, std::slice::from_ref(&ax.typ))?;
  let ax =
    Axiom { is_unsafe: ax.is_unsafe, lvls: ax.lvls, typ: roots[0].clone() };
  let constant =
    Constant::with_tables(ConstantInfo::Axio(ax), sharing, refs, univs);
  Ok(constant)
}

/// Apply the compiler's sharing under `limits` to a quotient payload.
#[allow(clippy::needless_pass_by_value)]
pub fn apply_sharing_to_quotient_with_limits(
  limits: &ExactSharingLimits,
  quot: Quotient,
  refs: Vec<Address>,
  univs: Vec<Arc<Univ>>,
) -> Result<Constant, CompileError> {
  let (roots, sharing) = share_roots(limits, std::slice::from_ref(&quot.typ))?;
  let quot =
    Quotient { kind: quot.kind, lvls: quot.lvls, typ: roots[0].clone() };
  let constant =
    Constant::with_tables(ConstantInfo::Quot(quot), sharing, refs, univs);
  Ok(constant)
}

/// Apply the compiler's sharing under `limits` to a recursor payload.
pub fn apply_sharing_to_recursor_with_limits(
  limits: &ExactSharingLimits,
  rec: Recursor,
  refs: Vec<Address>,
  univs: Vec<Arc<Univ>>,
) -> Result<Constant, CompileError> {
  // The roots: typ, then every rule rhs.
  let mut exprs = vec![rec.typ.clone()];
  for rule in &rec.rules {
    exprs.push(rule.rhs.clone());
  }

  let (roots, sharing) = share_roots(limits, &exprs)?;
  let typ = roots[0].clone();
  let rules: Vec<RecursorRule> = rec
    .rules
    .into_iter()
    .zip(roots.into_iter().skip(1))
    .map(|(r, rhs)| RecursorRule { fields: r.fields, rhs })
    .collect();

  let rec = Recursor {
    k: rec.k,
    is_unsafe: rec.is_unsafe,
    lvls: rec.lvls,
    params: rec.params,
    indices: rec.indices,
    motives: rec.motives,
    minors: rec.minors,
    typ,
    rules,
  };
  let constant =
    Constant::with_tables(ConstantInfo::Recr(rec), sharing, refs, univs);
  Ok(constant)
}

/// Apply the compiler's sharing under `limits` to a mutual block: one sharing
/// table for the roots of every member, in member order.
pub fn apply_sharing_to_mutual_block_with_limits(
  limits: &ExactSharingLimits,
  mut_consts: Vec<IxonMutConst>,
  refs: Vec<Address>,
  univs: Vec<Arc<Univ>>,
) -> Result<Constant, CompileError> {
  // The roots of every member, in member order.
  let mut all_exprs: Vec<Arc<Expr>> = Vec::new();
  let mut layout: Vec<(MutConstKind, Vec<usize>)> = Vec::new();

  for mc in &mut_consts {
    let (kind, indices) = match mc {
      IxonMutConst::Defn(def) => {
        let start = all_exprs.len();
        all_exprs.push(def.typ.clone());
        all_exprs.push(def.value.clone());
        (MutConstKind::Defn, vec![start, start + 1])
      },
      IxonMutConst::Indc(ind) => {
        let start = all_exprs.len();
        all_exprs.push(ind.typ.clone());
        let mut indices = vec![start];
        for ctor in &ind.ctors {
          indices.push(all_exprs.len());
          all_exprs.push(ctor.typ.clone());
        }
        (MutConstKind::Indc, indices)
      },
      IxonMutConst::Recr(rec) => {
        let start = all_exprs.len();
        all_exprs.push(rec.typ.clone());
        let mut indices = vec![start];
        for rule in &rec.rules {
          indices.push(all_exprs.len());
          all_exprs.push(rule.rhs.clone());
        }
        (MutConstKind::Recr, indices)
      },
    };
    layout.push((kind, indices));
  }

  // One sharing table for the whole block.
  let (rewritten, sharing) = share_roots(limits, &all_exprs)?;

  // Rebuild the constants with rewritten expressions
  let mut new_consts = Vec::with_capacity(mut_consts.len());
  for (i, mc) in mut_consts.into_iter().enumerate() {
    let (kind, indices) = &layout[i];
    let new_mc = match (kind, mc) {
      (MutConstKind::Defn, IxonMutConst::Defn(def)) => {
        IxonMutConst::Defn(Definition {
          kind: def.kind,
          safety: def.safety,
          lvls: def.lvls,
          typ: rewritten[indices[0]].clone(),
          value: rewritten[indices[1]].clone(),
        })
      },
      (MutConstKind::Indc, IxonMutConst::Indc(ind)) => {
        let new_ctors: Vec<Constructor> = ind
          .ctors
          .into_iter()
          .enumerate()
          .map(|(ci, ctor)| Constructor {
            is_unsafe: ctor.is_unsafe,
            lvls: ctor.lvls,
            cidx: ctor.cidx,
            params: ctor.params,
            fields: ctor.fields,
            typ: rewritten[indices[ci + 1]].clone(),
          })
          .collect();
        IxonMutConst::Indc(Inductive {
          is_unsafe: ind.is_unsafe,
          lvls: ind.lvls,
          params: ind.params,
          indices: ind.indices,
          typ: rewritten[indices[0]].clone(),
          ctors: new_ctors,
        })
      },
      (MutConstKind::Recr, IxonMutConst::Recr(rec)) => {
        let new_rules: Vec<RecursorRule> = rec
          .rules
          .into_iter()
          .enumerate()
          .map(|(ri, rule)| RecursorRule {
            fields: rule.fields,
            rhs: rewritten[indices[ri + 1]].clone(),
          })
          .collect();
        IxonMutConst::Recr(Recursor {
          k: rec.k,
          is_unsafe: rec.is_unsafe,
          lvls: rec.lvls,
          params: rec.params,
          indices: rec.indices,
          motives: rec.motives,
          minors: rec.minors,
          typ: rewritten[indices[0]].clone(),
          rules: new_rules,
        })
      },
      _ => unreachable!("layout mismatch"),
    };
    new_consts.push(new_mc);
  }

  let constant =
    Constant::with_tables(ConstantInfo::Muts(new_consts), sharing, refs, univs);
  Ok(constant)
}

/// Helper enum for tracking mutual constant layout during sharing.
#[derive(Clone, Copy)]
enum MutConstKind {
  Defn,
  Indc,
  Recr,
}

// ===========================================================================
// Constant compilation
// ===========================================================================

/// Compile a Definition.
/// Arena persists across type + value within a constant.
pub fn compile_definition(
  def: &Def,
  mut_ctx: &MutCtx,
  ctx_addrs: &[Address],
  cache: &mut BlockCache,
  stt: &CompileState,
) -> Result<(Definition, ConstantMeta), CompileError> {
  cache.compiling = Some(def.name.clone());
  let univ_params = &def.level_params;

  // Compile type expression (arena grows)
  let typ = compile_expr(&def.typ, univ_params, mut_ctx, cache, stt)?;
  let type_root = *cache.arena_roots.last().expect("missing type arena root");

  // Compile value expression (arena continues growing)
  let value = compile_expr(&def.value, univ_params, mut_ctx, cache, stt)?;
  let value_root = *cache.arena_roots.last().expect("missing value arena root");

  // Take arena, meta sharing, and level-spelling channels (canonicity
  // §10.6), clear for next constant
  let arena = std::mem::take(&mut cache.arena);
  let meta_sharing = std::mem::take(&mut cache.meta_sharing);
  let p3_meta_refs: Vec<Address> =
    std::mem::take(&mut cache.p3_meta_refs).into_iter().collect();
  cache.p3_records.clear();
  let meta_univs: Vec<Arc<Univ>> =
    std::mem::take(&mut cache.meta_univs).into_iter().collect();
  let univ_patches = std::mem::take(&mut cache.univ_patches);
  cache.arena_roots.clear();
  cache.exprs.clear();

  let name_addr = compile_name(&def.name, stt);
  let lvl_addrs: Vec<Address> =
    univ_params.iter().map(|n| compile_name(n, stt)).collect();
  let all_addrs: Vec<Address> =
    def.all.iter().map(|n| compile_name(n, stt)).collect();
  let ctx_addrs: Vec<Address> = ctx_addrs.to_vec();

  let data = Definition {
    kind: def.kind,
    safety: def.safety,
    lvls: def.level_params.len() as u64,
    typ,
    value,
  };

  let mut meta = ConstantMeta::new(ConstantMetaInfo::Def {
    name: name_addr,
    lvls: lvl_addrs,
    all: all_addrs,
    ctx: ctx_addrs,
    arena,
    type_root,
    value_root,
  });
  meta.meta_sharing = meta_sharing;
  meta.meta_refs = p3_meta_refs;
  meta.meta_univs = meta_univs;
  meta.univ_patches = univ_patches;
  stt.record_hint(&def.name, Some(def.hints));

  Ok((data, meta))
}

/// Compile a RecursorRule.
fn compile_recursor_rule(
  rule: &LeanRecursorRule,
  univ_params: &[Name],
  mut_ctx: &MutCtx,
  cache: &mut BlockCache,
  stt: &CompileState,
) -> Result<(RecursorRule, Address), CompileError> {
  let rhs = compile_expr(&rule.rhs, univ_params, mut_ctx, cache, stt)?;
  let ctor_addr = compile_name(&rule.ctor, stt);
  let fields = nat_to_u64(&rule.n_fields, "n_fields too large")?;

  Ok((RecursorRule { fields, rhs }, ctor_addr))
}

/// Compile a Recursor.
/// Arena grows across type and all rule RHS expressions.
pub fn compile_recursor(
  rec: &Rec,
  mut_ctx: &MutCtx,
  ctx_addrs: &[Address],
  cache: &mut BlockCache,
  stt: &CompileState,
) -> Result<(Recursor, ConstantMeta), CompileError> {
  cache.compiling = Some(rec.cnst.name.clone());
  let univ_params = &rec.cnst.level_params;

  // Compile type expression
  let typ = compile_expr(&rec.cnst.typ, univ_params, mut_ctx, cache, stt)?;
  let type_root =
    *cache.arena_roots.last().expect("missing recursor type arena root");

  let mut rules = Vec::with_capacity(rec.rules.len());
  let mut rule_addrs = Vec::new();
  let mut rule_roots = Vec::new();
  for rule in &rec.rules {
    let (r, ctor_addr) =
      compile_recursor_rule(rule, univ_params, mut_ctx, cache, stt)?;
    rule_roots
      .push(*cache.arena_roots.last().expect("missing rule arena root"));
    rule_addrs.push(ctor_addr);
    rules.push(r);
  }

  // Take arena and meta sharing, clear for next constant.
  // Rule RHS bodies can contain surgered call-sites (a recursor rule for
  // ctor C may reference another alpha-collapsed auxiliary), so any
  // collapsed args accumulated during rule compilation must be attached
  // to THIS recursor's meta — not left behind to corrupt the next
  // constant's `sharing_idx` offsets. Level-spelling channels (canonicity
  // §10.6) drain on the same boundary for the same reason.
  let arena = std::mem::take(&mut cache.arena);
  let meta_sharing = std::mem::take(&mut cache.meta_sharing);
  let p3_meta_refs: Vec<Address> =
    std::mem::take(&mut cache.p3_meta_refs).into_iter().collect();
  cache.p3_records.clear();
  let meta_univs: Vec<Arc<Univ>> =
    std::mem::take(&mut cache.meta_univs).into_iter().collect();
  let univ_patches = std::mem::take(&mut cache.univ_patches);
  cache.arena_roots.clear();
  cache.exprs.clear();

  let name_addr = compile_name(&rec.cnst.name, stt);
  let lvl_addrs: Vec<Address> =
    univ_params.iter().map(|n| compile_name(n, stt)).collect();

  let data = Recursor {
    k: rec.k,
    is_unsafe: rec.is_unsafe,
    lvls: univ_params.len() as u64,
    params: nat_to_u64(&rec.num_params, "num_params too large")?,
    indices: nat_to_u64(&rec.num_indices, "num_indices too large")?,
    motives: nat_to_u64(&rec.num_motives, "num_motives too large")?,
    minors: nat_to_u64(&rec.num_minors, "num_minors too large")?,
    typ,
    rules,
  };

  let all_addrs: Vec<Address> =
    rec.all.iter().map(|n| compile_name(n, stt)).collect();
  let ctx_addrs: Vec<Address> = ctx_addrs.to_vec();

  let mut meta = ConstantMeta::new(ConstantMetaInfo::Rec {
    name: name_addr,
    lvls: lvl_addrs,
    rules: rule_addrs,
    all: all_addrs,
    ctx: ctx_addrs,
    arena,
    type_root,
    rule_roots,
  });
  meta.meta_sharing = meta_sharing;
  meta.meta_refs = p3_meta_refs;
  meta.meta_univs = meta_univs;
  meta.univ_patches = univ_patches;

  Ok((data, meta))
}

/// Compile a Constructor.
/// Each constructor gets its own arena.
fn compile_constructor(
  ctor: &ConstructorVal,
  mut_ctx: &MutCtx,
  cache: &mut BlockCache,
  stt: &CompileState,
) -> Result<(Constructor, ConstantMeta), CompileError> {
  cache.compiling = Some(ctor.cnst.name.clone());
  let univ_params = &ctor.cnst.level_params;

  let typ = compile_expr(&ctor.cnst.typ, univ_params, mut_ctx, cache, stt)?;
  let type_root =
    *cache.arena_roots.last().expect("missing ctor type arena root");

  // Take arena and meta sharing for this constructor. A ctor's type
  // may contain surgered call-sites when the ctor's field types reference
  // alpha-collapsed auxiliaries, so drain here to attach to THIS ctor's
  // meta rather than leaking into whichever constant comes next.
  // Level-spelling channels (canonicity §10.6) drain on the same
  // boundary — the decompiler's ctor-scoped window installs them per
  // constructor.
  let arena = std::mem::take(&mut cache.arena);
  let meta_sharing = std::mem::take(&mut cache.meta_sharing);
  let p3_meta_refs: Vec<Address> =
    std::mem::take(&mut cache.p3_meta_refs).into_iter().collect();
  cache.p3_records.clear();
  let meta_univs: Vec<Arc<Univ>> =
    std::mem::take(&mut cache.meta_univs).into_iter().collect();
  let univ_patches = std::mem::take(&mut cache.univ_patches);
  cache.arena_roots.clear();
  cache.exprs.clear();

  let name_addr = compile_name(&ctor.cnst.name, stt);
  let lvl_addrs: Vec<Address> =
    univ_params.iter().map(|n| compile_name(n, stt)).collect();
  let induct_addr = compile_name(&ctor.induct, stt);

  let data = Constructor {
    is_unsafe: ctor.is_unsafe,
    lvls: univ_params.len() as u64,
    cidx: nat_to_u64(&ctor.cidx, "cidx too large")?,
    params: nat_to_u64(&ctor.num_params, "ctor num_params too large")?,
    fields: nat_to_u64(&ctor.num_fields, "num_fields too large")?,
    typ,
  };

  let mut meta = ConstantMeta::new(ConstantMetaInfo::Ctor {
    name: name_addr,
    lvls: lvl_addrs,
    induct: induct_addr,
    arena,
    type_root,
  });
  meta.meta_sharing = meta_sharing;
  meta.meta_refs = p3_meta_refs;
  meta.meta_univs = meta_univs;
  meta.univ_patches = univ_patches;

  Ok((data, meta))
}

/// Compile an Inductive.
/// The inductive type gets its own arena. Each constructor gets its own arena
/// via compile_constructor. No CtorMeta duplication — ConstantMeta::Indc only
/// stores constructor name addresses.
pub fn compile_inductive(
  ind: &Ind,
  mut_ctx: &MutCtx,
  ctx_addrs: &[Address],
  cache: &mut BlockCache,
  stt: &CompileState,
) -> Result<(Inductive, ConstantMeta, Vec<ConstantMeta>), CompileError> {
  cache.compiling = Some(ind.ind.cnst.name.clone());
  let univ_params = &ind.ind.cnst.level_params;

  // Compile inductive type
  let typ = compile_expr(&ind.ind.cnst.typ, univ_params, mut_ctx, cache, stt)?;
  let type_root =
    *cache.arena_roots.last().expect("missing indc type arena root");

  // Take arena and meta sharing for the inductive's OWN type. Any
  // surgered call-sites accumulated while compiling `ind.ind.cnst.typ`
  // belong to this inductive's meta. Ctor meta_sharing is handled
  // separately by `compile_constructor` below — each ctor attaches its
  // own sharing to its own meta. Level-spelling channels (canonicity
  // §10.6) split on the same boundary.
  let indc_arena = std::mem::take(&mut cache.arena);
  let indc_meta_sharing = std::mem::take(&mut cache.meta_sharing);
  let p3_meta_refs: Vec<Address> =
    std::mem::take(&mut cache.p3_meta_refs).into_iter().collect();
  cache.p3_records.clear();
  let indc_meta_univs: Vec<Arc<Univ>> =
    std::mem::take(&mut cache.meta_univs).into_iter().collect();
  let indc_univ_patches = std::mem::take(&mut cache.univ_patches);
  cache.arena_roots.clear();
  cache.exprs.clear();

  let mut ctors = Vec::with_capacity(ind.ctors.len());
  let mut ctor_const_metas = Vec::new();
  let mut ctor_name_addrs = Vec::new();
  for ctor in &ind.ctors {
    let (c, m) = compile_constructor(ctor, mut_ctx, cache, stt)?;
    let ctor_name_addr = compile_name(&ctor.cnst.name, stt);
    ctor_name_addrs.push(ctor_name_addr);
    ctor_const_metas.push(m);
    ctors.push(c);
  }

  let name_addr = compile_name(&ind.ind.cnst.name, stt);
  let lvl_addrs: Vec<Address> =
    univ_params.iter().map(|n| compile_name(n, stt)).collect();

  let data = Inductive {
    is_unsafe: ind.ind.is_unsafe,
    lvls: univ_params.len() as u64,
    params: nat_to_u64(&ind.ind.num_params, "inductive num_params too large")?,
    indices: nat_to_u64(
      &ind.ind.num_indices,
      "inductive num_indices too large",
    )?,
    typ,
    ctors,
  };

  let all_addrs: Vec<Address> =
    ind.ind.all.iter().map(|n| compile_name(n, stt)).collect();
  let ctx_addrs: Vec<Address> = ctx_addrs.to_vec();

  let mut meta = ConstantMeta::new(ConstantMetaInfo::Indc {
    name: name_addr,
    lvls: lvl_addrs,
    ctors: ctor_name_addrs,
    all: all_addrs,
    ctx: ctx_addrs,
    arena: indc_arena,
    type_root,
  });
  meta.meta_sharing = indc_meta_sharing;
  meta.meta_refs = p3_meta_refs;
  meta.meta_univs = indc_meta_univs;
  meta.univ_patches = indc_univ_patches;

  Ok((data, meta, ctor_const_metas))
}

/// Compile an Axiom.
fn compile_axiom(
  val: &AxiomVal,
  cache: &mut BlockCache,
  stt: &CompileState,
) -> Result<(Axiom, ConstantMeta), CompileError> {
  cache.compiling = Some(val.cnst.name.clone());
  let univ_params = &val.cnst.level_params;

  let typ =
    compile_expr(&val.cnst.typ, univ_params, &MutCtx::default(), cache, stt)?;
  let type_root =
    *cache.arena_roots.last().expect("missing axiom type arena root");

  // Drain meta sharing onto this axiom's meta. Axioms can reference
  // alpha-collapsed auxiliaries in their type; any collapsed args must
  // stay with this axiom rather than leak to the next constant. Same for
  // the level-spelling channels (canonicity §10.6).
  let arena = std::mem::take(&mut cache.arena);
  let meta_sharing = std::mem::take(&mut cache.meta_sharing);
  let p3_meta_refs: Vec<Address> =
    std::mem::take(&mut cache.p3_meta_refs).into_iter().collect();
  cache.p3_records.clear();
  let meta_univs: Vec<Arc<Univ>> =
    std::mem::take(&mut cache.meta_univs).into_iter().collect();
  let univ_patches = std::mem::take(&mut cache.univ_patches);
  cache.arena_roots.clear();
  cache.exprs.clear();

  let name_addr = compile_name(&val.cnst.name, stt);
  let lvl_addrs: Vec<Address> =
    univ_params.iter().map(|n| compile_name(n, stt)).collect();

  let data =
    Axiom { is_unsafe: val.is_unsafe, lvls: univ_params.len() as u64, typ };

  let mut meta = ConstantMeta::new(ConstantMetaInfo::Axio {
    name: name_addr,
    lvls: lvl_addrs,
    arena,
    type_root,
  });
  meta.meta_sharing = meta_sharing;
  meta.meta_refs = p3_meta_refs;
  meta.meta_univs = meta_univs;
  meta.univ_patches = univ_patches;

  Ok((data, meta))
}

/// Compile a Quotient.
fn compile_quotient(
  val: &QuotVal,
  cache: &mut BlockCache,
  stt: &CompileState,
) -> Result<(Quotient, ConstantMeta), CompileError> {
  cache.compiling = Some(val.cnst.name.clone());
  let univ_params = &val.cnst.level_params;

  let typ =
    compile_expr(&val.cnst.typ, univ_params, &MutCtx::default(), cache, stt)?;
  let type_root =
    *cache.arena_roots.last().expect("missing quot type arena root");

  // Drain meta sharing onto this quotient's meta — same reasoning as
  // in compile_axiom / compile_recursor / etc.: keep collapsed args
  // attached to the constant whose compilation produced them. Same for
  // the level-spelling channels (canonicity §10.6).
  let arena = std::mem::take(&mut cache.arena);
  let meta_sharing = std::mem::take(&mut cache.meta_sharing);
  let p3_meta_refs: Vec<Address> =
    std::mem::take(&mut cache.p3_meta_refs).into_iter().collect();
  cache.p3_records.clear();
  let meta_univs: Vec<Arc<Univ>> =
    std::mem::take(&mut cache.meta_univs).into_iter().collect();
  let univ_patches = std::mem::take(&mut cache.univ_patches);
  cache.arena_roots.clear();
  cache.exprs.clear();

  let name_addr = compile_name(&val.cnst.name, stt);
  let lvl_addrs: Vec<Address> =
    univ_params.iter().map(|n| compile_name(n, stt)).collect();

  let data = Quotient { kind: val.kind, lvls: univ_params.len() as u64, typ };

  let mut meta = ConstantMeta::new(ConstantMetaInfo::Quot {
    name: name_addr,
    lvls: lvl_addrs,
    arena,
    type_root,
  });
  meta.meta_sharing = meta_sharing;
  meta.meta_refs = p3_meta_refs;
  meta.meta_univs = meta_univs;
  meta.univ_patches = univ_patches;

  Ok((data, meta))
}

// ===========================================================================
// Mutual block compilation
// ===========================================================================

/// Result of compiling a mutual block.
pub struct CompiledMutualBlock {
  /// The compiled Constant
  pub constant: Constant,
  /// Content-addressed hash
  pub addr: Address,
}

/// Compile a mutual block with block-level sharing under `limits`.
/// Returns the Constant and its content-addressed hash.
pub fn compile_mutual_block(
  limits: &ExactSharingLimits,
  mut_consts: Vec<IxonMutConst>,
  refs: Vec<Address>,
  univs: Vec<Arc<Univ>>,
) -> Result<CompiledMutualBlock, CompileError> {
  // One sharing table across all expressions of the mutual block.
  let constant =
    apply_sharing_to_mutual_block_with_limits(limits, mut_consts, refs, univs)?;

  let mut bytes = Vec::new();
  constant.put(&mut bytes);
  let addr = Address::hash(&bytes);

  Ok(CompiledMutualBlock { constant, addr })
}

/// Create Inductive from InductiveVal and Env.
pub fn mk_indc(
  ind: &InductiveVal,
  env: &Arc<LeanEnv>,
) -> Result<Ind, CompileError> {
  let mut ctors = Vec::with_capacity(ind.ctors.len());
  for ctor_name in &ind.ctors {
    if let Some(LeanConstantInfo::CtorInfo(c)) =
      env.as_ref().get(ctor_name).as_deref()
    {
      ctors.push(c.clone());
    } else {
      return Err(CompileError::MissingConstant {
        name: ctor_name.pretty(),
        caller: "mk_indc(ctor_lookup)".into(),
      });
    }
  }
  Ok(Ind { ind: ind.clone(), ctors })
}

// ===========================================================================
// Alpha-invariant comparison and sorting
//
// These functions establish a canonical ordering for constants within mutual
// blocks. Since names are not alpha-invariant, we compare by structure:
// universe levels, expressions, field counts, etc. The `SOrd` return type
// tracks whether the comparison is "strong" (based solely on alpha-invariant
// data) or "weak" (needed a name-based tiebreaker).
// ===========================================================================

/// Compare two universe levels after `canon_univ`, with level parameters by
/// position (not name): both levels are compiled to `Univ` (parameter `i`
/// of its context is `Var(i)`), put in canonical form, and compared
/// structurally with the constructor order `Zero < Succ < Max < IMax < Var`.
///
/// Phase A decision (design document §2.8, A2-order; Lean
/// `Ix.Compile.Canon.compareLevel .afterCanonUniv`): collapse is equality of
/// compiled content, and the stored universes are canonical forms, so the
/// order does not depend on how a level was spelled. Before A2-order the
/// levels were compared syntactically; the A1C census measured that the
/// change moves no block or clique order in Init+Std or Mathlib.
pub fn compare_level(
  x: &Level,
  y: &Level,
  x_ctx: &[Name],
  y_ctx: &[Name],
) -> Result<SOrd, CompileError> {
  let ux = canon_univ(&level_to_univ(x, x_ctx)?);
  let uy = canon_univ(&level_to_univ(y, y_ctx)?);
  Ok(SOrd { strong: true, ordering: compare_univ(&ux, &uy) })
}

/// A level as a `Univ` with parameters by position, without simplification
/// (Lean `Ix.Compile.Canon.toUniv`).
fn level_to_univ(l: &Level, ctx: &[Name]) -> Result<Arc<Univ>, CompileError> {
  Ok(match l.as_data() {
    LevelData::Zero(_) => Univ::zero(),
    LevelData::Succ(a, _) => Univ::succ(level_to_univ(a, ctx)?),
    LevelData::Max(a, b, _) => {
      Univ::max(level_to_univ(a, ctx)?, level_to_univ(b, ctx)?)
    },
    LevelData::Imax(a, b, _) => {
      Univ::imax(level_to_univ(a, ctx)?, level_to_univ(b, ctx)?)
    },
    LevelData::Param(n, _) => {
      let i = ctx.iter().position(|m| m == n).ok_or_else(|| {
        CompileError::UnknownUnivParam {
          curr: String::new(),
          param: n.pretty(),
        }
      })?;
      Univ::var(i as u64)
    },
    LevelData::Mvar(..) => {
      return Err(CompileError::UnsupportedExpr {
        desc: "level metavariable in comparison".into(),
      });
    },
  })
}

/// Structural order on `Univ`: `Zero < Succ < Max < IMax < Var`, arguments
/// left to right, variables by index (Lean `Ix.Compile.Canon.compareUniv`;
/// the kernels' `compare_kuniv` and the certified `compareUniverse`).
fn compare_univ(x: &Univ, y: &Univ) -> Ordering {
  fn rank(u: &Univ) -> u8 {
    match u {
      Univ::Zero => 0,
      Univ::Succ(_) => 1,
      Univ::Max(..) => 2,
      Univ::IMax(..) => 3,
      Univ::Var(_) => 4,
    }
  }
  match (x, y) {
    (Univ::Succ(a), Univ::Succ(b)) => compare_univ(a, b),
    (Univ::Max(a, b), Univ::Max(c, d))
    | (Univ::IMax(a, b), Univ::IMax(c, d)) => {
      compare_univ(a, c).then_with(|| compare_univ(b, d))
    },
    (Univ::Var(i), Univ::Var(j)) => i.cmp(j),
    _ => rank(x).cmp(&rank(y)),
  }
}

/// Compare two non-mutual references by compiled address.
///
/// Canonical sorting must not fall back to name order here: unresolved names
/// would reintroduce namespace/source-order information into content hashes.
fn compare_external_refs(
  x: &Name,
  y: &Name,
  stt: &CompileState,
  caller: &'static str,
) -> Result<SOrd, CompileError> {
  match (stt.resolve_addr(x), stt.resolve_addr(y)) {
    (Some(xa), Some(ya)) => Ok(SOrd::cmp(&xa, &ya)),
    (None, _) => Err(CompileError::MissingConstant {
      name: x.pretty(),
      caller: caller.into(),
    }),
    (_, None) => Err(CompileError::MissingConstant {
      name: y.pretty(),
      caller: caller.into(),
    }),
  }
}

/// Compare two Lean expressions structurally for canonical ordering.
/// Strips `Mdata` wrappers, compares by constructor tag, then recurses
/// into subexpressions. Constants are compared by address (or mutual index).
pub fn compare_expr(
  x: &LeanExpr,
  y: &LeanExpr,
  mut_ctx: &MutCtx,
  x_lvls: &[Name],
  y_lvls: &[Name],
  stt: &CompileState,
) -> Result<SOrd, CompileError> {
  match (x.as_data(), y.as_data()) {
    (ExprData::Mvar(..), _) | (_, ExprData::Mvar(..)) => {
      Err(CompileError::UnsupportedExpr {
        desc: "metavariable in comparison".into(),
      })
    },
    (ExprData::Fvar(..), _) | (_, ExprData::Fvar(..)) => {
      Err(CompileError::UnsupportedExpr { desc: "fvar in comparison".into() })
    },
    (ExprData::Mdata(dx, xi, _), ExprData::Mdata(dy, yi, _)) => {
      if crate::semantic_contract::has_metadata(dx) {
        if crate::semantic_contract::has_metadata(dy) {
          let cx = crate::semantic_contract::read(dx)?;
          let cy = crate::semantic_contract::read(dy)?;
          let order = SOrd::cmp(&cx.order_key(), &cy.order_key());
          if order.ordering != Ordering::Equal {
            return Ok(order);
          }
          compare_expr(xi, yi, mut_ctx, x_lvls, y_lvls, stt)
        } else {
          compare_expr(x, yi, mut_ctx, x_lvls, y_lvls, stt)
        }
      } else {
        compare_expr(xi, y, mut_ctx, x_lvls, y_lvls, stt)
      }
    },
    (ExprData::Mdata(data, inner, _), _) => {
      if crate::semantic_contract::has_metadata(data) {
        Ok(SOrd::gt(true))
      } else {
        compare_expr(inner, y, mut_ctx, x_lvls, y_lvls, stt)
      }
    },
    (_, ExprData::Mdata(data, inner, _)) => {
      if crate::semantic_contract::has_metadata(data) {
        Ok(SOrd::lt(true))
      } else {
        compare_expr(x, inner, mut_ctx, x_lvls, y_lvls, stt)
      }
    },
    (ExprData::Bvar(x, _), ExprData::Bvar(y, _)) => Ok(SOrd::cmp(x, y)),
    (ExprData::Bvar(..), _) => Ok(SOrd::lt(true)),
    (_, ExprData::Bvar(..)) => Ok(SOrd::gt(true)),
    (ExprData::Sort(x, _), ExprData::Sort(y, _)) => {
      compare_level(x, y, x_lvls, y_lvls)
    },
    (ExprData::Sort(..), _) => Ok(SOrd::lt(true)),
    (_, ExprData::Sort(..)) => Ok(SOrd::gt(true)),
    (ExprData::Const(x, xls, _), ExprData::Const(y, yls, _)) => {
      let us =
        SOrd::try_zip(|a, b| compare_level(a, b, x_lvls, y_lvls), xls, yls)?;
      if us.ordering != Ordering::Equal {
        Ok(us)
      } else if x == y {
        Ok(SOrd::eq(true))
      } else {
        match (mut_ctx.get(x), mut_ctx.get(y)) {
          (Some(nx), Some(ny)) => Ok(SOrd::weak_cmp(nx, ny)),
          (Some(..), _) => Ok(SOrd::lt(true)),
          (None, Some(..)) => Ok(SOrd::gt(true)),
          (None, None) => {
            compare_external_refs(x, y, stt, "compare_expr(Const)")
          },
        }
      }
    },
    (ExprData::Const(..), _) => Ok(SOrd::lt(true)),
    (_, ExprData::Const(..)) => Ok(SOrd::gt(true)),
    (ExprData::App(xl, xr, _), ExprData::App(yl, yr, _)) => SOrd::try_compare(
      compare_expr(xl, yl, mut_ctx, x_lvls, y_lvls, stt)?,
      || compare_expr(xr, yr, mut_ctx, x_lvls, y_lvls, stt),
    ),
    (ExprData::App(..), _) => Ok(SOrd::lt(true)),
    (_, ExprData::App(..)) => Ok(SOrd::gt(true)),
    (ExprData::Lam(_, xt, xb, _, _), ExprData::Lam(_, yt, yb, _, _)) => {
      SOrd::try_compare(
        compare_expr(xt, yt, mut_ctx, x_lvls, y_lvls, stt)?,
        || compare_expr(xb, yb, mut_ctx, x_lvls, y_lvls, stt),
      )
    },
    (ExprData::Lam(..), _) => Ok(SOrd::lt(true)),
    (_, ExprData::Lam(..)) => Ok(SOrd::gt(true)),
    (
      ExprData::ForallE(_, xt, xb, _, _),
      ExprData::ForallE(_, yt, yb, _, _),
    ) => SOrd::try_compare(
      compare_expr(xt, yt, mut_ctx, x_lvls, y_lvls, stt)?,
      || compare_expr(xb, yb, mut_ctx, x_lvls, y_lvls, stt),
    ),
    (ExprData::ForallE(..), _) => Ok(SOrd::lt(true)),
    (_, ExprData::ForallE(..)) => Ok(SOrd::gt(true)),
    (
      ExprData::LetE(_, xt, xv, xb, xnd, _),
      ExprData::LetE(_, yt, yv, yb, ynd, _),
    ) => SOrd::try_compare(
      SOrd::try_zip(
        |a, b| compare_expr(a, b, mut_ctx, x_lvls, y_lvls, stt),
        &[xt, xv, xb],
        &[yt, yv, yb],
      )?,
      || Ok(SOrd::cmp(xnd, ynd)),
    ),
    (ExprData::LetE(..), _) => Ok(SOrd::lt(true)),
    (_, ExprData::LetE(..)) => Ok(SOrd::gt(true)),
    (ExprData::Lit(x, _), ExprData::Lit(y, _)) => Ok(SOrd::cmp(x, y)),
    (ExprData::Lit(..), _) => Ok(SOrd::lt(true)),
    (_, ExprData::Lit(..)) => Ok(SOrd::gt(true)),
    (ExprData::Proj(tnx, ix, tx, _), ExprData::Proj(tny, iy, ty, _)) => {
      let tn: Result<SOrd, CompileError> =
        match (mut_ctx.get(tnx), mut_ctx.get(tny)) {
          (Some(nx), Some(ny)) => Ok(SOrd::weak_cmp(nx, ny)),
          (Some(..), _) => Ok(SOrd::lt(true)),
          (None, Some(..)) => Ok(SOrd::gt(true)),
          (None, None) => {
            compare_external_refs(tnx, tny, stt, "compare_expr(Proj)")
          },
        };
      let tn = tn?;
      SOrd::try_compare(tn, || {
        SOrd::try_compare(SOrd::cmp(ix, iy), || {
          compare_expr(tx, ty, mut_ctx, x_lvls, y_lvls, stt)
        })
      })
    },
  }
}

// ===========================================================================
// Constant-level comparison and sorting
// ===========================================================================

/// Compare two definitions by kind, level parameter count, type, then value.
pub fn compare_defn(
  x: &Def,
  y: &Def,
  mut_ctx: &MutCtx,
  stt: &CompileState,
) -> Result<SOrd, CompileError> {
  SOrd::try_compare(
    SOrd { strong: true, ordering: x.kind.cmp(&y.kind) },
    || {
      SOrd::try_compare(
        SOrd::cmp(&x.level_params.len(), &y.level_params.len()),
        || {
          SOrd::try_compare(
            compare_expr(
              &x.typ,
              &y.typ,
              mut_ctx,
              &x.level_params,
              &y.level_params,
              stt,
            )?,
            || {
              compare_expr(
                &x.value,
                &y.value,
                mut_ctx,
                &x.level_params,
                &y.level_params,
                stt,
              )
            },
          )
        },
      )
    },
  )
}

/// Compare two constructors by level params, cidx, params, fields, then type.
pub fn compare_ctor_inner(
  x: &ConstructorVal,
  y: &ConstructorVal,
  mut_ctx: &MutCtx,
  stt: &CompileState,
) -> Result<SOrd, CompileError> {
  SOrd::try_compare(
    SOrd::cmp(&x.cnst.level_params.len(), &y.cnst.level_params.len()),
    || {
      SOrd::try_compare(SOrd::cmp(&x.cidx, &y.cidx), || {
        SOrd::try_compare(SOrd::cmp(&x.num_params, &y.num_params), || {
          SOrd::try_compare(SOrd::cmp(&x.num_fields, &y.num_fields), || {
            compare_expr(
              &x.cnst.typ,
              &y.cnst.typ,
              mut_ctx,
              &x.cnst.level_params,
              &y.cnst.level_params,
              stt,
            )
          })
        })
      })
    },
  )
}

/// Compare two constructors with result caching (keyed by name pair).
pub fn compare_ctor(
  x: &ConstructorVal,
  y: &ConstructorVal,
  mut_ctx: &MutCtx,
  cache: &mut BlockCache,
  stt: &CompileState,
) -> Result<SOrd, CompileError> {
  let (key, reversed) = if x.cnst.name <= y.cnst.name {
    ((x.cnst.name.clone(), y.cnst.name.clone()), false)
  } else {
    ((y.cnst.name.clone(), x.cnst.name.clone()), true)
  };
  if let Some(o) = cache.cmps.get(&key) {
    let ordering = if reversed { o.reverse() } else { *o };
    Ok(SOrd { strong: true, ordering })
  } else {
    let so = compare_ctor_inner(x, y, mut_ctx, stt)?;
    let stored = if reversed { so.ordering.reverse() } else { so.ordering };
    if so.strong {
      cache.cmps.insert(key, stored);
    }
    Ok(so)
  }
}

/// Compare two inductives by universe-parameter count, params, indices,
/// constructor count, type, then constructors, matching Lean's `compareInd`.
///
/// Recursion and safety flags remain inputs to validation, serialization and
/// auxiliary generation; they are not ordering keys. This comparator does not
/// validate a raw mutual block's flags.
pub fn compare_indc(
  x: &Ind,
  y: &Ind,
  mut_ctx: &MutCtx,
  cache: &mut BlockCache,
  stt: &CompileState,
) -> Result<SOrd, CompileError> {
  SOrd::try_compare(
    SOrd::cmp(&x.ind.cnst.level_params.len(), &y.ind.cnst.level_params.len()),
    || {
      SOrd::try_compare(SOrd::cmp(&x.ind.num_params, &y.ind.num_params), || {
        SOrd::try_compare(
          SOrd::cmp(&x.ind.num_indices, &y.ind.num_indices),
          || {
            SOrd::try_compare(
              SOrd::cmp(&x.ind.ctors.len(), &y.ind.ctors.len()),
              || {
                SOrd::try_compare(
                  compare_expr(
                    &x.ind.cnst.typ,
                    &y.ind.cnst.typ,
                    mut_ctx,
                    &x.ind.cnst.level_params,
                    &y.ind.cnst.level_params,
                    stt,
                  )?,
                  || {
                    SOrd::try_zip(
                      |a, b| compare_ctor(a, b, mut_ctx, cache, stt),
                      &x.ctors,
                      &y.ctors,
                    )
                  },
                )
              },
            )
          },
        )
      })
    },
  )
}

/// Compare two recursor rules by field count, then RHS expression.
pub fn compare_recr_rule(
  x: &LeanRecursorRule,
  y: &LeanRecursorRule,
  mut_ctx: &MutCtx,
  x_lvls: &[Name],
  y_lvls: &[Name],
  stt: &CompileState,
) -> Result<SOrd, CompileError> {
  SOrd::try_compare(SOrd::cmp(&x.n_fields, &y.n_fields), || {
    compare_expr(&x.rhs, &y.rhs, mut_ctx, x_lvls, y_lvls, stt)
  })
}

/// Compare two recursors by params, indices, motives, minors, k, type, then rules.
pub fn compare_recr(
  x: &Rec,
  y: &Rec,
  mut_ctx: &MutCtx,
  stt: &CompileState,
) -> Result<SOrd, CompileError> {
  SOrd::try_compare(
    SOrd::cmp(&x.cnst.level_params.len(), &y.cnst.level_params.len()),
    || {
      SOrd::try_compare(SOrd::cmp(&x.num_params, &y.num_params), || {
        SOrd::try_compare(SOrd::cmp(&x.num_indices, &y.num_indices), || {
          SOrd::try_compare(SOrd::cmp(&x.num_motives, &y.num_motives), || {
            SOrd::try_compare(SOrd::cmp(&x.num_minors, &y.num_minors), || {
              SOrd::try_compare(SOrd::cmp(&x.k, &y.k), || {
                SOrd::try_compare(
                  compare_expr(
                    &x.cnst.typ,
                    &y.cnst.typ,
                    mut_ctx,
                    &x.cnst.level_params,
                    &y.cnst.level_params,
                    stt,
                  )?,
                  || {
                    SOrd::try_zip(
                      |a, b| {
                        compare_recr_rule(
                          a,
                          b,
                          mut_ctx,
                          &x.cnst.level_params,
                          &y.cnst.level_params,
                          stt,
                        )
                      },
                      &x.rules,
                      &y.rules,
                    )
                  },
                )
              })
            })
          })
        })
      })
    },
  )
}

/// Returns a kind ordinal for cross-kind comparison of mutual constants.
fn mut_const_kind(c: &MutConst) -> u8 {
  match c {
    MutConst::Defn(_) => 0,
    MutConst::Indc(_) => 1,
    MutConst::Recr(_) => 2,
  }
}

/// Compare two mutual constants with caching. Dispatches to the appropriate
/// type-specific comparator (defn, indc, recr). Different-kind constants
/// are ordered by kind tag.
pub fn compare_const(
  x: &MutConst,
  y: &MutConst,
  mut_ctx: &MutCtx,
  cache: &mut BlockCache,
  stt: &CompileState,
) -> Result<Ordering, CompileError> {
  let (key, reversed) = if x.name() <= y.name() {
    ((x.name(), y.name()), false)
  } else {
    ((y.name(), x.name()), true)
  };
  if let Some(so) = cache.cmps.get(&key) {
    return Ok(if reversed { so.reverse() } else { *so });
  }
  let so: SOrd = match (x, y) {
    (MutConst::Defn(x), MutConst::Defn(y)) => compare_defn(x, y, mut_ctx, stt)?,
    (MutConst::Indc(x), MutConst::Indc(y)) => {
      compare_indc(x, y, mut_ctx, cache, stt)?
    },
    (MutConst::Recr(x), MutConst::Recr(y)) => compare_recr(x, y, mut_ctx, stt)?,
    _ => SOrd::cmp(&mut_const_kind(x), &mut_const_kind(y)),
  };
  if so.strong {
    cache.cmps.insert(key, so.ordering);
  }
  Ok(if reversed { so.ordering.reverse() } else { so.ordering })
}

/// Check if two mutual constants are structurally equal.
pub fn eq_const(
  x: &MutConst,
  y: &MutConst,
  mut_ctx: &MutCtx,
  cache: &mut BlockCache,
  stt: &CompileState,
) -> Result<bool, CompileError> {
  let ordering = compare_const(x, y, mut_ctx, cache, stt)?;
  Ok(ordering == Ordering::Equal)
}

/// Group consecutive equal elements in a sorted slice. Assumes the input
/// is already sorted by the same relation used for equality testing.
pub fn group_by<T, F>(
  items: Vec<&T>,
  mut eq: F,
) -> Result<Vec<Vec<&T>>, CompileError>
where
  F: FnMut(&T, &T) -> Result<bool, CompileError>,
{
  let mut groups = Vec::new();
  let mut current: Vec<&T> = Vec::new();
  for item in items {
    if let Some(last) = current.last() {
      if eq(last, item)? {
        current.push(item);
      } else {
        groups.push(std::mem::replace(&mut current, vec![item]));
      }
    } else {
      current.push(item);
    }
  }
  if !current.is_empty() {
    groups.push(current);
  }
  Ok(groups)
}

/// Merge two sorted sequences of mutual constants into one sorted sequence.
pub fn merge<'a>(
  left: Vec<&'a MutConst>,
  right: Vec<&'a MutConst>,
  ctx: &MutCtx,
  cache: &mut BlockCache,
  stt: &CompileState,
) -> Result<Vec<&'a MutConst>, CompileError> {
  let mut result = Vec::with_capacity(left.len() + right.len());
  let mut left_iter = left.into_iter();
  let mut right_iter = right.into_iter();
  let mut left_item = left_iter.next();
  let mut right_item = right_iter.next();

  while let (Some(l), Some(r)) = (&left_item, &right_item) {
    let cmp = compare_const(l, r, ctx, cache, stt)?;
    if cmp == Ordering::Greater {
      result.push(right_item.take().unwrap());
      right_item = right_iter.next();
    } else {
      result.push(left_item.take().unwrap());
      left_item = left_iter.next();
    }
  }

  if let Some(l) = left_item {
    result.push(l);
    result.extend(left_iter);
  }
  if let Some(r) = right_item {
    result.push(r);
    result.extend(right_iter);
  }

  Ok(result)
}

/// Merge-sort mutual constants using structural comparison.
pub fn sort_by_compare<'a>(
  items: &[&'a MutConst],
  ctx: &MutCtx,
  cache: &mut BlockCache,
  stt: &CompileState,
) -> Result<Vec<&'a MutConst>, CompileError> {
  if items.len() <= 1 {
    return Ok(items.to_vec());
  }
  let mid = items.len() / 2;
  let (left, right) = items.split_at(mid);
  let left = sort_by_compare(left, ctx, cache, stt)?;
  let right = sort_by_compare(right, ctx, cache, stt)?;
  merge(left, right, ctx, cache, stt)
}

/// Sort mutual constants into a canonical ordering and group equal ones.
/// Uses iterative refinement: sort by structure, group equals, re-sort with
/// updated mutual context indices, until the partition stabilizes.
pub fn sort_consts<'a>(
  cs: &[&'a MutConst],
  cache: &mut BlockCache,
  stt: &CompileState,
) -> Result<Vec<Vec<&'a MutConst>>, CompileError> {
  let dump =
    std::env::var("IX_RECURSOR_DUMP").ok().filter(|s| !s.is_empty()).filter(
      |prefix| cs.iter().any(|c| c.name().pretty().contains(prefix.as_str())),
    );
  // Sort by name first to match Lean's behavior and ensure deterministic output
  let mut sorted_cs: Vec<&'a MutConst> = cs.to_owned();
  sorted_cs.sort_by_key(|x| x.name());
  if dump.is_some() {
    eprintln!("[compile.sort_consts] seed-sorted by name:");
    for (i, c) in sorted_cs.iter().enumerate() {
      eprintln!("  seed[{i}] {}", c.name().pretty());
    }
  }
  let mut classes = vec![sorted_cs];
  let mut iter = 0;
  loop {
    let ctx = MutConst::ctx(&classes);
    let mut new_classes: Vec<Vec<&MutConst>> = vec![];
    for class in classes.iter() {
      match class.len() {
        0 => {
          return Err(CompileError::InvalidMutualBlock {
            reason: "empty class".into(),
          });
        },
        1 => {
          new_classes.push(class.clone());
        },
        _ => {
          let sorted = sort_by_compare(class.as_ref(), &ctx, cache, stt)?;
          let groups =
            group_by(sorted, |a, b| eq_const(a, b, &ctx, cache, stt))?;
          new_classes.extend(groups);
        },
      }
    }
    if dump.is_some() {
      eprintln!("[compile.sort_consts] iter {iter} → classes:");
      for (ci, class) in new_classes.iter().enumerate() {
        for (mi, m) in class.iter().enumerate() {
          eprintln!("  c[{ci}][{mi}] {}", m.name().pretty());
        }
      }
    }
    iter += 1;
    // No within-class re-sort by name. Items in a class are either
    // alpha-equivalent (any rep is fine) or weak-Equal pending future
    // refinement (and their order is whatever `sort_by_compare` gave —
    // stable on previous-iter order). Re-sorting by name here would
    // promote that "tentatively equal" relationship into a name-derived
    // tiebreak that propagates through subsequent iterations as if it
    // were a structural fact, producing a name-dependent canonical
    // order for purely-structural alpha-equivalence classes. Mirrors
    // the same removal in the kernel's `sort_kconsts_with_seed_key`.
    if classes == new_classes {
      return Ok(new_classes);
    }
    classes = new_classes;
  }
}

/// The declared flat position of a recursor in its family: `X.rec` of the
/// `i`-th member of `RecursorVal.all` is at `i`, and the nested auxiliary
/// recursor `all[0].rec_N` at `all.len() + N - 1` (`u64::MAX` otherwise).
pub fn recursor_family_position(rec: &ix_common::env::RecursorVal) -> u64 {
  let NameData::Str(parent, last, _) = rec.cnst.name.as_data() else {
    return u64::MAX;
  };
  if last == "rec" {
    return rec
      .all
      .iter()
      .position(|n| n == parent)
      .map_or(u64::MAX, |i| i as u64);
  }
  if let Some(k) = last.strip_prefix("rec_")
    && let Ok(k) = k.parse::<u64>()
    && k >= 1
    && rec.all.first() == Some(parent)
  {
    return rec.all.len() as u64 + k - 1;
  }
  u64::MAX
}

/// A block of recursors is laid out in its family's flat order (the order
/// the kernel's `populate_recursor_rules_from_block` pairs with the
/// inductive block's flat members), not in `sort_consts` order. The
/// regenerated families get this from `compile_aux_block_with_rename`'s
/// class-order key; this applies the same rule to a recursor block compiled
/// from Lean's own declarations (`Named.original`, and decompile's
/// verification recompile), using Lean's `RecursorVal.all`. On a block that
/// canonicalisation leaves unchanged the two layouts coincide, so Lean's
/// form and the Ix form of each recursor have one address (D6). The sort is
/// stable; other classes keep their `sort_consts` order.
pub fn order_recursor_family(classes: &mut [Vec<&MutConst>]) {
  if classes.is_empty()
    || !classes.iter().flatten().all(|c| matches!(c, MutConst::Recr(_)))
  {
    return;
  }
  classes.sort_by_key(|class| {
    class
      .iter()
      .map(|c| match c {
        MutConst::Recr(r) => recursor_family_position(r),
        _ => u64::MAX,
      })
      .min()
      .unwrap_or(u64::MAX)
  });
}
// ===========================================================================
// Main compilation entry points
// ===========================================================================

/// Compile a single constant.
pub fn compile_const(
  name: &Name,
  all: &NameSet,
  lean_env: &Arc<LeanEnv>,
  cache: &mut BlockCache,
  stt: &CompileState,
  kctx: &mut KernelCtx,
) -> Result<Address, CompileError> {
  compile_const_inner(name, all, lean_env, cache, stt, kctx, true)
}

/// Compile a constant without aux_gen: no `aux_name_to_addr` fallback,
/// no aux_gen side effects. Used to compile the original Lean form of
/// aux_gen-rewritten constants for metadata preservation.
pub fn compile_const_no_aux(
  name: &Name,
  all: &NameSet,
  lean_env: &Arc<LeanEnv>,
  cache: &mut BlockCache,
  stt: &CompileState,
  kctx: &mut KernelCtx,
) -> Result<Address, CompileError> {
  // Expand the SCC `all` to include same-phase aux_gen constants from
  // the full Lean mutual block. Each constant's `.all` field determines
  // its mutual block. We filter by the constant kind so the no-aux block
  // matches what `roundtrip_block` produces during decompilation:
  //
  //   .rec         → expand via .all, keep only RecInfo
  //   .below (Indc)→ expand via .below's own .all, keep only InductInfo
  //   .below (Def) → expand via .all as-is
  //   .below.rec   → expand via .below.rec's .all, keep only RecInfo
  //   .brecOn/*    → expand via .all as-is

  // First, collect the Lean .all names from any constant in the SCC.
  let mut lean_all: Vec<Name> = Vec::new();
  for n in all {
    if let Some(ci) = lean_env.get(n) {
      let block_all = match &*ci {
        LeanConstantInfo::InductInfo(v) => &v.all,
        LeanConstantInfo::RecInfo(v) => &v.all,
        LeanConstantInfo::DefnInfo(v) => &v.all,
        LeanConstantInfo::ThmInfo(v) => &v.all,
        _ => continue,
      };
      if lean_all.is_empty() {
        lean_all = block_all.clone();
      }
      break;
    }
  }

  // Determine phase from the first aux_gen constant in the SCC.
  #[derive(Clone, Copy, PartialEq, Debug)]
  enum Phase {
    Rec,
    BelowIndc,
    BelowDef,
    BelowRec,
    BrecOn,
  }
  let phase = all.iter().find_map(|n| {
    if !stt.aux_gen_extra_names.contains(n) {
      return None;
    }
    match lean_env.get(n).as_deref() {
      Some(LeanConstantInfo::RecInfo(_)) => {
        // Distinguish .rec from .below.rec
        if matches!(n.as_data(), NameData::Str(p, _, _) if p.last_str() == Some("below"))
        {
          Some(Phase::BelowRec)
        } else {
          Some(Phase::Rec)
        }
      },
      Some(LeanConstantInfo::InductInfo(_)) => Some(Phase::BelowIndc),
      Some(LeanConstantInfo::DefnInfo(_) | LeanConstantInfo::ThmInfo(_)) => {
        if matches!(n.last_str(), Some(s) if s == "below" || s.starts_with("below_"))
        {
          Some(Phase::BelowDef)
        } else {
          Some(Phase::BrecOn)
        }
      },
      _ => None,
    }
  });

  let Some(phase) = phase else {
    // No aux_gen constants found — just compile as-is.
    return compile_const_inner(name, all, lean_env, cache, stt, kctx, false);
  };

  // Build the filtered set from the .all field based on phase.
  let mut filtered = NameSet::default();
  match phase {
    Phase::Rec => {
      // All .rec and .rec_N from the mutual block that are in the current SCC.
      // lean_all only contains inductive names (from RecursorVal.all), not the
      // mutually-referencing recursor names. The scheduler's `all` has the full
      // SCC including rec_N names.
      for n in all {
        if stt.aux_gen_extra_names.contains(n)
          && matches!(
            lean_env.get(n).as_deref(),
            Some(LeanConstantInfo::RecInfo(_))
          )
        {
          filtered.insert(n.clone());
        }
      }
    },
    Phase::BelowIndc => {
      // Use .below's own .all, keep only inductives + their ctors.
      for n in all {
        if let Some(LeanConstantInfo::InductInfo(v)) =
          lean_env.get(n).as_deref()
        {
          for a in &v.all {
            if stt.aux_gen_extra_names.contains(a)
              && let Some(LeanConstantInfo::InductInfo(bi)) =
                lean_env.get(a).as_deref()
            {
              filtered.insert(a.clone());
              for ctor in &bi.ctors {
                filtered.insert(ctor.clone());
              }
            }
          }
          break;
        }
      }
    },
    Phase::BelowDef => {
      // lean_all for BelowDef already contains .below names
      // (from DefnInfo.all = [EqC.below]), so use directly.
      for a in &lean_all {
        if stt.aux_gen_extra_names.contains(a)
          && matches!(
            lean_env.get(a).as_deref(),
            Some(LeanConstantInfo::DefnInfo(_))
          )
        {
          filtered.insert(a.clone());
        }
      }
    },
    Phase::BelowRec => {
      // lean_all for .below.rec already contains .below names
      // (from RecursorVal.all = [A.below, B.below]), so just append ".rec".
      for ind_name in &lean_all {
        let below_rec = Name::str(ind_name.clone(), "rec".to_string());
        if stt.aux_gen_extra_names.contains(&below_rec)
          && matches!(
            lean_env.get(&below_rec).as_deref(),
            Some(LeanConstantInfo::RecInfo(_))
          )
        {
          filtered.insert(below_rec);
        }
      }
    },
    Phase::BrecOn => {
      // Use .all as-is — include all .brecOn/.brecOn.go/.brecOn.eq.
      for n in all {
        if stt.aux_gen_extra_names.contains(n) {
          filtered.insert(n.clone());
        }
      }
      for a in &lean_all {
        for suffix in &["brecOn"] {
          let base = Name::str(a.clone(), suffix.to_string());
          if stt.aux_gen_extra_names.contains(&base) {
            filtered.insert(base.clone());
          }
          for sub in &["go", "eq"] {
            let sub_name = Name::str(base.clone(), sub.to_string());
            if stt.aux_gen_extra_names.contains(&sub_name) {
              filtered.insert(sub_name);
            }
          }
        }
      }
      // Note: _N auxiliary brecOn (brecOn_1, brecOn_1.go, etc.) are NOT
      // included here. They're separate Lean constants with their own SCCs.
    },
  }

  if filtered.is_empty() {
    return compile_const_inner(name, all, lean_env, cache, stt, kctx, false);
  }

  compile_const_inner(name, &filtered, lean_env, cache, stt, kctx, false)
}

/// `aux = false` is the original-form compile of a regenerated auxiliary
/// (`Named.original` provenance): its constants are never stored.
fn compile_const_inner(
  name: &Name,
  all: &NameSet,
  lean_env: &Arc<LeanEnv>,
  cache: &mut BlockCache,
  stt: &CompileState,
  kctx: &mut KernelCtx,
  aux: bool,
) -> Result<Address, CompileError> {
  compile_const_inner_body(name, all, lean_env, cache, stt, kctx, aux)
}

/// Compile a single definition/theorem/opaque (non-mutual case). When `aux`
/// is false (ephemeral compilation for metadata capture), skip storing the
/// Ixon blob and Named entry.
pub(crate) fn compile_single_def(
  name: &Name,
  def: &Def,
  cache: &mut BlockCache,
  stt: &CompileState,
  aux: bool,
) -> Result<(Address, ConstantMeta), CompileError> {
  let (addr, meta, constant) = compile_single_def_parts(name, def, cache, stt)?;
  if aux {
    stt.env.store_const(addr.clone(), constant);
    stt.register_named(name.clone(), Named::new(addr.clone(), meta.clone()));
  } else {
    // Non-aux (compile_const_no_aux): promote aux_gen entry, storing the
    // original (addr, meta) in Named.original for decompilation metadata.
    // Do NOT store the constant blob — it's ephemeral and would pollute
    // the Ixon env with unreferenced constants.
    stt.promote_aux(name, addr.clone(), meta.clone())?;
  }
  Ok((addr, meta))
}

/// Compile a single definition standalone without storing anything: its
/// address, metadata and constant (the caller stores them; Pass 3's
/// canonical constants check a reserved name's binding first).
pub fn compile_single_def_parts(
  name: &Name,
  def: &Def,
  cache: &mut BlockCache,
  stt: &CompileState,
) -> Result<(Address, ConstantMeta, Constant), CompileError> {
  let _t0 = std::time::Instant::now();
  let _name_str_entry = name.pretty();
  let mut_ctx = MutConst::single_ctx(def.name.clone());
  preseed_expr_tables(
    &[
      (&def.typ, def.level_params.as_slice()),
      (&def.value, def.level_params.as_slice()),
    ],
    &mut_ctx,
    cache,
    stt,
    "compile_single_def",
  )?;
  let ctx_addrs: Vec<Address> =
    ctx_to_all(&mut_ctx).iter().map(|n| compile_name(n, stt)).collect();
  let (data, meta) = compile_definition(def, &mut_ctx, &ctx_addrs, cache, stt)?;
  let _t_compile = _t0.elapsed();
  let n_unique_exprs = cache.exprs.len();
  let refs: Vec<Address> = cache.refs.iter().cloned().collect();
  let univs: Vec<Arc<Univ>> = cache.univs.iter().cloned().collect();
  let _t1 = std::time::Instant::now();
  let constant = apply_sharing_to_definition_with_limits(
    &stt.sharing_limits,
    data,
    refs,
    univs,
  )?;
  let _t_sharing = _t1.elapsed();
  let _t2 = std::time::Instant::now();
  let mut bytes = Vec::new();
  constant.put(&mut bytes);
  let serialized_size = bytes.len();
  let addr = Address::hash(&bytes);
  let _t_serial = _t2.elapsed();
  if *IX_TIMING && _t0.elapsed().as_secs_f32() > 1.0 {
    eprintln!(
      "[slow_single] {:?} compile={:.2}s sharing={:.2}s serial={:.2}s unique_exprs={} refs={} bytes={}",
      name.pretty(),
      _t_compile.as_secs_f32(),
      _t_sharing.as_secs_f32(),
      _t_serial.as_secs_f32(),
      n_unique_exprs,
      cache.refs.len(),
      serialized_size,
    );
  }
  Ok((addr, meta, constant))
}

/// Compile a definition-like constant standalone under `name` and register
/// it (Pass 3 image constants).
pub fn compile_single_definition(
  name: &Name,
  def: &Def,
  cache: &mut BlockCache,
  stt: &CompileState,
) -> Result<(Address, ConstantMeta), CompileError> {
  compile_single_def(name, def, cache, stt, true)
}

fn compile_const_inner_body(
  name: &Name,
  all: &NameSet,
  lean_env: &Arc<LeanEnv>,
  cache: &mut BlockCache,
  stt: &CompileState,
  kctx: &mut KernelCtx,
  aux: bool,
) -> Result<Address, CompileError> {
  let _cci_start = std::time::Instant::now();
  if let Some(cached) = stt.resolve_addr_aux(name, aux) {
    return Ok(cached);
  }

  // `lean_env.get(name)` is a plain `Option<&ConstantInfo>` from an
  // `FxHashMap` (see `Env` alias in env.rs) — there's no guard to
  // release, so we clone the value and let the borrow expire on the
  // next line through NLL.
  // Pass 3: a member the call-site rewrite changed is read from the overlay.
  let cnst: LeanConstantInfo = match cache.p3_overlay.get(name) {
    Some(c) => c.clone(),
    None => lean_env
      .get(name)
      .ok_or_else(|| CompileError::MissingConstant {
        name: name.pretty(),
        caller: "compile_const".into(),
      })?
      .cloned(),
  };
  let _cnst_kind = match &cnst {
    LeanConstantInfo::DefnInfo(_) => "defn",
    LeanConstantInfo::ThmInfo(_) => "thm",
    LeanConstantInfo::InductInfo(_) => "indc",
    LeanConstantInfo::RecInfo(_) => "rec",
    LeanConstantInfo::CtorInfo(_) => "ctor",
    LeanConstantInfo::AxiomInfo(_) => "axio",
    LeanConstantInfo::OpaqueInfo(_) => "opaq",
    LeanConstantInfo::QuotInfo(_) => "quot",
  };

  // Handle each constant type
  let addr = match &cnst {
    LeanConstantInfo::DefnInfo(val) => {
      if all.len() == 1 {
        compile_single_def(name, &Def::mk_defn(val), cache, stt, aux)?.0
      } else {
        compile_mutual(name, all, lean_env, cache, stt, kctx, aux)?
      }
    },

    LeanConstantInfo::ThmInfo(val) => {
      if all.len() == 1 {
        compile_single_def(name, &Def::mk_theo(val), cache, stt, aux)?.0
      } else {
        compile_mutual(name, all, lean_env, cache, stt, kctx, aux)?
      }
    },

    LeanConstantInfo::OpaqueInfo(val) => {
      if all.len() == 1 {
        compile_single_def(name, &Def::mk_opaq(val), cache, stt, aux)?.0
      } else {
        compile_mutual(name, all, lean_env, cache, stt, kctx, aux)?
      }
    },

    LeanConstantInfo::AxiomInfo(val) => {
      preseed_expr_tables(
        &[(&val.cnst.typ, val.cnst.level_params.as_slice())],
        &MutCtx::default(),
        cache,
        stt,
        "compile_axiom",
      )?;
      let (data, meta) = compile_axiom(val, cache, stt)?;
      let refs: Vec<Address> = cache.refs.iter().cloned().collect();
      let univs: Vec<Arc<Univ>> = cache.univs.iter().cloned().collect();
      let constant = apply_sharing_to_axiom_with_limits(
        &stt.sharing_limits,
        data,
        refs,
        univs,
      )?;
      let mut bytes = Vec::new();
      constant.put(&mut bytes);
      let addr = Address::hash(&bytes);
      if aux {
        stt.env.store_const(addr.clone(), constant);
        stt.register_named(name.clone(), Named::new(addr.clone(), meta));
      }
      addr
    },

    LeanConstantInfo::QuotInfo(val) => {
      preseed_expr_tables(
        &[(&val.cnst.typ, val.cnst.level_params.as_slice())],
        &MutCtx::default(),
        cache,
        stt,
        "compile_quotient",
      )?;
      let (data, meta) = compile_quotient(val, cache, stt)?;
      let refs: Vec<Address> = cache.refs.iter().cloned().collect();
      let univs: Vec<Arc<Univ>> = cache.univs.iter().cloned().collect();
      let constant = apply_sharing_to_quotient_with_limits(
        &stt.sharing_limits,
        data,
        refs,
        univs,
      )?;
      let mut bytes = Vec::new();
      constant.put(&mut bytes);
      let addr = Address::hash(&bytes);
      if aux {
        stt.env.store_const(addr.clone(), constant);
        stt.register_named(name.clone(), Named::new(addr.clone(), meta));
      }
      addr
    },

    LeanConstantInfo::InductInfo(_) => {
      compile_mutual(name, all, lean_env, cache, stt, kctx, aux)?
    },

    LeanConstantInfo::RecInfo(val) => {
      if all.len() == 1 {
        let mut_ctx = MutConst::single_ctx(val.cnst.name.clone());
        let mut exprs = vec![(&val.cnst.typ, val.cnst.level_params.as_slice())];
        for rule in &val.rules {
          exprs.push((&rule.rhs, val.cnst.level_params.as_slice()));
        }
        preseed_expr_tables(&exprs, &mut_ctx, cache, stt, "compile_recursor")?;
        let ctx_addrs: Vec<Address> =
          ctx_to_all(&mut_ctx).iter().map(|n| compile_name(n, stt)).collect();
        let (data, meta) =
          compile_recursor(val, &mut_ctx, &ctx_addrs, cache, stt)?;
        let refs: Vec<Address> = cache.refs.iter().cloned().collect();
        let univs: Vec<Arc<Univ>> = cache.univs.iter().cloned().collect();
        let constant = apply_sharing_to_recursor_with_limits(
          &stt.sharing_limits,
          data,
          refs,
          univs,
        )?;
        let mut bytes = Vec::new();
        constant.put(&mut bytes);
        let addr = Address::hash(&bytes);
        if aux {
          stt.env.store_const(addr.clone(), constant);
          stt.register_named(
            name.clone(),
            Named::new(addr.clone(), meta.clone()),
          );
        } else {
          stt.promote_aux(name, addr.clone(), meta)?;
        }
        addr
      } else {
        compile_mutual(name, all, lean_env, cache, stt, kctx, aux)?
      }
    },

    LeanConstantInfo::CtorInfo(val) => {
      // Constructors are compiled as part of their inductive
      if let Some(LeanConstantInfo::InductInfo(_)) =
        lean_env.get(&val.induct).as_deref()
      {
        let _ =
          compile_mutual(&val.induct, all, lean_env, cache, stt, kctx, aux)?;
        stt
          .name_to_addr
          .get(name)
          .ok_or_else(|| CompileError::MissingConstant {
            name: name.pretty(),
            caller: "compile_const(ctor_lookup)".into(),
          })?
          .clone()
      } else {
        return Err(CompileError::MissingConstant {
          name: val.induct.pretty(),
          caller: "compile_const(ctor_induct)".into(),
        });
      }
    },
  };

  if aux {
    stt.claim_compiled_name(name, &addr)?;
  }
  Ok(addr)
}

/// Compile a mutual block.
///
/// When `aux` is true, auxiliary constants (`.rec`, `.below`, `.brecOn`) are
/// regenerated for alpha-collapsed blocks via `generate_and_compile_aux_recursors`.
fn compile_mutual(
  name: &Name,
  all: &NameSet,
  lean_env: &Arc<LeanEnv>,
  cache: &mut BlockCache,
  stt: &CompileState,
  kctx: &mut KernelCtx,
  aux: bool,
) -> Result<Address, CompileError> {
  // Collect all constants in the mutual block
  let mut cs = Vec::new();
  for n in all {
    // Clone out of the `EnvEntry` guard so the block owns its constants
    // and no env borrow is held across the compile below.
    // Pass 3: a member the call-site rewrite changed is read from the overlay.
    let const_info = match cache.p3_overlay.get(n) {
      Some(c) => c.clone(),
      None => match lean_env.get(n).map(|e| e.cloned()) {
        Some(c) => c,
        None => {
          return Err(CompileError::MissingConstant {
            name: n.pretty(),
            caller: "compile_mutual".into(),
          });
        },
      },
    };
    let mut_const = match &const_info {
      LeanConstantInfo::InductInfo(val) => {
        let mut ind = mk_indc(val, lean_env)?;
        for c in &mut ind.ctors {
          if let Some(LeanConstantInfo::CtorInfo(o)) =
            cache.p3_overlay.get(&c.cnst.name)
          {
            *c = o.clone();
          }
        }
        MutConst::Indc(ind)
      },
      LeanConstantInfo::DefnInfo(val) => MutConst::Defn(Def::mk_defn(val)),
      LeanConstantInfo::OpaqueInfo(val) => MutConst::Defn(Def::mk_opaq(val)),
      LeanConstantInfo::ThmInfo(val) => MutConst::Defn(Def::mk_theo(val)),
      LeanConstantInfo::RecInfo(val) => MutConst::Recr(val.clone()),
      _ => continue,
    };
    cs.push(mut_const);
  }

  // Sort constants
  let mut sorted_classes =
    sort_consts(&cs.iter().collect::<Vec<_>>(), cache, stt)?;
  order_recursor_family(&mut sorted_classes);
  let mut_ctx = MutConst::ctx(&sorted_classes);

  let mut exprs = Vec::new();
  for cnst in &cs {
    collect_mut_const_exprs(cnst, &mut exprs);
  }
  preseed_expr_tables(&exprs, &mut_ctx, cache, stt, "compile_mutual")?;

  // Compile each constant. The block-context address list is identical
  // for every member (a deterministic function of `mut_ctx`), so it is
  // computed once here instead of sorted+re-interned per member.
  let mut ixon_mutuals = Vec::new();
  let mut all_metas: FxHashMap<Name, ConstantMeta> = FxHashMap::default();
  let ctx_addrs: Vec<Address> =
    ctx_to_all(&mut_ctx).iter().map(|n| compile_name(n, stt)).collect();

  for class in &sorted_classes {
    // Only push one representative per equivalence class into ixon_mutuals,
    // since alpha-equivalent constants compile to identical data and share
    // the same class index in MutConst::ctx.
    let mut representative_pushed = false;
    for cnst in class {
      match cnst {
        MutConst::Defn(def) => {
          let (data, meta) =
            compile_definition(def, &mut_ctx, &ctx_addrs, cache, stt)?;
          if !representative_pushed {
            ixon_mutuals.push(IxonMutConst::Defn(data));
            representative_pushed = true;
          }
          all_metas.insert(def.name.clone(), meta);
        },
        MutConst::Indc(ind) => {
          let (data, meta, ctor_metas_vec) =
            compile_inductive(ind, &mut_ctx, &ctx_addrs, cache, stt)?;
          if !representative_pushed {
            ixon_mutuals.push(IxonMutConst::Indc(data));
            representative_pushed = true;
          }
          // Register per-constructor ConstantMeta::Ctor entries
          for (ctor, ctor_meta) in ind.ctors.iter().zip(ctor_metas_vec) {
            all_metas.insert(ctor.cnst.name.clone(), ctor_meta);
          }
          all_metas.insert(ind.ind.cnst.name.clone(), meta);
        },
        MutConst::Recr(rec) => {
          let (data, meta) =
            compile_recursor(rec, &mut_ctx, &ctx_addrs, cache, stt)?;
          if !representative_pushed {
            ixon_mutuals.push(IxonMutConst::Recr(data));
            representative_pushed = true;
          }
          all_metas.insert(rec.cnst.name.clone(), meta);
        },
      }
    }
  }

  // Create mutual block with sharing
  let refs: Vec<Address> = cache.refs.iter().cloned().collect();
  let univs: Vec<Arc<Univ>> = cache.univs.iter().cloned().collect();

  // Singleton non-inductive: emit as a standalone `Defn`/`Recr`
  // Constant instead of wrapping in `Muts(vec![one])`. Self-reference
  // inside the body still uses `Expr::Rec(0, …)`, which the kernel
  // resolves the same way for a single-member block. Eliminating the
  // wrapper keeps the env structurally uniform (no degenerate Muts
  // wrappers, no extra projection constants) and matches what
  // `compile_single_def` produces for a non-mutual Lean Defn.
  //
  // Inductives are never unwrapped — their projection scheme requires
  // the block.
  if ixon_mutuals.len() == 1
    && !matches!(&ixon_mutuals[0], IxonMutConst::Indc(_))
  {
    let single = ixon_mutuals.pop().unwrap();
    let limits = &stt.sharing_limits;
    let standalone_constant = match single {
      IxonMutConst::Defn(def) => {
        apply_sharing_to_definition_with_limits(limits, def, refs, univs)?
      },
      IxonMutConst::Recr(rec) => {
        apply_sharing_to_recursor_with_limits(limits, rec, refs, univs)?
      },
      IxonMutConst::Indc(_) => unreachable!(),
    };
    let mut bytes = Vec::new();
    standalone_constant.put(&mut bytes);
    let addr = Address::hash(&bytes);

    if aux {
      stt.env.store_const(addr.clone(), standalone_constant);
      for class in &sorted_classes {
        for cnst in class {
          let n = cnst.name();
          // `remove`, not `get().cloned()`: each name is consumed exactly
          // once, and ConstantMeta is an arena-sized deep clone.
          let meta = all_metas.remove(&n).unwrap_or_default();
          stt.register_named(n.clone(), Named::new(addr.clone(), meta));
          stt.claim_compiled_name(&n, &addr)?;
        }
      }
    } else {
      for class in &sorted_classes {
        for cnst in class {
          let n = cnst.name();
          let meta = all_metas.remove(&n).unwrap_or_default();
          stt.promote_aux(&n, addr.clone(), meta)?;
        }
      }
    }
    return Ok(addr);
  }

  let compiled =
    compile_mutual_block(&stt.sharing_limits, ixon_mutuals, refs, univs)?;
  let block_addr = compiled.addr.clone();

  if aux {
    stt.env.store_const(block_addr.clone(), compiled.constant);
    // Register class ordering for each inductive name in the block.
    let class_ordering: Vec<Vec<Name>> = sorted_classes
      .iter()
      .map(|class| class.iter().map(|c| c.name()).collect())
      .collect();
    for class in &sorted_classes {
      for cnst in class {
        stt.blocks.insert(cnst.name(), class_ordering.clone());
      }
    }
  }

  // Create projections for each constant.
  // When aux=true: store Ixon blobs and register Named entries (normal path).
  // When aux=false: promote from aux_name_to_addr, setting Named.original
  // with the original (proj_addr, meta) for decompilation roundtrip.
  let mut idx = 0u64;
  for class in &sorted_classes {
    for cnst in class {
      let n = cnst.name();
      // `remove`: consumed once per name (either the register_name arm
      // or the promote_aux arm below), so no deep clone is needed.
      let meta = all_metas.remove(&n).unwrap_or_default();

      let proj = match cnst {
        MutConst::Defn(_) => defn_proj_constant(idx, block_addr.clone()),
        MutConst::Indc(ind) => {
          // Inductive projection
          let indc_proj = indc_proj_constant(idx, block_addr.clone());
          let mut proj_bytes = Vec::new();
          indc_proj.put(&mut proj_bytes);
          let proj_addr = Address::hash(&proj_bytes);
          if aux {
            stt.env.store_const(proj_addr.clone(), indc_proj);
            stt.register_named(n.clone(), Named::new(proj_addr.clone(), meta));
            stt.claim_compiled_name(&n, &proj_addr)?;
          } else {
            stt.promote_aux(&n, proj_addr, meta)?;
          }

          // Constructor projections
          for (cidx, ctor) in ind.ctors.iter().enumerate() {
            let ctor_meta =
              all_metas.remove(&ctor.cnst.name).unwrap_or_default();
            let ctor_proj =
              ctor_proj_constant(idx, cidx as u64, block_addr.clone());
            let mut ctor_bytes = Vec::new();
            ctor_proj.put(&mut ctor_bytes);
            let ctor_addr = Address::hash(&ctor_bytes);
            if aux {
              stt.env.store_const(ctor_addr.clone(), ctor_proj);
              stt.register_named(
                ctor.cnst.name.clone(),
                Named::new(ctor_addr.clone(), ctor_meta),
              );
              stt.claim_compiled_name(&ctor.cnst.name, &ctor_addr)?;
            } else {
              stt.promote_aux(&ctor.cnst.name, ctor_addr, ctor_meta)?;
            }
          }

          continue;
        },
        MutConst::Recr(_) => recr_proj_constant(idx, block_addr.clone()),
      };

      let mut proj_bytes = Vec::new();
      proj.put(&mut proj_bytes);
      let proj_addr = Address::hash(&proj_bytes);
      if aux {
        stt.env.store_const(proj_addr.clone(), proj);
        stt.register_named(n.clone(), Named::new(proj_addr.clone(), meta));
        stt.claim_compiled_name(&n, &proj_addr)?;
      } else {
        stt.promote_aux(&n, proj_addr, meta)?;
      }
    }
    idx += 1;
  }

  // Register the synthetic Muts named entry for this block. `block_addr`
  // stores an `IxonCI::Muts(...)` constant, but kernel ingress only
  // discovers mutual blocks by scanning `ixon_env.named` for entries tagged
  // `ConstantMetaInfo::Muts { all }` and routing them to
  // `ingress_muts_block`. Without this entry, each member's projection-typed
  // named entry falls through ingress silently and none of its content
  // reaches the kernel env.
  //
  // Only register on `aux=true` since that's the path that actually stores
  // the block constant (`stt.env.store_const(block_addr, ...)` above is
  // guarded by `if aux`). The `aux=false` promotion path reuses entries
  // that were already registered in a prior `aux=true` call.
  if aux {
    let first_name = sorted_classes
      .first()
      .and_then(|c| c.first())
      .map(|c| c.name())
      .expect("compile_mutual invariant: at least one class with one member");
    let muts_all: Vec<Vec<Address>> = sorted_classes
      .iter()
      .map(|class| {
        class
          .iter()
          .map(|c| Address::from_blake3_hash(*c.name().get_hash()))
          .collect()
      })
      .collect();
    let muts_name = block_addr.muts_name(&first_name);
    compile_name(&muts_name, stt);
    stt.register_named(
      muts_name,
      Named::new(
        block_addr.clone(),
        ConstantMeta::new(ConstantMetaInfo::Muts {
          all: muts_all,
          aux_layout: None,
        }),
      ),
    );
  }

  // Regenerate auxiliary constants for alpha-collapsed inductive blocks.
  // Only runs when `aux` is true (i.e., not from compile_const_no_aux which
  // compiles original Lean forms for metadata).
  if aux {
    let class_names: Vec<Vec<Name>> = sorted_classes
      .iter()
      .map(|class| class.iter().map(|c| c.name()).collect())
      .collect();
    // Pass 3: the tail's registrations are journaled (and their release to
    // the scheduler deferred) so that a changed block's Ix auxiliaries can
    // move to their `_ix` display names before any dependent sees them.
    if stt.pass3 {
      pass3::journal_start();
    }
    let tail = mutual::generate_and_compile_aux_recursors(
      &cs,
      &class_names,
      lean_env,
      stt,
      kctx,
    );
    let journal = if stt.pass3 { pass3::journal_take() } else { None };
    let aux_layout_stored = tail?;

    // Change detection (Def 3.1; Lean `Ix.Compile.Pass.isChanged`): the
    // original inductive `all` list from any InductiveVal in the block, and
    // the canonical classes restricted to it.
    let original_all: Vec<Name> = cs
      .iter()
      .find_map(|c| match c {
        MutConst::Indc(ind) => Some(ind.ind.all.clone()),
        _ => None,
      })
      .unwrap_or_default();
    let user_class_names: Vec<Vec<Name>> = if original_all.is_empty() {
      Vec::new()
    } else {
      let original_all_lookup: FxHashMap<Name, ()> =
        original_all.iter().cloned().map(|n| (n, ())).collect();
      class_names
        .iter()
        .filter_map(|class| {
          let names: Vec<Name> = class
            .iter()
            .filter(|n| original_all_lookup.contains_key(*n))
            .cloned()
            .collect();
          (!names.is_empty()).then_some(names)
        })
        .collect()
    };

    // If the block carries an aux_layout, patch the primary Muts
    // metadata so the layout travels with the block through serialize /
    // decompile round-trip (spec §10.2 / §17.3). The layout returned by
    // `generate_and_compile_aux_recursors` is deliberately block-local:
    // SCC-split blocks from the same Lean mutual all share `all[0]`, so
    // looking it up through a global `all[0]` side table lets one block's
    // layout overwrite another's.
    //
    // The Muts name is `block_addr.muts_name(first_name)` — same key the
    // initial registration used — and `DashMap::insert` overwrites.
    if let Some(layout) = &aux_layout_stored {
      let first_name = sorted_classes
        .first()
        .and_then(|c| c.first())
        .map(|c| c.name())
        .expect("compile_mutual invariant: at least one class");
      let muts_name = block_addr.muts_name(&first_name);
      let muts_all: Vec<Vec<Address>> = sorted_classes
        .iter()
        .map(|class| {
          class
            .iter()
            .map(|c| Address::from_blake3_hash(*c.name().get_hash()))
            .collect()
        })
        .collect();
      stt.register_named(
        muts_name,
        Named::new(
          block_addr.clone(),
          ConstantMeta::new(ConstantMetaInfo::Muts {
            all: muts_all,
            aux_layout: Some(layout.clone()),
          }),
        ),
      );
    }

    let user_layout_changed = !original_all.is_empty()
      && (user_class_names.len() < original_all.len()
        || (user_class_names.len() == original_all.len()
          && user_class_names
            .iter()
            .zip(original_all.iter())
            .any(|(class, orig)| class[0] != *orig)));
    let aux_layout_changed = aux_layout_stored.as_ref().is_some_and(|layout| {
      // An evaporated position changes the block even when no canonical
      // slot moved (all-OUT perms). `user_layout_changed` happens to cover
      // today's shapes (evaporation requires an SCC split), but the
      // predicate must not depend on that coincidence. Keep it identical to
      // Lean's `isChanged`.
      layout.evaporated.iter().any(|&b| b)
        || layout.perm.iter().enumerate().any(|(source_j, &canonical_i)| {
          canonical_i != aux_gen::nested::PERM_OUT_OF_SCC
            && canonical_i != source_j
        })
    });

    // Pass 3: a changed block's Ix auxiliaries move to their `_ix` display
    // names and the block records its image-kind heads
    // (`Driver.editChangedBlock`). Only a driver-prepared state can do that
    // (the journal runs under `stt.pass3`); a hand-built one would leave the
    // Ix auxiliaries under Lean's names with no caller rewritten for them,
    // which the legacy call-site surgery did until M6R slice 6: refused,
    // with the Lean side's text (`compileBlockWithAux`).
    if let Some(journal) = journal {
      let release = if user_layout_changed || aux_layout_changed {
        pass3::driver::edit_changed_block(
          stt,
          lean_env,
          &original_all,
          &class_names,
          aux_layout_stored.as_ref(),
          journal,
        )?
      } else {
        // A3V-IPB: an unchanged block's permuted `IndPredBelow` family
        pass3::driver::edit_permuted_below_family(
          stt,
          lean_env,
          &original_all,
          journal,
        )?
      };
      if !release.is_empty() {
        pass3::release_pending(stt, release);
      }
    } else if user_layout_changed || aux_layout_changed {
      return Err(CompileError::InvalidMutualBlock {
        reason: format!(
          "changed block '{}' compiled with its aux tail outside a \
           driver-prepared environment (Pass 3 is the only mode since M6R \
           slice 6)",
          name.pretty()
        ),
      });
    }
  }

  // Return the address for the requested name
  stt
    .name_to_addr
    .get(name)
    .ok_or_else(|| CompileError::MissingConstant {
      name: name.pretty(),
      caller: "compile_mutual(result)".into(),
    })
    .map(|r| r.clone())
}

mod admission;
pub mod aux_gen;
pub mod aux_source;
pub mod block_txn;
mod env;
mod memory;
pub mod mutual;
pub mod nat_conv;
pub mod pass3;
pub(crate) mod validation;
pub use env::{
  compile_env, compile_env_with_options, compile_env_with_profile,
};

#[cfg(test)]
mod c6_flags_tests;

#[cfg(test)]
mod tests {
  use super::*;
  use ix_common::env::{BinderInfo, Expr as LeanExpr, Level};

  #[test]
  fn test_compile_univ_zero() {
    let level = Level::zero();
    let mut cache = BlockCache::default();
    let univ = compile_univ(&level, &[], &mut cache).unwrap();
    assert!(matches!(univ.as_ref(), Univ::Zero));
  }

  #[test]
  fn test_compile_univ_succ() {
    let level = Level::succ(Level::zero());
    let mut cache = BlockCache::default();
    let univ = compile_univ(&level, &[], &mut cache).unwrap();
    match univ.as_ref() {
      Univ::Succ(inner) => assert!(matches!(inner.as_ref(), Univ::Zero)),
      _ => panic!("expected Succ"),
    }
  }

  #[test]
  fn test_compile_univ_param() {
    let name = Name::str(Name::anon(), "u".to_string());
    let level = Level::param(name.clone());
    let mut cache = BlockCache::default();
    let univ = compile_univ(&level, &[name], &mut cache).unwrap();
    assert!(matches!(univ.as_ref(), Univ::Var(0)));
  }

  #[test]
  fn test_compile_univ_max() {
    let level = Level::max(Level::zero(), Level::succ(Level::zero()));
    let mut cache = BlockCache::default();
    let univ = compile_univ(&level, &[], &mut cache).unwrap();
    match univ.as_ref() {
      Univ::Max(a, b) => {
        assert!(matches!(a.as_ref(), Univ::Zero));
        match b.as_ref() {
          Univ::Succ(inner) => assert!(matches!(inner.as_ref(), Univ::Zero)),
          _ => panic!("expected Succ"),
        }
      },
      _ => panic!("expected Max"),
    }
  }

  #[test]
  fn test_store_string() {
    let stt = CompileState::default();
    let addr1 = store_string("hello", &stt);
    let addr2 = store_string("hello", &stt);
    // Same content should give same address
    assert_eq!(addr1, addr2);
    // Check we can retrieve it
    let bytes = stt.env.get_blob(&addr1).unwrap();
    assert_eq!(bytes, b"hello");
  }

  #[test]
  fn test_store_nat() {
    let stt = CompileState::default();
    let n = Nat::from(42u64);
    let addr = store_nat(&n, &stt);
    let bytes = stt.env.get_blob(&addr).unwrap();
    let n2 = Nat::from_le_bytes(&bytes);
    assert_eq!(n, n2);
  }

  #[test]
  fn test_compile_name_anon() {
    let stt = CompileState::default();
    let name = Name::anon();
    let addr = compile_name(&name, &stt);
    // Name is stored in env.names, not blobs
    let stored_name = stt.env.names.get(&addr).unwrap();
    assert_eq!(*stored_name, name);
  }

  #[test]
  fn test_compile_name_str() {
    let stt = CompileState::default();
    let name = Name::str(Name::anon(), "foo".to_string());
    let addr = compile_name(&name, &stt);
    // Name is stored in env.names
    let stored_name = stt.env.names.get(&addr).unwrap();
    assert_eq!(*stored_name, name);
    // String component should be in blobs
    let foo_bytes = "foo".as_bytes();
    let foo_addr = Address::hash(foo_bytes);
    assert!(stt.env.blobs.contains_key(&foo_addr));
  }

  #[test]
  fn test_compile_expr_bvar() {
    let stt = CompileState::default();
    let mut cache = BlockCache::default();
    let expr = LeanExpr::bvar(Nat::from(3u64));
    let result =
      compile_expr(&expr, &[], &MutCtx::default(), &mut cache, &stt).unwrap();
    assert!(matches!(result.as_ref(), Expr::Var(3)));
  }

  #[test]
  fn test_compile_expr_sort() {
    let stt = CompileState::default();
    let mut cache = BlockCache::default();
    let expr = LeanExpr::sort(Level::zero());
    let result =
      compile_expr(&expr, &[], &MutCtx::default(), &mut cache, &stt).unwrap();
    match result.as_ref() {
      Expr::Sort(idx) => {
        assert_eq!(*idx, 0);
        assert!(matches!(
          cache.univs.get_index(0).unwrap().as_ref(),
          Univ::Zero
        ));
      },
      _ => panic!("expected Sort"),
    }
  }

  #[test]
  fn test_compile_expr_app() {
    let stt = CompileState::default();
    let mut cache = BlockCache::default();
    let f = LeanExpr::bvar(Nat::from(0u64));
    let a = LeanExpr::bvar(Nat::from(1u64));
    let expr = LeanExpr::app(f, a);
    let result =
      compile_expr(&expr, &[], &MutCtx::default(), &mut cache, &stt).unwrap();
    match result.as_ref() {
      Expr::App(f, a) => {
        assert!(matches!(f.as_ref(), Expr::Var(0)));
        assert!(matches!(a.as_ref(), Expr::Var(1)));
      },
      _ => panic!("expected App"),
    }
  }

  #[test]
  fn test_compile_expr_lam() {
    let stt = CompileState::default();
    let mut cache = BlockCache::default();
    let ty = LeanExpr::sort(Level::zero());
    let body = LeanExpr::bvar(Nat::from(0u64));
    let expr = LeanExpr::lam(Name::anon(), ty, body, BinderInfo::Default);
    let result =
      compile_expr(&expr, &[], &MutCtx::default(), &mut cache, &stt).unwrap();
    match result.as_ref() {
      Expr::Lam(contract, ty, body) => {
        assert_eq!(*contract, ixon::contract::BinderContract::default());
        match ty.as_ref() {
          Expr::Sort(idx) => {
            assert_eq!(*idx, 0);
            assert!(matches!(
              cache.univs.get_index(0).unwrap().as_ref(),
              Univ::Zero
            ));
          },
          _ => panic!("expected Sort for ty"),
        }
        assert!(matches!(body.as_ref(), Expr::Var(0)));
      },
      _ => panic!("expected Lam"),
    }
  }

  #[test]
  fn test_compile_expr_nat_lit() {
    let stt = CompileState::default();
    let mut cache = BlockCache::default();
    let expr = LeanExpr::lit(Literal::NatVal(Nat::from(42u64)));
    let result =
      compile_expr(&expr, &[], &MutCtx::default(), &mut cache, &stt).unwrap();
    match result.as_ref() {
      Expr::Nat(ref_idx) => {
        let addr = cache.refs.get_index(*ref_idx as usize).unwrap();
        let bytes = stt.env.get_blob(addr).unwrap();
        let n = Nat::from_le_bytes(&bytes);
        assert_eq!(n, Nat::from(42u64));
      },
      _ => panic!("expected Nat"),
    }
  }

  #[test]
  fn test_compile_expr_str_lit() {
    let stt = CompileState::default();
    let mut cache = BlockCache::default();
    let expr = LeanExpr::lit(Literal::StrVal("hello".to_string()));
    let result =
      compile_expr(&expr, &[], &MutCtx::default(), &mut cache, &stt).unwrap();
    match result.as_ref() {
      Expr::Str(ref_idx) => {
        let addr = cache.refs.get_index(*ref_idx as usize).unwrap();
        let bytes = stt.env.get_blob(addr).unwrap();
        assert_eq!(String::from_utf8(bytes).unwrap(), "hello");
      },
      _ => panic!("expected Str"),
    }
  }

  #[test]
  fn test_compile_axiom() {
    use ix_common::env::{AxiomVal, ConstantVal};

    // Create a simple axiom: axiom myAxiom : Type
    let name = Name::str(Name::anon(), "myAxiom".to_string());
    let typ = LeanExpr::sort(Level::succ(Level::zero())); // Type 0
    let cnst = ConstantVal { name: name.clone(), level_params: vec![], typ };
    let axiom = AxiomVal { cnst, is_unsafe: false };

    let mut lean_env = LeanEnv::default();
    lean_env.insert(name.clone(), LeanConstantInfo::AxiomInfo(axiom));
    let lean_env = Arc::new(lean_env);

    let stt = CompileState::default();
    let mut cache = BlockCache::default();
    let mut all = NameSet::default();
    all.insert(name.clone());

    let result = compile_const(
      &name,
      &all,
      &lean_env,
      &mut cache,
      &stt,
      &mut KernelCtx::new(),
    );
    assert!(result.is_ok(), "compile_const failed: {:?}", result.err());

    let addr = result.unwrap();
    assert!(stt.name_to_addr.contains_key(&name));
    assert!(stt.env.get_const(&addr).is_some());
  }

  #[test]
  fn test_compile_simple_def() {
    use ix_common::env::{
      ConstantVal, DefinitionSafety, DefinitionVal, ReducibilityHints,
    };

    // Create a simple definition: def myDef : Nat := 42
    let name = Name::str(Name::anon(), "myDef".to_string());
    let nat_name = Name::str(Name::anon(), "Nat".to_string());
    let typ = LeanExpr::cnst(nat_name.clone(), vec![]);
    let value = LeanExpr::lit(Literal::NatVal(Nat::from(42u64)));
    let cnst = ConstantVal { name: name.clone(), level_params: vec![], typ };
    let def = DefinitionVal {
      cnst,
      value,
      hints: ReducibilityHints::Abbrev,
      safety: DefinitionSafety::Safe,
      all: vec![name.clone()],
    };

    let mut lean_env = LeanEnv::default();
    // Note: We also need Nat in the env for the reference to work,
    // but for this test we just check the compile doesn't crash
    lean_env.insert(name.clone(), LeanConstantInfo::DefnInfo(def));
    let lean_env = Arc::new(lean_env);

    let stt = CompileState::default();
    let mut cache = BlockCache::default();
    let mut all = NameSet::default();
    all.insert(name.clone());

    // This will fail because nat_name isn't in name_to_addr, but let's see the error
    let result = compile_const(
      &name,
      &all,
      &lean_env,
      &mut cache,
      &stt,
      &mut KernelCtx::new(),
    );
    // We expect this to fail with MissingConstant for Nat
    match result {
      Err(CompileError::MissingConstant { name: missing, .. }) => {
        assert!(
          missing.contains("Nat"),
          "Expected missing Nat, got: {}",
          missing
        );
      },
      Err(e) => panic!("Unexpected error: {:?}", e),
      Ok(_) => panic!("Expected error for missing Nat reference"),
    }
  }

  #[test]
  fn test_compile_self_referential_def() {
    use ix_common::env::{
      ConstantInfo as LeanConstantInfo, ConstantVal, DefinitionSafety,
      DefinitionVal, Env as LeanEnv, ReducibilityHints,
    };
    use ixon::constant::ConstantInfo;

    // Create a self-referential definition (like a recursive function placeholder)
    // def myDef : Type := myDef  (this is silly but tests the mutual handling)
    let name = Name::str(Name::anon(), "myDef".to_string());
    let typ = LeanExpr::sort(Level::succ(Level::zero())); // Type
    let value = LeanExpr::cnst(name.clone(), vec![]); // self-reference
    let cnst = ConstantVal { name: name.clone(), level_params: vec![], typ };
    let def = DefinitionVal {
      cnst,
      value,
      hints: ReducibilityHints::Abbrev,
      safety: DefinitionSafety::Safe,
      all: vec![name.clone()],
    };

    let mut lean_env = LeanEnv::default();
    lean_env.insert(name.clone(), LeanConstantInfo::DefnInfo(def));
    let lean_env = Arc::new(lean_env);

    let stt = CompileState::default();
    let mut cache = BlockCache::default();
    let mut all = NameSet::default();
    all.insert(name.clone());

    // This should work because it's a single self-referential def
    let result = compile_const(
      &name,
      &all,
      &lean_env,
      &mut cache,
      &stt,
      &mut KernelCtx::new(),
    );
    assert!(result.is_ok(), "compile_const failed: {:?}", result.err());

    let addr = result.unwrap();
    assert!(stt.name_to_addr.contains_key(&name));

    // Check the constant was stored
    let cnst = stt.env.get_const(&addr);
    assert!(cnst.is_some());
    match cnst.unwrap().as_ref() {
      Constant { info: ConstantInfo::Defn(d), .. } => {
        // Value should be a Rec(0) since it's self-referential in a single-element block
        match d.value.as_ref() {
          Expr::Rec(0, _) => {}, // Expected
          other => panic!("Expected Rec(0), got {:?}", other),
        }
      },
      other => panic!("Expected Defn, got {:?}", other),
    }
  }

  #[test]
  fn test_compile_env_single_axiom() {
    use ix_common::env::{AxiomVal, ConstantVal};

    // Create a minimal environment with just one axiom
    let name = Name::str(Name::anon(), "myAxiom".to_string());
    let typ = LeanExpr::sort(Level::succ(Level::zero())); // Type 0
    let cnst = ConstantVal { name: name.clone(), level_params: vec![], typ };
    let axiom = AxiomVal { cnst, is_unsafe: false };

    let mut lean_env = LeanEnv::default();
    lean_env.insert(name.clone(), LeanConstantInfo::AxiomInfo(axiom));
    let lean_env = Arc::new(lean_env);

    let result = compile_env(&lean_env);
    assert!(result.is_ok(), "compile_env failed: {:?}", result.err());

    let stt = result.unwrap();
    assert!(stt.name_to_addr.contains_key(&name), "name not in name_to_addr");
    assert_eq!(stt.env.const_count(), 1, "expected 1 constant");
  }

  #[test]
  fn test_compile_env_two_independent_axioms() {
    use ix_common::env::{AxiomVal, ConstantVal};

    let name1 = Name::str(Name::anon(), "axiom1".to_string());
    let name2 = Name::str(Name::anon(), "axiom2".to_string());
    let typ = LeanExpr::sort(Level::succ(Level::zero()));

    let axiom1 = AxiomVal {
      cnst: ConstantVal {
        name: name1.clone(),
        level_params: vec![],
        typ: typ.clone(),
      },
      is_unsafe: false,
    };
    let axiom2 = AxiomVal {
      cnst: ConstantVal { name: name2.clone(), level_params: vec![], typ },
      is_unsafe: false,
    };

    let mut lean_env = LeanEnv::default();
    lean_env.insert(name1.clone(), LeanConstantInfo::AxiomInfo(axiom1));
    lean_env.insert(name2.clone(), LeanConstantInfo::AxiomInfo(axiom2));
    let lean_env = Arc::new(lean_env);

    let result = compile_env(&lean_env);
    assert!(result.is_ok(), "compile_env failed: {:?}", result.err());

    let stt = result.unwrap();
    // Both names should be registered
    assert!(stt.name_to_addr.contains_key(&name1), "name1 not in name_to_addr");
    assert!(stt.name_to_addr.contains_key(&name2), "name2 not in name_to_addr");
    // Both names point to the same constant (alpha-equivalent axioms)
    let addr1 = stt.name_to_addr.get(&name1).unwrap().clone();
    let addr2 = stt.name_to_addr.get(&name2).unwrap().clone();
    assert_eq!(
      addr1, addr2,
      "alpha-equivalent axioms should have same address"
    );
    // Only 1 unique constant in the store (alpha-equivalent axioms deduplicated)
    assert_eq!(stt.env.const_count(), 1);
  }

  #[test]
  fn test_compile_env_def_referencing_axiom() {
    use ix_common::env::{
      AxiomVal, ConstantVal, DefinitionSafety, DefinitionVal, ReducibilityHints,
    };

    let axiom_name = Name::str(Name::anon(), "myType".to_string());
    let def_name = Name::str(Name::anon(), "myDef".to_string());

    // axiom myType : Type
    let axiom = AxiomVal {
      cnst: ConstantVal {
        name: axiom_name.clone(),
        level_params: vec![],
        typ: LeanExpr::sort(Level::succ(Level::zero())),
      },
      is_unsafe: false,
    };

    // def myDef : myType := myType (referencing the axiom in the value)
    let def = DefinitionVal {
      cnst: ConstantVal {
        name: def_name.clone(),
        level_params: vec![],
        typ: LeanExpr::cnst(axiom_name.clone(), vec![]),
      },
      value: LeanExpr::cnst(axiom_name.clone(), vec![]), // reference the axiom
      hints: ReducibilityHints::Abbrev,
      safety: DefinitionSafety::Safe,
      all: vec![def_name.clone()],
    };

    let mut lean_env = LeanEnv::default();
    lean_env.insert(axiom_name.clone(), LeanConstantInfo::AxiomInfo(axiom));
    lean_env.insert(def_name.clone(), LeanConstantInfo::DefnInfo(def));
    let lean_env = Arc::new(lean_env);

    let result = compile_env(&lean_env);
    assert!(result.is_ok(), "compile_env failed: {:?}", result.err());

    let stt = result.unwrap();
    assert!(stt.name_to_addr.contains_key(&axiom_name));
    assert!(stt.name_to_addr.contains_key(&def_name));
    assert_eq!(stt.env.const_count(), 2);
  }

  #[test]
  fn test_compile_env_worker_limits_preserve_serialized_dependency_graph() {
    use ix_common::env::{
      AxiomVal, ConstantVal, DefinitionSafety, DefinitionVal,
    };
    let base = Name::str(Name::anon(), "Base".into());
    let typ = LeanExpr::sort(Level::succ(Level::zero()));
    let mut source = LeanEnv::default();
    source.insert(
      base.clone(),
      LeanConstantInfo::AxiomInfo(AxiomVal {
        cnst: ConstantVal {
          name: base.clone(),
          level_params: vec![],
          typ: typ.clone(),
        },
        is_unsafe: false,
      }),
    );
    let mut previous = vec![base; 8];
    for layer in 0..5 {
      for (column, prior) in previous.iter_mut().enumerate() {
        let name = Name::str(Name::anon(), format!("alias_{layer}_{column}"));
        source.insert(
          name.clone(),
          LeanConstantInfo::DefnInfo(DefinitionVal {
            cnst: ConstantVal {
              name: name.clone(),
              level_params: vec![],
              typ: typ.clone(),
            },
            value: LeanExpr::cnst(prior.clone(), vec![]),
            hints: ReducibilityHints::Abbrev,
            safety: DefinitionSafety::Safe,
            all: vec![name.clone()],
          }),
        );
        *prior = name;
      }
    }
    // A final block depends on every branch, testing dependency publication
    // as well as byte-identical metadata for alpha-equivalent aliases.
    let join = Name::str(Name::anon(), "Join".into());
    let mut value = LeanExpr::sort(Level::zero());
    for name in previous {
      value = LeanExpr::all(
        Name::anon(),
        LeanExpr::cnst(name, vec![]),
        value,
        BinderInfo::Default,
      );
    }
    source.insert(
      join.clone(),
      LeanConstantInfo::DefnInfo(DefinitionVal {
        cnst: ConstantVal { name: join.clone(), level_params: vec![], typ },
        value,
        hints: ReducibilityHints::Abbrev,
        safety: DefinitionSafety::Safe,
        all: vec![join],
      }),
    );
    let source = Arc::new(source);
    let mut outputs = Vec::new();
    for max_workers in [1, 4] {
      let compiled = compile_env_with_options(
        &source,
        CompileOptions { max_workers: Some(max_workers) },
      )
      .unwrap();
      assert!(compiled.ungrounded.is_empty());
      assert_eq!(compiled.name_to_addr.len(), 42);
      let mut bytes = Vec::new();
      compiled.env.put(&mut bytes).unwrap();
      outputs.push(bytes);
    }
    assert_eq!(outputs[0], outputs[1]);
  }

  /// Test that alpha-equivalent mutual definitions produce correct projection
  /// indices. Two definitions with identical type/value structure (but different
  /// names) should form one equivalence class, and projections should resolve
  /// to the single representative in the Muts array.
  #[test]
  fn test_compile_mutual_alpha_equivalent_defs() {
    use ix_common::env::{
      ConstantVal, DefinitionSafety, DefinitionVal, ReducibilityHints,
    };

    // Create two mutually recursive definitions with identical structure.
    // Both: def X : Type := Type (referencing each other, same shape)
    let name_f = Name::str(Name::anon(), "f".to_string());
    let name_g = Name::str(Name::anon(), "g".to_string());

    let typ = LeanExpr::sort(Level::succ(Level::zero())); // Type

    // f and g reference each other but with identical structure:
    // f : Type := g   and   g : Type := f
    // After alpha-normalization (mutual refs become recur indices),
    // both become: recur(0) since they're in the same class.
    let def_f = DefinitionVal {
      cnst: ConstantVal {
        name: name_f.clone(),
        level_params: vec![],
        typ: typ.clone(),
      },
      value: LeanExpr::cnst(name_g.clone(), vec![]),
      hints: ReducibilityHints::Opaque,
      safety: DefinitionSafety::Safe,
      all: vec![name_f.clone(), name_g.clone()],
    };

    let def_g = DefinitionVal {
      cnst: ConstantVal {
        name: name_g.clone(),
        level_params: vec![],
        typ: typ.clone(),
      },
      value: LeanExpr::cnst(name_f.clone(), vec![]),
      hints: ReducibilityHints::Opaque,
      safety: DefinitionSafety::Safe,
      all: vec![name_f.clone(), name_g.clone()],
    };

    let mut lean_env = LeanEnv::default();
    lean_env.insert(name_f.clone(), LeanConstantInfo::DefnInfo(def_f));
    lean_env.insert(name_g.clone(), LeanConstantInfo::DefnInfo(def_g));
    let lean_env = Arc::new(lean_env);

    let result = compile_env(&lean_env);
    assert!(result.is_ok(), "compile_env failed: {:?}", result.err());

    let stt = result.unwrap();

    // Both names should be registered
    assert!(stt.name_to_addr.contains_key(&name_f), "f not in name_to_addr");
    assert!(stt.name_to_addr.contains_key(&name_g), "g not in name_to_addr");

    // Both should point to the same block address (same projection,
    // since they're alpha-equivalent and share idx=0)
    let addr_f = stt.name_to_addr.get(&name_f).unwrap().clone();
    let addr_g = stt.name_to_addr.get(&name_g).unwrap().clone();
    assert_eq!(
      addr_f, addr_g,
      "alpha-equivalent mutual defs should have same projection address"
    );

    // Alpha-equivalent mutual defs collapse to a singleton non-inductive
    // class, which the compiler now unwraps to a standalone `Defn`
    // Constant (no Muts wrapper, no block entry). Both Lean names
    // point to the same standalone address (asserted above); no Ixon
    // block is created.
    assert!(
      stt.blocks.is_empty(),
      "singleton-unwrapped mutual should have no block entry"
    );
  }

  /// Test that alpha-equivalent defs in a mutual block with a non-equivalent
  /// third definition produce correct indices: 2 classes → 2 Muts entries,
  /// with projections indexing correctly into the array.
  #[test]
  fn test_compile_mutual_alpha_equiv_with_different_third() {
    use ix_common::env::{
      ConstantVal, DefinitionSafety, DefinitionVal, ReducibilityHints,
    };

    let name_f = Name::str(Name::anon(), "f".to_string());
    let name_g = Name::str(Name::anon(), "g".to_string());
    let name_h = Name::str(Name::anon(), "h".to_string());

    let typ = LeanExpr::sort(Level::succ(Level::zero())); // Type

    // f and g are alpha-equivalent to each other:
    //   f : Type := App(g, h)     g : Type := App(f, h)
    // After alpha-normalization, both become App(recur(class_of_fg), recur(class_of_h))
    // h is structurally different:
    //   h : Type := f
    // After alpha-normalization: recur(class_of_fg)
    // All three form one SCC: f→g,h  g→f,h  h→f
    let def_f = DefinitionVal {
      cnst: ConstantVal {
        name: name_f.clone(),
        level_params: vec![],
        typ: typ.clone(),
      },
      value: LeanExpr::app(
        LeanExpr::cnst(name_g.clone(), vec![]),
        LeanExpr::cnst(name_h.clone(), vec![]),
      ),
      hints: ReducibilityHints::Opaque,
      safety: DefinitionSafety::Safe,
      all: vec![name_f.clone(), name_g.clone(), name_h.clone()],
    };

    let def_g = DefinitionVal {
      cnst: ConstantVal {
        name: name_g.clone(),
        level_params: vec![],
        typ: typ.clone(),
      },
      value: LeanExpr::app(
        LeanExpr::cnst(name_f.clone(), vec![]),
        LeanExpr::cnst(name_h.clone(), vec![]),
      ),
      hints: ReducibilityHints::Opaque,
      safety: DefinitionSafety::Safe,
      all: vec![name_f.clone(), name_g.clone(), name_h.clone()],
    };

    let def_h = DefinitionVal {
      cnst: ConstantVal {
        name: name_h.clone(),
        level_params: vec![],
        typ: typ.clone(),
      },
      value: LeanExpr::cnst(name_f.clone(), vec![]),
      hints: ReducibilityHints::Opaque,
      safety: DefinitionSafety::Safe,
      all: vec![name_f.clone(), name_g.clone(), name_h.clone()],
    };

    let mut lean_env = LeanEnv::default();
    lean_env.insert(name_f.clone(), LeanConstantInfo::DefnInfo(def_f));
    lean_env.insert(name_g.clone(), LeanConstantInfo::DefnInfo(def_g));
    lean_env.insert(name_h.clone(), LeanConstantInfo::DefnInfo(def_h));
    let lean_env = Arc::new(lean_env);

    let result = compile_env(&lean_env);
    assert!(result.is_ok(), "compile_env failed: {:?}", result.err());

    let stt = result.unwrap();

    // All three should be registered
    assert!(stt.name_to_addr.contains_key(&name_f));
    assert!(stt.name_to_addr.contains_key(&name_g));
    assert!(stt.name_to_addr.contains_key(&name_h));

    // f and g are alpha-equivalent → same projection address
    let addr_f = stt.name_to_addr.get(&name_f).unwrap().clone();
    let addr_g = stt.name_to_addr.get(&name_g).unwrap().clone();
    assert_eq!(
      addr_f, addr_g,
      "alpha-equivalent f and g should share projection address"
    );

    // h is different → different projection address
    let addr_h = stt.name_to_addr.get(&name_h).unwrap().clone();
    assert_ne!(
      addr_f, addr_h,
      "h should have a different projection address than f/g"
    );

    // Verify block has exactly 2 equivalence classes
    assert!(!stt.blocks.is_empty(), "Expected at least one block entry");
    for entry in stt.blocks.iter() {
      let classes = entry.value();
      assert_eq!(
        classes.len(),
        2,
        "2 equivalence classes should produce 2 classes, got {}",
        classes.len()
      );
    }
  }

  // =========================================================================
  // Sharing tests
  // =========================================================================

  #[test]
  fn test_mutual_block_roundtrip() {
    use ix_common::env::DefinitionSafety;
    use ixon::constant::{DefKind, Definition};

    // Create a mutual block and verify it roundtrips through serialization
    let sort0 = Expr::sort(0);
    let ty = Expr::all(sort0.clone(), Expr::var(0));

    let def1 = IxonMutConst::Defn(Definition {
      kind: DefKind::Definition,
      safety: DefinitionSafety::Safe,
      lvls: 0,
      typ: ty.clone(),
      value: Expr::var(0),
    });

    let def2 = IxonMutConst::Defn(Definition {
      kind: DefKind::Theorem,
      safety: DefinitionSafety::Safe,
      lvls: 0,
      typ: ty,
      value: Expr::var(1),
    });

    let compiled = compile_mutual_block(
      &ExactSharingLimits::default(),
      vec![def1, def2],
      vec![],
      vec![],
    )
    .unwrap();
    let constant = compiled.constant;
    let addr = compiled.addr;

    // Serialize
    let mut buf = Vec::new();
    constant.put(&mut buf);

    // Deserialize
    let recovered = Constant::get(&mut buf.as_slice()).unwrap();

    // Re-serialize to check determinism
    let mut buf2 = Vec::new();
    recovered.put(&mut buf2);

    assert_eq!(buf, buf2, "Serialization should be deterministic");

    // Re-hash to check address stability
    let addr2 = Address::hash(&buf2);
    assert_eq!(addr, addr2, "Content address should be stable");
  }

  // =========================================================================
  // Constant-level sharing tests
  // =========================================================================

  /// The compiler's sharing (the canonical construction) of `exprs` under
  /// the default limits: the rewritten roots and the table.
  #[allow(clippy::needless_pass_by_value)]
  fn apply_sharing(exprs: Vec<Arc<Expr>>) -> (Vec<Arc<Expr>>, Vec<Arc<Expr>>) {
    share_roots(&ExactSharingLimits::default(), &exprs).unwrap()
  }

  #[test]
  fn test_apply_sharing_basic() {
    // Test the apply_sharing helper function with a repeated subterm
    let sort0 = Expr::sort(0);
    let var0 = Expr::var(0);
    // Create term: App(Lam(Sort0, Var0), Lam(Sort0, Var0))
    // Lam(Sort0, Var0) is repeated and should be shared
    let lam = Expr::lam(sort0.clone(), var0);
    let app = Expr::app(lam.clone(), lam);

    let (rewritten, sharing) = apply_sharing(vec![app]);

    // Should have sharing since lam is used twice
    assert!(!sharing.is_empty(), "Expected sharing for repeated subterm");
    // The sharing vector should contain the shared Lam
    assert!(sharing.iter().any(|e| matches!(e.as_ref(), Expr::Lam(_, _, _))));
    // The rewritten expression should have Share references
    assert!(matches!(rewritten[0].as_ref(), Expr::App(_, _)));
  }

  #[test]
  fn test_definition_with_sharing() {
    use ixon::constant::{DefKind, Definition};

    // Create a definition where typ and value share structure
    let sort0 = Expr::sort(0);
    let shared_subterm = Expr::all(sort0.clone(), Expr::var(0));
    // typ = App(shared, shared) -- shared twice
    let typ = Expr::app(shared_subterm.clone(), shared_subterm.clone());
    // value = shared
    let value = shared_subterm;

    let (rewritten, sharing) = apply_sharing(vec![typ, value]);

    // shared_subterm appears 3 times total, should definitely be shared
    assert!(
      !sharing.is_empty(),
      "Expected sharing for definition with repeated subterms"
    );

    // Create constant with sharing at Constant level
    let def = Definition {
      kind: DefKind::Definition,
      safety: ix_common::env::DefinitionSafety::Safe,
      lvls: 0,
      typ: rewritten[0].clone(),
      value: rewritten[1].clone(),
    };

    let constant = Constant::with_tables(
      ConstantInfo::Defn(def),
      sharing.clone(),
      vec![],
      vec![],
    );

    let mut buf = Vec::new();
    constant.put(&mut buf);
    let recovered = Constant::get(&mut buf.as_slice()).unwrap();

    assert_eq!(sharing.len(), recovered.sharing.len());
    assert!(matches!(recovered.info, ConstantInfo::Defn(_)));
  }

  #[test]
  fn test_axiom_with_sharing() {
    use ixon::constant::Axiom;

    // Axiom with repeated subterms in its type
    let sort0 = Expr::sort(0);
    let shared = Expr::all(sort0.clone(), Expr::var(0));
    // typ = All(shared, All(shared, Var(0)))
    let typ =
      Expr::all(shared.clone(), Expr::all(shared.clone(), Expr::var(0)));

    let (rewritten, sharing) = apply_sharing(vec![typ]);

    // shared appears twice, should be shared
    assert!(
      !sharing.is_empty(),
      "Expected sharing for axiom with repeated subterms"
    );

    let axiom = Axiom { is_unsafe: false, lvls: 0, typ: rewritten[0].clone() };
    let constant = Constant::with_tables(
      ConstantInfo::Axio(axiom),
      sharing.clone(),
      vec![],
      vec![],
    );

    let mut buf = Vec::new();
    constant.put(&mut buf);
    let recovered = Constant::get(&mut buf.as_slice()).unwrap();

    assert_eq!(sharing.len(), recovered.sharing.len());
    assert!(matches!(recovered.info, ConstantInfo::Axio(_)));
  }

  #[test]
  fn test_recursor_with_sharing() {
    use ixon::constant::{Recursor, RecursorRule};

    // Recursor with shared subterms across typ and rules
    let sort0 = Expr::sort(0);
    let shared = Expr::lam(sort0.clone(), Expr::var(0));

    // typ uses shared twice
    let typ = Expr::app(shared.clone(), shared.clone());

    // rules also use shared
    let rules = vec![
      RecursorRule { fields: 0, rhs: shared.clone() },
      RecursorRule { fields: 1, rhs: shared },
    ];

    // Collect all expressions
    let mut all_exprs = vec![typ];
    for r in &rules {
      all_exprs.push(r.rhs.clone());
    }

    let (rewritten, sharing) = apply_sharing(all_exprs);

    // shared appears 4 times, should definitely be shared
    assert!(
      !sharing.is_empty(),
      "Expected sharing for recursor with repeated subterms"
    );

    let rec = Recursor {
      k: false,
      is_unsafe: false,
      lvls: 0,
      params: 0,
      indices: 0,
      motives: 1,
      minors: 2,
      typ: rewritten[0].clone(),
      rules: rules
        .into_iter()
        .zip(rewritten.into_iter().skip(1))
        .map(|(r, rhs)| RecursorRule { fields: r.fields, rhs })
        .collect(),
    };

    let constant = Constant::with_tables(
      ConstantInfo::Recr(rec),
      sharing.clone(),
      vec![],
      vec![],
    );

    let mut buf = Vec::new();
    constant.put(&mut buf);
    let recovered = Constant::get(&mut buf.as_slice()).unwrap();

    assert_eq!(sharing.len(), recovered.sharing.len());
    if let ConstantInfo::Recr(rec2) = &recovered.info {
      assert_eq!(2, rec2.rules.len());
    } else {
      panic!("Expected Recursor");
    }
  }

  #[test]
  fn test_inductive_with_sharing() {
    use ixon::constant::{Constructor, Inductive};

    // Inductive with shared subterms across type and constructors
    let sort0 = Expr::sort(0);
    let shared = Expr::all(sort0.clone(), Expr::var(0));

    let typ = Expr::app(shared.clone(), shared.clone());

    let ctors = vec![
      Constructor {
        is_unsafe: false,
        lvls: 0,
        cidx: 0,
        params: 0,
        fields: 0,
        typ: shared.clone(),
      },
      Constructor {
        is_unsafe: false,
        lvls: 0,
        cidx: 1,
        params: 0,
        fields: 1,
        typ: shared,
      },
    ];

    // Collect all expressions
    let mut all_exprs = vec![typ];
    for c in &ctors {
      all_exprs.push(c.typ.clone());
    }

    let (rewritten, sharing) = apply_sharing(all_exprs);

    // shared appears 4 times, should be shared
    assert!(
      !sharing.is_empty(),
      "Expected sharing for inductive with repeated subterms"
    );

    let ind = Inductive {
      is_unsafe: false,
      lvls: 0,
      params: 0,
      indices: 0,
      typ: rewritten[0].clone(),
      ctors: ctors
        .into_iter()
        .zip(rewritten.into_iter().skip(1))
        .map(|(c, typ)| Constructor {
          is_unsafe: c.is_unsafe,
          lvls: c.lvls,
          cidx: c.cidx,
          params: c.params,
          fields: c.fields,
          typ,
        })
        .collect(),
    };

    // Wrap in MutConst for serialization with sharing at Constant level
    let constant = Constant::with_tables(
      ConstantInfo::Muts(vec![IxonMutConst::Indc(ind)]),
      sharing.clone(),
      vec![],
      vec![],
    );

    let mut buf = Vec::new();
    constant.put(&mut buf);
    let recovered = Constant::get(&mut buf.as_slice()).unwrap();

    assert_eq!(sharing.len(), recovered.sharing.len());
    if let ConstantInfo::Muts(mutuals) = &recovered.info {
      if let Some(IxonMutConst::Indc(ind2)) = mutuals.first() {
        assert_eq!(2, ind2.ctors.len());
      } else {
        panic!("Expected Inductive in Muts");
      }
    } else {
      panic!("Expected Muts");
    }
  }

  #[test]
  fn test_no_sharing_when_not_repeated() {
    // When a subterm only appears once, it shouldn't be shared
    let _sort0 = Expr::sort(0);
    let var0 = Expr::var(0);
    let var1 = Expr::var(1);
    let app = Expr::app(var0, var1);

    let (rewritten, sharing) = apply_sharing(vec![app.clone()]);

    // No repeated subterms, so no sharing
    assert!(sharing.is_empty(), "Expected no sharing when nothing is repeated");
    // Rewritten should be identical to original
    assert_eq!(rewritten[0].as_ref(), app.as_ref());
  }

  // =========================================================================
  // Compile/Decompile Roundtrip Tests
  // =========================================================================

  #[test]
  fn test_roundtrip_axiom() {
    use crate::decompile::decompile_env;
    use ix_common::env::{AxiomVal, ConstantVal};

    // Create an axiom: axiom myAxiom : Type
    let name = Name::str(Name::anon(), "myAxiom".to_string());
    let typ = LeanExpr::sort(Level::succ(Level::zero())); // Type 0
    let cnst = ConstantVal { name: name.clone(), level_params: vec![], typ };
    let axiom = AxiomVal { cnst, is_unsafe: false };

    let mut lean_env = LeanEnv::default();
    lean_env.insert(name.clone(), LeanConstantInfo::AxiomInfo(axiom.clone()));
    let lean_env = Arc::new(lean_env);

    // Compile
    let stt = compile_env(&lean_env).expect("compile_env failed");

    // Decompile
    let dstt = decompile_env(&stt).expect("decompile_env failed");

    // Check roundtrip
    let recovered =
      dstt.env.get(&name).expect("name not found in decompiled env");
    match &*recovered {
      LeanConstantInfo::AxiomInfo(ax) => {
        assert_eq!(ax.cnst.name, axiom.cnst.name);
        assert_eq!(ax.is_unsafe, axiom.is_unsafe);
        assert_eq!(ax.cnst.level_params.len(), axiom.cnst.level_params.len());
      },
      _ => panic!("Expected AxiomInfo"),
    }
  }

  /// Canonicity §10.6 end-to-end at unit scale: compile emits
  /// `canon_univ`-fixed primary tables plus `univ_patches`/`meta_univs`
  /// for changed spellings, and decompile replays the patches so every
  /// source spelling roundtrips EXACTLY (content-hash equality).
  #[test]
  fn test_level_canonicalization_tables_patches_and_replay() {
    use crate::decompile::decompile_env;
    use ix_common::env::{AxiomVal, ConstantVal, Env as LeanEnv};

    let u = Name::str(Name::anon(), "u".to_string());
    let v = Name::str(Name::anon(), "v".to_string());
    let lu = || Level::param(u.clone());
    let lv = || Level::param(v.clone());
    // Succ-lifted twin: `(max u v)+1` — the Géran-canonical form
    // distributes the succ (`max (u+1) (v+1)`), so this spelling must
    // be patched.
    let succ_dist = || Level::succ(Level::max(lu(), lv()));

    let mk_axiom = |name: &Name, typ: LeanExpr| {
      LeanConstantInfo::AxiomInfo(AxiomVal {
        cnst: ConstantVal {
          name: name.clone(),
          level_params: vec![u.clone(), v.clone()],
          typ,
        },
        is_unsafe: false,
      })
    };

    let twin_name = Name::str(Name::anon(), "twinAx".to_string());
    let ctrl_name = Name::str(Name::anon(), "ctrlAx".to_string());
    let use_name = Name::str(Name::anon(), "useAx".to_string());

    let mut lean_env = LeanEnv::default();
    lean_env.insert(
      twin_name.clone(),
      mk_axiom(&twin_name, LeanExpr::sort(succ_dist())),
    );
    // Control: an already-canonical spelling must emit NO patches.
    lean_env.insert(
      ctrl_name.clone(),
      mk_axiom(&ctrl_name, LeanExpr::sort(Level::max(lu(), lv()))),
    );
    // Const-arm coverage: a reference with a noncanonical level ARG —
    // the patch must carry the full arg list.
    lean_env.insert(
      use_name.clone(),
      mk_axiom(
        &use_name,
        LeanExpr::cnst(twin_name.clone(), vec![succ_dist(), lv()]),
      ),
    );
    let lean_env = Arc::new(lean_env);

    let stt = compile_env(&lean_env).expect("compile_env failed");

    // (1) Every stored primary univ-table entry is canon_univ-fixed.
    for entry in stt.env.consts.iter() {
      let c = stt.env.get_const(entry.key()).expect("stored constant");
      for uv in &c.univs {
        assert_eq!(
          &canon_univ(uv),
          uv,
          "non-canonical entry in a stored constant's univ table"
        );
      }
    }

    // (2) Patch emission: the twins carry patches + extension spellings,
    // the control carries none.
    let twin_meta = stt.env.named.get(&twin_name).expect("twin named");
    assert_eq!(twin_meta.meta().univ_patches.len(), 1, "twin sort patch");
    assert_eq!(twin_meta.meta().univ_patches[0].univ_idxs.len(), 1);
    assert_eq!(twin_meta.meta().meta_univs.len(), 1, "twin extension");
    drop(twin_meta);
    let use_meta = stt.env.named.get(&use_name).expect("use named");
    assert_eq!(use_meta.meta().univ_patches.len(), 1, "const-arg patch");
    assert_eq!(
      use_meta.meta().univ_patches[0].univ_idxs.len(),
      2,
      "const patch carries the FULL level-arg list"
    );
    drop(use_meta);
    let ctrl_meta = stt.env.named.get(&ctrl_name).expect("ctrl named");
    assert!(ctrl_meta.meta().univ_patches.is_empty(), "control patchless");
    assert!(ctrl_meta.meta().meta_univs.is_empty(), "control no extension");
    drop(ctrl_meta);

    // (3) Decompile replays every spelling exactly.
    let dstt = decompile_env(&stt).expect("decompile_env failed");
    for (name, orig_ci) in lean_env.iter() {
      let rec = dstt.env.get(name).expect("decompiled constant");
      assert_eq!(
        orig_ci.get_type().get_hash(),
        rec.get_type().get_hash(),
        "type spelling roundtrip for {name}"
      );
    }
  }

  /// Canonicity §10.6, constructor window: an inductive whose ctor TYPES
  /// carry noncanonical spellings exercises the per-ctor
  /// `meta_univs`/`univ_patches` swap in the decompiler (extensions
  /// installed at the PRIMARY offset per ctor, restored between
  /// siblings). Multiple ctors make the window cycle; the strict
  /// roundtrip pins that no sibling's extension leaks into another's
  /// replay.
  #[test]
  fn test_level_canonicalization_inductive_ctor_windows() {
    use crate::decompile::decompile_env;
    use ix_common::env::{
      ConstantVal, ConstructorVal, Env as LeanEnv, InductiveVal,
    };

    let u = Name::str(Name::anon(), "u".to_string());
    let v = Name::str(Name::anon(), "v".to_string());
    let lps = vec![u.clone(), v.clone()];
    let lu = || Level::param(u.clone());
    let lv = || Level::param(v.clone());

    let ind_name = Name::str(Name::anon(), "Twine".to_string());
    let c0_name = Name::str(ind_name.clone(), "lift".to_string());
    let c1_name = Name::str(ind_name.clone(), "flip".to_string());
    let c2_name = Name::str(ind_name.clone(), "plain".to_string());

    // Inductive type itself carries a noncanonical sort spelling.
    let ind_typ = LeanExpr::sort(Level::succ(Level::max(lu(), lv())));
    let ind_ref = || LeanExpr::cnst(ind_name.clone(), vec![lu(), lv()]);
    // Ctor 0: succ-lifted twin `(max u v)+1` (patched).
    let c0_typ = LeanExpr::all(
      Name::str(Name::anon(), "x".to_string()),
      LeanExpr::sort(Level::succ(Level::max(lu(), lv()))),
      ind_ref(),
      ix_common::env::BinderInfo::Default,
    );
    // Ctor 1: commuted twin `max v u` (patched, DIFFERENT spelling).
    let c1_typ = LeanExpr::all(
      Name::str(Name::anon(), "y".to_string()),
      LeanExpr::sort(Level::max(lv(), lu())),
      ind_ref(),
      ix_common::env::BinderInfo::Default,
    );
    // Ctor 2: canonical control (no patch).
    let c2_typ = LeanExpr::all(
      Name::str(Name::anon(), "z".to_string()),
      LeanExpr::sort(Level::max(lu(), lv())),
      ind_ref(),
      ix_common::env::BinderInfo::Default,
    );

    let inductive = InductiveVal {
      cnst: ConstantVal {
        name: ind_name.clone(),
        level_params: lps.clone(),
        typ: ind_typ,
      },
      num_params: Nat::from(0u64),
      num_indices: Nat::from(0u64),
      all: vec![ind_name.clone()],
      ctors: vec![c0_name.clone(), c1_name.clone(), c2_name.clone()],
      num_nested: Nat::from(0u64),
      is_rec: false,
      is_unsafe: false,
      is_reflexive: false,
    };
    let mk_ctor = |name: &Name, cidx: u64, typ: LeanExpr| ConstructorVal {
      cnst: ConstantVal { name: name.clone(), level_params: lps.clone(), typ },
      induct: ind_name.clone(),
      cidx: Nat::from(cidx),
      num_params: Nat::from(0u64),
      num_fields: Nat::from(1u64),
      is_unsafe: false,
    };

    let mut lean_env = LeanEnv::default();
    lean_env.insert(ind_name.clone(), LeanConstantInfo::InductInfo(inductive));
    lean_env.insert(
      c0_name.clone(),
      LeanConstantInfo::CtorInfo(mk_ctor(&c0_name, 0, c0_typ)),
    );
    lean_env.insert(
      c1_name.clone(),
      LeanConstantInfo::CtorInfo(mk_ctor(&c1_name, 1, c1_typ)),
    );
    lean_env.insert(
      c2_name.clone(),
      LeanConstantInfo::CtorInfo(mk_ctor(&c2_name, 2, c2_typ)),
    );
    let lean_env = Arc::new(lean_env);

    let stt = compile_env(&lean_env).expect("compile_env failed");

    // The two twin ctors carry their own patches; the control does not.
    for (name, want_patch) in
      [(&c0_name, true), (&c1_name, true), (&c2_name, false)]
    {
      let named = stt.env.named.get(name).expect("ctor named");
      assert_eq!(
        !named.meta().univ_patches.is_empty(),
        want_patch,
        "patch presence for {name}"
      );
    }

    let dstt = decompile_env(&stt).expect("decompile_env failed");
    for (name, orig_ci) in lean_env.iter() {
      let rec = dstt.env.get(name).expect("decompiled constant");
      assert_eq!(
        orig_ci.get_type().get_hash(),
        rec.get_type().get_hash(),
        "ctor-window spelling roundtrip for {name}"
      );
    }
  }

  #[test]
  fn test_roundtrip_axiom_with_level_params() {
    use crate::decompile::decompile_env;
    use ix_common::env::{AxiomVal, ConstantVal, Env as LeanEnv};

    // Create an axiom with universe params: axiom myAxiom.{u, v} : Sort (max u v)
    let name = Name::str(Name::anon(), "myAxiom".to_string());
    let u = Name::str(Name::anon(), "u".to_string());
    let v = Name::str(Name::anon(), "v".to_string());
    let typ = LeanExpr::sort(Level::max(
      Level::param(u.clone()),
      Level::param(v.clone()),
    ));
    let cnst = ConstantVal {
      name: name.clone(),
      level_params: vec![u.clone(), v.clone()],
      typ,
    };
    let axiom = AxiomVal { cnst, is_unsafe: false };

    let mut lean_env = LeanEnv::default();
    lean_env.insert(name.clone(), LeanConstantInfo::AxiomInfo(axiom.clone()));
    let lean_env = Arc::new(lean_env);

    // Compile
    let stt = compile_env(&lean_env).expect("compile_env failed");

    // Decompile
    let dstt = decompile_env(&stt).expect("decompile_env failed");

    // Check roundtrip
    let recovered = dstt.env.get(&name).expect("name not found");
    match &*recovered {
      LeanConstantInfo::AxiomInfo(ax) => {
        assert_eq!(ax.cnst.name, name);
        assert_eq!(ax.cnst.level_params.len(), 2);
        assert_eq!(ax.cnst.level_params[0], u);
        assert_eq!(ax.cnst.level_params[1], v);
      },
      _ => panic!("Expected AxiomInfo"),
    }
  }

  #[test]
  fn test_roundtrip_definition() {
    use crate::decompile::decompile_env;
    use ix_common::env::{
      ConstantVal, DefinitionSafety, DefinitionVal, ReducibilityHints,
    };

    // Create a definition: def id : Type -> Type := fun x => x
    let name = Name::str(Name::anon(), "id".to_string());
    let type1 = LeanExpr::sort(Level::succ(Level::zero())); // Type
    let typ = LeanExpr::all(
      Name::str(Name::anon(), "x".to_string()),
      type1.clone(),
      type1.clone(),
      ix_common::env::BinderInfo::Default,
    );
    let value = LeanExpr::lam(
      Name::str(Name::anon(), "x".to_string()),
      type1,
      LeanExpr::bvar(Nat::from(0u64)),
      ix_common::env::BinderInfo::Default,
    );
    let def = DefinitionVal {
      cnst: ConstantVal { name: name.clone(), level_params: vec![], typ },
      value,
      hints: ReducibilityHints::Abbrev,
      safety: DefinitionSafety::Safe,
      all: vec![name.clone()],
    };

    let mut lean_env = LeanEnv::default();
    lean_env.insert(name.clone(), LeanConstantInfo::DefnInfo(def.clone()));
    let lean_env = Arc::new(lean_env);

    // Compile
    let stt = compile_env(&lean_env).expect("compile_env failed");

    // Decompile
    let dstt = decompile_env(&stt).expect("decompile_env failed");

    // Check roundtrip
    let recovered = dstt.env.get(&name).expect("name not found");
    match &*recovered {
      LeanConstantInfo::DefnInfo(d) => {
        assert_eq!(d.cnst.name, name);
        assert_eq!(d.hints, def.hints);
        assert_eq!(d.safety, def.safety);
        assert_eq!(d.all.len(), def.all.len());
      },
      _ => panic!("Expected DefnInfo"),
    }
  }

  #[test]
  fn test_roundtrip_def_referencing_axiom() {
    use crate::decompile::decompile_env;
    use ix_common::env::{
      AxiomVal, ConstantVal, DefinitionSafety, DefinitionVal, Env as LeanEnv,
      ReducibilityHints,
    };

    // Create axiom A : Type and def B : A := A
    let axiom_name = Name::str(Name::anon(), "A".to_string());
    let def_name = Name::str(Name::anon(), "B".to_string());

    let type0 = LeanExpr::sort(Level::succ(Level::zero()));
    let axiom = AxiomVal {
      cnst: ConstantVal {
        name: axiom_name.clone(),
        level_params: vec![],
        typ: type0,
      },
      is_unsafe: false,
    };

    let def = DefinitionVal {
      cnst: ConstantVal {
        name: def_name.clone(),
        level_params: vec![],
        typ: LeanExpr::cnst(axiom_name.clone(), vec![]),
      },
      value: LeanExpr::cnst(axiom_name.clone(), vec![]),
      hints: ReducibilityHints::Abbrev,
      safety: DefinitionSafety::Safe,
      all: vec![def_name.clone()],
    };

    let mut lean_env = LeanEnv::default();
    lean_env.insert(axiom_name.clone(), LeanConstantInfo::AxiomInfo(axiom));
    lean_env.insert(def_name.clone(), LeanConstantInfo::DefnInfo(def));
    let lean_env = Arc::new(lean_env);

    // Compile
    let stt = compile_env(&lean_env).expect("compile_env failed");

    // Decompile
    let dstt = decompile_env(&stt).expect("decompile_env failed");

    // Check both roundtrip
    assert!(dstt.env.contains_key(&axiom_name));
    assert!(dstt.env.contains_key(&def_name));

    match &*dstt.env.get(&def_name).unwrap() {
      LeanConstantInfo::DefnInfo(d) => {
        assert_eq!(d.cnst.name, def_name);
      },
      _ => panic!("Expected DefnInfo"),
    }
  }

  #[test]
  fn test_roundtrip_quotient() {
    use crate::decompile::decompile_env;
    use ix_common::env::{ConstantVal, Env as LeanEnv, QuotKind, QuotVal};

    // Create quotient constants
    let quot_name = Name::str(Name::anon(), "Quot".to_string());
    let u = Name::str(Name::anon(), "u".to_string());

    // Quot.{u} : (α : Sort u) → (α → α → Prop) → Sort u
    let alpha = Name::str(Name::anon(), "α".to_string());
    let sort_u = LeanExpr::sort(Level::param(u.clone()));
    let prop = LeanExpr::sort(Level::zero());

    // Build: (α : Sort u) → (α → α → Prop) → Sort u
    let rel_type = LeanExpr::all(
      Name::anon(),
      LeanExpr::bvar(Nat::from(0u64)),
      LeanExpr::all(
        Name::anon(),
        LeanExpr::bvar(Nat::from(1u64)),
        prop.clone(),
        ix_common::env::BinderInfo::Default,
      ),
      ix_common::env::BinderInfo::Default,
    );
    let typ = LeanExpr::all(
      alpha,
      sort_u.clone(),
      LeanExpr::all(
        Name::anon(),
        rel_type,
        sort_u.clone(),
        ix_common::env::BinderInfo::Default,
      ),
      ix_common::env::BinderInfo::Default,
    );

    let quot = QuotVal {
      cnst: ConstantVal {
        name: quot_name.clone(),
        level_params: vec![u.clone()],
        typ,
      },
      kind: QuotKind::Type,
    };

    let mut lean_env = LeanEnv::default();
    lean_env
      .insert(quot_name.clone(), LeanConstantInfo::QuotInfo(quot.clone()));
    let lean_env = Arc::new(lean_env);

    // Compile
    let stt = compile_env(&lean_env).expect("compile_env failed");

    // Decompile
    let dstt = decompile_env(&stt).expect("decompile_env failed");

    // Check roundtrip
    let recovered = dstt.env.get(&quot_name).expect("name not found");
    match &*recovered {
      LeanConstantInfo::QuotInfo(q) => {
        assert_eq!(q.cnst.name, quot_name);
        assert_eq!(q.kind, QuotKind::Type);
        assert_eq!(q.cnst.level_params.len(), 1);
      },
      _ => panic!("Expected QuotInfo"),
    }
  }

  #[test]
  fn test_roundtrip_theorem() {
    use crate::decompile::decompile_env;
    use ix_common::env::{ConstantVal, Env as LeanEnv, TheoremVal};

    // Create a theorem: theorem trivial : True := True.intro
    let name = Name::str(Name::anon(), "trivial".to_string());
    let prop = LeanExpr::sort(Level::zero()); // Prop

    // For simplicity, just use Prop as both type and value
    let thm = TheoremVal {
      cnst: ConstantVal {
        name: name.clone(),
        level_params: vec![],
        typ: prop.clone(),
      },
      value: prop,
      all: vec![name.clone()],
    };

    let mut lean_env = LeanEnv::default();
    lean_env.insert(name.clone(), LeanConstantInfo::ThmInfo(thm.clone()));
    let lean_env = Arc::new(lean_env);

    // Compile
    let stt = compile_env(&lean_env).expect("compile_env failed");

    // Decompile
    let dstt = decompile_env(&stt).expect("decompile_env failed");

    // Check roundtrip
    let recovered = dstt.env.get(&name).expect("name not found");
    match &*recovered {
      LeanConstantInfo::ThmInfo(t) => {
        assert_eq!(t.cnst.name, name);
        assert_eq!(t.all.len(), 1);
      },
      _ => panic!("Expected ThmInfo"),
    }
  }

  #[test]
  fn test_roundtrip_opaque() {
    use crate::decompile::decompile_env;
    use ix_common::env::{ConstantVal, Env as LeanEnv, OpaqueVal};

    // Create an opaque: opaque secret : Nat := 42
    let name = Name::str(Name::anon(), "secret".to_string());
    let nat_type = LeanExpr::sort(Level::zero()); // Using Prop as placeholder

    let opaq = OpaqueVal {
      cnst: ConstantVal {
        name: name.clone(),
        level_params: vec![],
        typ: nat_type.clone(),
      },
      value: nat_type,
      is_unsafe: false,
      all: vec![name.clone()],
    };

    let mut lean_env = LeanEnv::default();
    lean_env.insert(name.clone(), LeanConstantInfo::OpaqueInfo(opaq.clone()));
    let lean_env = Arc::new(lean_env);

    // Compile
    let stt = compile_env(&lean_env).expect("compile_env failed");

    // Decompile
    let dstt = decompile_env(&stt).expect("decompile_env failed");

    // Check roundtrip
    let recovered = dstt.env.get(&name).expect("name not found");
    match &*recovered {
      LeanConstantInfo::OpaqueInfo(o) => {
        assert_eq!(o.cnst.name, name);
        assert!(!o.is_unsafe);
        assert_eq!(o.all.len(), 1);
      },
      _ => panic!("Expected OpaqueInfo"),
    }
  }

  #[test]
  fn test_roundtrip_multiple_constants() {
    use crate::decompile::decompile_env;
    use ix_common::env::{
      AxiomVal, ConstantVal, DefinitionSafety, DefinitionVal, Env as LeanEnv,
      ReducibilityHints, TheoremVal,
    };

    // Create multiple constants of different types
    let axiom_name = Name::str(Name::anon(), "A".to_string());
    let def_name = Name::str(Name::anon(), "B".to_string());
    let thm_name = Name::str(Name::anon(), "C".to_string());

    let type0 = LeanExpr::sort(Level::succ(Level::zero()));
    let prop = LeanExpr::sort(Level::zero());

    let axiom = AxiomVal {
      cnst: ConstantVal {
        name: axiom_name.clone(),
        level_params: vec![],
        typ: type0.clone(),
      },
      is_unsafe: false,
    };

    let def = DefinitionVal {
      cnst: ConstantVal {
        name: def_name.clone(),
        level_params: vec![],
        typ: type0,
      },
      value: LeanExpr::cnst(axiom_name.clone(), vec![]),
      hints: ReducibilityHints::Regular(10),
      safety: DefinitionSafety::Safe,
      all: vec![def_name.clone()],
    };

    let thm = TheoremVal {
      cnst: ConstantVal {
        name: thm_name.clone(),
        level_params: vec![],
        typ: prop.clone(),
      },
      value: prop,
      all: vec![thm_name.clone()],
    };

    let mut lean_env = LeanEnv::default();
    lean_env.insert(axiom_name.clone(), LeanConstantInfo::AxiomInfo(axiom));
    lean_env.insert(def_name.clone(), LeanConstantInfo::DefnInfo(def));
    lean_env.insert(thm_name.clone(), LeanConstantInfo::ThmInfo(thm));
    let lean_env = Arc::new(lean_env);

    // Compile
    let stt = compile_env(&lean_env).expect("compile_env failed");
    assert_eq!(stt.env.const_count(), 3);

    // Decompile
    let dstt = decompile_env(&stt).expect("decompile_env failed");

    // Check all constants roundtrip
    assert!(matches!(
      &*dstt.env.get(&axiom_name).unwrap(),
      LeanConstantInfo::AxiomInfo(_)
    ));
    assert!(matches!(
      &*dstt.env.get(&def_name).unwrap(),
      LeanConstantInfo::DefnInfo(_)
    ));
    assert!(matches!(
      &*dstt.env.get(&thm_name).unwrap(),
      LeanConstantInfo::ThmInfo(_)
    ));
  }

  #[test]
  fn test_roundtrip_inductive_simple() {
    use crate::decompile::decompile_env;
    use ix_common::env::{
      ConstantVal, ConstructorVal, Env as LeanEnv, InductiveVal,
    };

    // Create a simple inductive: inductive Unit : Type where | unit : Unit
    // No recursor to keep it simple and self-contained
    let unit_name = Name::str(Name::anon(), "Unit".to_string());
    let unit_ctor_name = Name::str(unit_name.clone(), "unit".to_string());

    let type0 = LeanExpr::sort(Level::succ(Level::zero())); // Type

    // Unit : Type
    let inductive = InductiveVal {
      cnst: ConstantVal {
        name: unit_name.clone(),
        level_params: vec![],
        typ: type0.clone(),
      },
      num_params: Nat::from(0u64),
      num_indices: Nat::from(0u64),
      all: vec![unit_name.clone()],
      ctors: vec![unit_ctor_name.clone()],
      num_nested: Nat::from(0u64),
      is_rec: false,
      is_unsafe: false,
      is_reflexive: false,
    };

    // Unit.unit : Unit
    let ctor = ConstructorVal {
      cnst: ConstantVal {
        name: unit_ctor_name.clone(),
        level_params: vec![],
        typ: LeanExpr::cnst(unit_name.clone(), vec![]),
      },
      induct: unit_name.clone(),
      cidx: Nat::from(0u64),
      num_params: Nat::from(0u64),
      num_fields: Nat::from(0u64),
      is_unsafe: false,
    };

    let mut lean_env = LeanEnv::default();
    lean_env.insert(
      unit_name.clone(),
      LeanConstantInfo::InductInfo(inductive.clone()),
    );
    lean_env
      .insert(unit_ctor_name.clone(), LeanConstantInfo::CtorInfo(ctor.clone()));
    let lean_env = Arc::new(lean_env);

    // Compile
    let stt = compile_env(&lean_env).expect("compile_env failed");

    // Decompile
    let dstt = decompile_env(&stt).expect("decompile_env failed");

    // Check roundtrip for inductive
    let recovered_ind = dstt.env.get(&unit_name).expect("Unit not found");
    match &*recovered_ind {
      LeanConstantInfo::InductInfo(i) => {
        assert_eq!(i.cnst.name, unit_name);
        assert_eq!(i.ctors.len(), 1);
        assert_eq!(i.all.len(), 1);
      },
      _ => panic!("Expected InductInfo"),
    }

    // Check roundtrip for constructor
    let recovered_ctor =
      dstt.env.get(&unit_ctor_name).expect("Unit.unit not found");
    match &*recovered_ctor {
      LeanConstantInfo::CtorInfo(c) => {
        assert_eq!(c.cnst.name, unit_ctor_name);
        assert_eq!(c.induct, unit_name);
      },
      _ => panic!("Expected CtorInfo"),
    }
  }

  #[test]
  fn test_roundtrip_inductive_with_multiple_ctors() {
    use crate::decompile::decompile_env;
    use ix_common::env::{
      ConstantVal, ConstructorVal, Env as LeanEnv, InductiveVal,
    };

    // Create Bool with two constructors (no recursor to keep self-contained)
    let bool_name = Name::str(Name::anon(), "Bool".to_string());
    let false_name = Name::str(bool_name.clone(), "false".to_string());
    let true_name = Name::str(bool_name.clone(), "true".to_string());

    let type0 = LeanExpr::sort(Level::succ(Level::zero()));
    let bool_type = LeanExpr::cnst(bool_name.clone(), vec![]);

    let inductive = InductiveVal {
      cnst: ConstantVal {
        name: bool_name.clone(),
        level_params: vec![],
        typ: type0,
      },
      num_params: Nat::from(0u64),
      num_indices: Nat::from(0u64),
      all: vec![bool_name.clone()],
      ctors: vec![false_name.clone(), true_name.clone()],
      num_nested: Nat::from(0u64),
      is_rec: false,
      is_unsafe: false,
      is_reflexive: false,
    };

    let ctor_false = ConstructorVal {
      cnst: ConstantVal {
        name: false_name.clone(),
        level_params: vec![],
        typ: bool_type.clone(),
      },
      induct: bool_name.clone(),
      cidx: Nat::from(0u64),
      num_params: Nat::from(0u64),
      num_fields: Nat::from(0u64),
      is_unsafe: false,
    };

    let ctor_true = ConstructorVal {
      cnst: ConstantVal {
        name: true_name.clone(),
        level_params: vec![],
        typ: bool_type.clone(),
      },
      induct: bool_name.clone(),
      cidx: Nat::from(1u64),
      num_params: Nat::from(0u64),
      num_fields: Nat::from(0u64),
      is_unsafe: false,
    };

    let mut lean_env = LeanEnv::default();
    lean_env.insert(bool_name.clone(), LeanConstantInfo::InductInfo(inductive));
    lean_env.insert(false_name.clone(), LeanConstantInfo::CtorInfo(ctor_false));
    lean_env.insert(true_name.clone(), LeanConstantInfo::CtorInfo(ctor_true));
    let lean_env = Arc::new(lean_env);

    // Compile
    let stt = compile_env(&lean_env).expect("compile_env failed");

    // Decompile
    let dstt = decompile_env(&stt).expect("decompile_env failed");

    // Check roundtrip
    let recovered = dstt.env.get(&bool_name).expect("Bool not found");
    match &*recovered {
      LeanConstantInfo::InductInfo(i) => {
        assert_eq!(i.cnst.name, bool_name);
        assert_eq!(i.ctors.len(), 2);
      },
      _ => panic!("Expected InductInfo"),
    }

    // Check both constructors
    assert!(dstt.env.contains_key(&false_name));
    assert!(dstt.env.contains_key(&true_name));
  }

  #[test]
  fn test_roundtrip_mutual_definitions() {
    use crate::decompile::decompile_env;
    use ix_common::env::{
      ConstantVal, DefinitionSafety, DefinitionVal, Env as LeanEnv,
      ReducibilityHints,
    };

    // Create mutual definitions that only reference each other (self-contained)
    // def f : Type → Type and def g : Type → Type
    // where f references g and g references f
    let f_name = Name::str(Name::anon(), "f".to_string());
    let g_name = Name::str(Name::anon(), "g".to_string());

    let type0 = LeanExpr::sort(Level::succ(Level::zero())); // Type
    let fn_type = LeanExpr::all(
      Name::anon(),
      type0.clone(),
      type0.clone(),
      ix_common::env::BinderInfo::Default,
    );

    // f := fun x => g x
    let f_value = LeanExpr::lam(
      Name::str(Name::anon(), "x".to_string()),
      type0.clone(),
      LeanExpr::app(
        LeanExpr::cnst(g_name.clone(), vec![]),
        LeanExpr::bvar(Nat::from(0u64)),
      ),
      ix_common::env::BinderInfo::Default,
    );

    // g := fun x => f x
    let g_value = LeanExpr::lam(
      Name::str(Name::anon(), "x".to_string()),
      type0.clone(),
      LeanExpr::app(
        LeanExpr::cnst(f_name.clone(), vec![]),
        LeanExpr::bvar(Nat::from(0u64)),
      ),
      ix_common::env::BinderInfo::Default,
    );

    // Mutual block: both reference each other
    let all = vec![f_name.clone(), g_name.clone()];

    let f_def = DefinitionVal {
      cnst: ConstantVal {
        name: f_name.clone(),
        level_params: vec![],
        typ: fn_type.clone(),
      },
      value: f_value,
      hints: ReducibilityHints::Regular(1),
      safety: DefinitionSafety::Safe,
      all: all.clone(),
    };

    let g_def = DefinitionVal {
      cnst: ConstantVal {
        name: g_name.clone(),
        level_params: vec![],
        typ: fn_type,
      },
      value: g_value,
      hints: ReducibilityHints::Regular(1),
      safety: DefinitionSafety::Safe,
      all: all.clone(),
    };

    let mut lean_env = LeanEnv::default();
    lean_env.insert(f_name.clone(), LeanConstantInfo::DefnInfo(f_def));
    lean_env.insert(g_name.clone(), LeanConstantInfo::DefnInfo(g_def));
    let lean_env = Arc::new(lean_env);

    // Compile
    let stt = compile_env(&lean_env).expect("compile_env failed");

    // f and g are alpha-equivalent (both `λ x => other x` with the same
    // type) so they collapse to a singleton non-inductive class. The
    // compiler unwraps this to a standalone Defn — no Ixon block entry.
    assert!(
      stt.blocks.is_empty(),
      "singleton-unwrapped mutual should have no block entry"
    );

    // Decompile
    let dstt = decompile_env(&stt).expect("decompile_env failed");

    // Check both definitions roundtrip
    let recovered_f = dstt.env.get(&f_name).expect("f not found");
    match &*recovered_f {
      LeanConstantInfo::DefnInfo(d) => {
        assert_eq!(d.cnst.name, f_name);
        // The all field should contain both names
        assert_eq!(d.all.len(), 2);
      },
      _ => panic!("Expected DefnInfo for f"),
    }

    let recovered_g = dstt.env.get(&g_name).expect("g not found");
    match &*recovered_g {
      LeanConstantInfo::DefnInfo(d) => {
        assert_eq!(d.cnst.name, g_name);
        assert_eq!(d.all.len(), 2);
      },
      _ => panic!("Expected DefnInfo for g"),
    }
  }

  #[test]
  fn test_roundtrip_mutual_inductives() {
    use crate::decompile::decompile_env;
    use ix_common::env::{
      ConstantVal, ConstructorVal, Env as LeanEnv, InductiveVal,
    };

    // Create two mutually recursive inductives (simplified):
    // inductive Even : Type where | zero : Even | succ : Odd → Even
    // inductive Odd : Type where | succ : Even → Odd
    let even_name = Name::str(Name::anon(), "Even".to_string());
    let odd_name = Name::str(Name::anon(), "Odd".to_string());
    let even_zero = Name::str(even_name.clone(), "zero".to_string());
    let even_succ = Name::str(even_name.clone(), "succ".to_string());
    let odd_succ = Name::str(odd_name.clone(), "succ".to_string());

    let type0 = LeanExpr::sort(Level::succ(Level::zero())); // Type
    let even_type = LeanExpr::cnst(even_name.clone(), vec![]);
    let odd_type = LeanExpr::cnst(odd_name.clone(), vec![]);

    let all = vec![even_name.clone(), odd_name.clone()];

    let even_ind = InductiveVal {
      cnst: ConstantVal {
        name: even_name.clone(),
        level_params: vec![],
        typ: type0.clone(),
      },
      num_params: Nat::from(0u64),
      num_indices: Nat::from(0u64),
      all: all.clone(),
      ctors: vec![even_zero.clone(), even_succ.clone()],
      num_nested: Nat::from(0u64),
      is_rec: true, // mutually recursive
      is_unsafe: false,
      is_reflexive: false,
    };

    let odd_ind = InductiveVal {
      cnst: ConstantVal {
        name: odd_name.clone(),
        level_params: vec![],
        typ: type0.clone(),
      },
      num_params: Nat::from(0u64),
      num_indices: Nat::from(0u64),
      all: all.clone(),
      ctors: vec![odd_succ.clone()],
      num_nested: Nat::from(0u64),
      is_rec: true,
      is_unsafe: false,
      is_reflexive: false,
    };

    // Even.zero : Even
    let even_zero_ctor = ConstructorVal {
      cnst: ConstantVal {
        name: even_zero.clone(),
        level_params: vec![],
        typ: even_type.clone(),
      },
      induct: even_name.clone(),
      cidx: Nat::from(0u64),
      num_params: Nat::from(0u64),
      num_fields: Nat::from(0u64),
      is_unsafe: false,
    };

    // Even.succ : Odd → Even
    let even_succ_type = LeanExpr::all(
      Name::anon(),
      odd_type.clone(),
      even_type.clone(),
      ix_common::env::BinderInfo::Default,
    );

    let even_succ_ctor = ConstructorVal {
      cnst: ConstantVal {
        name: even_succ.clone(),
        level_params: vec![],
        typ: even_succ_type,
      },
      induct: even_name.clone(),
      cidx: Nat::from(1u64),
      num_params: Nat::from(0u64),
      num_fields: Nat::from(1u64),
      is_unsafe: false,
    };

    // Odd.succ : Even → Odd
    let odd_succ_type = LeanExpr::all(
      Name::anon(),
      even_type.clone(),
      odd_type.clone(),
      ix_common::env::BinderInfo::Default,
    );

    let odd_succ_ctor = ConstructorVal {
      cnst: ConstantVal {
        name: odd_succ.clone(),
        level_params: vec![],
        typ: odd_succ_type,
      },
      induct: odd_name.clone(),
      cidx: Nat::from(0u64),
      num_params: Nat::from(0u64),
      num_fields: Nat::from(1u64),
      is_unsafe: false,
    };

    let mut lean_env = LeanEnv::default();
    lean_env.insert(even_name.clone(), LeanConstantInfo::InductInfo(even_ind));
    lean_env.insert(odd_name.clone(), LeanConstantInfo::InductInfo(odd_ind));
    lean_env
      .insert(even_zero.clone(), LeanConstantInfo::CtorInfo(even_zero_ctor));
    lean_env
      .insert(even_succ.clone(), LeanConstantInfo::CtorInfo(even_succ_ctor));
    lean_env
      .insert(odd_succ.clone(), LeanConstantInfo::CtorInfo(odd_succ_ctor));
    let lean_env = Arc::new(lean_env);

    // Compile
    let stt = compile_env(&lean_env).expect("compile_env failed");

    // Should have at least one mutual block
    assert!(!stt.blocks.is_empty(), "Expected mutual block for Even/Odd");

    // Decompile
    let dstt = decompile_env(&stt).expect("decompile_env failed");

    // Check Even roundtrip
    let recovered_even = dstt.env.get(&even_name).expect("Even not found");
    match &*recovered_even {
      LeanConstantInfo::InductInfo(i) => {
        assert_eq!(i.cnst.name, even_name);
        assert_eq!(i.ctors.len(), 2);
        assert_eq!(i.all.len(), 2); // Even and Odd in mutual block
      },
      _ => panic!("Expected InductInfo for Even"),
    }

    // Check Odd roundtrip
    let recovered_odd = dstt.env.get(&odd_name).expect("Odd not found");
    match &*recovered_odd {
      LeanConstantInfo::InductInfo(i) => {
        assert_eq!(i.cnst.name, odd_name);
        assert_eq!(i.ctors.len(), 1);
        assert_eq!(i.all.len(), 2);
      },
      _ => panic!("Expected InductInfo for Odd"),
    }

    // Check all constructors exist
    assert!(dstt.env.contains_key(&even_zero));
    assert!(dstt.env.contains_key(&even_succ));
    assert!(dstt.env.contains_key(&odd_succ));
  }

  #[test]
  fn test_roundtrip_inductive_with_recursor() {
    use crate::decompile::decompile_env;
    use ix_common::env::{ConstantVal, InductiveVal, RecursorVal};

    // Create Empty type with recursor (no constructors)
    // inductive Empty : Type
    // Empty.rec.{u} : (motive : Empty → Sort u) → (e : Empty) → motive e
    let empty_name = Name::str(Name::anon(), "Empty".to_string());
    let empty_rec_name = Name::str(empty_name.clone(), "rec".to_string());
    let u = Name::str(Name::anon(), "u".to_string());

    let type0 = LeanExpr::sort(Level::succ(Level::zero())); // Type
    let empty_type = LeanExpr::cnst(empty_name.clone(), vec![]);

    let inductive = InductiveVal {
      cnst: ConstantVal {
        name: empty_name.clone(),
        level_params: vec![],
        typ: type0.clone(),
      },
      num_params: Nat::from(0u64),
      num_indices: Nat::from(0u64),
      all: vec![empty_name.clone()],
      ctors: vec![], // No constructors!
      num_nested: Nat::from(0u64),
      is_rec: false,
      is_unsafe: false,
      is_reflexive: false,
    };

    // Empty.rec.{u} : (motive : Empty → Sort u) → (e : Empty) → motive e
    let motive_type = LeanExpr::all(
      Name::anon(),
      empty_type.clone(),
      LeanExpr::sort(Level::param(u.clone())),
      ix_common::env::BinderInfo::Default,
    );
    let rec_type = LeanExpr::all(
      Name::str(Name::anon(), "motive".to_string()),
      motive_type,
      LeanExpr::all(
        Name::str(Name::anon(), "e".to_string()),
        empty_type.clone(),
        LeanExpr::app(
          LeanExpr::bvar(Nat::from(1u64)),
          LeanExpr::bvar(Nat::from(0u64)),
        ),
        ix_common::env::BinderInfo::Default,
      ),
      ix_common::env::BinderInfo::Implicit,
    );

    let recursor = RecursorVal {
      cnst: ConstantVal {
        name: empty_rec_name.clone(),
        level_params: vec![u.clone()],
        typ: rec_type,
      },
      all: vec![empty_name.clone()],
      num_params: Nat::from(0u64),
      num_indices: Nat::from(0u64),
      num_motives: Nat::from(1u64),
      num_minors: Nat::from(0u64), // No minor premises for Empty
      rules: vec![],               // No rules since no constructors
      k: true,
      is_unsafe: false,
    };

    let mut lean_env = LeanEnv::default();
    lean_env
      .insert(empty_name.clone(), LeanConstantInfo::InductInfo(inductive));
    lean_env
      .insert(empty_rec_name.clone(), LeanConstantInfo::RecInfo(recursor));
    let lean_env = Arc::new(lean_env);

    // Compile
    let stt = compile_env(&lean_env).expect("compile_env failed");

    // Decompile
    let dstt = decompile_env(&stt).expect("decompile_env failed");

    // Check inductive roundtrip
    let recovered_ind = dstt.env.get(&empty_name).expect("Empty not found");
    match &*recovered_ind {
      LeanConstantInfo::InductInfo(i) => {
        assert_eq!(i.cnst.name, empty_name);
        assert_eq!(i.ctors.len(), 0);
      },
      _ => panic!("Expected InductInfo"),
    }

    // Check recursor roundtrip
    let recovered_rec =
      dstt.env.get(&empty_rec_name).expect("Empty.rec not found");
    match &*recovered_rec {
      LeanConstantInfo::RecInfo(r) => {
        assert_eq!(r.cnst.name, empty_rec_name);
        assert_eq!(r.rules.len(), 0);
        assert_eq!(r.cnst.level_params.len(), 1);
      },
      _ => panic!("Expected RecInfo"),
    }
  }

  // ==========================================================================
  // The canonical sharing route
  // ==========================================================================

  /// The `T2 → T2` witness of `docs/sharing-minimum.md` §2 as an axiom
  /// payload (with univs `[Zero]` and no refs).
  fn t2_arrow_t2() -> Axiom {
    let p = Expr::sort(0);
    let t1 = Expr::all(p.clone(), p.clone());
    let t2 = Expr::all(p, t1);
    Axiom { is_unsafe: false, lvls: 0, typ: Expr::all(t2.clone(), t2) }
  }

  fn constant_hex(c: &Constant) -> String {
    let mut buf = Vec::new();
    c.put(&mut buf);
    buf.iter().map(|b| format!("{b:02x}")).collect()
  }

  /// The compiler route is the canonical construction: it reaches the
  /// 17-byte minimum of the witness.
  #[test]
  fn compiler_route_reaches_the_17_byte_minimum() {
    let r = apply_sharing_to_axiom_with_limits(
      &ExactSharingLimits::default(),
      t2_arrow_t2(),
      vec![],
      vec![Univ::zero()],
    )
    .unwrap();
    assert_eq!(constant_hex(&r), "d200009117b0b001921700170000000100");
  }

  /// The compiler route builds exactly what the library normalizer builds
  /// from the unshared Constant, for every payload kind it dispatches on.
  #[test]
  fn compiler_route_matches_the_normalizer() {
    use ixon::constant::{DefKind, Definition, MutConst as IxonMutConst};
    use ixon::sharing_exact::normalize_constant_sharing_tiered;
    let ax = t2_arrow_t2();
    let def = Definition {
      kind: DefKind::Definition,
      safety: ix_common::env::DefinitionSafety::Safe,
      lvls: 0,
      typ: ax.typ.clone(),
      value: Expr::app(ax.typ.clone(), ax.typ.clone()),
    };
    let limits = ExactSharingLimits::default();
    let univs = vec![Univ::zero()];
    let cases = [
      (
        ConstantInfo::Axio(ax.clone()),
        apply_sharing_to_axiom_with_limits(
          &limits,
          ax.clone(),
          vec![],
          univs.clone(),
        )
        .unwrap(),
      ),
      (
        ConstantInfo::Defn(def.clone()),
        apply_sharing_to_definition_with_limits(
          &limits,
          def.clone(),
          vec![],
          univs.clone(),
        )
        .unwrap(),
      ),
      (
        ConstantInfo::Muts(vec![
          IxonMutConst::Defn(def.clone()),
          IxonMutConst::Defn(def.clone()),
        ]),
        apply_sharing_to_mutual_block_with_limits(
          &limits,
          vec![IxonMutConst::Defn(def.clone()), IxonMutConst::Defn(def)],
          vec![],
          univs.clone(),
        )
        .unwrap(),
      ),
    ];
    for (info, routed) in cases {
      let unshared = Constant::with_tables(info, vec![], vec![], univs.clone());
      let (normalized, _) = normalize_constant_sharing_tiered(
        ShareLayout::TagN,
        &unshared,
        &limits,
      )
      .unwrap();
      assert_eq!(routed, normalized);
    }
  }

  /// A construction that runs out of its limits is a compile error; there is
  /// no fallback.
  #[test]
  fn compiler_route_fails_closed() {
    let limits = ExactSharingLimits {
      max_distinct_nodes: 2,
      ..ExactSharingLimits::default()
    };
    let err = apply_sharing_to_axiom_with_limits(
      &limits,
      t2_arrow_t2(),
      vec![],
      vec![Univ::zero()],
    )
    .expect_err("the route must fail under these limits");
    assert!(matches!(err, CompileError::ResourceLimit { .. }), "{err}");
    // The error names the limit and how to raise it.
    let msg = format!("{err}");
    assert!(
      msg.contains("resource exhausted: distinct_nodes (limit 2)")
        && msg.contains("--sharing-limits distinct_nodes=N")
        && msg.contains(SHARING_LIMITS_ENV),
      "{msg}"
    );
  }

  /// The compiler limits are the library defaults plus the override, and an
  /// invalid override is an error that names the variable.
  #[test]
  fn compiler_sharing_limits_override() {
    assert_eq!(
      compiler_sharing_limits_with(None).unwrap(),
      ExactSharingLimits::default()
    );
    let l = compiler_sharing_limits_with(Some("states=2^10, work=7,depth=3"))
      .unwrap();
    assert_eq!((l.max_states, l.max_work), (1024, 7));
    assert_eq!(l.max_height, ExactSharingLimits::default().max_height);
    let err = compiler_sharing_limits_with(Some("bogus=1")).unwrap_err();
    assert!(err.starts_with("IX_SHARING_LIMITS: unknown sharing limit bogus"));
  }
}
