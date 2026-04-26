//! Permutation-aware alpha-equivalence for aux_gen congruence tests.
//!
//! # Motivation
//!
//! `aux_gen::generate_aux_patches` emits constants in **canonical layout**
//! — nested auxiliaries are hash-sorted, alpha-collapsed class members
//! collapse to their representatives. Lean's originals, by contrast, use
//! **source-walk layout** — aux positions are determined by the elaborator's
//! traversal order, alpha-aliased inductives appear under their original
//! names. A naive structural comparison therefore diverges at:
//!
//! 1. **Motive/minor positions** in the outer binder chain: gen has them
//!    in canonical (hash-sorted) order, orig has them in source order.
//!    A single `perm: source_j → canonical_i` describes the mapping.
//!
//! 2. **Const references to alpha-collapsed aliases**: gen uses
//!    `TreeA` (class representative) where orig references `TreeB` (alias).
//!    A name map `TreeB → TreeA` is sufficient; derived names (`.rec`,
//!    `.below`, `.brecOn`, etc.) and constructors follow positionally.
//!
//! 3. **`.rec` application spines inside `.casesOn` / `.recOn` /
//!    `.below` / `.brecOn` values**: gen passes motive/minor args in
//!    canonical positions; orig passes them in source positions. Same
//!    `perm` applies to the args of the inner App spine.
//!
//! # Design
//!
//! The previous implementation (`aux_gen::canonicalize`) rebuilt the Lean
//! original into canonical layout by opening its outer binder chain,
//! reordering `LocalDecl`s, and re-closing with `mk_forall` / `mk_lambda`.
//! That approach has three failure modes:
//!
//! - It doesn't rewrite `Const` references (aux-name and alias mismatches
//!   slip through silently),
//! - Its inner rec-call-spine recognizer bails on complex value shapes
//!   (`.brecOn.go`, `.brecOn.eq`, `.recOn`), leaving BVar references stale
//!   against reordered outer decls,
//! - Its rule rhs BVar arithmetic works only for the flat `rec` case.
//!
//! This module instead **walks both trees in lockstep** with a permutation
//! context in scope:
//!
//! - Outer binder chain is opened on **both** sides into fresh FVars.
//! - An FVar correspondence `orig_fv[source_pos] → gen_fv[canonical_pos]`
//!   is built once from [`PermCtx`].
//! - Bodies are compared via [`expr_alpha_eq_ctx`], which resolves
//!   FVars through the correspondence, Const names through
//!   [`PermCtx::const_map`], and App spines through
//!   [`app_spine_alpha_eq_ctx`] (the only place that peeks at app heads
//!   to apply arg permutation at known rec heads).
//!
//! All three failure modes from the old approach dissolve: Const
//! rewrites happen at every node, no re-closing means no BVar
//! arithmetic, and App-spine permutation is uniform across all value
//! shapes.
//!
//! # Scope
//!
//! Handles:
//! - `RecInfo` — type (∀ params motives minors indices major, body) and
//!   rules (each rhs is `λ params motives minors fields, body`).
//! - `DefnInfo` / `ThmInfo` / `OpaqueInfo` — type (∀ params motives
//!   [minors] indices major, body) and value (λ params motives
//!   [indices major [minors]], body).
//! - `InductInfo`, `CtorInfo`, `AxiomInfo`, `QuotInfo` — pass-through
//!   (no permutation needed).

use lean_ffi::nat::Nat;
use rustc_hash::FxHashMap;

use crate::ix::compile::aux_gen::expr_utils::{
  forall_telescope, lambda_telescope,
};
use crate::ix::{
  address::Address,
  env::{
    ConstantInfo, ConstantVal, Expr, ExprData, Name, RecursorRule, RecursorVal,
  },
};

use super::{check_nat_eq, expr_alpha_eq, level_alpha_eq, strip_mdata};

/// Sentinel for `aux_perm` entries that don't correspond to any canonical
/// aux — the source aux references inductives outside the current SCC
/// block. Matches `aux_gen::nested::PERM_OUT_OF_SCC`.
pub const PERM_OUT_OF_SCC: usize = usize::MAX;

/// Per-block permutation context for [`const_alpha_eq_with_perm`].
///
/// Built once per mutual block (from `aux_gen`'s `AuxPatchesOutput` plus
/// the surrounding env/class information). Passed unchanged into every
/// per-patch congruence check for that block.
///
/// All counts are relative to the **block**, not to any particular
/// recursor — so a single `PermCtx` suffices for every patch produced
/// from that block (primary recursor, aux recursors, `.below`, `.brecOn`,
/// `.casesOn`, `.recOn`, etc.).
#[derive(Debug, Clone)]
pub struct PermCtx {
  /// `aux_perm[source_j] = canonical_i`. May contain [`PERM_OUT_OF_SCC`]
  /// for source auxes that don't correspond to any canonical aux in the
  /// current SCC (those auxes belong to a different block's
  /// compilation). Not in `None` state — callers build an identity
  /// perm when the block has no nested auxes, and `PermCtx::is_identity`
  /// detects that.
  pub aux_perm: Vec<usize>,
  /// Number of block parameters (unchanged between source and canonical).
  pub n_params: usize,
  /// Number of primary (non-aux) class members.
  pub n_primary: usize,
  /// Ctor counts per primary member, in primary order. Same on both
  /// sides under Phase 2 singleton classes; may differ under
  /// alpha-collapse.
  pub primary_ctor_counts: Vec<usize>,
  /// Ctor counts per source-walk aux member, indexed by source position.
  /// Length equals `aux_perm.len()`.
  pub source_aux_ctor_counts: Vec<usize>,
  /// Const-name substitution: applied to `orig`-side [`Expr::Const`]
  /// nodes before comparison. Covers:
  /// - alpha-collapse aliases (`TreeB → TreeA`),
  /// - source-indexed aux names (`_nested.List_5 → _nested.List_2`),
  /// - derived names (`.rec`, `.below`, `.brecOn`, `.casesOn`, `.recOn`)
  ///   of both of the above,
  /// - constructor names of alpha-collapsed classes.
  ///
  /// Identity-mapped keys (e.g., `Nat → Nat`) may be present but add no
  /// cost — the comparator short-circuits when mapped name equals orig
  /// name.
  pub const_map: FxHashMap<Name, Name>,
  /// Content-address equivalence for constants that are canonically equal but
  /// may appear with different source names inside nested aux domains.
  pub const_addr: FxHashMap<Name, Address>,
  /// App-spine info for known recursor heads. When the comparator
  /// encounters `Const(name, _) arg₁ arg₂ …` where `name` (after
  /// `const_map`) is a key in this map, it permutes the motive / minor
  /// arg sections per the aux layout before recursing.
  ///
  /// Only populated for the block's own recursors — external recursors
  /// (e.g. `PProd.rec`, `Nat.rec`) don't need permutation because their
  /// motive/minor positions are shared between source and canonical.
  pub rec_heads: FxHashMap<Name, RecHeadInfo>,
}

/// Kind of permutation-sensitive head: tells
/// [`app_spine_alpha_eq_ctx`] which sections of the App spine to
/// permute.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RecHeadKind {
  /// Full recursor: `params | motives | minors | indices | major`.
  /// Motives **and** minors are permuted (minors group-wise by aux
  /// position).
  Rec,
  /// `.below` family (Type-level definition or Prop-level inductive):
  /// `params | motives | indices | major`. Motives are permuted;
  /// no minors or fs.
  Below,
  /// `.brecOn` / `.brecOn.go` / `.brecOn.eq`:
  /// `params | motives | indices | major | fs` (one F_k per motive).
  /// Motives and fs are permuted with the same permutation (the fs
  /// are per-motive in Lean's layout).
  BRecOn,
  /// `.casesOn`: outer chain is `params | target_motive | indices |
  /// major | target_minors`. The public spine has only one motive
  /// and one ctor-group's worth of minors — **no block-wide
  /// permutation** applies to its args. Listed for completeness;
  /// the comparator shouldn't need to permute `.casesOn` spines,
  /// but if a downstream caller wants to explicitly flag `.casesOn`
  /// heads (e.g., to catch shape mismatches early) this kind lets
  /// it do so.
  CasesOn,
}

/// Structural metadata for a permutation-sensitive head, used by
/// [`app_spine_alpha_eq_ctx`] to slice App spines and permute the
/// motive / minor / fs argument sections.
#[derive(Debug, Clone)]
pub struct RecHeadInfo {
  /// Which head kind this is.
  pub kind: RecHeadKind,
  /// Same as [`PermCtx::n_params`] for the recursor's block.
  pub n_params: usize,
  /// `n_primary + n_source_aux` — total motive count in the source layout.
  pub n_motives: usize,
  /// Total minor count (sum of ctor counts). Only used for
  /// [`RecHeadKind::Rec`]; other kinds leave this at 0.
  pub n_minors: usize,
  /// Number of indices between minors and major premise.
  pub n_indices: usize,
  /// Ctor counts per primary member, shared with `PermCtx`.
  pub primary_ctor_counts: Vec<usize>,
  /// Ctor counts per source-walk aux member, shared with `PermCtx`.
  pub source_aux_ctor_counts: Vec<usize>,
  /// `aux_perm` copy so the comparator can permute independently of the
  /// per-block context (future-proofing for mixed-block App spines).
  pub aux_perm: Vec<usize>,
}

impl PermCtx {
  /// Number of source-walk aux members (= `source_aux_ctor_counts.len()`).
  pub fn n_source_aux(&self) -> usize {
    self.source_aux_ctor_counts.len()
  }

  /// Number of canonical aux members (distinct `canonical_i` values in
  /// `aux_perm`, ignoring [`PERM_OUT_OF_SCC`]).
  pub fn n_canonical_aux(&self) -> usize {
    let mut max_c: Option<usize> = None;
    for &c in &self.aux_perm {
      if c != PERM_OUT_OF_SCC {
        max_c = Some(max_c.map_or(c, |m| m.max(c)));
      }
    }
    max_c.map_or(0, |m| m + 1)
  }

  /// Total source-layout motive count: `n_primary + n_source_aux`.
  pub fn n_source_motives(&self) -> usize {
    self.n_primary + self.n_source_aux()
  }

  /// Total canonical-layout motive count: `n_primary + n_canonical_aux`.
  pub fn n_canonical_motives(&self) -> usize {
    self.n_primary + self.n_canonical_aux()
  }

  /// Total source-layout minor count.
  pub fn n_source_minors(&self) -> usize {
    self.primary_ctor_counts.iter().sum::<usize>()
      + self.source_aux_ctor_counts.iter().sum::<usize>()
  }

  /// Total canonical-layout minor count.
  pub fn n_canonical_minors(&self) -> usize {
    let primary: usize = self.primary_ctor_counts.iter().sum();
    let mut aux = 0usize;
    for ci in 0..self.n_canonical_aux() {
      aux += self.canonical_aux_ctor_count(ci);
    }
    primary + aux
  }

  /// Whether the context is trivial: identity permutation, empty
  /// const_map, and no rec heads to permute. If so, [`const_alpha_eq_with_perm`]
  /// delegates to plain [`const_alpha_eq`](super::const_alpha_eq).
  pub fn is_identity(&self) -> bool {
    self.const_map.is_empty()
      && self.const_addr.is_empty()
      && self.rec_heads.is_empty()
      && self.aux_perm.iter().enumerate().all(|(i, &p)| i == p)
  }

  /// Apply `const_map` to an orig-side const name; returns the original
  /// name if no mapping exists.
  pub fn map_name<'a>(&'a self, name: &'a Name) -> &'a Name {
    self.const_map.get(name).unwrap_or(name)
  }

  pub fn const_names_equiv(&self, generated: &Name, orig: &Name) -> bool {
    let mapped = self.map_name(orig);
    generated == mapped
      || matches!(
        (self.const_addr.get(generated), self.const_addr.get(orig)),
        (Some(a), Some(b)) if a == b
      )
  }

  /// Canonical-aux minor-group offset: `primary_minors + sum_of_source_ctor_counts_of_canonical_aux_preceding(canonical_i)`.
  ///
  /// Each canonical aux inherits its ctor count from its min-source
  /// representative (the smallest `source_j` with `aux_perm[source_j]
  /// == canonical_i`). For a bijective perm, this equals
  /// `source_aux_ctor_counts[inv_perm[canonical_i]]`.
  fn canonical_aux_minor_offset(&self, canonical_i: usize) -> usize {
    let primary_minors: usize = self.primary_ctor_counts.iter().sum();
    let mut off = primary_minors;
    for ci in 0..canonical_i {
      off += self.canonical_aux_ctor_count(ci);
    }
    off
  }

  /// Ctor count for the canonical aux at position `canonical_i`, taken
  /// from the first source aux that maps to it (stable under duplicate
  /// `aux_perm` entries from alpha-collapse).
  fn canonical_aux_ctor_count(&self, canonical_i: usize) -> usize {
    for (source_j, &c) in self.aux_perm.iter().enumerate() {
      if c == canonical_i {
        return self.source_aux_ctor_counts[source_j];
      }
    }
    // Unreachable for well-formed perms (every `canonical_i` has ≥1
    // source mapping). Falling back to 0 avoids a panic path in the
    // comparator; downstream count mismatches will surface via
    // `check_nat_eq` on the recursor's `num_minors`.
    0
  }

  /// Translate a source-layout scope position to its canonical-layout
  /// counterpart for an abstract section = "params + motives + minors".
  /// Returns `None` if this source position has no canonical equivalent
  /// (e.g., an out-of-SCC aux motive).
  fn source_to_canonical_pos(&self, source_pos: usize) -> Option<usize> {
    let n_primary = self.n_primary;
    let _n_source_aux = self.n_source_aux();
    let n_source_motives = self.n_source_motives();
    let primary_minors: usize = self.primary_ctor_counts.iter().sum();

    if source_pos < self.n_params {
      // Params: identity.
      Some(source_pos)
    } else if source_pos < self.n_params + n_primary {
      // Primary motives: identity (primary classes aren't permuted).
      Some(source_pos)
    } else if source_pos < self.n_params + n_source_motives {
      // Aux motive.
      let source_j = source_pos - self.n_params - n_primary;
      let canonical_i = self.aux_perm[source_j];
      if canonical_i == PERM_OUT_OF_SCC {
        return None;
      }
      Some(self.n_params + n_primary + canonical_i)
    } else if source_pos < self.n_params + n_source_motives + primary_minors {
      // Primary minors: identity.
      let canonical_motives = self.n_canonical_motives();
      let minor_off = source_pos - (self.n_params + n_source_motives);
      Some(self.n_params + canonical_motives + minor_off)
    } else {
      // Aux minor.
      let minor_off = source_pos - (self.n_params + n_source_motives);
      let aux_minor_off = minor_off - primary_minors;
      // Find which source aux group this minor belongs to.
      let mut acc = 0usize;
      for (source_j, &cnt) in self.source_aux_ctor_counts.iter().enumerate() {
        if aux_minor_off < acc + cnt {
          let k = aux_minor_off - acc;
          let canonical_i = self.aux_perm[source_j];
          if canonical_i == PERM_OUT_OF_SCC {
            return None;
          }
          let canonical_motives = self.n_canonical_motives();
          let canon_group_off = self.canonical_aux_minor_offset(canonical_i);
          return Some(self.n_params + canonical_motives + canon_group_off + k);
        }
        acc += cnt;
      }
      None
    }
  }
}

/// FVar correspondence: maps orig-side FVar names to their gen-side
/// counterparts. Built once per binder telescope, passed by shared
/// reference into the alpha-eq walk.
#[derive(Default, Clone)]
pub(crate) struct Corr {
  fvar_map: FxHashMap<Name, Name>,
  fvar_alts: FxHashMap<Name, Vec<Name>>,
  punit_motive_gen: Vec<Name>,
  punit_motive_orig: Vec<Name>,
}

impl Corr {
  fn new() -> Self {
    Corr {
      fvar_map: FxHashMap::default(),
      fvar_alts: FxHashMap::default(),
      punit_motive_gen: Vec::new(),
      punit_motive_orig: Vec::new(),
    }
  }

  fn insert(&mut self, orig_name: Name, gen_name: Name) {
    self.fvar_map.insert(orig_name, gen_name);
  }

  fn insert_alt(&mut self, orig_name: Name, gen_name: Name) {
    let alts = self.fvar_alts.entry(orig_name).or_default();
    if !alts.iter().any(|n| n == &gen_name) {
      alts.push(gen_name);
    }
  }

  fn insert_punit_motive(&mut self, orig_name: Name, gen_name: Name) {
    if !self.punit_motive_orig.iter().any(|n| n == &orig_name) {
      self.punit_motive_orig.push(orig_name);
    }
    if !self.punit_motive_gen.iter().any(|n| n == &gen_name) {
      self.punit_motive_gen.push(gen_name);
    }
  }

  /// Whether the orig-side FVar `name` has a gen-side counterpart.
  fn get<'a>(&'a self, name: &Name) -> Option<&'a Name> {
    self.fvar_map.get(name)
  }

  fn accepts(&self, orig_name: &Name, gen_name: &Name) -> bool {
    self.fvar_map.get(orig_name).is_some_and(|expected| expected == gen_name)
      || self
        .fvar_alts
        .get(orig_name)
        .is_some_and(|alts| alts.iter().any(|alt| alt == gen_name))
  }
}

// =========================================================================
// Public entry point
// =========================================================================

/// Compare a canonical-layout generated constant against a Lean
/// source-order original, with [`PermCtx`] describing how positions map
/// between the two layouts.
///
/// If the context is trivial (no permutation, no renames), delegates to
/// [`const_alpha_eq`](super::const_alpha_eq) for a plain structural
/// comparison.
///
/// Dispatches on [`ConstantInfo`] variant. `InductInfo`, `CtorInfo`,
/// `AxiomInfo`, and `QuotInfo` fall through to `const_alpha_eq`: their
/// structures don't embed motive/minor positions so permutation has no
/// effect on them, and non-motive alpha-collapse renames are applied
/// elsewhere (via the `all` list and the class-representative address
/// map).
pub fn const_alpha_eq_with_perm(
  generated: &ConstantInfo,
  orig: &ConstantInfo,
  ctx: &PermCtx,
) -> Result<(), String> {
  if ctx.is_identity() {
    return super::const_alpha_eq(generated, orig);
  }
  if std::env::var("IX_MAPPOS_DEBUG")
    .ok()
    .is_some_and(|v| generated.get_name().pretty().contains(&v))
  {
    eprintln!(
      "[cape] comparing {} (shape={:?})",
      generated.get_name().pretty(),
      classify_defn_shape(generated.get_name())
    );
  }

  // Level params: positional alpha-eq (handled by `const_alpha_eq`'s own
  // level_params check — we replicate the arity check here rather than
  // calling const_alpha_eq since we're about to walk types and values
  // with permutation awareness).
  if generated.get_level_params().len() != orig.get_level_params().len() {
    return Err(format!(
      "level_params count: generated={} orig={}",
      generated.get_level_params().len(),
      orig.get_level_params().len(),
    ));
  }

  // Name-based shape hint for defn-like patches. `.recOn` has minors at
  // the end of the outer binder chain (different from `.rec`'s middle
  // position), and `.casesOn` has only one motive (not the whole
  // block's motives). Both need special-case treatment in
  // `outer_telescope_alpha_eq` because the generic rec-shaped
  // classifier mis-identifies their section boundaries.
  let shape = classify_defn_shape(generated.get_name());

  match (generated, orig) {
    (ConstantInfo::RecInfo(g), ConstantInfo::RecInfo(o)) => {
      rec_alpha_eq_with_perm(g, o, ctx)
    },
    (ConstantInfo::DefnInfo(g), ConstantInfo::DefnInfo(o)) => {
      defn_alpha_eq_with_perm(&g.cnst, &g.value, &o.cnst, &o.value, ctx, shape)
    },
    (ConstantInfo::DefnInfo(g), ConstantInfo::ThmInfo(o)) => {
      defn_alpha_eq_with_perm(&g.cnst, &g.value, &o.cnst, &o.value, ctx, shape)
    },
    (ConstantInfo::ThmInfo(g), ConstantInfo::DefnInfo(o)) => {
      defn_alpha_eq_with_perm(&g.cnst, &g.value, &o.cnst, &o.value, ctx, shape)
    },
    (ConstantInfo::ThmInfo(g), ConstantInfo::ThmInfo(o)) => {
      defn_alpha_eq_with_perm(&g.cnst, &g.value, &o.cnst, &o.value, ctx, shape)
    },
    (ConstantInfo::OpaqueInfo(g), ConstantInfo::OpaqueInfo(o)) => {
      defn_alpha_eq_with_perm(&g.cnst, &g.value, &o.cnst, &o.value, ctx, shape)
    },

    // These don't embed permuted positions — plain alpha-eq suffices.
    // `const_alpha_eq` applies zero renames, so Const-name mismatches
    // due to alpha-collapse aliasing will still fail. That's intentional
    // at this layer: the tests that flag those as `const name mismatch`
    // on an inductive or constructor need the class-representative
    // address resolution, which lives in a different code path (not
    // congruence).
    _ => super::const_alpha_eq(generated, orig),
  }
}

/// Structural shape of a defn-like patch's outer binder chain.
///
/// See [`outer_telescope_alpha_eq`] for how each shape is consumed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum DefnShape {
  /// `.below`: `params | motives | indices | major | [sort]`.
  /// Motives are permuted.
  Below,
  /// `.brecOn` / `.brecOn.go` / `.brecOn.eq`:
  /// `params | motives | indices | major | fs` (one `F_k` per motive).
  /// Motives and fs are permuted with the same permutation.
  BRecOn,
  /// `.recOn`: `params | motives | indices | major | minors`.
  /// Motives and minors are permuted.
  RecOn,
  /// `.casesOn`: `params | 1 motive | indices | major | target_minors`.
  /// No block-wide permutation — only one motive and one ctor group,
  /// fall through to a whole-tree walk with `const_map` + `rec_heads`.
  CasesOn,
  /// Anything else — try the heuristic shape detector in
  /// `outer_telescope_alpha_eq`.
  Unknown,
}

fn classify_defn_shape(name: &Name) -> DefnShape {
  // Walk the name's suffix chain, collecting the trailing Str segments
  // in leaf-first order.
  let suffixes = collect_name_tail_strs(name, 3);
  // `.brecOn.go`, `.brecOn.eq`, or `.brecOn` (or `_N` variants).
  if has_suffix_with_optional_index(&suffixes, "brecOn") {
    return DefnShape::BRecOn;
  }
  if has_suffix_with_optional_index(&suffixes, "casesOn") {
    return DefnShape::CasesOn;
  }
  if has_suffix_with_optional_index(&suffixes, "recOn") {
    return DefnShape::RecOn;
  }
  if has_suffix_with_optional_index(&suffixes, "below") {
    return DefnShape::Below;
  }
  DefnShape::Unknown
}

/// Collect up to `n` trailing `Str` segments of `name`, from leaf
/// outward. `Num` segments or `Anonymous` terminate collection early.
fn collect_name_tail_strs(name: &Name, n: usize) -> Vec<String> {
  use crate::ix::env::NameData;
  let mut out: Vec<String> = Vec::with_capacity(n);
  let mut cur = name.clone();
  for _ in 0..n {
    match cur.as_data() {
      NameData::Str(parent, s, _) => {
        out.push(s.clone());
        cur = parent.clone();
      },
      _ => break,
    }
  }
  out
}

/// Check whether the leafmost segment of `suffixes` (or the first
/// segment underneath an `_N` suffix like `brecOn_1`) matches `base`.
///
/// Accepted forms (with suffixes collected leaf-first):
/// - `base`
/// - `base.go`, `base.eq`
/// - `base_N`, `base_N.go`, `base_N.eq`
fn has_suffix_with_optional_index(suffixes: &[String], base: &str) -> bool {
  if suffixes.is_empty() {
    return false;
  }
  // Candidate positions:
  //   [0] is the leaf; match base directly OR match a `.go`/`.eq` leaf
  //       with [1] matching base (or base_N).
  let matches_base_or_base_n = |s: &str| -> bool {
    s == base
      || (s.starts_with(base)
        && s.len() > base.len() + 1
        && &s[base.len()..base.len() + 1] == "_"
        && s[base.len() + 1..].chars().all(|c| c.is_ascii_digit()))
  };
  if matches_base_or_base_n(&suffixes[0]) {
    return true;
  }
  // Leafs like `.go` / `.eq` — check parent segment.
  if suffixes.len() >= 2
    && (suffixes[0] == "go" || suffixes[0] == "eq")
    && matches_base_or_base_n(&suffixes[1])
  {
    return true;
  }
  false
}

// =========================================================================
// RecInfo
// =========================================================================

/// Compare two recursors, treating gen as canonical and orig as source.
///
/// The recursor type has binder structure
/// `∀ params, ∀ motives, ∀ minors, ∀ indices, ∀ major, body_ret`.
///
/// Total outer binder count on each side:
/// `n_params + n_source_motives + n_source_minors + n_indices + 1`.
/// Under Phase 2 singleton classes and bijective `aux_perm`, gen and orig
/// have **the same** total binder count — only motive/minor sections are
/// permuted, not added or removed.
fn rec_alpha_eq_with_perm(
  g: &RecursorVal,
  o: &RecursorVal,
  ctx: &PermCtx,
) -> Result<(), String> {
  // Numeric attributes agree by layout, not by equality: Lean's original is
  // source-walk layout, while generated is canonical layout. Aux
  // alpha-collapse and over-merge splitting can make the canonical side
  // smaller.
  check_nat_eq(&g.num_params, &o.num_params, "params")?;
  check_nat_eq(&g.num_indices, &o.num_indices, "indices")?;
  check_nat_usize_eq(
    &g.num_motives,
    ctx.n_canonical_motives(),
    "generated motives",
  )?;
  check_nat_usize_eq(&o.num_motives, ctx.n_source_motives(), "orig motives")?;
  check_nat_usize_eq(
    &g.num_minors,
    ctx.n_canonical_minors(),
    "generated minors",
  )?;
  check_nat_usize_eq(&o.num_minors, ctx.n_source_minors(), "orig minors")?;
  if g.k != o.k {
    return Err(format!("k: generated={} orig={}", g.k, o.k));
  }
  if g.rules.len() != o.rules.len() {
    return Err(format!(
      "rule count: generated={} orig={}",
      g.rules.len(),
      o.rules.len()
    ));
  }

  let n_params = ctx.n_params;
  let n_source_motives = ctx.n_source_motives();
  let n_source_minors = ctx.n_source_minors();
  let n_source_outer = n_params + n_source_motives + n_source_minors;
  let n_gen_outer =
    n_params + ctx.n_canonical_motives() + ctx.n_canonical_minors();

  // Open gen's outer binders. Gen is in CANONICAL layout: its motive
  // positions are [n_params + n_primary .. n_params + n_primary +
  // n_canonical_aux) and minor groups are in canonical order.
  let (_, gen_decls, gen_body) =
    forall_telescope(&g.cnst.typ, n_gen_outer, "rg", 0);
  let (_, orig_decls, orig_body) =
    forall_telescope(&o.cnst.typ, n_source_outer, "ro", 0);

  if gen_decls.len() < n_gen_outer || orig_decls.len() < n_source_outer {
    return expr_alpha_eq(&g.cnst.typ, &o.cnst.typ)
      .map_err(|e| format!("type (fallback, short telescope): {e}"));
  }

  // Build FVar correspondence: for each orig-side outer position, find
  // its gen-side counterpart via `source_to_canonical_pos`.
  let mut corr = Corr::new();
  for (source_pos, orig_decl) in
    orig_decls.iter().take(n_source_outer).enumerate()
  {
    let gen_pos = match ctx.source_to_canonical_pos(source_pos) {
      Some(p) => p,
      None => {
        // Out-of-SCC source aux position. Shouldn't happen for a patch
        // we're comparing — those patches come from the block itself.
        return Err(format!(
          "rec type: source position {source_pos} has no canonical map"
        ));
      },
    };
    corr.insert(
      orig_decl.fvar_name.clone(),
      gen_decls[gen_pos].fvar_name.clone(),
    );
  }
  add_motive_alts(&mut corr, ctx, &orig_decls, &gen_decls);

  // Compare each decl's domain in its own binder scope.
  // Decl at outer position P has domain in scope of decls 0..P (i.e.,
  // FVars 0..P are accessible). On orig side the domain is the one
  // stored at orig_decls[P]; on gen side we need to look at
  // gen_decls[source_to_canonical_pos(P)] because the correspondence
  // inverted the position.
  //
  // The decl order matters for scope reasoning but the DOMAIN we compare
  // is content — walk with corr.
  for (source_pos, orig_decl) in
    orig_decls.iter().take(n_source_outer).enumerate()
  {
    let gen_pos = ctx.source_to_canonical_pos(source_pos).unwrap();
    expr_alpha_eq_ctx(
      &gen_decls[gen_pos].domain,
      &orig_decl.domain,
      ctx,
      &corr,
    )
    .map_err(|e| format!("rec type: decl@{source_pos} dom: {e}"))?;
  }

  // Compare the remaining body (indices + major + return telescope).
  expr_alpha_eq_ctx(&gen_body, &orig_body, ctx, &corr)
    .map_err(|e| format!("rec type body: {e}"))?;

  // Rules: both sides have the same count. The ORDER may differ:
  // gen emits rules grouped by canonical member (primary in sort order,
  // then canonical aux in hash-sort order); orig emits in source order.
  //
  // We need to pair each gen rule with its corresponding orig rule. The
  // pairing is: for each gen rule, find the orig rule whose ctor maps
  // (via const_map + positional alpha-equivalence) to gen's ctor.
  //
  // Simpler approach: iterate source order, compute the canonical
  // position for each source rule, find the matching gen rule there.
  rule_alpha_eq_with_perm(&g.rules, &o.rules, ctx, &corr)
    .map_err(|e| format!("rules: {e}"))?;

  Ok(())
}

/// Compare rec rules with permutation.
///
/// Recursor rules are local to the recursor's target inductive, not a flat
/// copy of the whole minor section. Primary recursors and nested `rec_N`s
/// can therefore have only the target constructor rules even though their
/// types quantify all motives/minors. Pair rules by constructor name after
/// applying `const_map`; using global minor positions here incorrectly maps
/// local `rec_N.rules[1]` to positions like 3 or 6 in the full minor band.
fn rule_alpha_eq_with_perm(
  gen_rules: &[RecursorRule],
  orig_rules: &[RecursorRule],
  ctx: &PermCtx,
  corr: &Corr,
) -> Result<(), String> {
  let mut used_gen = vec![false; gen_rules.len()];

  for (source_idx, orig_rule) in orig_rules.iter().enumerate() {
    let eff_orig_ctor = ctx.map_name(&orig_rule.ctor);
    let gen_idx = gen_rules
      .iter()
      .enumerate()
      .find_map(|(idx, gen_rule)| {
        (!used_gen[idx] && &gen_rule.ctor == eff_orig_ctor).then_some(idx)
      })
      .ok_or_else(|| {
        let available = gen_rules
          .iter()
          .enumerate()
          .filter(|(idx, _)| !used_gen[*idx])
          .map(|(_, rule)| rule.ctor.pretty())
          .collect::<Vec<_>>()
          .join(", ");
        format!(
          "rule[{source_idx}].ctor: no generated rule for orig={} \
           (mapped={}); remaining=[{}]",
          orig_rule.ctor.pretty(),
          eff_orig_ctor.pretty(),
          available,
        )
      })?;
    used_gen[gen_idx] = true;
    let gen_rule = &gen_rules[gen_idx];

    // n_fields must match.
    check_nat_eq(
      &gen_rule.n_fields,
      &orig_rule.n_fields,
      &format!("rule[{source_idx}].n_fields"),
    )?;

    // RHS: a lambda chain `λ params, λ motives, λ minors, λ fields,
    // body`. Total depth = n_params + n_motives + n_minors + n_fields.
    // The outer scope's FVar correspondence is already in `corr`; we
    // need to open the rhs and extend corr with field-binder identity
    // pairs (fields don't get permuted — both sides have the same ctor
    // field structure).
    rhs_alpha_eq_with_perm(&gen_rule.rhs, &orig_rule.rhs, ctx, corr)
      .map_err(|e| format!("rule[{source_idx}].rhs: {e}"))?;
  }

  Ok(())
}

/// Compare two rec rule rhss. Both are lambda chains
/// `λ params motives minors fields, body`.
///
/// The outer scope's correspondence is already given in `corr` (from
/// the rec type's binder chain). We reuse those same FVar names by
/// peeling the lambda chain in lockstep on both sides and substituting
/// the previously-opened FVars for each lambda's BVar 0.
///
/// For field binders (innermost), both sides have the same count and
/// the same field types (up to the permutation-aware comparison we
/// apply to field types themselves); we pair them identity-wise.
fn rhs_alpha_eq_with_perm(
  gen_rhs: &Expr,
  orig_rhs: &Expr,
  ctx: &PermCtx,
  corr: &Corr,
) -> Result<(), String> {
  // Under our conventions, the rhs is closed under `params + motives +
  // minors + fields` — i.e., n_params + n_source_motives +
  // n_source_minors + n_fields lambdas.
  //
  // Open the OUTER scope first (params + motives + minors) on each side
  // so those FVars align with `corr`. This requires fresh FVars that
  // MATCH the already-established corr mapping — we can't just call
  // `lambda_telescope` and get fresh names, because corr was built with
  // different names.
  //
  // Simpler: open fresh on each side, build a NEW corr extending the
  // existing one positionally. The outer-scope compare has already
  // verified the decls agree structurally; for the rhs we only need to
  // track that the bodies use the new scope consistently.
  //
  // Note: the original `corr` we received was built for the TYPE's
  // binders (separate FVar names). For the rhs, we get another set of
  // fresh FVars. The correspondence is the same structural mapping.

  let n_params = ctx.n_params;
  let n_source_motives = ctx.n_source_motives();
  let n_source_minors = ctx.n_source_minors();
  let n_canonical_motives = ctx.n_canonical_motives();
  let n_canonical_minors = ctx.n_canonical_minors();

  let outer_source = n_params + n_source_motives + n_source_minors;
  let outer_canonical = n_params + n_canonical_motives + n_canonical_minors;

  // Peel outer scope and all remaining fields from both sides. We don't
  // know n_fields from the context, so use `peel_all_lambdas`.
  let (_, gen_decls, gen_body) = peel_all_lambdas(gen_rhs, "rhg", 0);
  let (_, orig_decls, orig_body) = peel_all_lambdas(orig_rhs, "rho", 0);

  if gen_decls.len() < outer_canonical || orig_decls.len() < outer_source {
    return Err(format!(
      "rhs short telescope: gen={} need={} orig={} need={}",
      gen_decls.len(),
      outer_canonical,
      orig_decls.len(),
      outer_source,
    ));
  }

  let n_gen_fields = gen_decls.len() - outer_canonical;
  let n_orig_fields = orig_decls.len() - outer_source;
  if n_gen_fields != n_orig_fields {
    return Err(format!(
      "rhs field lambda count mismatch: gen={} orig={}",
      n_gen_fields, n_orig_fields
    ));
  }

  // Build NEW correspondence for the rhs's fresh FVars:
  // - Outer section [0..outer_source) uses source→canonical permutation
  //   (same structural mapping as the type's corr).
  // - Field section [outer_source..] pairs identity-wise after accounting
  //   for the shorter canonical aux band.
  let mut rhs_corr = Corr::new();
  for (source_pos, orig_decl) in
    orig_decls.iter().take(outer_source).enumerate()
  {
    let gen_pos = ctx
      .source_to_canonical_pos(source_pos)
      .ok_or_else(|| format!("rhs pos {source_pos}: out-of-SCC"))?;
    rhs_corr.insert(
      orig_decl.fvar_name.clone(),
      gen_decls[gen_pos].fvar_name.clone(),
    );
  }
  for field_i in 0..n_orig_fields {
    // Fields: identity — both sides have the same ctor structure.
    let field_pos = outer_source + field_i;
    rhs_corr.insert(
      orig_decls[field_pos].fvar_name.clone(),
      gen_decls[outer_canonical + field_i].fvar_name.clone(),
    );
  }
  add_motive_alts(&mut rhs_corr, ctx, &orig_decls, &gen_decls);

  // `corr` from the enclosing caller is unused here (the rhs introduces
  // its own FVars); we still accept it as an argument for API symmetry
  // and in case future refactors want to carry outer FVar info in.
  let _ = corr;

  // Compare domains pair-wise under increasing scope.
  for (source_pos, orig_decl) in
    orig_decls.iter().take(outer_source).enumerate()
  {
    let gen_pos = ctx.source_to_canonical_pos(source_pos).unwrap();
    expr_alpha_eq_ctx(
      &gen_decls[gen_pos].domain,
      &orig_decl.domain,
      ctx,
      &rhs_corr,
    )
    .map_err(|e| format!("rhs decl@{source_pos} dom: {e}"))?;
  }
  for field_i in 0..n_orig_fields {
    let source_pos = outer_source + field_i;
    let gen_pos = outer_canonical + field_i;
    expr_alpha_eq_ctx(
      &gen_decls[gen_pos].domain,
      &orig_decls[source_pos].domain,
      ctx,
      &rhs_corr,
    )
    .map_err(|e| format!("rhs field@{field_i} dom: {e}"))?;
  }

  // Compare bodies.
  expr_alpha_eq_ctx(&gen_body, &orig_body, ctx, &rhs_corr)
    .map_err(|e| format!("rhs body: {e}"))
}

// =========================================================================
// DefnInfo / ThmInfo / OpaqueInfo
// =========================================================================

/// Compare a generated definition / theorem / opaque against its orig
/// counterpart with permutation awareness.
///
/// Handles the types/values produced by `aux_gen` for `.below`,
/// `.brecOn`, `.brecOn.go`, `.brecOn.eq`, `.casesOn`, `.recOn`.
///
/// - **Type**: `∀ params, motives, [minors for .casesOn / .recOn], indices, major, body`.
/// - **Value**: `λ params, motives, [indices, major, [minors for .recOn]], body`.
///
/// We don't know the exact binder shape in advance (`.casesOn` has its
/// motive/minor split; `.recOn` puts minors after major; `.below` and
/// `.brecOn` have no minors in the public signature). Instead of
/// dispatching on name, we open ALL leading foralls / lambdas on both
/// sides in lockstep, build an FVar correspondence that permutes only
/// the motive section (identity for all other sections), and walk. If
/// the permutation context is for a block whose aux section has been
/// permuted, the motive section covers the aux-motive tail.
fn defn_alpha_eq_with_perm(
  g_cnst: &ConstantVal,
  g_value: &Expr,
  o_cnst: &ConstantVal,
  o_value: &Expr,
  ctx: &PermCtx,
  shape: DefnShape,
) -> Result<(), String> {
  // Type comparison.
  outer_telescope_alpha_eq(
    &g_cnst.typ,
    &o_cnst.typ,
    ctx,
    /* pi */ true,
    shape,
  )
  .map_err(|e| format!("type: {e}"))?;
  // Value comparison.
  outer_telescope_alpha_eq(g_value, o_value, ctx, /* pi */ false, shape)
    .map_err(|e| format!("value: {e}"))?;
  Ok(())
}

/// Open all leading binders (foralls or lambdas) on both sides, build a
/// motive-permuted correspondence, and walk the bodies.
///
/// Different aux kinds have different outer binder chains:
/// - `.below`: `params + motives + indices + major + [Sort | target]`,
///   total = `n_params + n_motives + n_indices + 1`.
/// - `.brecOn` / `.brecOn.go` / `.brecOn.eq`: adds `fs` at the end —
///   one F_k per motive, permuted the same way as motives. Total =
///   `n_params + 2*n_motives + n_indices + 1`.
/// - `.casesOn` / `.recOn`: outer chain has a single target motive
///   (not `n_motives`). Total shape doesn't match either of the above.
///
/// We detect the shape from the peeled binder count:
/// 1. Peel **all** leading binders on both sides.
/// 2. If counts diverge, non-bijective perm or weird shape — fall back
///    to whole-tree [`expr_alpha_eq_ctx`] with an empty correspondence.
/// 3. If total ≥ `n_params + 2*n_motives`, assume brecOn-shape: permute
///    motives at `[n_params, n_params + n_motives)` and fs at the tail
///    `[total - n_motives, total)`. Everything else is identity.
/// 4. Elif total ≥ `n_params + n_motives`, assume below-shape: permute
///    motives only; rest is identity.
/// 5. Else: short — fall back.
///
/// In all cases, after setting up the correspondence we walk every
/// decl's domain and the final body with [`expr_alpha_eq_ctx`], which
/// threads `const_map` + `rec_heads` through.
fn outer_telescope_alpha_eq(
  gen_expr: &Expr,
  orig_expr: &Expr,
  ctx: &PermCtx,
  is_pi: bool,
  shape: DefnShape,
) -> Result<(), String> {
  let n_params = ctx.n_params;
  let n_source_motives = ctx.n_source_motives();
  let n_canonical_motives = ctx.n_canonical_motives();

  // Peel as many leading binders as possible on each side. A very
  // generous `max` is safe — telescope peels only what's present.
  let peel_max = 10_000usize;
  let (_, gen_decls, gen_body) = if is_pi {
    forall_telescope(gen_expr, peel_max, "dg", 0)
  } else {
    lambda_telescope(gen_expr, peel_max, "dg", 0)
  };
  let (_, orig_decls, orig_body) = if is_pi {
    forall_telescope(orig_expr, peel_max, "do", 0)
  } else {
    lambda_telescope(orig_expr, peel_max, "do", 0)
  };

  let total = orig_decls.len();

  if matches!(shape, DefnShape::CasesOn) {
    return cases_on_alpha_eq(gen_expr, orig_expr, ctx, is_pi);
  }

  let is_motive_shape = total >= n_params + n_source_motives;
  if !is_motive_shape {
    let empty_corr = Corr::new();
    return expr_alpha_eq_ctx(gen_expr, orig_expr, ctx, &empty_corr);
  }

  // Classify the outer-binder layout for section slicing.
  //
  // Every shape begins with `params` then `motives`:
  //   params:  [0, n_params)
  //   motives: [n_params, n_params + n_motives)
  //
  // Suffix layouts (in outer-to-inner order):
  //   - Below:  indices | major
  //   - BRecOn: indices | major | fs
  //   - RecOn:  indices | major | minors
  //   - Unknown (heuristic): if `total ≥ n_params + 2*n_motives + 1`
  //                          treat as BRecOn; else as Below.
  let (has_fs_section, has_tail_minors) = match shape {
    DefnShape::Below => (false, false),
    DefnShape::BRecOn => (true, false),
    DefnShape::RecOn => (false, true),
    DefnShape::CasesOn => unreachable!("handled above"),
    DefnShape::Unknown => {
      let looks_brecon = total > n_params + 2 * n_source_motives;
      (looks_brecon, false)
    },
  };

  // Compute section boundaries (on the orig/source side).
  //
  // Tail section (fs or minors) has different length per shape:
  //   - fs:     n_motives (one F_k per motive)
  //   - minors: n_minors  (sum of primary + source-aux ctor counts)
  let n_source_minors = ctx.n_source_minors();
  let tail_len = if has_fs_section {
    n_source_motives
  } else if has_tail_minors {
    n_source_minors
  } else {
    0
  };

  let mid_len = total.saturating_sub(n_params + n_source_motives + tail_len);
  let mid_start_src = n_params + n_source_motives;
  let mid_end_src = mid_start_src + mid_len;
  let tail_start_src = mid_end_src;
  let tail_end_src = total;

  // On the gen/canonical side:
  //   params identity, motives canonical-count-many, middle same
  //   length, tail = fs (canonical motives) or minors (canonical
  //   minors).
  let n_canonical_minors = n_canonical_minors_of(ctx);
  let gen_tail_len = if has_fs_section {
    n_canonical_motives
  } else if has_tail_minors {
    n_canonical_minors
  } else {
    0
  };
  let gen_mid_start = n_params + n_canonical_motives;
  let gen_tail_start = gen_mid_start + mid_len;
  let expected_gen_total = gen_tail_start + gen_tail_len;
  if gen_decls.len() != expected_gen_total {
    let empty_corr = Corr::new();
    return expr_alpha_eq_ctx(gen_expr, orig_expr, ctx, &empty_corr);
  }

  let map_pos = |src_pos: usize| -> Option<usize> {
    if src_pos < n_params + n_source_motives {
      ctx.source_to_canonical_pos(src_pos)
    } else if src_pos < mid_end_src {
      // Middle (indices + major) — identity.
      Some(gen_mid_start + (src_pos - mid_start_src))
    } else if src_pos < tail_end_src && has_fs_section {
      // fs: same permutation as motives.
      let fs_offset = src_pos - tail_start_src;
      if fs_offset < ctx.n_primary {
        Some(gen_tail_start + fs_offset)
      } else {
        let source_j = fs_offset - ctx.n_primary;
        if source_j >= ctx.n_source_aux() {
          return None;
        }
        let canonical_i = ctx.aux_perm[source_j];
        if canonical_i == PERM_OUT_OF_SCC {
          return None;
        }
        Some(gen_tail_start + ctx.n_primary + canonical_i)
      }
    } else if src_pos < tail_end_src && has_tail_minors {
      // Minors at tail (.recOn layout). Same permutation as minors
      // section for rec: primary identity, aux groups permuted.
      let minor_offset = src_pos - tail_start_src;
      let primary_minor_total: usize = ctx.primary_ctor_counts.iter().sum();
      if minor_offset < primary_minor_total {
        Some(gen_tail_start + minor_offset)
      } else {
        // Aux minor — find source aux group.
        let aux_minor_offset = minor_offset - primary_minor_total;
        let mut acc = 0usize;
        for (source_j, &cnt) in ctx.source_aux_ctor_counts.iter().enumerate() {
          if aux_minor_offset < acc + cnt {
            let k = aux_minor_offset - acc;
            let canonical_i = ctx.aux_perm[source_j];
            if canonical_i == PERM_OUT_OF_SCC {
              return None;
            }
            // Compute canonical group offset.
            let mut canon_group_off = primary_minor_total;
            for ci in 0..canonical_i {
              canon_group_off += canonical_ctor_count_at(ctx, ci);
            }
            return Some(gen_tail_start + canon_group_off + k);
          }
          acc += cnt;
        }
        None
      }
    } else {
      None
    }
  };

  // Build FVar correspondence.
  let mut corr = Corr::new();
  for (src_pos, orig_decl) in orig_decls.iter().take(total).enumerate() {
    let gen_pos = map_pos(src_pos)
      .ok_or_else(|| format!("outer pos {src_pos}: no canonical map"))?;
    if gen_pos >= gen_decls.len() {
      return Err(format!(
        "outer pos {src_pos}: canonical gen_pos {gen_pos} out of bounds ({})",
        gen_decls.len()
      ));
    }
    corr.insert(
      orig_decl.fvar_name.clone(),
      gen_decls[gen_pos].fvar_name.clone(),
    );
  }
  add_motive_alts(&mut corr, ctx, &orig_decls, &gen_decls);

  if std::env::var("IX_MAPPOS_DEBUG").is_ok() {
    eprintln!(
      "[mappos] shape={:?} total={} n_params={} n_src_mot={} n_canon_mot={} mid_len={} has_fs={} has_tail_minors={}",
      shape,
      total,
      n_params,
      n_source_motives,
      n_canonical_motives,
      mid_len,
      has_fs_section,
      has_tail_minors,
    );
  }
  // Walk each decl's domain. Each domain is in scope of the previous
  // binders; any FVar reference in a domain resolves through `corr`.
  for (src_pos, orig_decl) in orig_decls.iter().take(total).enumerate() {
    let gen_pos = map_pos(src_pos).unwrap();
    if std::env::var("IX_MAPPOS_DEBUG").is_ok() && total == 17 && src_pos == 11
    {
      eprintln!(
        "[mappos-detail] total=17 src_pos={} gen_pos={} aux_perm={:?}\n  orig_decls[{}].domain: {}\n  gen_decls[{}].domain: {}",
        src_pos,
        gen_pos,
        ctx.aux_perm,
        src_pos,
        orig_decl.domain.pretty(),
        gen_pos,
        gen_decls[gen_pos].domain.pretty(),
      );
    }
    expr_alpha_eq_ctx(
      &gen_decls[gen_pos].domain,
      &orig_decl.domain,
      ctx,
      &corr,
    )
    .map_err(|e| format!("decl@{src_pos} dom: {e}"))?;
  }

  // Walk the innermost body.
  expr_alpha_eq_ctx(&gen_body, &orig_body, ctx, &corr)
    .map_err(|e| format!("body: {e}"))
}

/// Ctor count for canonical aux `canonical_i`, taken from the first
/// source aux that maps to it under `ctx.aux_perm`. Shared with
/// `PermCtx::canonical_aux_ctor_count` (private API) — reimplemented
/// here to keep `outer_telescope_alpha_eq` self-contained.
fn canonical_ctor_count_at(ctx: &PermCtx, canonical_i: usize) -> usize {
  for (source_j, &c) in ctx.aux_perm.iter().enumerate() {
    if c == canonical_i {
      return ctx.source_aux_ctor_counts[source_j];
    }
  }
  0
}

fn cases_on_alpha_eq(
  gen_expr: &Expr,
  orig_expr: &Expr,
  ctx: &PermCtx,
  is_pi: bool,
) -> Result<(), String> {
  let peel_max = 10_000usize;
  let (_, gen_decls, gen_body) = if is_pi {
    forall_telescope(gen_expr, peel_max, "cg", 0)
  } else {
    lambda_telescope(gen_expr, peel_max, "cg", 0)
  };
  let (_, orig_decls, orig_body) = if is_pi {
    forall_telescope(orig_expr, peel_max, "co", 0)
  } else {
    lambda_telescope(orig_expr, peel_max, "co", 0)
  };

  if gen_decls.len() != orig_decls.len() {
    let empty_corr = Corr::new();
    return expr_alpha_eq_ctx(gen_expr, orig_expr, ctx, &empty_corr);
  }

  let mut corr = Corr::new();
  for (gen_decl, orig_decl) in gen_decls.iter().zip(orig_decls.iter()) {
    corr.insert(orig_decl.fvar_name.clone(), gen_decl.fvar_name.clone());
  }
  if gen_decls.len() > ctx.n_params && orig_decls.len() > ctx.n_params {
    corr.insert_punit_motive(
      orig_decls[ctx.n_params].fvar_name.clone(),
      gen_decls[ctx.n_params].fvar_name.clone(),
    );
  }

  for (i, (gen_decl, orig_decl)) in
    gen_decls.iter().zip(orig_decls.iter()).enumerate()
  {
    expr_alpha_eq_ctx(&gen_decl.domain, &orig_decl.domain, ctx, &corr)
      .map_err(|e| format!("decl@{i} dom: {e}"))?;
  }
  expr_alpha_eq_ctx(&gen_body, &orig_body, ctx, &corr)
    .map_err(|e| format!("body: {e}"))
}

/// Total canonical minor count. Sum of primary ctor counts plus each
/// canonical aux's ctor count (from its first source representative).
fn n_canonical_minors_of(ctx: &PermCtx) -> usize {
  let primary: usize = ctx.primary_ctor_counts.iter().sum();
  let mut aux = 0usize;
  for ci in 0..ctx.n_canonical_aux() {
    aux += canonical_ctor_count_at(ctx, ci);
  }
  primary + aux
}

fn add_motive_alts(
  corr: &mut Corr,
  ctx: &PermCtx,
  orig_decls: &[crate::ix::compile::aux_gen::expr_utils::LocalDecl],
  gen_decls: &[crate::ix::compile::aux_gen::expr_utils::LocalDecl],
) {
  let n_params = ctx.n_params;
  let n_source_motives = ctx.n_source_motives();
  let n_canonical_motives = ctx.n_canonical_motives();
  if orig_decls.len() < n_params + n_source_motives
    || gen_decls.len() < n_params + n_canonical_motives
  {
    return;
  }

  let mut param_corr = Corr::new();
  for p in 0..n_params {
    param_corr
      .insert(orig_decls[p].fvar_name.clone(), gen_decls[p].fvar_name.clone());
  }

  for src_i in 0..n_source_motives {
    let orig_pos = n_params + src_i;
    for gen_i in 0..n_canonical_motives {
      let gen_pos = n_params + gen_i;
      if expr_alpha_eq_ctx(
        &gen_decls[gen_pos].domain,
        &orig_decls[orig_pos].domain,
        ctx,
        &param_corr,
      )
      .is_ok()
      {
        corr.insert_alt(
          orig_decls[orig_pos].fvar_name.clone(),
          gen_decls[gen_pos].fvar_name.clone(),
        );
      }
    }
  }
}

fn punit_motive_equiv(g: &Expr, orig: &Expr, corr: &Corr) -> bool {
  (is_punit_type(g) && is_motive_app(orig, &corr.punit_motive_orig))
    || (is_motive_app(g, &corr.punit_motive_gen) && is_punit_type(orig))
}

fn is_punit_type(e: &Expr) -> bool {
  matches!(e.as_data(), ExprData::Const(n, _, _) if n.pretty() == "PUnit")
}

fn is_motive_app(e: &Expr, motives: &[Name]) -> bool {
  if motives.is_empty() {
    return false;
  }
  let (head, args) = decompose_app_spine(e);
  !args.is_empty()
    && matches!(head.as_data(), ExprData::Fvar(n, _) if motives.iter().any(|m| m == n))
}

// =========================================================================
// Permutation-aware expression walk
// =========================================================================

/// Walk two expressions in lockstep under `ctx` and `corr`.
///
/// - `Fvar`: resolve orig's FVar through `corr`; accept if gen has the
///   mapped FVar (or if orig's FVar is not in corr, require literal
///   equality — this handles references to FVars introduced by inner
///   binders during this walk).
/// - `Bvar`: compare indices literally. BVars at this layer are
///   body-local (outer binders were opened to FVars) so they always
///   refer to inner binders introduced during the walk itself.
/// - `Const`: apply `ctx.map_name` to orig before comparing names.
/// - `App`: spine-decompose and check if head is a known rec
///   ([`PermCtx::rec_heads`]); if so, permute the orig's motive/minor
///   arg positions before pairwise comparison.
/// - `Lam` / `ForallE`: recurse into domain and body; bodies are
///   inside one more binder so BVar(0) on each side is already
///   consistent (pairs identity-wise).
/// - `LetE` / `Proj` / `Mdata`: recurse; `Mdata` is stripped before
///   matching so it's essentially a no-op.
/// - `Sort`, `Lit`: compare literally.
pub(crate) fn expr_alpha_eq_ctx(
  g: &Expr,
  orig: &Expr,
  ctx: &PermCtx,
  corr: &Corr,
) -> Result<(), String> {
  let g = strip_mdata(g);
  let orig = strip_mdata(orig);

  if punit_motive_equiv(g, orig, corr) {
    return Ok(());
  }

  match (g.as_data(), orig.as_data()) {
    (ExprData::Bvar(n1, _), ExprData::Bvar(n2, _)) => {
      if n1 == n2 {
        Ok(())
      } else {
        Err(format!(
          "bvar mismatch: {n1} vs {n2}\n    gen ctx: {}\n    orig ctx: {}",
          g.pretty(),
          orig.pretty()
        ))
      }
    },
    (ExprData::Fvar(n_gen, _), ExprData::Fvar(n_orig, _)) => {
      match corr.get(n_orig) {
        Some(expected) => {
          if corr.accepts(n_orig, n_gen) {
            Ok(())
          } else {
            Err(format!(
              "fvar mismatch: gen={} vs orig={} (corr expected gen={})",
              n_gen.pretty(),
              n_orig.pretty(),
              expected.pretty()
            ))
          }
        },
        None => {
          // No correspondence entry — either this FVar was introduced
          // by inner lambdas (hence same name on both sides) or a stale
          // reference. Compare literally.
          if n_gen == n_orig {
            Ok(())
          } else {
            Err(format!(
              "fvar mismatch (unmapped): gen={} vs orig={}",
              n_gen.pretty(),
              n_orig.pretty()
            ))
          }
        },
      }
    },

    (ExprData::Sort(l1, _), ExprData::Sort(l2, _)) => {
      level_alpha_eq(l1, l2).map_err(|e| format!("sort: {e}"))
    },

    (
      ExprData::Const(n_gen, lvls_gen, _),
      ExprData::Const(n_orig, lvls_orig, _),
    ) => {
      let eff_orig = ctx.map_name(n_orig);
      if !ctx.const_names_equiv(n_gen, n_orig) {
        return Err(format!(
          "const name mismatch: {} vs {} (orig mapped to {})",
          n_gen.pretty(),
          n_orig.pretty(),
          eff_orig.pretty(),
        ));
      }
      if lvls_gen.len() != lvls_orig.len() {
        return Err(format!(
          "const {} level count: {} vs {}",
          n_gen.pretty(),
          lvls_gen.len(),
          lvls_orig.len(),
        ));
      }
      for (i, (l1, l2)) in lvls_gen.iter().zip(lvls_orig.iter()).enumerate() {
        level_alpha_eq(l1, l2)
          .map_err(|e| format!("const {}.lvl[{i}]: {e}", n_gen.pretty()))?;
      }
      Ok(())
    },

    (ExprData::App(..), ExprData::App(..)) => {
      app_spine_alpha_eq_ctx(g, orig, ctx, corr)
    },

    (
      ExprData::Lam(_, ty1, body1, _, _),
      ExprData::Lam(_, ty2, body2, _, _),
    ) => {
      expr_alpha_eq_ctx(ty1, ty2, ctx, corr)
        .map_err(|e| format!("lam.ty: {e}"))?;
      expr_alpha_eq_ctx(body1, body2, ctx, corr)
        .map_err(|e| format!("lam.body: {e}"))
    },

    (
      ExprData::ForallE(_, ty1, body1, _, _),
      ExprData::ForallE(_, ty2, body2, _, _),
    ) => {
      expr_alpha_eq_ctx(ty1, ty2, ctx, corr)
        .map_err(|e| format!("∀.ty: {e}"))?;
      expr_alpha_eq_ctx(body1, body2, ctx, corr)
        .map_err(|e| format!("∀.body: {e}"))
    },

    (
      ExprData::LetE(_, ty1, val1, body1, _, _),
      ExprData::LetE(_, ty2, val2, body2, _, _),
    ) => {
      expr_alpha_eq_ctx(ty1, ty2, ctx, corr)
        .map_err(|e| format!("let.ty: {e}"))?;
      expr_alpha_eq_ctx(val1, val2, ctx, corr)
        .map_err(|e| format!("let.val: {e}"))?;
      expr_alpha_eq_ctx(body1, body2, ctx, corr)
        .map_err(|e| format!("let.body: {e}"))
    },

    (ExprData::Lit(l1, _), ExprData::Lit(l2, _)) => {
      if l1 == l2 {
        Ok(())
      } else {
        Err("lit mismatch".to_string())
      }
    },

    (ExprData::Proj(n1, idx1, val1, _), ExprData::Proj(n2, idx2, val2, _)) => {
      // Projection structure type: orig may reference an aliased
      // inductive name; map before comparing.
      let eff_n2 = ctx.map_name(n2);
      if !ctx.const_names_equiv(n1, n2) {
        return Err(format!(
          "proj type mismatch: {} vs {} (mapped {})",
          n1.pretty(),
          n2.pretty(),
          eff_n2.pretty()
        ));
      }
      if idx1 != idx2 {
        return Err(format!("proj idx mismatch: {idx1} vs {idx2}"));
      }
      expr_alpha_eq_ctx(val1, val2, ctx, corr)
        .map_err(|e| format!("proj.val: {e}"))
    },

    (ExprData::Mvar(..), _) | (_, ExprData::Mvar(..)) => {
      Err("unexpected MVar in constant".into())
    },

    _ => Err(format!(
      "expr shape mismatch: gen={} orig={}\n    gen: {}\n    orig: {}",
      expr_tag(g),
      expr_tag(orig),
      g.pretty(),
      orig.pretty(),
    )),
  }
}

/// App-spine comparison with motive/minor arg permutation at known
/// rec heads.
///
/// Both sides' App spines are decomposed. If the head is a known rec
/// (via [`PermCtx::rec_heads`] after applying `const_map`), the orig
/// side's motive and minor arg sections are permuted before pairwise
/// comparison. Otherwise, arguments are compared pairwise in order.
///
/// Under-applied rec calls (spine shorter than `n_params + n_motives +
/// n_minors`) degrade gracefully: permutation only applies to whatever
/// section is fully present in both spines.
fn app_spine_alpha_eq_ctx(
  g: &Expr,
  orig: &Expr,
  ctx: &PermCtx,
  corr: &Corr,
) -> Result<(), String> {
  let (gen_head, gen_args) = decompose_app_spine(g);
  let (orig_head, orig_args) = decompose_app_spine(orig);

  // Compare heads first (this resolves const names through `const_map`
  // and catches head mismatches before we compare potentially-costly
  // arg spines).
  expr_alpha_eq_ctx(&gen_head, &orig_head, ctx, corr)
    .map_err(|e| format!("app.fun: {e}"))?;

  // Check head for rec-spine permutation. The orig-side head might be a
  // source-indexed aux rec name (e.g. `A.rec_5`) while the gen-side has
  // the canonical-indexed equivalent (e.g. `A.rec_2`). After `map_name`,
  // they should agree on the same gen-side name, which is what we look
  // up in `rec_heads`.
  let rec_info = match orig_head.as_data() {
    ExprData::Const(n_orig, _, _) => {
      let eff = ctx.map_name(n_orig);
      ctx.rec_heads.get(eff)
    },
    _ => None,
  };

  if let Some(rh) = rec_info {
    // Permute orig args' motive/minor sections into gen's canonical
    // layout, then compare positionally.
    let permuted_orig = permute_rec_app_args(&orig_args, rh);
    if gen_args.len() != permuted_orig.len() {
      return Err(format!(
        "app arg count mismatch after canonicalization: gen={} orig={} canon_orig={}",
        gen_args.len(),
        orig_args.len(),
        permuted_orig.len()
      ));
    }
    for (i, (g, o)) in gen_args.iter().zip(permuted_orig.iter()).enumerate() {
      expr_alpha_eq_ctx(g, o, ctx, corr)
        .map_err(|e| format!("app.arg[{i}]: {e}"))?;
    }
  } else {
    if gen_args.len() != orig_args.len() {
      return Err(format!(
        "app arg count mismatch: gen={} orig={}",
        gen_args.len(),
        orig_args.len()
      ));
    }
    for (i, (g, o)) in gen_args.iter().zip(orig_args.iter()).enumerate() {
      expr_alpha_eq_ctx(g, o, ctx, corr)
        .map_err(|e| format!("app.arg[{i}]: {e}"))?;
    }
  }

  Ok(())
}

/// Permute the motive / minor / fs sections of an orig-side App's
/// argument list into gen-side canonical layout.
///
/// The layout depends on `rh.kind`:
/// - `Rec`:    `params | motives | minors | indices | major`.
/// - `Below`:  `params | motives | indices | major`.
/// - `BRecOn`: `params | motives | indices | major | fs` (one F_k
///   per motive).
/// - `CasesOn`: no permutation — the public spine has only one motive
///   and one ctor-group's worth of minors.
///
/// For primary (non-aux) positions the permutation is identity (under
/// Phase 2 singleton classes); for aux positions we apply `aux_perm`.
///
/// If the spine is shorter than expected for the head kind, the
/// sections that ARE fully present still get permuted; partial
/// sections get left alone (preserving positional args).
fn permute_rec_app_args(orig_args: &[Expr], rh: &RecHeadInfo) -> Vec<Expr> {
  if matches!(rh.kind, RecHeadKind::CasesOn) {
    return orig_args.to_vec();
  }

  let n_params = rh.n_params;
  let n_source_motives = rh.n_motives;
  let n_primary = rh.primary_ctor_counts.len();
  let n_source_aux = rh.source_aux_ctor_counts.len();
  let n_canonical_aux = n_canonical_aux_for_perm(&rh.aux_perm);
  let n_canonical_motives = n_primary + n_canonical_aux;

  let push_canonical_motives = |out: &mut Vec<Expr>, source: &[Expr]| {
    out.extend(source.iter().take(n_primary).cloned());
    for canonical_i in 0..n_canonical_aux {
      if let Some(source_j) =
        first_source_for_canonical(&rh.aux_perm, canonical_i)
        && source_j < n_source_aux
      {
        out.push(source[n_primary + source_j].clone());
      }
    }
  };

  let primary_minors: usize = rh.primary_ctor_counts.iter().sum();
  let push_canonical_minors = |out: &mut Vec<Expr>, source: &[Expr]| {
    out.extend(source.iter().take(primary_minors).cloned());
    let mut group_start = primary_minors;
    let mut source_group_starts = Vec::with_capacity(n_source_aux);
    for &cnt in &rh.source_aux_ctor_counts {
      source_group_starts.push(group_start);
      group_start += cnt;
    }
    for canonical_i in 0..n_canonical_aux {
      if let Some(source_j) =
        first_source_for_canonical(&rh.aux_perm, canonical_i)
        && let Some(&start) = source_group_starts.get(source_j)
      {
        let cnt = rh.source_aux_ctor_counts[source_j];
        out.extend(source[start..start + cnt].iter().cloned());
      }
    }
  };

  match rh.kind {
    RecHeadKind::Rec => {
      let source_full =
        n_params + n_source_motives + rh.n_minors + rh.n_indices + 1;
      if orig_args.len() < source_full {
        return orig_args.to_vec();
      }
      let mut out = Vec::with_capacity(
        n_params
          + n_canonical_motives
          + canonical_minor_count_for_head(rh)
          + rh.n_indices
          + 1
          + orig_args.len().saturating_sub(source_full),
      );
      out.extend(orig_args[..n_params].iter().cloned());
      let motive_start = n_params;
      let motive_end = motive_start + n_source_motives;
      push_canonical_motives(&mut out, &orig_args[motive_start..motive_end]);
      let minor_start = motive_end;
      let minor_end = minor_start + rh.n_minors;
      push_canonical_minors(&mut out, &orig_args[minor_start..minor_end]);
      out.extend(orig_args[minor_end..source_full].iter().cloned());
      out.extend(orig_args[source_full..].iter().cloned());
      out
    },
    RecHeadKind::Below => {
      let source_full = n_params + n_source_motives + rh.n_indices + 1;
      if orig_args.len() < source_full {
        return orig_args.to_vec();
      }
      let mut out = Vec::with_capacity(
        n_params
          + n_canonical_motives
          + rh.n_indices
          + 1
          + orig_args.len().saturating_sub(source_full),
      );
      out.extend(orig_args[..n_params].iter().cloned());
      let motive_start = n_params;
      let motive_end = motive_start + n_source_motives;
      push_canonical_motives(&mut out, &orig_args[motive_start..motive_end]);
      out.extend(orig_args[motive_end..source_full].iter().cloned());
      out.extend(orig_args[source_full..].iter().cloned());
      out
    },
    RecHeadKind::BRecOn => {
      let source_mid_len = rh.n_indices + 1;
      let source_full =
        n_params + n_source_motives + source_mid_len + n_source_motives;
      if orig_args.len() < source_full {
        return orig_args.to_vec();
      }
      let mut out = Vec::with_capacity(
        n_params
          + n_canonical_motives
          + source_mid_len
          + n_canonical_motives
          + orig_args.len().saturating_sub(source_full),
      );
      out.extend(orig_args[..n_params].iter().cloned());
      let motive_start = n_params;
      let motive_end = motive_start + n_source_motives;
      push_canonical_motives(&mut out, &orig_args[motive_start..motive_end]);
      let mid_end = motive_end + source_mid_len;
      out.extend(orig_args[motive_end..mid_end].iter().cloned());
      push_canonical_motives(&mut out, &orig_args[mid_end..source_full]);
      out.extend(orig_args[source_full..].iter().cloned());
      out
    },
    RecHeadKind::CasesOn => orig_args.to_vec(),
  }
}

fn n_canonical_aux_for_perm(aux_perm: &[usize]) -> usize {
  aux_perm
    .iter()
    .copied()
    .filter(|&c| c != PERM_OUT_OF_SCC)
    .max()
    .map_or(0, |m| m + 1)
}

fn first_source_for_canonical(
  aux_perm: &[usize],
  canonical_i: usize,
) -> Option<usize> {
  aux_perm.iter().position(|&c| c == canonical_i)
}

fn canonical_aux_ctor_count_for_head(
  rh: &RecHeadInfo,
  canonical_i: usize,
) -> usize {
  first_source_for_canonical(&rh.aux_perm, canonical_i)
    .and_then(|source_j| rh.source_aux_ctor_counts.get(source_j).copied())
    .unwrap_or(0)
}

fn canonical_minor_count_for_head(rh: &RecHeadInfo) -> usize {
  let primary: usize = rh.primary_ctor_counts.iter().sum();
  let aux = (0..n_canonical_aux_for_perm(&rh.aux_perm))
    .map(|ci| canonical_aux_ctor_count_for_head(rh, ci))
    .sum::<usize>();
  primary + aux
}

// =========================================================================
// Helpers
// =========================================================================

/// Decompose a left-associative App spine into `(head, args)`. Arguments
/// are returned in application order (outermost-left-first). This is
/// the same convention as `surgery::collect_lean_telescope`.
fn decompose_app_spine(e: &Expr) -> (Expr, Vec<Expr>) {
  let mut args: Vec<Expr> = Vec::new();
  let mut cur = e.clone();
  while let ExprData::App(f, a, _) = cur.as_data() {
    args.push(a.clone());
    cur = f.clone();
  }
  args.reverse();
  (cur, args)
}

fn check_nat_usize_eq(
  n: &Nat,
  expected: usize,
  what: &str,
) -> Result<(), String> {
  let actual = n
    .to_u64()
    .and_then(|v| usize::try_from(v).ok())
    .ok_or_else(|| format!("{what}: value too large"))?;
  if actual == expected {
    Ok(())
  } else {
    Err(format!(
      "{what}: generated/orig layout count={actual} expected={expected}"
    ))
  }
}

/// Peel every leading lambda into FVars. Continues past `min_count` as
/// long as the body is still a lambda.
fn peel_all_lambdas(
  expr: &Expr,
  prefix: &str,
  min_count: usize,
) -> (Vec<Expr>, Vec<crate::ix::compile::aux_gen::expr_utils::LocalDecl>, Expr)
{
  use crate::ix::compile::aux_gen::expr_utils::LocalDecl;

  let (mut fvars, mut decls, mut body): (Vec<Expr>, Vec<LocalDecl>, Expr) =
    if min_count == 0 {
      (Vec::new(), Vec::new(), expr.clone())
    } else {
      lambda_telescope(expr, min_count, prefix, 0)
    };
  if decls.len() < min_count {
    return (fvars, decls, body);
  }
  while let ExprData::Lam(..) = body.as_data() {
    let (extra_fvars, extra_decls, next_body) =
      lambda_telescope(&body, 1, prefix, decls.len());
    if extra_decls.is_empty() {
      break;
    }
    fvars.extend(extra_fvars);
    decls.extend(extra_decls);
    body = next_body;
  }
  (fvars, decls, body)
}

fn expr_tag(e: &Expr) -> &'static str {
  match e.as_data() {
    ExprData::Bvar(_, _) => "Bvar",
    ExprData::Sort(_, _) => "Sort",
    ExprData::Const(_, _, _) => "Const",
    ExprData::App(_, _, _) => "App",
    ExprData::Lam(_, _, _, _, _) => "Lam",
    ExprData::ForallE(_, _, _, _, _) => "ForallE",
    ExprData::LetE(_, _, _, _, _, _) => "LetE",
    ExprData::Lit(_, _) => "Lit",
    ExprData::Mdata(_, _, _) => "Mdata",
    ExprData::Proj(_, _, _, _) => "Proj",
    ExprData::Fvar(_, _) => "Fvar",
    ExprData::Mvar(_, _) => "Mvar",
  }
}
