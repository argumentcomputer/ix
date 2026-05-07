//! Call-site surgery for argument reordering.
//!
//! When `sort_consts` reorders or collapses mutual inductives into equivalence
//! classes, the `aux_gen` pipeline regenerates auxiliaries (`.rec`, `.below`,
//! `.brecOn`, etc.) with canonical argument ordering. User-written Lean code
//! calling these auxiliaries still has arguments in source order. This module
//! provides:
//!
//! 1. **`CallSitePlan`**: Per-auxiliary surgery plan describing how source-order
//!    motive/minor arguments map to canonical positions (permutation + keep mask).
//!
//! 2. **Telescope utilities**: `collect_lean_telescope` / `collect_ixon_telescope`
//!    for peeling App spines into `(head, args)` pairs — one walk, O(depth).
//!
//! 3. **Plan computation**: `compute_call_site_plans` derives plans from the
//!    canonical class ordering and the original Lean recursor structure.
//!
//! The surgery plan differs per original recursor name: for mutual `[A, B]`
//! where `A ~ B`, `A.rec` keeps `motive_A` while `B.rec` keeps `motive_B`,
//! because each recursor's result type uses the motive for its "self" type.

use std::sync::Arc;

use rustc_hash::FxHashMap;

use crate::ix::env::{
  ConstantInfo as LeanConstantInfo, ConstructorVal, Env as LeanEnv,
  Expr as LeanExpr, ExprData, Level, Name, NameData, RecursorVal,
};
use crate::ix::ixon::error::CompileError;
use crate::ix::ixon::expr::Expr as IxonExpr;

use super::{
  aux_gen::expr_utils::{
    LocalDecl, consume_type_annotations, decompose_apps, fresh_fvar,
    instantiate1, mk_lambda, subst_levels,
  },
  nat_conv::nat_to_usize,
};

// NOTE: an `AuxKind` enum (Rec / BelowDef / BelowIndc / BrecOn / CasesOn /
// RecOn) used to live here to tag the region layout for each auxiliary
// kind. In practice only `.rec` ever gets a surgery plan — the other
// auxiliaries are regenerated from scratch by aux_gen and never need
// call-site surgery — so every `CallSitePlan` had `kind: AuxKind::Rec`
// and no consumer ever read the field. Removed in Round 4 cleanup.
// (The decompile side has its own, different `AuxKind` enum for
// classifying auxiliary name suffixes — that one is live and unchanged.)

/// Per-auxiliary surgery plan for call-site argument reordering.
///
/// Computed per original recursor name (not per equivalence class), because
/// the choice of which collapsed motive to keep depends on which member of
/// the equivalence class the recursor "belongs to".
#[derive(Clone, Debug)]
pub struct CallSitePlan {
  /// Number of parameters (unchanged between source and canonical).
  pub n_params: usize,
  /// Source-order motive count (from original `rec.all.len()`).
  pub n_source_motives: usize,
  /// Source-order minor count.
  pub n_source_minors: usize,
  /// Number of indices (between minors and major premise).
  pub n_indices: usize,
  /// `keep[i]`: true if source motive `i` survives collapse.
  /// For `A.rec`, `keep[A_pos]` = true. For `B.rec`, `keep[B_pos]` = true.
  pub motive_keep: Vec<bool>,
  /// `keep[i]`: true if source minor `i` survives collapse.
  pub minor_keep: Vec<bool>,
  /// `source_to_canon[i]` = canonical position of source motive `i`.
  /// Collapsed positions share the same canonical index as their representative.
  pub source_to_canon_motive: Vec<usize>,
  /// Same for minors.
  pub source_to_canon_minor: Vec<usize>,
  /// `true` when the source motive belongs to this canonical SCC.
  ///
  /// Source recursor types use Lean's original `all` block, but canonical
  /// recursors are generated per minimal SCC. A source motive can therefore
  /// be present in the source telescope while absent from this canonical
  /// block. Call-site minor adaptation uses this bit to distinguish
  /// "canonical recursor supplies an IH binder" from "the IH must be
  /// synthesized by a recursive call into another canonical block".
  pub source_in_block: Vec<bool>,
}

impl CallSitePlan {
  /// Number of canonical (kept) motives.
  pub fn n_canonical_motives(&self) -> usize {
    self.motive_keep.iter().filter(|&&k| k).count()
  }

  /// Number of canonical (kept) minors.
  pub fn n_canonical_minors(&self) -> usize {
    self.minor_keep.iter().filter(|&&k| k).count()
  }

  /// Total canonical args in the telescope (params + kept motives + kept minors + indices + 1 major).
  pub fn n_canonical_args(&self) -> usize {
    self.n_params
      + self.n_canonical_motives()
      + self.n_canonical_minors()
      + self.n_indices
      + 1 // major premise
  }

  /// Whether this plan is an identity (no reordering, no collapse).
  pub fn is_identity(&self) -> bool {
    self.motive_keep.iter().all(|&k| k)
      && self.minor_keep.iter().all(|&k| k)
      && self.source_to_canon_motive.iter().enumerate().all(|(i, &c)| c == i)
      && self.source_to_canon_minor.iter().enumerate().all(|(i, &c)| c == i)
  }
}

/// Call-site surgery plan for `.brecOn` / `.brecOn_N`.
///
/// `.rec` telescope layout is:
/// `params, motives, minors, indices, major`.
///
/// `.brecOn` telescope layout is:
/// `params, motives, indices, major, handlers`, with one handler per motive.
/// The motive permutation/drop decision is the same as the corresponding
/// recursor plan, and the handlers mirror that motive layout.
#[derive(Clone, Debug)]
pub struct BRecOnCallSitePlan {
  pub n_params: usize,
  pub n_source_motives: usize,
  pub n_indices: usize,
  pub motive_keep: Vec<bool>,
  pub source_to_canon_motive: Vec<usize>,
}

impl BRecOnCallSitePlan {
  pub fn from_rec_plan(plan: &CallSitePlan) -> Self {
    Self {
      n_params: plan.n_params,
      n_source_motives: plan.n_source_motives,
      n_indices: plan.n_indices,
      motive_keep: plan.motive_keep.clone(),
      source_to_canon_motive: plan.source_to_canon_motive.clone(),
    }
  }

  pub fn n_canonical_motives(&self) -> usize {
    self.motive_keep.iter().filter(|&&k| k).count()
  }

  pub fn is_identity(&self) -> bool {
    self.motive_keep.iter().all(|&k| k)
      && self.source_to_canon_motive.iter().enumerate().all(|(i, &c)| c == i)
  }
}

pub(crate) fn rec_name_to_brecon_name(name: &Name) -> Option<Name> {
  match name.as_data() {
    NameData::Str(parent, s, _) if s == "rec" => {
      Some(Name::str(parent.clone(), "brecOn".to_string()))
    },
    NameData::Str(parent, s, _) if s.starts_with("rec_") => {
      Some(Name::str(parent.clone(), format!("brecOn_{}", &s[4..])))
    },
    _ => None,
  }
}

pub(crate) fn rec_name_to_below_name(name: &Name) -> Option<Name> {
  match name.as_data() {
    NameData::Str(parent, s, _) if s == "rec" => {
      Some(Name::str(parent.clone(), "below".to_string()))
    },
    NameData::Str(parent, s, _) if s.starts_with("rec_") => {
      Some(Name::str(parent.clone(), format!("below_{}", &s[4..])))
    },
    _ => None,
  }
}

// ===========================================================================
// Telescope utilities
// ===========================================================================

/// Collect a Lean App telescope: peel App nodes to get `(head, [a1, ..., aN])`.
///
/// Arguments are returned in application order (leftmost first).
pub(crate) fn collect_lean_telescope<'a>(
  e: &'a LeanExpr,
) -> (&'a LeanExpr, Vec<&'a LeanExpr>) {
  let mut args: Vec<&'a LeanExpr> = Vec::new();
  let mut cur = e;
  while let ExprData::App(f, a, _) = cur.as_data() {
    args.push(a);
    cur = f;
  }
  args.reverse();
  (cur, args)
}

/// Collect an Ixon App telescope: peel App nodes to get `(head, [a1, ..., aN])`.
///
/// Arguments are returned in application order (leftmost first).
#[allow(dead_code)]
pub(crate) fn collect_ixon_telescope(
  e: &Arc<IxonExpr>,
) -> (Arc<IxonExpr>, Vec<Arc<IxonExpr>>) {
  let mut args: Vec<Arc<IxonExpr>> = Vec::new();
  let mut cur = e.clone();
  while let IxonExpr::App(f, a) = cur.as_ref() {
    args.push(a.clone());
    cur = f.clone();
  }
  args.reverse();
  (cur, args)
}

// ===========================================================================
// Plan computation
// ===========================================================================

/// Compute call-site surgery plans for all auxiliary names in a collapsed block.
///
/// `sorted_classes`: canonical equivalence classes from `sort_consts`, each
/// inner vec is a list of inductive names in the class (first = representative).
///
/// `original_all`: the original `rec.all` list from the Lean recursor (source order).
///
/// `lean_env`: the Lean environment for looking up constructor counts.
///
/// Returns a map from auxiliary name (e.g. `A.rec`, `B.rec`) to its surgery plan.
/// Only produces plans for `.rec` auxiliaries initially.
///
/// Note on "phantom" names: Lean's `all` field on a recursor is the full
/// user-written mutual block. SCC analysis may split that block into
/// several canonical blocks; in that case `original_all` legitimately
/// contains names that are NOT in the current block's `sorted_classes`.
/// Such phantom names get their motive/minors dropped by the surgery
/// plan (they belong to a different canonical block which will produce
/// its own plan). We skip generating a plan for a phantom `X.rec`
/// itself, since that belongs to the block owning `X`.
///
/// The [`AuxLayout`] type is re-exported from `crate::ix::ixon::env` so it
/// can live in the Ixon env side-table and survive serialization — see the
/// doc on [`crate::ix::ixon::env::AuxLayout`] for the canonical definition.
pub(crate) use crate::ix::ixon::env::AuxLayout;

const PERM_OUT_OF_SCC: usize = usize::MAX;

pub(crate) fn compute_call_site_plans(
  sorted_classes: &[Vec<Name>],
  original_all: &[Name],
  lean_env: &LeanEnv,
  aux_layout: Option<&AuxLayout>,
) -> Result<FxHashMap<Name, CallSitePlan>, CompileError> {
  let mut plans: FxHashMap<Name, CallSitePlan> = FxHashMap::default();
  let n_classes = sorted_classes.len();
  let n_source = original_all.len();

  if n_source == 0 || n_classes == 0 {
    return Ok(plans);
  }

  // Build name → class index
  let mut name_to_class: FxHashMap<Name, usize> = FxHashMap::default();
  for (ci, class) in sorted_classes.iter().enumerate() {
    for name in class {
      name_to_class.insert(name.clone(), ci);
    }
  }

  // Per-source-inductive constructor counts, indexed by `original_all` position.
  // Only covers USER-visible source inductives. Nested-aux inductives' ctor
  // counts are not included here; they're handled separately below.
  let ctor_counts: Vec<usize> = original_all
    .iter()
    .map(|n| match lean_env.get(n) {
      Some(LeanConstantInfo::InductInfo(v)) => v.ctors.len(),
      _ => 0,
    })
    .collect();

  // Read the Lean source recursor's structural info directly. Crucially,
  // `num_motives` / `num_minors` already include nested-auxiliary counts
  // — see `IndGroupInfo.numMotives = all.size + numNested` in
  // `refs/lean4/src/Lean/Elab/PreDefinition/Structural/IndGroupInfo.lean:40`.
  // Deriving `n_source_motives` from `original_all.len()` alone would
  // undercount by `numNested`, which then mis-slices the call telescope
  // at compile.rs:BuildCallSite — the first `numNested` aux motives would
  // land in the `minors` slice and everything downstream shifts,
  // producing AppTypeMismatches like "Code minor in Array-Alt motive slot"
  // on surgered `_sizeOf_N` bodies of nested mutuals (LCNF et al.).
  let (n_params, n_indices, lean_num_motives, lean_num_minors) = original_all
    .iter()
    .find_map(|n| {
      let rec_name = Name::str(n.clone(), "rec".to_string());
      match lean_env.get(&rec_name) {
        Some(LeanConstantInfo::RecInfo(r)) => Some((
          nat_to_usize(&r.num_params),
          nat_to_usize(&r.num_indices),
          nat_to_usize(&r.num_motives),
          nat_to_usize(&r.num_minors),
        )),
        _ => None,
      }
    })
    .unwrap_or((0, 0, n_source, ctor_counts.iter().sum()));

  // User vs aux split. The user-visible portion has one motive per
  // `original_all` entry; anything Lean's recursor carries beyond that is
  // a nested-auxiliary motive (e.g. `Array Alt`'s motive for LCNF).
  let n_user_motives = n_source;
  let n_source_motives = lean_num_motives.max(n_user_motives);
  let n_source_aux_motives = n_source_motives.saturating_sub(n_user_motives);
  let n_user_minors: usize = ctor_counts.iter().sum();
  let n_source_minors = lean_num_minors.max(n_user_minors);
  let n_aux_minors = n_source_minors - n_user_minors;
  let aux_perm = aux_layout.map(|l| l.perm.as_slice());

  let aux_canonical_count = aux_perm
    .and_then(|p| {
      p.iter().copied().filter(|&c| c != PERM_OUT_OF_SCC).max().map(|m| m + 1)
    })
    .unwrap_or(n_source_aux_motives);

  let aux_canon_of_source = |source_aux_j: usize| -> Option<usize> {
    match aux_perm.and_then(|p| p.get(source_aux_j).copied()) {
      Some(PERM_OUT_OF_SCC) => None,
      Some(canon_i) => Some(canon_i),
      None => Some(source_aux_j),
    }
  };

  // Representative source aux for each canonical aux class. Under
  // aux-alpha-collapse, multiple Lean-source `_N`s can point at the same
  // canonical aux slot; source-order reconstruction must keep exactly one
  // source arg per canonical slot and preserve the others in CallSite
  // collapsed metadata.
  let mut aux_repr_for_canon = vec![usize::MAX; aux_canonical_count];
  for source_aux_j in 0..n_source_aux_motives {
    if let Some(canon_i) = aux_canon_of_source(source_aux_j)
      && let Some(slot) = aux_repr_for_canon.get_mut(canon_i)
      && *slot == usize::MAX
    {
      *slot = source_aux_j;
    }
  }

  // source_to_canon_motive[src_i] = canonical class index of the src_i-th
  // source motive (0-based within the motive block). For user motives
  // (src_i < n_user_motives) this is `name_to_class[original_all[src_i]]`,
  // with a placeholder 0 for "phantom" names (SCC-split — their motive is
  // dropped, and consumers only read this value when motive_keep is true).
  //
  // For aux motives (src_i >= n_user_motives): Lean's aux ordering is the
  // source-walk-discovery order of its C++ `elim_nested_inductive_fn`;
  // our aux_gen canonicalizes by content hash. They coincide only when
  // the block has no alpha-collapse AND the hash-sort happens to match
  // source-walk. For the general case, the caller passes `aux_perm`
  // mapping `perm[source_j] = canonical_i` (from `nested::compute_aux_perm`).
  // When `aux_perm` is absent, we fall back to identity — correct for
  // blocks where walk orders coincide (the common case pre-fix).
  let is_phantom: Vec<bool> = (0..n_source_motives)
    .map(|src_i| {
      if src_i < n_user_motives {
        !name_to_class.contains_key(&original_all[src_i])
      } else {
        false // aux motives are never phantom
      }
    })
    .collect();
  let source_in_block: Vec<bool> = (0..n_source_motives)
    .map(|src_i| {
      if src_i < n_user_motives {
        !is_phantom[src_i]
      } else {
        aux_canon_of_source(src_i - n_user_motives).is_some()
      }
    })
    .collect();
  let source_to_canon_motive: Vec<usize> = (0..n_source_motives)
    .map(|src_i| {
      if src_i < n_user_motives {
        name_to_class.get(&original_all[src_i]).copied().unwrap_or(0)
      } else {
        let source_aux_j = src_i - n_user_motives;
        match aux_canon_of_source(source_aux_j) {
          Some(canon_aux_i) => n_classes + canon_aux_i,
          None => 0,
        }
      }
    })
    .collect();

  // Compute canonical ctor counts per class (for source_to_canon_minor).
  // In the canonical recursor, minors are ordered by class. Each class's
  // ctor count = representative's ctor count. Only covers user classes;
  // aux classes' ctor counts are handled by the identity-map pass for
  // aux minors below.
  let canon_ctor_counts: Vec<usize> = sorted_classes
    .iter()
    .map(|class| {
      let rep = &class[0];
      match lean_env.get(rep) {
        Some(LeanConstantInfo::InductInfo(v)) => v.ctors.len(),
        _ => 0,
      }
    })
    .collect();
  let n_canon_user_minors: usize = canon_ctor_counts.iter().sum();

  // Build cumulative canonical minor offset per user class (shared across
  // all plan computations — minor layout is class-driven, not target-driven).
  let mut canon_minor_offset = vec![0usize; n_classes];
  {
    let mut offset = 0;
    for (ci, cc) in canon_ctor_counts.iter().enumerate() {
      canon_minor_offset[ci] = offset;
      offset += cc;
    }
  }

  // Build one CallSitePlan for a specific target x_pos (the source
  // motive index this recursor is "for"). Factored out so we can
  // generate plans for both user `X.rec` (x_pos ∈ [0, n_user_motives))
  // and nested-aux `X.rec_N` (x_pos ∈ [n_user_motives, n_source_motives)).
  let build_plan = |x_pos: usize| -> CallSitePlan {
    let x_class = source_to_canon_motive[x_pos];

    // --- Motive keep/permute ---
    // `motive_keep` / `source_to_canon_motive` cover BOTH user and aux
    // motives (sized `n_source_motives = user + aux`). User motives:
    // alpha-collapse logic (keep-self-in-class, keep-rep-in-other-class).
    // Aux motives: always kept, identity-mapped (our aux_gen and Lean's
    // nested-recursor builder agree on the aux-inductive order).
    let mut motive_keep = vec![false; n_source_motives];
    for (src_i, src_name) in original_all.iter().enumerate() {
      if is_phantom[src_i] {
        // Phantom src_i's motive belongs to another canonical block;
        // always drop it here.
        continue;
      }
      let src_class = source_to_canon_motive[src_i];
      if src_class == x_class {
        // Self class: keep only X's own motive
        motive_keep[src_i] = src_i == x_pos;
      } else {
        // Non-self class: keep the representative's motive.
        // Representative = first name in sorted_classes[src_class].
        let rep = &sorted_classes[src_class][0];
        motive_keep[src_i] = src_name == rep;
      }
    }
    // Aux motives mirror the user-class collapse rule. For each canonical
    // aux class, keep the representative source aux; if the target recursor
    // itself is an aux in that canonical class, keep the target source aux
    // instead. Other source aux motives are restored from CallSite metadata.
    let target_aux = x_pos.checked_sub(n_user_motives);
    let target_aux_canon = target_aux.and_then(aux_canon_of_source);
    for source_aux_j in 0..n_source_aux_motives {
      let src_i = n_user_motives + source_aux_j;
      motive_keep[src_i] = match aux_canon_of_source(source_aux_j) {
        Some(canon_i) if Some(canon_i) == target_aux_canon => {
          target_aux == Some(source_aux_j)
        },
        Some(canon_i) => {
          aux_repr_for_canon.get(canon_i).copied() == Some(source_aux_j)
        },
        None => false,
      };
    }
    // When the target is an aux position, the "keep self" rule above
    // was written assuming X is a user inductive. For aux targets the
    // self motive (x_pos in the aux band) is already set to true by
    // the loop just above (aux always kept). But we should ALSO drop
    // any other-aux-class "representative" treatment — with singleton
    // aux classes under no alpha-collapse, the representative-keep
    // logic for non-self user classes already chose correctly, and aux
    // classes are never collapsed in this plan model so every aux
    // motive is its own (trivial) representative. No extra work.

    // --- Minor keep/permute ---
    // Source minors layout: [user_inductive_0.ctors ... user_inductive_{N-1}.ctors |
    // aux_inductive_0.ctors ... aux_inductive_{M-1}.ctors]. User minors
    // follow the alpha-collapse logic (kept iff parent motive kept,
    // permuted to canonical class-grouped order). Aux minors follow the
    // aux motive's keep/drop decision and are mapped into the canonical
    // aux-minor band starting at `n_canon_user_minors`.
    let mut minor_keep = Vec::with_capacity(n_source_minors);
    let mut source_to_canon_minor = Vec::with_capacity(n_source_minors);

    // Track how many minors we've placed per class (for positioning).
    let mut class_minor_placed = vec![0usize; n_classes];

    // User minors — existing logic.
    for (src_i, _src_name) in original_all.iter().enumerate() {
      let n_ctors = ctor_counts[src_i];
      let src_class = source_to_canon_motive[src_i];
      let parent_kept = motive_keep[src_i];

      for ctor_j in 0..n_ctors {
        minor_keep.push(parent_kept);
        if parent_kept {
          let canon_pos =
            canon_minor_offset[src_class] + class_minor_placed[src_class];
          source_to_canon_minor.push(canon_pos);
          class_minor_placed[src_class] += 1;
        } else {
          // Collapsed — the source minor is dropped at the call site
          // (`minor_keep[src_i] = false`), so consumers at
          // compile.rs:~609 never read this value. We push a placeholder
          // index (rep's ctor_j) purely to keep the index space aligned
          // with the source minor count; the specific value is
          // irrelevant for correctness. Note: class members may have
          // different ctor arities in principle (see
          // `test_plan_minor_collapse`), so we do NOT assert equal
          // arity here.
          let rep_minor_base = canon_minor_offset[src_class];
          source_to_canon_minor.push(rep_minor_base + ctor_j);
        }
      }
    }

    // Aux minors — permuted through the aux-band.
    //
    // Each source aux class j has `source_ctor_counts[j]` minors. Those
    // minors are grouped in the source minor list (flat aux band) in
    // class order. Canonically, the block reorders aux classes by
    // `aux_layout.perm`, so source class j's minors move to the slot
    // starting at `canon_aux_minor_offset[perm[j]]`. Without `aux_layout`,
    // we fall back to identity mapping — correct when source walk ==
    // canonical (the common pre-fix case).
    if let Some(layout) = aux_layout {
      // Canonical aux ctor counts (indexed by canonical aux position).
      // source_j at canonical position perm[source_j] contributes
      // source_ctor_counts[source_j] ctors.
      let mut canon_aux_ctor_counts = vec![0usize; aux_canonical_count];
      for (source_j, &canon_i) in layout.perm.iter().enumerate() {
        if canon_i != PERM_OUT_OF_SCC
          && canon_i < aux_canonical_count
          && let Some(&cc) = layout.source_ctor_counts.get(source_j)
        {
          canon_aux_ctor_counts[canon_i] = cc;
        }
      }
      // Cumulative canonical aux minor offsets.
      let mut canon_aux_offset = vec![0usize; aux_canonical_count];
      {
        let mut offset = 0;
        for (canon_i, cc) in canon_aux_ctor_counts.iter().enumerate() {
          canon_aux_offset[canon_i] = offset;
          offset += *cc;
        }
      }
      // Walk source aux classes in source order, placing their minors
      // at the canonical positions of perm[j]'s class.
      for (source_j, &n_ctors) in layout.source_ctor_counts.iter().enumerate() {
        let src_i = n_user_motives + source_j;
        let parent_kept = motive_keep.get(src_i).copied().unwrap_or(true);
        let canon_i = aux_canon_of_source(source_j);
        let base = canon_i
          .and_then(|canon_i| canon_aux_offset.get(canon_i).copied())
          .unwrap_or(0);
        for k in 0..n_ctors {
          minor_keep.push(parent_kept);
          // Both kept and unkept positions reuse the canonical slot — this
          // mirrors the user-side mapping where dropped sources still record
          // where their canonical sibling landed.
          source_to_canon_minor.push(n_canon_user_minors + base + k);
        }
      }
      // Safety fallback: if layout inventories don't sum to n_aux_minors
      // (shouldn't happen for well-formed input but defend against it),
      // pad with identity entries to keep the minor arrays sized to
      // n_source_minors.
      while minor_keep.len() < n_source_minors {
        let k = source_to_canon_minor.len().saturating_sub(n_user_minors);
        minor_keep.push(true);
        source_to_canon_minor.push(n_canon_user_minors + k);
      }
    } else {
      // Identity mapping when no layout is provided.
      for k in 0..n_aux_minors {
        minor_keep.push(true);
        source_to_canon_minor.push(n_canon_user_minors + k);
      }
    }

    CallSitePlan {
      n_params,
      n_source_motives,
      n_source_minors,
      n_indices,
      motive_keep,
      minor_keep,
      source_to_canon_motive: source_to_canon_motive.clone(),
      source_to_canon_minor,
      source_in_block: source_in_block.clone(),
    }
  };

  // Register plans for each user inductive's `X.rec` (x_pos ∈ [0, n_user)).
  for (x_pos, x_name) in original_all.iter().enumerate() {
    // Skip phantom X names: they belong to a different canonical block
    // (SCC-split from the user-written mutual), and that block will
    // produce their plan.
    if is_phantom[x_pos] {
      continue;
    }
    let plan = build_plan(x_pos);
    if plan.is_identity() {
      continue;
    }
    let rec_name = Name::str(x_name.clone(), "rec".to_string());
    if lean_env.get(&rec_name).is_some() {
      plans.insert(rec_name, plan);
    }
  }

  // Register plans for each nested-auxiliary recursor `all[0].rec_N`
  // (x_pos ∈ [n_user, n_source_motives)).
  //
  // Why: Lean's `mkSizeOfFns`
  // (refs/lean4/src/Lean/Meta/SizeOf.lean:167-187) generates
  // `_sizeOf_{all.size + j + 1}` bodies that call
  // `(mkRecName all[0]).appendIndexAfter (j+1)` — e.g. `Alt.rec_1`,
  // `Alt.rec_2`, … — for each nested-aux `j ∈ [0, numNested)`. Those
  // rec_N recursors share the main recursor's motive/minor layout
  // (same canonical permutation under reordering), they just target a
  // different class. Without plans for them, aux `_sizeOf_N` bodies
  // pass source-order args to our canonical rec_N, producing the
  // AppTypeMismatch observed on e.g. `LCNF.Alt._sizeOf_6` (where
  // canonical class 0 wasn't the user's source-order class 0).
  if n_source_motives > n_user_motives
    && let Some(head_name) = original_all.first()
  {
    for aux_idx in 0..(n_source_motives - n_user_motives) {
      if aux_perm
        .and_then(|p| p.get(aux_idx).copied())
        .is_some_and(|canon_i| canon_i == PERM_OUT_OF_SCC)
      {
        continue;
      }
      let x_pos = n_user_motives + aux_idx;
      let plan = build_plan(x_pos);
      if plan.is_identity() {
        continue;
      }
      let rec_name =
        Name::str(head_name.clone(), format!("rec_{}", aux_idx + 1));
      if lean_env.get(&rec_name).is_some() {
        plans.insert(rec_name, plan);
      }
    }
  }

  // -----------------------------------------------------------------------
  // Gated diagnostic dump — IX_SURGERY_DUMP=<prefix>
  //
  // When the env var is set and its value is a prefix of `original_all[0]`'s
  // pretty name, dump the full intermediate state of this call-site-plan
  // computation. Used to pin down where a Category A/B mismatch originates
  // (see plans/the-nested-inductive-work-declarative-naur.md).
  // -----------------------------------------------------------------------
  if let Ok(filter) = std::env::var("IX_SURGERY_DUMP")
    && !filter.is_empty()
    && let Some(head) = original_all.first()
    && head.pretty().starts_with(&filter)
  {
    dump_plan_state(
      &filter,
      sorted_classes,
      original_all,
      lean_env,
      aux_layout,
      n_params,
      n_indices,
      lean_num_motives,
      lean_num_minors,
      n_user_motives,
      n_source_motives,
      n_source_aux_motives,
      n_user_minors,
      n_source_minors,
      n_aux_minors,
      aux_canonical_count,
      &ctor_counts,
      &canon_ctor_counts,
      &canon_minor_offset,
      &aux_repr_for_canon,
      &is_phantom,
      &source_to_canon_motive,
      &plans,
    );
  }

  Ok(plans)
}

/// Adapt a kept source minor for a canonical recursor whose SCC is smaller
/// than Lean's original mutual `all` block.
///
/// Lean's source recursor minor for a constructor receives an IH argument for
/// every recursive field targeting any inductive in the original mutual block.
/// After canonical SCC splitting, the regenerated recursor only supplies IHs
/// for fields targeting the current SCC. For fields targeting another SCC, we
/// synthesize the missing IH by recursively calling the target's source
/// recursor with the original source-order motive/minor telescope. That inner
/// recursor call then goes through the normal call-site surgery for its own
/// SCC.
#[allow(clippy::too_many_arguments)]
pub(crate) fn adapt_split_minor(
  rec_name: &Name,
  rec_levels: &[Level],
  plan: &CallSitePlan,
  src_minor_idx: usize,
  minor: &LeanExpr,
  params: &[LeanExpr],
  motives: &[LeanExpr],
  minors: &[LeanExpr],
  lean_env: &LeanEnv,
) -> Option<LeanExpr> {
  if plan.source_in_block.iter().all(|&in_block| in_block) {
    return None;
  }

  let rec_info = lean_env.get(rec_name)?;
  let rec = match rec_info {
    LeanConstantInfo::RecInfo(rec) => rec,
    _ => return None,
  };
  let original_all = rec.all.as_slice();
  let (_parent_src, ctor) =
    source_ctor_for_minor(src_minor_idx, rec, lean_env)?;
  let n_fields = nat_to_usize(&ctor.num_fields);
  let source_minor_ty =
    source_minor_type(rec, rec_levels, params, motives, minors, src_minor_idx)?;

  let (field_decls, field_fvars, after_fields) =
    peel_binders(source_minor_ty, n_fields, "split_field", 0)?;

  let mut rec_fields = Vec::new();
  for (field_idx, decl) in field_decls.iter().enumerate() {
    if let Some(target) = find_source_rec_target(
      &decl.domain,
      original_all,
      params,
      lean_env,
      "split_xs",
      field_idx,
    ) {
      rec_fields.push((field_idx, target));
    }
  }

  if !rec_fields.iter().any(|(_, target)| {
    !plan.source_in_block.get(target.source_pos).copied().unwrap_or(false)
  }) {
    return None;
  }

  let (source_ih_decls, source_ih_fvars, _) =
    peel_binders(after_fields, rec_fields.len(), "split_ih", 0)?;
  if source_ih_decls.len() != rec_fields.len() {
    return None;
  }

  let mut wrapper_decls = field_decls.clone();
  let mut body = minor.clone();
  for fv in &field_fvars {
    body = LeanExpr::app(body, fv.clone());
  }

  for (ih_idx, (field_idx, target)) in rec_fields.iter().enumerate() {
    if plan.source_in_block.get(target.source_pos).copied().unwrap_or(false) {
      wrapper_decls.push(source_ih_decls[ih_idx].clone());
      body = LeanExpr::app(body, source_ih_fvars[ih_idx].clone());
    } else {
      let synth = synthesize_external_ih(
        target,
        &field_fvars[*field_idx],
        original_all,
        rec_levels,
        params,
        motives,
        minors,
      );
      body = LeanExpr::app(body, synth);
    }
  }

  Some(mk_lambda(body, &wrapper_decls))
}

fn source_ctor_for_minor(
  src_minor_idx: usize,
  rec: &RecursorVal,
  lean_env: &LeanEnv,
) -> Option<(usize, ConstructorVal)> {
  let mut offset = 0usize;
  for (source_pos, ind_name) in rec.all.iter().enumerate() {
    let ind_info = lean_env.get(ind_name)?;
    let ind = match ind_info {
      LeanConstantInfo::InductInfo(ind) => ind,
      _ => return None,
    };
    let n_ctors = ind.ctors.len();
    if src_minor_idx < offset + n_ctors {
      let ctor_name = &ind.ctors[src_minor_idx - offset];
      let ctor = match lean_env.get(ctor_name)? {
        LeanConstantInfo::CtorInfo(ctor) => ctor.clone(),
        _ => return None,
      };
      return Some((source_pos, ctor));
    }
    offset += n_ctors;
  }
  None
}

fn source_minor_type(
  rec: &RecursorVal,
  rec_levels: &[Level],
  params: &[LeanExpr],
  motives: &[LeanExpr],
  minors: &[LeanExpr],
  src_minor_idx: usize,
) -> Option<LeanExpr> {
  let mut cur = subst_levels(&rec.cnst.typ, &rec.cnst.level_params, rec_levels);
  for arg in
    params.iter().chain(motives.iter()).chain(minors.iter().take(src_minor_idx))
  {
    match cur.as_data() {
      ExprData::ForallE(_, _, body, _, _) => {
        cur = instantiate1(body, arg);
      },
      _ => return None,
    }
  }
  match cur.as_data() {
    ExprData::ForallE(_, dom, _, _, _) => Some(consume_type_annotations(dom)),
    _ => None,
  }
}

fn peel_binders(
  mut cur: LeanExpr,
  n: usize,
  prefix: &str,
  offset: usize,
) -> Option<(Vec<LocalDecl>, Vec<LeanExpr>, LeanExpr)> {
  let mut decls = Vec::with_capacity(n);
  let mut fvars = Vec::with_capacity(n);
  for i in 0..n {
    match cur.as_data() {
      ExprData::ForallE(name, dom, body, bi, _) => {
        let (fv_name, fv) = fresh_fvar(prefix, offset + i);
        let decl = LocalDecl {
          fvar_name: fv_name,
          binder_name: name.clone(),
          domain: consume_type_annotations(dom),
          info: bi.clone(),
        };
        cur = instantiate1(body, &fv);
        fvars.push(fv);
        decls.push(decl);
      },
      _ => return None,
    }
  }
  Some((decls, fvars, cur))
}

#[derive(Clone)]
struct SourceRecTarget {
  source_pos: usize,
  idx_args: Vec<LeanExpr>,
  xs_decls: Vec<LocalDecl>,
  xs_fvars: Vec<LeanExpr>,
}

fn find_source_rec_target(
  dom: &LeanExpr,
  original_all: &[Name],
  params: &[LeanExpr],
  lean_env: &LeanEnv,
  prefix: &str,
  field_idx: usize,
) -> Option<SourceRecTarget> {
  let mut cur = consume_type_annotations(dom);
  let mut xs_decls = Vec::new();
  let mut xs_fvars = Vec::new();

  while let ExprData::ForallE(name, dom, body, bi, _) = cur.as_data() {
    let (fv_name, fv) =
      fresh_fvar(prefix, field_idx.saturating_mul(1024) + xs_fvars.len());
    let decl = LocalDecl {
      fvar_name: fv_name,
      binder_name: name.clone(),
      domain: consume_type_annotations(dom),
      info: bi.clone(),
    };
    cur = instantiate1(body, &fv);
    xs_fvars.push(fv);
    xs_decls.push(decl);
  }

  let (head, args) = decompose_apps(&cur);
  let ExprData::Const(target_name, _, _) = head.as_data() else {
    return None;
  };
  let source_pos = original_all.iter().position(|n| n == target_name)?;
  let target_n_params = match lean_env.get(target_name)? {
    LeanConstantInfo::InductInfo(ind) => nat_to_usize(&ind.num_params),
    _ => return None,
  };
  if args.len() < target_n_params || params.len() < target_n_params {
    return None;
  }
  if !args[..target_n_params]
    .iter()
    .zip(params.iter())
    .all(|(arg, param)| arg.get_hash() == param.get_hash())
  {
    return None;
  }

  Some(SourceRecTarget {
    source_pos,
    idx_args: args.into_iter().skip(target_n_params).collect(),
    xs_decls,
    xs_fvars,
  })
}

fn synthesize_external_ih(
  target: &SourceRecTarget,
  field_fvar: &LeanExpr,
  original_all: &[Name],
  rec_levels: &[Level],
  params: &[LeanExpr],
  motives: &[LeanExpr],
  minors: &[LeanExpr],
) -> LeanExpr {
  let target_name = &original_all[target.source_pos];
  let target_rec_name = Name::str(target_name.clone(), "rec".to_string());
  let mut ih = LeanExpr::cnst(target_rec_name, rec_levels.to_vec());

  for arg in params {
    ih = LeanExpr::app(ih, arg.clone());
  }
  for arg in motives {
    ih = LeanExpr::app(ih, arg.clone());
  }
  for arg in minors {
    ih = LeanExpr::app(ih, arg.clone());
  }
  for idx in &target.idx_args {
    ih = LeanExpr::app(ih, idx.clone());
  }

  let mut field_app = field_fvar.clone();
  for fv in &target.xs_fvars {
    field_app = LeanExpr::app(field_app, fv.clone());
  }
  ih = LeanExpr::app(ih, field_app);

  mk_lambda(ih, &target.xs_decls)
}

/// Dump the intermediate state of `compute_call_site_plans` for a single
/// block. Gated by `IX_SURGERY_DUMP=<prefix>`. See the call site for the
/// full set of scalars and vectors printed.
#[allow(clippy::too_many_arguments)]
fn dump_plan_state(
  filter: &str,
  sorted_classes: &[Vec<Name>],
  original_all: &[Name],
  lean_env: &LeanEnv,
  aux_layout: Option<&AuxLayout>,
  n_params: usize,
  n_indices: usize,
  lean_num_motives: usize,
  lean_num_minors: usize,
  n_user_motives: usize,
  n_source_motives: usize,
  n_source_aux_motives: usize,
  n_user_minors: usize,
  n_source_minors: usize,
  n_aux_minors: usize,
  aux_canonical_count: usize,
  ctor_counts: &[usize],
  canon_ctor_counts: &[usize],
  canon_minor_offset: &[usize],
  aux_repr_for_canon: &[usize],
  is_phantom: &[bool],
  source_to_canon_motive: &[usize],
  plans: &FxHashMap<Name, CallSitePlan>,
) {
  let head0 = original_all.first().map(|n| n.pretty()).unwrap_or_default();
  eprintln!(
    "[surgery.dump] ═══════════════════════════════════════════════════"
  );
  eprintln!("[surgery.dump] filter={filter} head_all[0]={head0}");
  eprintln!(
    "[surgery.dump] sorted_classes ({} classes):",
    sorted_classes.len()
  );
  for (ci, class) in sorted_classes.iter().enumerate() {
    let names: Vec<String> = class.iter().map(|n| n.pretty()).collect();
    eprintln!("  class[{ci:2}] = {names:?}");
  }
  eprintln!("[surgery.dump] original_all ({} names):", original_all.len());
  for (i, n) in original_all.iter().enumerate() {
    let phantom = if is_phantom.get(i).copied().unwrap_or(false) {
      " [phantom]"
    } else {
      ""
    };
    eprintln!("  [{i:2}] {}{phantom}", n.pretty());
  }
  eprintln!(
    "[surgery.dump] scalars: n_params={n_params} n_indices={n_indices} \
     lean_num_motives={lean_num_motives} lean_num_minors={lean_num_minors} \
     n_user_motives={n_user_motives} n_source_motives={n_source_motives} \
     n_source_aux_motives={n_source_aux_motives} n_user_minors={n_user_minors} \
     n_source_minors={n_source_minors} n_aux_minors={n_aux_minors} \
     aux_canonical_count={aux_canonical_count}"
  );
  if let Some(layout) = aux_layout {
    eprintln!(
      "[surgery.dump] aux_layout.perm               = {:?}",
      layout.perm
    );
    eprintln!(
      "[surgery.dump] aux_layout.source_ctor_counts = {:?}",
      layout.source_ctor_counts
    );
  } else {
    eprintln!("[surgery.dump] aux_layout = None");
  }
  eprintln!(
    "[surgery.dump] ctor_counts        (per user src) = {ctor_counts:?}"
  );
  eprintln!(
    "[surgery.dump] canon_ctor_counts  (per user class) = {canon_ctor_counts:?}"
  );
  eprintln!(
    "[surgery.dump] canon_minor_offset (per user class) = {canon_minor_offset:?}"
  );
  eprintln!(
    "[surgery.dump] aux_repr_for_canon (canon_i -> rep source_j) = {aux_repr_for_canon:?}"
  );
  eprintln!(
    "[surgery.dump] source_to_canon_motive (all plans share) = {source_to_canon_motive:?}"
  );

  // Dump Lean's source recursor telescope, labelled per binder section.
  let first_rec = original_all.iter().find_map(|n| {
    let rec_name = Name::str(n.clone(), "rec".to_string());
    match lean_env.get(&rec_name) {
      Some(LeanConstantInfo::RecInfo(r)) => {
        Some((rec_name, r.cnst.typ.clone()))
      },
      _ => None,
    }
  });
  if let Some((rname, rty)) = first_rec {
    let total = n_params + n_source_motives + n_source_minors + n_indices + 1;
    eprintln!(
      "[surgery.dump] source recursor {} (expecting {} binders):",
      rname.pretty(),
      total
    );
    let mut cur = &rty;
    for bi in 0..total {
      let tag = if bi < n_params {
        "param"
      } else if bi < n_params + n_source_motives {
        "motive"
      } else if bi < n_params + n_source_motives + n_source_minors {
        "minor"
      } else if bi < n_params + n_source_motives + n_source_minors + n_indices {
        "index"
      } else {
        "major"
      };
      match cur.as_data() {
        ExprData::ForallE(bn, dom, body, _, _) => {
          eprintln!("  [{bi:3} {tag:6}] {} : {}", bn.pretty(), dom.pretty());
          cur = body;
        },
        _ => {
          eprintln!("  [{bi:3} {tag:6}] <telescope ended early>");
          break;
        },
      }
    }
  }

  // Per-plan details.
  let mut plan_names: Vec<&Name> = plans.keys().collect();
  plan_names.sort_by_key(|n| n.pretty());
  eprintln!("[surgery.dump] plans registered ({}):", plan_names.len());
  for name in plan_names {
    let plan = &plans[name];
    eprintln!("  {}", name.pretty());
    eprintln!("    motive_keep            = {:?}", plan.motive_keep);
    eprintln!("    minor_keep             = {:?}", plan.minor_keep);
    eprintln!("    source_to_canon_motive = {:?}", plan.source_to_canon_motive);
    eprintln!("    source_to_canon_minor  = {:?}", plan.source_to_canon_minor);
  }
  eprintln!(
    "[surgery.dump] ═══════════════════════════════════════════════════"
  );
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::ix::env::{ConstantVal, ConstructorVal, InductiveVal};
  use lean_ffi::nat::Nat;

  fn n(s: &str) -> Name {
    Name::str(Name::anon(), s.to_string())
  }

  fn nn(parent: &str, child: &str) -> Name {
    Name::str(n(parent), child.to_string())
  }

  // -----------------------------------------------------------------------
  // Telescope utilities
  // -----------------------------------------------------------------------

  #[test]
  fn test_collect_lean_telescope() {
    let f = LeanExpr::cnst(n("f"), vec![]);
    let a1 = LeanExpr::bvar(Nat::from(0u64));
    let a2 = LeanExpr::bvar(Nat::from(1u64));
    let a3 = LeanExpr::bvar(Nat::from(2u64));
    let app = LeanExpr::app(
      LeanExpr::app(LeanExpr::app(f.clone(), a1.clone()), a2.clone()),
      a3.clone(),
    );
    let (head, args) = collect_lean_telescope(&app);
    assert_eq!(head.get_hash(), f.get_hash());
    assert_eq!(args.len(), 3);
    assert_eq!(args[0].get_hash(), a1.get_hash());
    assert_eq!(args[1].get_hash(), a2.get_hash());
    assert_eq!(args[2].get_hash(), a3.get_hash());
  }

  // -----------------------------------------------------------------------
  // CallSitePlan identity detection
  // -----------------------------------------------------------------------

  #[test]
  fn test_identity_plan() {
    let plan = CallSitePlan {
      n_params: 1,
      n_source_motives: 2,
      n_source_minors: 2,
      n_indices: 0,
      motive_keep: vec![true, true],
      minor_keep: vec![true, true],
      source_to_canon_motive: vec![0, 1],
      source_to_canon_minor: vec![0, 1],
      source_in_block: vec![true, true],
    };
    assert!(plan.is_identity());
  }

  #[test]
  fn test_non_identity_plan_collapsed() {
    let plan = CallSitePlan {
      n_params: 0,
      n_source_motives: 3,
      n_source_minors: 3,
      n_indices: 0,
      motive_keep: vec![true, true, false], // 3rd collapsed
      minor_keep: vec![true, true, false],
      source_to_canon_motive: vec![0, 1, 0],
      source_to_canon_minor: vec![0, 1, 0],
      source_in_block: vec![true, true, true],
    };
    assert!(!plan.is_identity());
  }

  #[test]
  fn test_non_identity_plan_permuted() {
    let plan = CallSitePlan {
      n_params: 0,
      n_source_motives: 3,
      n_source_minors: 3,
      n_indices: 0,
      motive_keep: vec![true, true, true],
      minor_keep: vec![true, true, true],
      source_to_canon_motive: vec![2, 0, 1], // permuted
      source_to_canon_minor: vec![2, 0, 1],
      source_in_block: vec![true, true, true],
    };
    assert!(!plan.is_identity());
  }

  // -----------------------------------------------------------------------
  // compute_call_site_plans
  // -----------------------------------------------------------------------

  /// Helper: build a minimal Lean environment with mutual inductives.
  fn build_test_env(
    names: &[&str],
    ctor_counts: &[usize],
  ) -> crate::ix::env::Env {
    let mut env = crate::ix::env::Env::default();
    let all: Vec<Name> = names.iter().map(|s| n(s)).collect();

    for (i, &name_str) in names.iter().enumerate() {
      let ind_name = n(name_str);
      let ctors: Vec<Name> = (0..ctor_counts[i])
        .map(|j| nn(name_str, &format!("ctor{j}")))
        .collect();

      // Register the inductive
      env.insert(
        ind_name.clone(),
        LeanConstantInfo::InductInfo(InductiveVal {
          cnst: ConstantVal {
            name: ind_name.clone(),
            level_params: vec![],
            typ: LeanExpr::sort(Level::zero()),
          },
          num_params: Nat::from(0u64),
          num_indices: Nat::from(0u64),
          all: all.clone(),
          ctors: ctors.clone(),
          num_nested: Nat::from(0u64),
          is_rec: false,
          is_unsafe: false,
          is_reflexive: false,
        }),
      );

      // Register constructors
      for ctor_name in &ctors {
        env.insert(
          ctor_name.clone(),
          LeanConstantInfo::CtorInfo(ConstructorVal {
            cnst: ConstantVal {
              name: ctor_name.clone(),
              level_params: vec![],
              typ: LeanExpr::sort(Level::zero()),
            },
            induct: ind_name.clone(),
            cidx: Nat::from(0u64),
            num_params: Nat::from(0u64),
            num_fields: Nat::from(0u64),
            is_unsafe: false,
          }),
        );
      }

      // Register recursor
      let rec_name = nn(name_str, "rec");
      env.insert(
        rec_name,
        LeanConstantInfo::RecInfo(RecursorVal {
          cnst: ConstantVal {
            name: nn(name_str, "rec"),
            level_params: vec![],
            typ: LeanExpr::sort(Level::zero()),
          },
          all: all.clone(),
          num_params: Nat::from(0u64),
          num_indices: Nat::from(0u64),
          num_motives: Nat::from(names.len() as u64),
          num_minors: Nat::from(ctor_counts.iter().sum::<usize>() as u64),
          rules: vec![],
          k: false,
          is_unsafe: false,
        }),
      );
    }
    env
  }

  #[test]
  fn test_plan_no_collapse_no_reorder() {
    // [A, B] with classes [[A], [B]] — identity, no plans generated
    let env = build_test_env(&["A", "B"], &[1, 1]);
    let sorted_classes = vec![vec![n("A")], vec![n("B")]];
    let original_all = vec![n("A"), n("B")];
    let plans =
      compute_call_site_plans(&sorted_classes, &original_all, &env, None)
        .expect("test data is well-formed");
    assert!(plans.is_empty(), "identity plans should be skipped");
  }

  #[test]
  fn test_plan_reorder_no_collapse() {
    // Source: [C, A, B], canonical: [[A], [B], [C]]
    // All kept, but permuted: source motives [mC, mA, mB] → canon [mA, mB, mC]
    let env = build_test_env(&["C", "A", "B"], &[1, 1, 1]);
    let sorted_classes = vec![vec![n("A")], vec![n("B")], vec![n("C")]];
    let original_all = vec![n("C"), n("A"), n("B")];
    let plans =
      compute_call_site_plans(&sorted_classes, &original_all, &env, None)
        .expect("test data is well-formed");

    // All 3 recursors should have plans (since the permutation is non-identity)
    assert!(plans.contains_key(&nn("C", "rec")));
    assert!(plans.contains_key(&nn("A", "rec")));
    assert!(plans.contains_key(&nn("B", "rec")));

    let plan_c = &plans[&nn("C", "rec")];
    // Source: [C=0, A=1, B=2], canon: [A=0, B=1, C=2]
    // source_to_canon: C→2, A→0, B→1
    assert_eq!(plan_c.source_to_canon_motive, vec![2, 0, 1]);
    // All kept (no collapse)
    assert_eq!(plan_c.motive_keep, vec![true, true, true]);
  }

  #[test]
  fn test_plan_collapse_a_b_equivalent() {
    // Source: [A, B, C], A~B collapsed: classes [[A, B], [C]]
    // A.rec keeps motive_A (self), B.rec keeps motive_B (self)
    let env = build_test_env(&["A", "B", "C"], &[1, 1, 1]);
    let sorted_classes = vec![vec![n("A"), n("B")], vec![n("C")]];
    let original_all = vec![n("A"), n("B"), n("C")];
    let plans =
      compute_call_site_plans(&sorted_classes, &original_all, &env, None)
        .expect("test data is well-formed");

    // A.rec: keep motive_A (pos 0), drop motive_B (pos 1), keep motive_C (pos 2)
    let plan_a = &plans[&nn("A", "rec")];
    assert_eq!(plan_a.motive_keep, vec![true, false, true]);
    assert_eq!(plan_a.source_to_canon_motive, vec![0, 0, 1]);
    assert_eq!(plan_a.n_canonical_motives(), 2);

    // B.rec: drop motive_A (pos 0), keep motive_B (pos 1), keep motive_C (pos 2)
    let plan_b = &plans[&nn("B", "rec")];
    assert_eq!(plan_b.motive_keep, vec![false, true, true]);
    assert_eq!(plan_b.source_to_canon_motive, vec![0, 0, 1]);
    assert_eq!(plan_b.n_canonical_motives(), 2);

    // C.rec: keep motive_A (rep of class 0), drop motive_B, keep motive_C
    let plan_c = &plans[&nn("C", "rec")];
    assert_eq!(plan_c.motive_keep, vec![true, false, true]);
    assert_eq!(plan_c.source_to_canon_motive, vec![0, 0, 1]);
  }

  #[test]
  fn test_plan_minor_collapse() {
    // A has 2 ctors, B has 1 ctor, A~B collapsed: classes [[A, B]]
    // Source minors: [A.c1, A.c2, B.c1] → canon minors: [A.c1, A.c2]
    let env = build_test_env(&["A", "B"], &[2, 1]);
    let sorted_classes = vec![vec![n("A"), n("B")]];
    let original_all = vec![n("A"), n("B")];
    let plans =
      compute_call_site_plans(&sorted_classes, &original_all, &env, None)
        .expect("test data is well-formed");

    let plan_a = &plans[&nn("A", "rec")];
    // A.rec: keep A's minors (pos 0, 1), drop B's minor (pos 2)
    assert_eq!(plan_a.minor_keep, vec![true, true, false]);
    assert_eq!(plan_a.n_canonical_minors(), 2);

    let plan_b = &plans[&nn("B", "rec")];
    // B.rec: drop A's minors (pos 0, 1), keep B's minor (pos 2)
    assert_eq!(plan_b.minor_keep, vec![false, false, true]);
    assert_eq!(plan_b.n_canonical_minors(), 1);
  }

  // -----------------------------------------------------------------------
  // Nested-inductive plan computation
  //
  // Lean's `IndGroupInfo.numMotives = all.size + numNested` (see
  // refs/lean4/src/Lean/Elab/PreDefinition/Structural/IndGroupInfo.lean:40).
  // For a user-visible mutual with nested-aux inductives (e.g. `Cases`
  // containing `Array Alt` in LCNF), the Lean `.rec` actually carries MORE
  // motives and minors than `original_all.len()` / `sum(ctor_counts)` would
  // suggest — one motive and a minor-group per nested aux.
  //
  // `compute_call_site_plans` must therefore read `num_motives` /
  // `num_minors` from `RecursorVal` directly and extend its keep/permute
  // vectors to cover the aux band. Aux motives and minors are always Kept
  // and identity-mapped into the canonical aux band that starts right
  // after the user classes/minors. The tests below pin that behaviour;
  // without this handling, the first `numNested` aux motives fall into
  // the `minors` slice of surgery's call-site slicing and the kernel
  // rejects the compiled `_sizeOf_N` bodies with AppTypeMismatch.
  // -----------------------------------------------------------------------

  /// Build a test env where each recursor reports `num_motives` and
  /// `num_minors` with `aux_motives` / `aux_minors` added on top of the
  /// user-visible counts. Simulates what Lean stores for a nested mutual
  /// inductive's recursor without us having to spin up real nested
  /// inductives.
  fn build_test_env_with_nested(
    names: &[&str],
    ctor_counts: &[usize],
    aux_motives: usize,
    aux_minors: usize,
  ) -> crate::ix::env::Env {
    let mut env = build_test_env(names, ctor_counts);
    // Overwrite each inductive's recursor with inflated motive/minor counts.
    let total_motives = (names.len() + aux_motives) as u64;
    let total_minors = (ctor_counts.iter().sum::<usize>() + aux_minors) as u64;
    for &name_str in names {
      let rec_name = nn(name_str, "rec");
      env.insert(
        rec_name.clone(),
        LeanConstantInfo::RecInfo(RecursorVal {
          cnst: ConstantVal {
            name: rec_name,
            level_params: vec![],
            typ: LeanExpr::sort(Level::zero()),
          },
          all: names.iter().map(|s| n(s)).collect(),
          num_params: Nat::from(0u64),
          num_indices: Nat::from(0u64),
          num_motives: Nat::from(total_motives),
          num_minors: Nat::from(total_minors),
          rules: vec![],
          k: false,
          is_unsafe: false,
        }),
      );
    }
    env
  }

  #[test]
  fn test_plan_nested_n_source_motives_reads_recursor() {
    // A single nested inductive `T` with 1 ctor, plus 1 nested aux
    // motive and 2 nested aux minors. No reorder, no collapse — the plan
    // would be identity and therefore skipped BUT only if n_source_motives
    // was derived correctly from the recursor (not from original_all.len()).
    // If the derivation is wrong, motive_keep and friends get sized wrong
    // and plan.is_identity() reports a stale answer.
    let env = build_test_env_with_nested(
      &["T"],
      &[1],
      /*aux_motives=*/ 1,
      /*aux_minors=*/ 2,
    );
    let sorted_classes = vec![vec![n("T")]];
    let original_all = vec![n("T")];
    let plans =
      compute_call_site_plans(&sorted_classes, &original_all, &env, None)
        .expect("test data is well-formed");
    assert!(plans.is_empty(), "nested-but-identity plan should be skipped",);
  }

  #[test]
  fn test_plan_nested_with_reorder() {
    // Two user inductives [Y, X] with one aux-motive and one aux-minor
    // each (simulating e.g. `Array X`, `Array Y` nested auxiliaries).
    // Canonical order is [X, Y] (user classes reordered). Expected plan:
    //   - n_source_motives = 2 user + 2 aux = 4
    //   - n_source_minors  = 2 user + 2 aux = 4
    //   - source_to_canon_motive = [1, 0, 2, 3]
    //       Y (src 0) → canon 1, X (src 1) → canon 0,
    //       aux0 (src 2) → canon 2 (identity into aux band),
    //       aux1 (src 3) → canon 3 (identity into aux band).
    //   - motive_keep = [true, true, true, true]  (all kept, just permuted)
    //   - source_to_canon_minor for aux positions is identity into the
    //     canonical aux-minor band starting at n_canon_user_minors = 2.
    let env = build_test_env_with_nested(
      &["Y", "X"],
      &[1, 1],
      /*aux_motives=*/ 2,
      /*aux_minors=*/ 2,
    );
    let sorted_classes = vec![vec![n("X")], vec![n("Y")]];
    let original_all = vec![n("Y"), n("X")];
    let plans =
      compute_call_site_plans(&sorted_classes, &original_all, &env, None)
        .expect("test data is well-formed");

    let plan_y = plans
      .get(&nn("Y", "rec"))
      .expect("Y.rec should have a plan (non-identity under reorder)");
    assert_eq!(
      plan_y.n_source_motives, 4,
      "n_source_motives must match Lean's num_motives (user + aux), not just user count",
    );
    assert_eq!(
      plan_y.n_source_minors, 4,
      "n_source_minors must match Lean's num_minors (user + aux), not just user count",
    );
    assert_eq!(plan_y.motive_keep, vec![true, true, true, true]);
    assert_eq!(plan_y.source_to_canon_motive, vec![1, 0, 2, 3]);
    // User minors: Y has 1 ctor (src 0 → canon minor offset for Y's class=1 = 1),
    // X has 1 ctor (src 1 → canon minor offset for X's class=0 = 0).
    // Aux minors (src 2, 3): identity into aux band starting at n_canon_user_minors=2.
    assert_eq!(plan_y.source_to_canon_minor, vec![1, 0, 2, 3]);
    assert_eq!(plan_y.minor_keep, vec![true, true, true, true]);
  }

  #[test]
  fn test_plan_nested_lcnf_shape() {
    // LCNF-style fixture: 4 user inductives [Alt, FunDecl, Cases, Code],
    // each with one source ctor, plus 1 nested aux motive + 1 aux minor
    // (Array Alt). Canonical order: the alphabetical permutation
    // [Alt, Cases, Code, FunDecl] (reorder but no collapse). Exercises
    // the exact aux-bookkeeping that broke kernel-check-const on
    // `Lean.Compiler.LCNF.Alt._sizeOf_4` before this fix.
    let env = build_test_env_with_nested(
      &["Alt", "FunDecl", "Cases", "Code"],
      &[1, 1, 1, 1],
      /*aux_motives=*/ 1,
      /*aux_minors=*/ 1,
    );
    let sorted_classes = vec![
      vec![n("Alt")],
      vec![n("Cases")],
      vec![n("Code")],
      vec![n("FunDecl")],
    ];
    let original_all = vec![n("Alt"), n("FunDecl"), n("Cases"), n("Code")];
    let plans =
      compute_call_site_plans(&sorted_classes, &original_all, &env, None)
        .expect("test data is well-formed");

    let plan_alt = plans
      .get(&nn("Alt", "rec"))
      .expect("Alt.rec should have a plan under reorder");
    // 4 user motives + 1 aux motive.
    assert_eq!(plan_alt.n_source_motives, 5);
    // 4 user minors + 1 aux minor.
    assert_eq!(plan_alt.n_source_minors, 5);
    // Canon classes: Alt=0, Cases=1, Code=2, FunDecl=3.
    // Source positions: Alt=0, FunDecl=1, Cases=2, Code=3.
    // Aux motive: src 4 → canon 4 (identity into aux band).
    assert_eq!(plan_alt.source_to_canon_motive, vec![0, 3, 1, 2, 4]);
    // All motives kept (no collapse).
    assert_eq!(plan_alt.motive_keep, vec![true, true, true, true, true]);
    // User minors: canon class offsets = [0, 1, 2, 3] (1 ctor each),
    // so src[0]=Alt→0, src[1]=FunDecl→3, src[2]=Cases→1, src[3]=Code→2.
    // Aux minor: src 4 → canon 4 (n_canon_user_minors=4 + aux offset 0).
    assert_eq!(plan_alt.source_to_canon_minor, vec![0, 3, 1, 2, 4]);
    assert_eq!(plan_alt.minor_keep, vec![true, true, true, true, true]);
  }

  #[test]
  #[allow(non_snake_case)]
  fn test_plan_nested_registers_rec_N_names() {
    // Lean's `mkSizeOfFns` generates `_sizeOf_{all.size + j + 1}` bodies
    // that call `all[0].rec_{j+1}` (one per nested aux), NOT `X.rec`.
    // If we only register plans for `X.rec`, aux `_sizeOf_N` bodies
    // miss surgery and emit source-order args (kernel rejects).
    //
    // Fixture: [Y, X] user + 2 aux motives/minors, reordered canonically
    // to [X, Y]. Expected: plans for `Y.rec`, `X.rec`, `Y.rec_1`, `Y.rec_2`
    // (Y is original_all[0], the head).
    let mut env = build_test_env_with_nested(
      &["Y", "X"],
      &[1, 1],
      /*aux_motives=*/ 2,
      /*aux_minors=*/ 2,
    );
    // Also register `Y.rec_1` and `Y.rec_2` in the env so
    // compute_call_site_plans' `lean_env.get(&rec_name).is_some()`
    // gate accepts them.
    for j in 1..=2u64 {
      let rec_name = nn("Y", &format!("rec_{j}"));
      env.insert(
        rec_name.clone(),
        LeanConstantInfo::RecInfo(RecursorVal {
          cnst: ConstantVal {
            name: rec_name,
            level_params: vec![],
            typ: LeanExpr::sort(Level::zero()),
          },
          all: vec![n("Y"), n("X")],
          num_params: Nat::from(0u64),
          num_indices: Nat::from(0u64),
          num_motives: Nat::from(4u64),
          num_minors: Nat::from(4u64),
          rules: vec![],
          k: false,
          is_unsafe: false,
        }),
      );
    }
    let sorted_classes = vec![vec![n("X")], vec![n("Y")]];
    let original_all = vec![n("Y"), n("X")];
    let plans =
      compute_call_site_plans(&sorted_classes, &original_all, &env, None)
        .expect("test data is well-formed");

    // Both user recursors get plans.
    assert!(plans.contains_key(&nn("Y", "rec")), "Y.rec should have a plan");
    assert!(plans.contains_key(&nn("X", "rec")), "X.rec should have a plan");
    // AND both aux recursors get plans (keyed under head = original_all[0] = Y).
    // This is the regression guard: pre-fix these were missing, so aux
    // `_sizeOf_N` bodies never got surgery and kernel-check failed.
    assert!(
      plans.contains_key(&nn("Y", "rec_1")),
      "Y.rec_1 should have a plan (aux rec for nested aux 0)"
    );
    assert!(
      plans.contains_key(&nn("Y", "rec_2")),
      "Y.rec_2 should have a plan (aux rec for nested aux 1)"
    );
    // Aux-rec plans share the same motive permutation as user-rec plans.
    assert_eq!(
      plans[&nn("Y", "rec_1")].source_to_canon_motive,
      plans[&nn("Y", "rec")].source_to_canon_motive,
    );
  }

  #[test]
  #[allow(non_snake_case)]
  fn test_plan_nested_aux_perm_registers_rec_N_without_user_reorder() {
    // User classes stay in source order [A, B], but nested aux classes
    // are canonically permuted. `_sizeOf_N` bodies still call `A.rec_N`
    // with Lean source-order aux motive/minor args, so compile must build
    // plans whenever AuxLayout.perm is non-identity.
    let mut env = build_test_env_with_nested(
      &["A", "B"],
      &[1, 1],
      /*aux_motives=*/ 2,
      /*aux_minors=*/ 2,
    );
    for j in 1..=2u64 {
      let rec_name = nn("A", &format!("rec_{j}"));
      env.insert(
        rec_name.clone(),
        LeanConstantInfo::RecInfo(RecursorVal {
          cnst: ConstantVal {
            name: rec_name,
            level_params: vec![],
            typ: LeanExpr::sort(Level::zero()),
          },
          all: vec![n("A"), n("B")],
          num_params: Nat::from(0u64),
          num_indices: Nat::from(0u64),
          num_motives: Nat::from(4u64),
          num_minors: Nat::from(4u64),
          rules: vec![],
          k: false,
          is_unsafe: false,
        }),
      );
    }

    let sorted_classes = vec![vec![n("A")], vec![n("B")]];
    let original_all = vec![n("A"), n("B")];
    let layout = AuxLayout { perm: vec![1, 0], source_ctor_counts: vec![1, 1] };
    let plans = compute_call_site_plans(
      &sorted_classes,
      &original_all,
      &env,
      Some(&layout),
    )
    .expect("test data is well-formed");

    assert!(
      plans.contains_key(&nn("A", "rec_1")),
      "A.rec_1 should have a plan when only aux order changes"
    );
    assert!(
      plans.contains_key(&nn("A", "rec_2")),
      "A.rec_2 should have a plan when only aux order changes"
    );
    assert_eq!(
      plans[&nn("A", "rec_1")].source_to_canon_motive,
      vec![0, 1, 3, 2],
      "user motives stay fixed while aux motives follow AuxLayout.perm"
    );
    assert_eq!(
      plans[&nn("A", "rec_1")].source_to_canon_minor,
      vec![0, 1, 3, 2],
      "aux minor groups follow AuxLayout.perm"
    );
  }

  #[test]
  #[allow(non_snake_case)]
  fn test_plan_nested_skips_out_of_scc_rec_N() {
    // SCC-split original mutual: Lean's source recursor has user motives
    // [A, B, C] and aux motives [List A, List B, List C], but the current
    // canonical block owns only A/B plus their list auxiliaries. The C/List C
    // positions must be reconstructed from CallSite metadata, and this block
    // must not register a plan for `A.rec_3` (owned by the C block).
    let mut env = build_test_env_with_nested(
      &["A", "B", "C"],
      &[1, 1, 1],
      /*aux_motives=*/ 3,
      /*aux_minors=*/ 6,
    );
    for j in 1..=3u64 {
      let rec_name = nn("A", &format!("rec_{j}"));
      env.insert(
        rec_name.clone(),
        LeanConstantInfo::RecInfo(RecursorVal {
          cnst: ConstantVal {
            name: rec_name,
            level_params: vec![],
            typ: LeanExpr::sort(Level::zero()),
          },
          all: vec![n("A"), n("B"), n("C")],
          num_params: Nat::from(0u64),
          num_indices: Nat::from(0u64),
          num_motives: Nat::from(6u64),
          num_minors: Nat::from(9u64),
          rules: vec![],
          k: false,
          is_unsafe: false,
        }),
      );
    }

    let sorted_classes = vec![vec![n("A")], vec![n("B")]];
    let original_all = vec![n("A"), n("B"), n("C")];
    let layout = AuxLayout {
      // Source auxes are [List A, List B, List C]; canonical A/B block
      // owns [List B, List A]. List C belongs to a different SCC.
      perm: vec![1, 0, PERM_OUT_OF_SCC],
      source_ctor_counts: vec![2, 2, 2],
    };
    let plans = compute_call_site_plans(
      &sorted_classes,
      &original_all,
      &env,
      Some(&layout),
    )
    .expect("test data is well-formed");

    assert!(plans.contains_key(&nn("A", "rec_1")));
    assert!(plans.contains_key(&nn("A", "rec_2")));
    assert!(
      !plans.contains_key(&nn("A", "rec_3")),
      "out-of-SCC aux recursor plans must be left to their owning block"
    );

    let plan = &plans[&nn("A", "rec_2")];
    assert_eq!(
      plan.motive_keep,
      vec![true, true, false, true, true, false],
      "C and List C source motives are out-of-SCC and must be collapsed"
    );
    assert_eq!(
      plan.minor_keep,
      vec![true, true, false, true, true, true, true, false, false],
      "C and List C source minors are out-of-SCC and must be collapsed"
    );
    let kept_minors: Vec<usize> = plan
      .minor_keep
      .iter()
      .zip(plan.source_to_canon_minor.iter())
      .filter_map(|(&keep, &canon)| keep.then_some(canon))
      .collect();
    assert_eq!(
      kept_minors,
      vec![0, 1, 4, 5, 2, 3],
      "kept aux minor groups must map bijectively into canonical positions"
    );
  }

  #[test]
  fn test_plan_nested_aux_minors_span_multiple() {
    // Verify the aux-minor identity band handles multiple aux minors
    // correctly, even when their count differs from the aux-motive count
    // (a nested aux inductive can have multiple ctors).
    //
    // Fixture: 2 user inductives [A, B] (1 ctor each), 1 aux motive,
    // 3 aux minors. Canonical order [B, A] — user motives reordered.
    let env = build_test_env_with_nested(
      &["A", "B"],
      &[1, 1],
      /*aux_motives=*/ 1,
      /*aux_minors=*/ 3,
    );
    let sorted_classes = vec![vec![n("B")], vec![n("A")]];
    let original_all = vec![n("A"), n("B")];
    let plans =
      compute_call_site_plans(&sorted_classes, &original_all, &env, None)
        .expect("test data is well-formed");

    let plan_a = plans
      .get(&nn("A", "rec"))
      .expect("A.rec should have a plan under reorder");
    assert_eq!(plan_a.n_source_motives, 3); // 2 user + 1 aux
    assert_eq!(plan_a.n_source_minors, 5); // 2 user + 3 aux
    // Aux minor positions: source 2..5 map to canon
    // n_canon_user_minors + [0, 1, 2] = [2, 3, 4].
    assert_eq!(
      &plan_a.source_to_canon_minor[2..],
      &[2, 3, 4],
      "aux minors must identity-map into the canonical aux-minor band"
    );
    assert!(
      plan_a.minor_keep[2..].iter().all(|&k| k),
      "aux minors must all be Kept"
    );
  }
}
