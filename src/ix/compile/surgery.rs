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
  ConstantInfo as LeanConstantInfo, Env as LeanEnv, Expr as LeanExpr, ExprData,
  Name,
};
use crate::ix::ixon::error::CompileError;
use crate::ix::ixon::expr::Expr as IxonExpr;

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

// ===========================================================================
// Telescope utilities
// ===========================================================================

/// Collect a Lean App telescope: peel App nodes to get `(head, [a1, ..., aN])`.
///
/// Arguments are returned in application order (leftmost first).
pub fn collect_lean_telescope<'a>(
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
pub fn collect_ixon_telescope(
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
pub fn compute_call_site_plans(
  sorted_classes: &[Vec<Name>],
  original_all: &[Name],
  lean_env: &LeanEnv,
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

  // source_to_canon_motive[src_i] = class index of original_all[src_i],
  // or a placeholder 0 if the name is "phantom" (not in the current
  // canonical block — see the function-level comment). The placeholder
  // is safe because consumers only read this value when
  // motive_keep[src_i] is true, and motive_keep below always evaluates
  // to false for phantom src_i.
  let is_phantom: Vec<bool> =
    original_all.iter().map(|n| !name_to_class.contains_key(n)).collect();
  let source_to_canon_motive: Vec<usize> = original_all
    .iter()
    .map(|n| name_to_class.get(n).copied().unwrap_or(0))
    .collect();

  // Get constructor counts per source inductive (for minor mapping)
  let ctor_counts: Vec<usize> = original_all
    .iter()
    .map(|n| match lean_env.get(n).as_deref() {
      Some(LeanConstantInfo::InductInfo(v)) => v.ctors.len(),
      _ => 0,
    })
    .collect();

  // Get recursor structural info from any recursor in the block
  let (n_params, n_indices) = original_all
    .iter()
    .find_map(|n| {
      let rec_name = Name::str(n.clone(), "rec".to_string());
      match lean_env.get(&rec_name).as_deref() {
        Some(LeanConstantInfo::RecInfo(r)) => Some((
          crate::ix::compile::nat_conv::nat_to_usize(&r.num_params),
          crate::ix::compile::nat_conv::nat_to_usize(&r.num_indices),
        )),
        _ => None,
      }
    })
    .unwrap_or((0, 0));

  let n_source_motives = n_source;
  let n_source_minors: usize = ctor_counts.iter().sum();

  // Compute canonical ctor counts per class (for canon_to_source_minor)
  // In the canonical recursor, minors are ordered by class.
  // Each class's ctor count = representative's ctor count.
  let canon_ctor_counts: Vec<usize> = sorted_classes
    .iter()
    .map(|class| {
      let rep = &class[0];
      match lean_env.get(rep).as_deref() {
        Some(LeanConstantInfo::InductInfo(v)) => v.ctors.len(),
        _ => 0,
      }
    })
    .collect();

  // For each inductive X in original_all, compute the .rec plan for X.rec.
  for (x_pos, x_name) in original_all.iter().enumerate() {
    // Skip phantom X names: they belong to a different canonical block
    // (SCC-split from the user-written mutual), and that block will
    // produce their plan.
    if is_phantom[x_pos] {
      continue;
    }
    let x_class = source_to_canon_motive[x_pos];

    // --- Motive keep/permute ---
    let mut motive_keep = vec![false; n_source];
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

    // --- Minor keep/permute ---
    // Minors are grouped by parent inductive: [all[0].ctors, all[1].ctors, ...]
    // A minor is kept iff its parent inductive's motive is kept.
    let mut minor_keep = Vec::with_capacity(n_source_minors);
    let mut source_to_canon_minor = Vec::with_capacity(n_source_minors);

    // Build cumulative canonical minor offset per class
    let mut canon_minor_offset = vec![0usize; n_classes];
    {
      let mut offset = 0;
      for (ci, cc) in canon_ctor_counts.iter().enumerate() {
        canon_minor_offset[ci] = offset;
        offset += cc;
      }
    }

    // Track how many minors we've placed per class (for positioning)
    let mut class_minor_placed = vec![0usize; n_classes];

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

    let plan = CallSitePlan {
      n_params,
      n_source_motives,
      n_source_minors,
      n_indices,
      motive_keep,
      minor_keep,
      source_to_canon_motive: source_to_canon_motive.clone(),
      source_to_canon_minor,
    };

    // Skip identity plans
    if plan.is_identity() {
      continue;
    }

    // Register under X.rec
    let rec_name = Name::str(x_name.clone(), "rec".to_string());
    if lean_env.get(&rec_name).is_some() {
      plans.insert(rec_name, plan);
    }
  }

  Ok(plans)
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
            typ: LeanExpr::sort(crate::ix::env::Level::zero()),
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
              typ: LeanExpr::sort(crate::ix::env::Level::zero()),
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
        LeanConstantInfo::RecInfo(crate::ix::env::RecursorVal {
          cnst: ConstantVal {
            name: nn(name_str, "rec"),
            level_params: vec![],
            typ: LeanExpr::sort(crate::ix::env::Level::zero()),
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
    let plans = compute_call_site_plans(&sorted_classes, &original_all, &env)
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
    let plans = compute_call_site_plans(&sorted_classes, &original_all, &env)
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
    let plans = compute_call_site_plans(&sorted_classes, &original_all, &env)
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
    let plans = compute_call_site_plans(&sorted_classes, &original_all, &env)
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
}
