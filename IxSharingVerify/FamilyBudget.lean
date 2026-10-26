import IxSharingVerify.BudgetMono
import IxSharingVerify.CanonicalProduction
import Ix.Sharing.FamilyNormalizeSpec

/-! Budget independence of the production family route.

Raising any resource limit (`LimitsLe`) keeps every successful run of the
family pipeline, with the same result: the uniform selection's component loop,
knapsack and finisher, the slot allocation, the re-materialization at the
layout widths, the three-width selection, and the production entries. Two
successful runs under any two limits therefore return the same result,
statistics included (`canonicalSharingTiered_budget_independent`): limits
decide only whether a run is refused, never what it returns. -/

namespace Ix.Sharing.Verify.Budget

open Ix.Sharing.Exact
open Ix.Sharing.Family
open Ix.Sharing.Verify.SharingExact (bind_eq_ok)

theorem not_gt_mono {x a b : Nat} (le : a ≤ b) (h : ¬ x > a) : ¬ x > b :=
  fun above => h (Nat.lt_of_le_of_lt le above)

/-! ## Uniform selection -/

theorem familyReferenceStep_mono {a b : Limits} (le : LimitsLe a b) (cfg : Config) (ex : Expanded)
    (sg : UStage) (width : Nat) (acc : MeterState) (members : Array Nat) {out : MeterState}
    (ran : familyReferenceStep cfg a ex sg width acc members = .ok out) :
    familyReferenceStep cfg b ex sg width acc members = .ok out := by
  obtain ⟨results, states, work⟩ := acc
  unfold familyReferenceStep at ran ⊢
  dsimp only at ran ⊢
  cases first : bump states (familyCalls cfg members.size) a.maxStates .states with
  | error error => rw [first] at ran; cases ran
  | ok states' =>
    rw [first] at ran
    rw [bump_mono le.states first]
    cases second : bump work (familyWork cfg members.size (componentContext ex sg members).closure.size)
        a.maxCostEvals .costEvals with
    | error error => rw [second] at ran; cases ran
    | ok work' =>
      rw [second] at ran
      rw [bump_mono le.costEvals second]
      exact ran

theorem familyReferenceFold_mono {a b : Limits} (le : LimitsLe a b) (cfg : Config) (ex : Expanded)
    (sg : UStage) (width : Nat) :
    ∀ (comps : List (Array Nat)) (acc : MeterState) {out : MeterState},
      comps.foldlM (familyReferenceStep cfg a ex sg width) acc = .ok out →
        comps.foldlM (familyReferenceStep cfg b ex sg width) acc = .ok out
  | [], acc, out, ran => by
    simp only [List.foldlM_nil] at ran ⊢
    exact ran
  | members :: rest, acc, out, ran => by
    rw [List.foldlM_cons] at ran ⊢
    obtain ⟨middle, step, tail⟩ := bind_eq_ok ran
    rw [bind_ok_eq (familyReferenceStep_mono le cfg ex sg width acc members step)]
    exact familyReferenceFold_mono le cfg ex sg width rest middle tail

theorem familyComponents_mono {a b : Limits} (le : LimitsLe a b) (cfg : Config) (ex : Expanded)
    (sg : UStage) (width : Nat) (hcp : childrenPrecede ex.dag.nodes = true) {out : MeterState}
    (ran : familyComponents cfg a ex sg width (parentsOf ex.dag) = .ok out) :
    familyComponents cfg b ex sg width (parentsOf ex.dag) = .ok out := by
  rw [familyComponents_eq_reference cfg a ex sg width hcp] at ran
  rw [familyComponents_eq_reference cfg b ex sg width hcp]
  unfold familyReferenceComponents at ran ⊢
  rw [← Array.foldlM_toList] at ran ⊢
  exact familyReferenceFold_mono le cfg ex sg width _ _ ran

theorem uniformKnapsack_mono {a b : Limits} (le : LimitsLe a b) {kCS : Nat} {results : Array CompResult}
    {out : _root_.Int × Array Nat × Bool} (ran : uniformKnapsack a kCS results = .ok out) :
    uniformKnapsack b kCS results = .ok out := by
  unfold uniformKnapsack at ran ⊢
  dsimp only at ran ⊢
  split at ran
  · rename_i above
    rw [ite_eq_left above]
    split at ran
    · cases ran
    · rename_i fits
      rw [ite_eq_right (not_gt_mono le.knapsackCells fits)]
      exact ran
  · rename_i below
    rw [ite_eq_right below]
    exact ran

theorem materializeDependent_mono {a b : Limits} (le : LimitsLe a b) (p : Prep) (table roots : Array Nat)
    (width : Array (Option Nat)) {out : Array Ixon.Expr × Array Ixon.Expr × Nat × Nat}
    (ran : p.materializeDependent table roots width a = .ok out) :
    p.materializeDependent table roots width b = .ok out := by
  unfold Prep.materializeDependent at ran ⊢
  dsimp only at ran ⊢
  split at ran
  · cases ran
  · rename_i small
    rw [ite_eq_right small]
    split at ran
    · cases ran
    · rename_i within
      rw [ite_eq_right (not_gt_mono le.materialize within)]
      exact ran

theorem reexpand_mono {a b : Limits} (le : LimitsLe a b) {dag : Dag} {sharing roots : Array Ixon.Expr}
    {out : Array Nat × Array Nat × Nat} (ran : reexpand a dag sharing roots = .ok out) :
    reexpand b dag sharing roots = .ok out := by
  unfold reexpand at ran ⊢
  obtain ⟨⟨⟨entryIds, rootIds⟩, st⟩, ingested, finished⟩ := bind_eq_ok ran
  rw [bind_ok_eq (ingestTable_refines le sharing roots true _ _ ingested)]
  exact finished

theorem uniformFinishF_mono {a b : Limits} (le : LimitsLe a b) (w : Nat) (ex : Expanded) (p : Prep)
    (deg : Array Nat) (c : UniformChoice) {out : UniformSharingResult}
    (ran : uniformFinishF w a ex p deg c = .ok out) : uniformFinishF w b ex p deg c = .ok out := by
  unfold uniformFinishF at ran ⊢
  dsimp only at ran ⊢
  split at ran
  · rename_i inRange
    rw [ite_eq_left inRange]
    split at ran
    · rename_i inClass
      rw [ite_eq_left inClass]
      obtain ⟨⟨entries, roots, predicted, work⟩, materialized, ran⟩ := bind_eq_ok ran
      rw [bind_ok_eq (materializeDependent_mono le _ _ _ _ materialized)]
      dsimp only at ran ⊢
      split at ran
      · rename_i modelled
        rw [ite_eq_left modelled]
        obtain ⟨⟨entryIds, rootIds, visits⟩, expanded, ran⟩ := bind_eq_ok ran
        rw [bind_ok_eq (reexpand_mono le expanded)]
        exact ran
      · cases ran
    · cases ran
  · cases ran

theorem familyUniform_mono {a b : Limits} (le : LimitsLe a b) (cfg : Config) (ex : Expanded)
    (facts : GraphFacts) (width : Nat) (hcp : childrenPrecede ex.dag.nodes = true)
    {out : UniformSharingResult}
    (ran : familyUniform cfg a ex (Prep.ofDag ex.dag) facts (parentsOf ex.dag) width = .ok out) :
    familyUniform cfg b ex (Prep.ofDag ex.dag) facts (parentsOf ex.dag) width = .ok out := by
  unfold familyUniform at ran ⊢
  dsimp only at ran ⊢
  split at ran
  · rename_i checked
    rw [ite_eq_left checked]
    obtain ⟨⟨results, states, work⟩, produced, ran⟩ := bind_eq_ok ran
    rw [bind_ok_eq (familyComponents_mono le cfg ex _ width hcp produced)]
    dsimp only at ran ⊢
    obtain ⟨⟨delta, chosen, lowerBracket⟩, picked, ran⟩ := bind_eq_ok ran
    rw [bind_ok_eq (uniformKnapsack_mono le picked)]
    dsimp only at ran ⊢
    split at ran
    · cases ran
    · rename_i nonnegative
      rw [ite_eq_right nonnegative]
      split at ran
      · cases ran
      · rename_i bounded
        rw [ite_eq_right (not_gt_mono le.outputBytes bounded)]
        exact uniformFinishF_mono le _ _ _ _ _ ran
  · cases ran

/-! ## Slot allocation -/

theorem ok_bind_congr {ε α β : Type} {x y : Except ε α} {f g : α → Except ε β} {out : β}
    (hx : ∀ v, x = .ok v → y = .ok v) (hf : ∀ v o, f v = .ok o → g v = .ok o)
    (ran : (x >>= f) = .ok out) : (y >>= g) = .ok out := by
  obtain ⟨v, xv, fv⟩ := bind_eq_ok ran
  rw [bind_ok_eq (hx v xv)]
  exact hf v out fv

theorem tierDfs_mono {a b : Limits} (le : LimitsLe a b) (items : Array Nat) (weight : Nat → Nat)
    (closure : Nat → Option (List Nat)) (cap : Nat) :
    ∀ (fuel pos cur : Nat) (inF : List Nat) (excluded : Std.HashSet Nat) (st : TierState)
      {out : TierState},
      tierDfs items weight closure cap a fuel pos cur inF excluded st = .ok out →
        tierDfs items weight closure cap b fuel pos cur inF excluded st = .ok out
  | 0, _, _, _, _, _, _, ran => by
    simp only [tierDfs] at ran
    cases ran
  | fuel + 1, pos, cur, inF, excluded, st, out, ran => by
    rw [tierDfs.eq_2] at ran
    rw [tierDfs.eq_2]
    split at ran
    · cases ran
    · rename_i within
      rw [ite_eq_right (not_gt_mono le.states within)]
      try dsimp only at ran ⊢
      split at ran
      · rename_i pruned
        rw [ite_eq_left pruned]
        exact ran
      · rename_i open'
        rw [ite_eq_right open']
        split at ran
        · rename_i finished
          rw [ite_eq_left finished]
          exact ran
        · rename_i inside
          rw [ite_eq_right inside]
          split at ran
          · rename_i member
            rw [ite_eq_left member]
            exact tierDfs_mono le items weight closure cap fuel _ _ _ _ _ ran
          · rename_i fresh
            rw [ite_eq_right fresh]
            cases hc : closure items[pos]! with
            | none =>
              rw [hc] at ran
              dsimp only at ran ⊢
              obtain ⟨mid, first, last⟩ := bind_eq_ok ran
              rw [bind_ok_eq first]
              exact tierDfs_mono le items weight closure cap fuel _ _ _ _ _ last
            | some c =>
              rw [hc] at ran
              dsimp only at ran ⊢
              split at ran
              · rename_i fits
                rw [ite_eq_left fits]
                obtain ⟨mid, first, last⟩ := bind_eq_ok ran
                rw [bind_ok_eq (tierDfs_mono le items weight closure cap fuel _ _ _ _ _ first)]
                exact tierDfs_mono le items weight closure cap fuel _ _ _ _ _ last
              · rename_i fits
                rw [ite_eq_right fits]
                obtain ⟨mid, first, last⟩ := bind_eq_ok ran
                rw [bind_ok_eq first]
                exact tierDfs_mono le items weight closure cap fuel _ _ _ _ _ last

theorem firstTier_mono {a b : Limits} (le : LimitsLe a b) (topo : Array Nat) (weight : Nat → Nat)
    (deps : Nat → List Nat) (cap : Nat) {out : Array Nat × Nat}
    (ran : firstTier topo weight deps cap a = .ok out) : firstTier topo weight deps cap b = .ok out := by
  unfold firstTier at ran ⊢
  dsimp only at ran ⊢
  obtain ⟨cl, closures, ran⟩ := bind_eq_ok ran
  rw [bind_ok_eq closures]
  obtain ⟨st, searched, ran⟩ := bind_eq_ok ran
  rw [bind_ok_eq (tierDfs_mono le _ _ _ _ _ _ _ _ _ _ searched)]
  exact ran

theorem allocate_mono {a b : Limits} (le : LimitsLe a b) (layout : ShareLayout) (dag : Dag)
    (deg : Array Nat) (order1 : Array Nat) (entries1 roots1 : Array Ixon.Expr) {out : Allocation}
    (ran : allocate layout a dag deg order1 entries1 roots1 = .ok out) :
    allocate layout b dag deg order1 entries1 roots1 = .ok out := by
  unfold allocate at ran ⊢
  dsimp only at ran ⊢
  obtain ⟨⟨tier, slotStates⟩, searched, ran⟩ := bind_eq_ok ran
  rw [bind_ok_eq (firstTier_mono le _ _ _ _ searched)]
  exact ran

/-! ## Re-materialization -/

theorem materializeStep_mono {a b : Limits} (le : LimitsLe a b) (p : Prep) (table : Array Nat)
    (widthAt : Nat → Nat) (st : TableState) (i : Nat) {out : TableState}
    (ran : materializeStep p table a widthAt st i = .ok out) :
    materializeStep p table b widthAt st i = .ok out := by
  unfold materializeStep at ran ⊢
  dsimp only at ran ⊢
  split at ran
  · cases ran
  · rename_i within
    rw [ite_eq_right (not_gt_mono le.materialize within)]
    obtain ⟨e, built, ran⟩ := bind_eq_ok ran
    rw [bind_ok_eq built]
    try dsimp only at ran ⊢
    split at ran
    · cases ran
    · rename_i bounded
      rw [ite_eq_right (not_gt_mono le.materializeWork bounded)]
      exact ran

theorem materializeSteps_mono {a b : Limits} (le : LimitsLe a b) (p : Prep) (table : Array Nat)
    (widthAt : Nat → Nat) :
    ∀ (items : List Nat) (st : TableState) {out : TableState},
      items.foldlM (materializeStep p table a widthAt) st = .ok out →
        items.foldlM (materializeStep p table b widthAt) st = .ok out
  | [], st, out, ran => by
    simp only [List.foldlM_nil] at ran ⊢
    exact ran
  | i :: rest, st, out, ran => by
    rw [List.foldlM_cons] at ran ⊢
    obtain ⟨middle, step, tail⟩ := bind_eq_ok ran
    rw [bind_ok_eq (materializeStep_mono le p table widthAt st i step)]
    exact materializeSteps_mono le p table widthAt rest middle tail

theorem materializeTable_mono {a b : Limits} (le : LimitsLe a b) (p : Prep) (table roots : Array Nat)
    (widthAt : Nat → Nat) {out : Array Ixon.Expr × Array Ixon.Expr × Nat × Nat}
    (ran : materializeTable p table roots a widthAt = .ok out) :
    materializeTable p table roots b widthAt = .ok out := by
  unfold materializeTable at ran ⊢
  dsimp only at ran ⊢
  split at ran
  · cases ran
  · rename_i small
    rw [ite_eq_right small]
    split at ran
    · cases ran
    · rename_i inRange
      rw [ite_eq_right inRange]
      obtain ⟨st, stepped, ran⟩ := bind_eq_ok ran
      rw [bind_ok_eq (materializeSteps_mono le p table widthAt _ _ stepped)]
      try dsimp only at ran ⊢
      split at ran
      · cases ran
      · rename_i within
        rw [ite_eq_right (not_gt_mono le.materialize within)]
        obtain ⟨rs, built, ran⟩ := bind_eq_ok ran
        rw [bind_ok_eq built]
        try dsimp only at ran ⊢
        split at ran
        · cases ran
        · rename_i bounded
          rw [ite_eq_right (not_gt_mono le.materializeWork bounded)]
          exact ran

theorem rematerialize_mono {a b : Limits} (le : LimitsLe a b) (layout : ShareLayout) (ex : Expanded)
    (order : Array Nat) (phase1 : Nat) {out : Rematerialized}
    (ran : rematerialize layout a ex order phase1 = .ok out) :
    rematerialize layout b ex order phase1 = .ok out := by
  unfold rematerialize at ran ⊢
  rw [Ix.Sharing.Verify.Tiered.materializeTableOnePass_eq] at ran ⊢
  obtain ⟨⟨entries, roots, predicted, work⟩, materialized, ran⟩ := bind_eq_ok ran
  rw [bind_ok_eq (materializeTable_mono le _ _ _ _ materialized)]
  dsimp only at ran ⊢
  obtain ⟨_, priced, ran⟩ := bind_eq_ok ran
  rw [bind_ok_eq priced]
  obtain ⟨_, shorter, ran⟩ := bind_eq_ok ran
  rw [bind_ok_eq shorter]
  obtain ⟨⟨entryIds, rootIds, visits⟩, expanded, ran⟩ := bind_eq_ok ran
  rw [bind_ok_eq (reexpand_mono le expanded)]
  exact ran

/-! ## The family entry -/

theorem familyAtWidth_mono {a b : Limits} (le : LimitsLe a b) (cfg : Config) (layout : ShareLayout)
    (ex : Expanded) (facts : GraphFacts) (candidates width : Nat)
    (hcp : childrenPrecede ex.dag.nodes = true) {out : TieredSharingResult}
    (ran : familyAtWidth cfg layout a ex (Prep.ofDag ex.dag) facts (parentsOf ex.dag) candidates width =
      .ok out) :
    familyAtWidth cfg layout b ex (Prep.ofDag ex.dag) facts (parentsOf ex.dag) candidates width =
      .ok out := by
  unfold familyAtWidth at ran ⊢
  obtain ⟨uniform, first, ran⟩ := bind_eq_ok ran
  rw [bind_ok_eq (familyUniform_mono le cfg ex facts width hcp first)]
  obtain ⟨allocation, second, ran⟩ := bind_eq_ok ran
  rw [bind_ok_eq (allocate_mono le _ _ _ _ _ _ second)]
  dsimp only at ran ⊢
  rw [← rematerialize_eq_P] at ran ⊢
  obtain ⟨materialized, third, ran⟩ := bind_eq_ok ran
  rw [bind_ok_eq (rematerialize_mono le _ _ _ _ third)]
  exact ran

theorem familyExpanded_mono {a b : Limits} (le : LimitsLe a b) (cfg : Config) (layout : ShareLayout)
    (ex : Expanded) {out : TieredSharingResult} (ran : familyExpanded cfg layout a ex = .ok out) :
    familyExpanded cfg layout b ex = .ok out := by
  unfold familyExpanded at ran ⊢
  obtain ⟨u, checks, ran⟩ := bind_eq_ok ran
  cases u
  rw [bind_ok_eq checks]
  have hcp : childrenPrecede ex.dag.nodes = true := by
    cases h : childrenPrecede ex.dag.nodes
    · unfold uniformDagChecks at checks
      simp [h] at checks <;> cases checks
    · rfl
  dsimp only at ran ⊢
  obtain ⟨picked, selected, ran⟩ := bind_eq_ok ran
  rw [tieredCandidates_eq] at selected ⊢
  obtain ⟨c1, first, selected⟩ := bind_eq_ok selected
  obtain ⟨c2, second, selected⟩ := bind_eq_ok selected
  obtain ⟨c3, third, selected⟩ := bind_eq_ok selected
  rw [bind_ok_eq (familyAtWidth_mono le cfg layout ex _ _ 1 hcp first),
    bind_ok_eq (familyAtWidth_mono le cfg layout ex _ _ 2 hcp second),
    bind_ok_eq (familyAtWidth_mono le cfg layout ex _ _ 3 hcp third)]
  rw [bind_ok_eq selected]
  exact ran

theorem canonicalSharingTiered_mono {a b : Limits} (le : LimitsLe a b) (layout : ShareLayout)
    (roots : Array Ixon.Expr) {out : TieredSharingResult}
    (ran : canonicalSharingTiered layout roots a = .ok out) :
    canonicalSharingTiered layout roots b = .ok out := by
  unfold canonicalSharingTiered at ran ⊢
  rw [familyReferenceExpanded_eq_cached] at ran ⊢
  obtain ⟨expanded, before, after⟩ := bind_eq_ok ran
  rw [bind_ok_eq (expand_mono le before)]
  exact familyExpanded_mono le _ _ _ after

theorem canonicalSharingTieredTable_mono {a b : Limits} (le : LimitsLe a b) (layout : ShareLayout)
    (sharing roots : Array Ixon.Expr) {out : TieredSharingResult}
    (ran : canonicalSharingTieredTable layout sharing roots a = .ok out) :
    canonicalSharingTieredTable layout sharing roots b = .ok out := by
  unfold canonicalSharingTieredTable at ran ⊢
  rw [familyReferenceExpanded_eq_cached] at ran ⊢
  obtain ⟨expanded, before, after⟩ := bind_eq_ok ran
  rw [bind_ok_eq (expand_mono le before)]
  exact familyExpanded_mono le _ _ _ after

theorem normalizeConstantSharingTiered_mono {a b : Limits} (le : LimitsLe a b) (layout : ShareLayout)
    (input : Ixon.Constant) {out : Ixon.Constant}
    (ran : normalizeConstantSharingTiered layout input a = .ok out) :
    normalizeConstantSharingTiered layout input b = .ok out := by
  unfold normalizeConstantSharingTiered at ran ⊢
  obtain ⟨result, normalized, ran⟩ := bind_eq_ok ran
  rw [bind_ok_eq (canonicalSharingTieredTable_mono le _ _ _ normalized)]
  exact ran

/-- Limits decide only whether the production entry refuses: two successful
runs under any two limits return the same result. -/
theorem canonicalSharingTiered_budget_independent {a b : Limits} (layout : ShareLayout)
    (roots : Array Ixon.Expr) {first second : TieredSharingResult}
    (ranA : canonicalSharingTiered layout roots a = .ok first)
    (ranB : canonicalSharingTiered layout roots b = .ok second) : first = second := by
  have left := canonicalSharingTiered_mono (LimitsLe.join_left a b) layout roots ranA
  have right := canonicalSharingTiered_mono (LimitsLe.join_right a b) layout roots ranB
  rw [left] at right
  exact Except.ok.inj right

/-- The same for re-sharing a complete constant with an existing table. -/
theorem normalizeConstantSharingTiered_budget_independent {a b : Limits} (layout : ShareLayout)
    (input : Ixon.Constant) {first second : Ixon.Constant}
    (ranA : normalizeConstantSharingTiered layout input a = .ok first)
    (ranB : normalizeConstantSharingTiered layout input b = .ok second) : first = second := by
  have left := normalizeConstantSharingTiered_mono (LimitsLe.join_left a b) layout input ranA
  have right :=
    normalizeConstantSharingTiered_mono (LimitsLe.join_right a b) layout input ranB
  rw [left] at right
  exact Except.ok.inj right

end Ix.Sharing.Verify.Budget

#guard_kernel_axioms Ix.Sharing.Verify.Budget.canonicalSharingTiered_mono [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Verify.Budget.canonicalSharingTiered_budget_independent [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Verify.Budget.normalizeConstantSharingTiered_budget_independent [propext, Classical.choice, Quot.sound]
