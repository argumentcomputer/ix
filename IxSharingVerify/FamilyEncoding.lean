import IxSharingVerify.FamilyExpand

/-! The actual family pipeline depends on an Expanded input's DAG
and ordered root IDs for encoding and errors. Expansion statistics are
transported explicitly; cfg, layout and limits remain fixed. -/

namespace Ix.Sharing.Family

open Ix.Sharing.Exact
open Ix.Sharing.Verify.Tiered (encodingOf)

def recordUniformStats (visits nodes : Nat) (out : UniformSharingResult) : UniformSharingResult :=
  let stats := { out.result.stats with exprVisits := visits, internedNodes := nodes }
  { out with result := { out.result with stats } }

def recordTieredStats (visits nodes : Nat) (out : TieredSharingResult) : TieredSharingResult :=
  let stats := { out.result.stats with exprVisits := visits, internedNodes := nodes }
  let result := { out.result with stats }
  { out with result, phase1 := recordUniformStats visits nodes out.phase1 }

theorem except_map_bind (action : Except ε α) (next : α → Except ε β) (f : β → γ) :
    (action >>= next).map f = action >>= fun value => (next value).map f := by
  cases action <;> rfl

theorem except_bind_map (action : Except ε α) (f : α → β) (next : β → Except ε γ) :
    (action.map f >>= next) = action >>= fun value => next (f value) := by
  cases action <;> rfl

theorem except_map_ite (condition : Prop) [Decidable condition] (yes no : Except ε α) (f : α → β) :
    (if condition then yes else no).map f = if condition then yes.map f else no.map f := by
  by_cases h : condition <;> simp only [h, ↓reduceIte]

theorem familyComponents_stats (cfg : Config) (limits : Limits) (ex : Expanded) (sg : UStage)
    (width : Nat) (parents : Array (Array Nat)) (visits nodes : Nat) :
    familyComponents cfg limits { ex with visits, internedNodes := nodes } sg width parents =
      familyComponents cfg limits ex sg width parents := by
  rfl

theorem uniformFinishF_stats (width : Nat) (limits : Limits) (ex : Expanded) (prep : Prep)
    (deg : Array Nat) (choice : UniformChoice) (visits nodes : Nat) :
    uniformFinishF width limits { ex with visits, internedNodes := nodes } prep deg choice =
      (uniformFinishF width limits ex prep deg choice).map (recordUniformStats visits nodes) := by
  unfold uniformFinishF
  simp only [except_map_bind, except_map_ite]
  rfl

theorem familyUniform_stats (cfg : Config) (limits : Limits) (ex : Expanded) (prep : Prep)
    (facts : GraphFacts) (parents : Array (Array Nat)) (width visits nodes : Nat) :
    familyUniform cfg limits { ex with visits, internedNodes := nodes } prep facts parents width =
      (familyUniform cfg limits ex prep facts parents width).map (recordUniformStats visits nodes) := by
  unfold familyUniform
  simp only [familyComponents_stats, uniformFinishF_stats, except_map_bind, except_map_ite]
  rfl

theorem familyAtWidth_stats (cfg : Config) (layout : ShareLayout) (limits : Limits) (ex : Expanded)
    (prep : Prep) (facts : GraphFacts) (parents : Array (Array Nat)) (candidates width visits nodes : Nat) :
    familyAtWidth cfg layout limits { ex with visits, internedNodes := nodes } prep facts parents candidates width =
      (familyAtWidth cfg layout limits ex prep facts parents candidates width).map (recordTieredStats visits nodes) := by
  unfold familyAtWidth
  rw [familyUniform_stats]
  simp only [except_bind_map, except_map_bind]
  rfl

theorem tieredPick_stats (first second third : TieredSharingResult) (visits nodes : Nat) :
    tieredPick (recordTieredStats visits nodes first) (recordTieredStats visits nodes second)
        (recordTieredStats visits nodes third) = recordTieredStats visits nodes (tieredPick first second third) := by
  have fold (a b c : TieredSharingResult) :
      #[b, c].foldl (fun best next => if tieredBetter next best then next else best) a =
        if tieredBetter c (if tieredBetter b a then b else a) then c else if tieredBetter b a then b else a := by simp
  have better (a b : TieredSharingResult) :
      tieredBetter (recordTieredStats visits nodes a) (recordTieredStats visits nodes b) = tieredBetter a b := rfl
  simp only [tieredPick, fold, better]
  repeat' first
    | rfl
    | (split <;> try simp_all only)
  all_goals simp_all [recordTieredStats, recordUniformStats]

theorem tieredCandidates_stats (count : Nat) (run : Nat → Except SharingError TieredSharingResult)
    (visits nodes : Nat) :
    tieredCandidates count (fun width => (run width).map (recordTieredStats visits nodes)) =
      (tieredCandidates count run).map (recordTieredStats visits nodes) := by
  rw [tieredCandidates_eq, tieredCandidates_eq]
  simp only [except_bind_map, except_map_bind, tieredPick_stats]
  rfl

/-- The actual entry commutes with changing only the prior expansion
counters. This equation covers errors as well as successful results. -/
theorem familyExpanded_stats (cfg : Config) (layout : ShareLayout) (limits : Limits) (ex : Expanded)
    (visits nodes : Nat) :
    familyExpanded cfg layout limits { ex with visits, internedNodes := nodes } =
      (familyExpanded cfg layout limits ex).map (recordTieredStats visits nodes) := by
  have widths : familyAtWidth cfg layout limits { ex with visits, internedNodes := nodes }
      (Prep.ofDag ex.dag) (graphFacts ex.dag ex.roots) (parentsOf ex.dag)
      (tieredCandidateCount ex.dag.size (Prep.ofDag ex.dag) (graphFacts ex.dag ex.roots)) =
      fun width => (familyAtWidth cfg layout limits ex (Prep.ofDag ex.dag) (graphFacts ex.dag ex.roots)
        (parentsOf ex.dag) (tieredCandidateCount ex.dag.size (Prep.ofDag ex.dag) (graphFacts ex.dag ex.roots))
        width).map (recordTieredStats visits nodes) := by
    funext width
    exact familyAtWidth_stats _ _ _ _ _ _ _ _ _ _ _
  unfold familyExpanded
  dsimp only
  rw [widths, tieredCandidates_stats]
  simp only [except_map_bind, except_bind_map]
  rfl

/-- Equal DAG/root data suffices. The returned expansion counters are those
of the second input, so equality of complete result statistics is not assumed. -/
theorem familyExpanded_transport (cfg : Config) (layout : ShareLayout) (limits : Limits)
    {first second : Expanded} (dag : first.dag = second.dag) (roots : first.roots = second.roots) :
    familyExpanded cfg layout limits second =
      (familyExpanded cfg layout limits first).map (recordTieredStats second.visits second.internedNodes) := by
  have same : second = { first with visits := second.visits, internedNodes := second.internedNodes } := by
    cases first
    cases second
    cases dag
    cases roots
    rfl
  conv => lhs; rw [same]
  exact familyExpanded_stats cfg layout limits first second.visits second.internedNodes

/-- Encoding includes the sharing bodies, ordered roots and table-term IDs.
Configuration, layout and every resource limit are held fixed. -/
theorem familyExpanded_encoding_congr (cfg : Config) (layout : ShareLayout) (limits : Limits)
    {first second : Expanded} (dag : first.dag = second.dag) (roots : first.roots = second.roots) :
    (familyExpanded cfg layout limits first).map encodingOf =
      (familyExpanded cfg layout limits second).map encodingOf := by
  rw [familyExpanded_transport cfg layout limits dag roots]
  cases familyExpanded cfg layout limits first <;> rfl

/-- Success of the second input follows here from the proved transport
equation, specifically for the same DAG/roots and fixed limits. -/
theorem familyExpanded_transport_success {cfg : Config} {layout : ShareLayout} {limits : Limits}
    {first second : Expanded} (dag : first.dag = second.dag) (roots : first.roots = second.roots)
    {out : TieredSharingResult} (run : familyExpanded cfg layout limits first = .ok out) :
    familyExpanded cfg layout limits second = .ok (recordTieredStats second.visits second.internedNodes out) := by
  rw [familyExpanded_transport cfg layout limits dag roots, run]
  rfl

theorem familyExpanded_same_encoding {cfg : Config} {layout : ShareLayout} {limits : Limits}
    {first second : Expanded} (dag : first.dag = second.dag) (roots : first.roots = second.roots)
    {left right : TieredSharingResult}
    (leftRun : familyExpanded cfg layout limits first = .ok left)
    (rightRun : familyExpanded cfg layout limits second = .ok right) : encodingOf left = encodingOf right := by
  have same := familyExpanded_encoding_congr cfg layout limits dag roots
  rw [leftRun, rightRun] at same
  exact Except.ok.inj same

end Ix.Sharing.Family

#guard_kernel_axioms Ix.Sharing.Family.familyComponents_stats [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Family.uniformFinishF_stats [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Family.familyUniform_stats [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Family.familyAtWidth_stats [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Family.tieredPick_stats [propext, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Family.tieredCandidates_stats [propext, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Family.familyExpanded_stats [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Family.familyExpanded_transport [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Family.familyExpanded_encoding_congr [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Family.familyExpanded_transport_success [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Family.familyExpanded_same_encoding [propext, Classical.choice, Quot.sound]
