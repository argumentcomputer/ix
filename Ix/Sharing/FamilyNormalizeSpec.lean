module

public import Ix.Sharing.FamilyNormalize
import all Ix.Sharing.Exact.TieredFast

@[expose] public section

/-! Reference specification for the metered family pipeline. The mathematical
component loop uses the original context/evaluator; the compiled twin reuses
cleared positions and the proved closure-local evaluator. Equality includes
errors and resource-charge timing. Neither side changes a family on refusal. -/

namespace Ix.Sharing.Family

open Ix.Sharing.Exact

abbrev MeterState := Array CompResult × Nat × Nat

def familyReferenceStep (cfg : Config) (limits : Limits) (ex : Expanded) (sg : UStage)
    (width : Nat) (acc : MeterState) (members : Array Nat) : Except SharingError MeterState := do
  let (results, states, work) := acc
  let states ← bump states (familyCalls cfg members.size) limits.maxStates .states
  let cx := componentContext ex sg members
  let work ← bump work (familyWork cfg members.size cx.closure.size) limits.maxCostEvals .costEvals
  let result ← retainedResult sg.slack (component cfg ex sg width results.size members)
  return (results.push result, states, work)

def familyReferenceComponents (cfg : Config) (limits : Limits) (ex : Expanded) (sg : UStage)
    (width : Nat) : Except SharingError MeterState :=
  sg.comps.foldlM (familyReferenceStep cfg limits ex sg width) (#[], 0, 0)

private theorem exceptMap_bind (action : Except ε α) (next : α → Except ε β) (f : β → γ) :
    (action >>= next).map f = action >>= fun value => (next value).map f := by cases action <;> rfl

private theorem exceptBind_map (action : Except ε α) (f : α → β) (next : β → Except ε γ) :
    (action.map f >>= next) = action >>= fun value => next (f value) := by cases action <;> rfl

/-- Complete one-step equality, including every refusal, from cleared buffers. -/
theorem familyStep_eq_reference (cfg : Config) (limits : Limits) (ex : Expanded) (sg : UStage)
    (width : Nat) (hcp : childrenPrecede ex.dag.nodes = true) (acc : MeterState) (members : Array Nat) :
    familyStep cfg limits ex sg width (parentsOf ex.dag)
        (acc, Array.replicate sg.up.prep.dag.size 0, Array.replicate ex.dag.size 0) members =
      (familyReferenceStep cfg limits ex sg width acc members).map
        (fun next => (next, Array.replicate sg.up.prep.dag.size 0, Array.replicate ex.dag.size 0)) := by
  obtain ⟨results, states, work⟩ := acc
  have context := LocalSearch.mkSCtxL_eq ex sg.f sg.up sg.cand sg.b0 sg.vis0 sg.rootCount
    sg.slack sg.theta sg.baseEv sg.widthCs sg.allTrue sg.unc members hcp
  have evaluated := cachedComponent_eq cfg ex sg width hcp members results.size
  unfold cachedComponent at evaluated
  rw [context] at evaluated
  dsimp only at evaluated
  unfold familyStep familyReferenceStep
  dsimp only
  rw [context]
  dsimp only
  rw [evaluated]
  simp only [exceptMap_bind]
  rfl

theorem familyFold_eq_reference (cfg : Config) (limits : Limits) (ex : Expanded) (sg : UStage)
    (width : Nat) (hcp : childrenPrecede ex.dag.nodes = true) (members : List (Array Nat)) (acc : MeterState) :
    members.foldlM (familyStep cfg limits ex sg width (parentsOf ex.dag))
        (acc, Array.replicate sg.up.prep.dag.size 0, Array.replicate ex.dag.size 0) =
      (members.foldlM (familyReferenceStep cfg limits ex sg width) acc).map
        (fun next => (next, Array.replicate sg.up.prep.dag.size 0, Array.replicate ex.dag.size 0)) := by
  induction members generalizing acc with
  | nil => rfl
  | cons member rest ih =>
    rw [List.foldlM_cons, List.foldlM_cons, familyStep_eq_reference cfg limits ex sg width hcp]
    simp only [exceptBind_map, exceptMap_bind, ih]

theorem familyComponents_eq_reference (cfg : Config) (limits : Limits) (ex : Expanded) (sg : UStage)
    (width : Nat) (hcp : childrenPrecede ex.dag.nodes = true) :
    familyComponents cfg limits ex sg width (parentsOf ex.dag) = familyReferenceComponents cfg limits ex sg width := by
  unfold familyComponents familyReferenceComponents
  rw [← Array.foldlM_toList, ← Array.foldlM_toList, familyFold_eq_reference cfg limits ex sg width hcp]
  cases sg.comps.toList.foldlM (familyReferenceStep cfg limits ex sg width) (#[], 0, 0) <;> rfl

def familyReferenceUniform (cfg : Config) (limits : Limits) (ex : Expanded) (p : Prep)
    (facts : GraphFacts) (width : Nat) : Except SharingError UniformSharingResult := do
  let sg := uniformStageF width ex p facts
  unless componentsChecked ex.dag sg.cls sg.opaq sg.comps (componentLabels ex.dag.size sg.comps) do
    throw (.internal "uncertain components are not a separated partition")
  let (results, states, costEvals) ← familyReferenceComponents cfg limits ex sg width
  let (delta, chosen, lowerBracket) ← uniformKnapsack limits sg.cs.size results
  let modelInt : _root_.Int := (csBase ex p sg : Nat) + delta + (tag0Size (sg.cs.size + chosen.size) : _root_.Int)
  if modelInt < 0 then throw (.internal "negative model length")
  let model := modelInt.toNat
  if model > limits.maxOutputBytes then throw (.resourceExhausted .outputBytes limits.maxOutputBytes)
  let choice : UniformChoice :=
    { facts, certainStored := sg.cs, certainExcluded := sg.ce, uncertain := sg.unc,
      lowDegree := sg.low, components := sg.comps, stored := mergeSorted sg.cs chosen,
      model, states, costEvals, lowerBracket }
  uniformFinishF width limits ex p facts.deg choice

theorem familyUniform_eq_reference (cfg : Config) (limits : Limits) (ex : Expanded) (p : Prep)
    (facts : GraphFacts) (width : Nat) (hcp : childrenPrecede ex.dag.nodes = true) :
    familyUniform cfg limits ex p facts (parentsOf ex.dag) width =
      familyReferenceUniform cfg limits ex p facts width := by
  unfold familyUniform familyReferenceUniform
  dsimp only
  rw [familyComponents_eq_reference cfg limits ex _ width hcp]

def familyReferenceAtWidth (cfg : Config) (layout : ShareLayout) (limits : Limits) (ex : Expanded)
    (p : Prep) (facts : GraphFacts) (candidates width : Nat) : Except SharingError TieredSharingResult := do
  let uniform ← familyReferenceUniform cfg limits ex p facts width
  let allocation ← allocate layout limits ex.dag facts.deg uniform.result.tableTerms
    uniform.result.sharing uniform.result.roots
  let phase1 := layoutBytes layout uniform.result.sharing uniform.result.roots
  let materialized ← rematerializeP p layout limits ex allocation.order phase1
  return tieredResultF layout width uniform allocation materialized candidates phase1

theorem familyAtWidth_eq_reference (cfg : Config) (layout : ShareLayout) (limits : Limits) (ex : Expanded)
    (p : Prep) (facts : GraphFacts) (candidates width : Nat) (hcp : childrenPrecede ex.dag.nodes = true) :
    familyAtWidth cfg layout limits ex p facts (parentsOf ex.dag) candidates width =
      familyReferenceAtWidth cfg layout limits ex p facts candidates width := by
  unfold familyAtWidth familyReferenceAtWidth
  rw [familyUniform_eq_reference cfg limits ex p facts width hcp]

def familyReferenceExpanded (cfg : Config) (layout : ShareLayout) (limits : Limits) (ex : Expanded) :
    Except SharingError TieredSharingResult := do
  uniformDagChecks ex
  let prep := Prep.ofDag ex.dag
  let facts := graphFacts ex.dag ex.roots
  let candidates := tieredCandidateCount ex.dag.size prep facts
  let result ← tieredCandidates ex.dag.size (familyReferenceAtWidth cfg layout limits ex prep facts candidates)
  return withExpansionStats ex result

/-- The entry's executed DAG check supplies the cached walk's premise.
Every invalid input and every budget/error path has the same result. -/
@[csimp] theorem familyReferenceExpanded_eq_cached : @familyReferenceExpanded = @familyExpanded := by
  funext cfg layout limits ex
  unfold familyReferenceExpanded familyExpanded
  cases checks : uniformDagChecks ex with
  | error error => rfl
  | ok u =>
    cases u
    by_cases hcp : childrenPrecede ex.dag.nodes = true
    · have widths (prep : Prep) (facts : GraphFacts) (candidates : Nat) :
          familyAtWidth cfg layout limits ex prep facts (parentsOf ex.dag) candidates =
            familyReferenceAtWidth cfg layout limits ex prep facts candidates := by
        funext width
        exact familyAtWidth_eq_reference cfg layout limits ex prep facts candidates width hcp
      simp only [widths]
    · simp only [uniformDagChecks, hcp] at checks
      cases checks

end Ix.Sharing.Family
