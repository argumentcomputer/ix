module

public import Ix.Sharing.FamilyPrototypeCached
public import Ix.Sharing.Exact.TieredFast
import all Ix.Sharing.Exact.UniformSearch

@[expose] public section

/-! Experimental whole-constant family normalization, with no production
routing or format change. Existing allocation/materialization/serialization
checks remain. Family-relative leastness and the semantic finish bridge are
separate proof obligations; successful replay is not a totality proof.

The family meter counts mathematical cost calls (excluding the empty baseline)
and the exact sum of `phiE`'s existing work field (including that baseline).
It does NOT claim complete native, allocation, telescope-scan or bit costs.
No resource refusal changes the chosen family. -/

namespace Ix.Sharing.FamilyPrototype

open Ix.Sharing.Exact

/-- Calls made by the existing table recipe: exact subsets, or greedy
extensions followed by one evaluation of each emitted chain row. -/
def familyCalls (cfg : Config) (m : Nat) : Nat :=
  if m ≤ cfg.experimentK then 2 ^ m else m * (m + 1) / 2 + m + 1

/-- Sum of stored-set lengths over those calls. Exact subsets contribute
`m * 2^(m-1)`; greedy extensions at size q occur `m-q+1` times, then the
chain emits sizes 0..m. Nat subtraction at m=0 is harmless (factor m=0). -/
def familyStoredSum (cfg : Config) (m : Nat) : Nat :=
  if m ≤ cfg.experimentK then m * 2 ^ (m - 1)
  else m * (m + 1) * (m + 2) / 6 + m * (m + 1) / 2

def familyWork (cfg : Config) (m closure : Nat) : Nat :=
  (familyCalls cfg m + 1) * closure + familyStoredSum cfg m

/-- The work formula being charged, not a statement about native execution. -/
theorem phiE_work (cx : SCtx) (avail : Nat → Bool) (stored : Array Nat) :
    (cx.phiE avail stored).2 = cx.closure.size + stored.size := by rfl

/-- Retain the same strict slack band and an actual indexed best row.
The explicit coherence check is useful to the separate entry-origin proof. -/
def retainedResult (slack : Nat) (trace : ComponentTrace) : Except SharingError CompResult := do
  let bySize := trace.rows.trim slack
  let some bestDelta := bySize.best | throw (.internal "experimental family has no row")
  let some bestSet := bestSetOf bySize bestDelta
    | throw (.internal "experimental family has no best set")
  unless bySize[bestSet.size]! == some (bestDelta, bestSet) do
    throw (.internal "experimental best row is not at its actual count")
  return { members := trace.members, bySize, bestDelta, bestSet }

abbrev FamilyState := (Array CompResult × Nat × Nat) × Array Nat × Array Nat

/-- Precharge before evaluating the component family. State refusal occurs
before context preparation; work refusal after its closure is known, but
before the baseline or any subset cost. Buffers are reused as in checkpoint A. -/
def familyStep (cfg : Config) (limits : Limits) (ex : Expanded) (sg : UStage)
    (width : Nat) (parents : Array (Array Nat)) (acc : FamilyState) (members : Array Nat) :
    Except SharingError FamilyState := do
  let ((results, states, work), posA, posC) := acc
  let states ← bump states (familyCalls cfg members.size) limits.maxStates .states
  let (cx, posC) := mkSCtxL ex sg.f sg.up sg.cand sg.b0 sg.vis0 sg.rootCount
    sg.slack sg.theta sg.baseEv sg.widthCs sg.allTrue sg.unc parents posC members
  let work ← bump work (familyWork cfg members.size cx.closure.size) limits.maxCostEvals .costEvals
  let (trace, posA, posC) := cachedEvaluation cfg cx width results.size members posA posC
  let result ← retainedResult sg.slack trace
  return ((results.push result, states, work), posA, posC)

def familyComponents (cfg : Config) (limits : Limits) (ex : Expanded) (sg : UStage)
    (width : Nat) (parents : Array (Array Nat)) :
    Except SharingError (Array CompResult × Nat × Nat) :=
  (sg.comps.foldlM (familyStep cfg limits ex sg width parents)
    ((#[], 0, 0), Array.replicate sg.up.prep.dag.size 0, Array.replicate ex.dag.size 0)).map (·.1)

/-- Family rows feed the existing bracket/slack knapsack; this entry never
invokes the exact component search or uses a budget to choose greedy mode. -/
def familyUniform (cfg : Config) (limits : Limits) (ex : Expanded) (p : Prep)
    (facts : GraphFacts) (parents : Array (Array Nat)) (width : Nat) :
    Except SharingError UniformSharingResult := do
  let sg := uniformStageF width ex p facts
  unless componentsChecked ex.dag sg.cls sg.opaq sg.comps (componentLabels ex.dag.size sg.comps) do
    throw (.internal "uncertain components are not a separated partition")
  let (results, states, costEvals) ← familyComponents cfg limits ex sg width parents
  let (delta, chosen, lowerBracket) ← uniformKnapsack limits sg.cs.size results
  let modelInt : _root_.Int := (csBase ex p sg : Nat) + delta + tag0Size (sg.cs.size + chosen.size)
  if modelInt < 0 then throw (.internal "negative model length")
  let model := modelInt.toNat
  if model > limits.maxOutputBytes then throw (.resourceExhausted .outputBytes limits.maxOutputBytes)
  let choice : UniformChoice :=
    { facts, certainStored := sg.cs, certainExcluded := sg.ce, uncertain := sg.unc,
      lowDegree := sg.low, components := sg.comps, stored := mergeSorted sg.cs chosen,
      model, states, costEvals, lowerBracket }
  uniformFinishF width limits ex p facts.deg choice

/-- Existing phase 2 and phase 3, including permutation, dependency, reference
cost, length, expansion, wire-count and resource checks. -/
def familyAtWidth (cfg : Config) (layout : ShareLayout) (limits : Limits) (ex : Expanded)
    (p : Prep) (facts : GraphFacts) (parents : Array (Array Nat)) (candidates width : Nat) :
    Except SharingError TieredSharingResult := do
  let uniform ← familyUniform cfg limits ex p facts parents width
  let allocation ← allocate layout limits ex.dag facts.deg uniform.result.tableTerms
    uniform.result.sharing uniform.result.roots
  let phase1 := layoutBytes layout uniform.result.sharing uniform.result.roots
  let materialized ← rematerializeP p layout limits ex allocation.order phase1
  return tieredResultF layout width uniform allocation materialized candidates phase1

/-- Width-independent data is prepared once; each width owns its component
buffers. Selection and error ordering are the existing tieredCandidates rule. -/
def familyExpanded (cfg : Config) (layout : ShareLayout) (limits : Limits) (ex : Expanded) :
    Except SharingError TieredSharingResult := do
  uniformDagChecks ex
  let prep := Prep.ofDag ex.dag
  uniformSpineCheck ex prep
  let facts := graphFacts ex.dag ex.roots
  let parents := parentsOf ex.dag
  let candidates := tieredCandidateCount ex.dag.size prep facts
  let result ← tieredCandidates ex.dag.size
    (familyAtWidth cfg layout limits ex prep facts parents candidates)
  return withExpansionStats ex result

/-- Explicit offline API. Keep all non-root fields, refs and universes.
The old normalizeConstantSharingTiered and production callers are unchanged. -/
def normalizeFamily (cfg : Config) (layout : ShareLayout) (constant : Ixon.Constant)
    (limits : Limits := {}) : Except SharingError (Ixon.Constant × TieredSharingResult) := do
  let expanded ← expand limits constant.sharing (constantInfoRoots constant.info) true
  let result ← familyExpanded cfg layout limits expanded
  let info ← withRoots constant.info result.result.roots
  return ({ constant with info, sharing := result.result.sharing }, result)

end Ix.Sharing.FamilyPrototype
