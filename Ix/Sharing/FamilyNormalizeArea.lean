module

public import Ix.Sharing.FamilyNormalizeSpec
public import Ix.Sharing.Exact.AreaSearchEq
public import Ix.Sharing.Exact.AreaRowsRel
import all Ix.Sharing.FamilyCached
import all Ix.Sharing.Exact.TieredFast
import all Ix.Sharing.Exact.AreaSearchEq
import all Ix.Sharing.Exact.AreaCostEq
import all Ix.Sharing.Exact.AreaTruncRows

@[expose] public section

/-! Area-local evaluation of the unchanged component family. Closure preparation
and precharging retain their original order. One truncated base table is shared
by every component of a width; failed representation/opacity checks retain the
closure evaluator. The equalities include full cost/work pairs and refusals. -/

namespace Ix.Sharing.Family

open Ix.Sharing.Exact

def familyOutsideSum (terms posA costs : Array Nat) : Nat :=
  terms.foldl (fun acc t => if posA[t]! == 0 then acc + costs[t]! else acc) 0

def familyAreaAux (ex : Expanded) (cx : SCtx) (posA : Array Nat) (tb : TBase) : AAux :=
  { csize := cx.closure.size
    K := familyOutsideSum cx.rootsC posA tb.cost + familyOutsideSum cx.storedInC posA tb.inl
    rootsA := ex.roots.filter (fun r => posA[r]! != 0)
    storedA := cx.area.filter (cx.up.opaq[·]!) }

/-- Checked stopped-area facts; this selects an evaluator, never a family. -/
def familyAreaOK (ex : Expanded) (cx : SCtx) (parents : Array (Array Nat))
    (posA posC : Array Nat) : Bool :=
  cx.members.all (fun m => decide (m < ex.dag.size) && !cx.up.opaq[m]!) &&
    areaOK ex.dag.size cx.up.opaq parents cx.members cx.area posA &&
    cx.area.all (fun y => posC[y]! != 0)

def familyTraceArea (cfg : Config) (ex : Expanded) (cx : SCtx) (tb : TBase)
    (parents : Array (Array Nat)) (width index : Nat) (members posA posC : Array Nat) : ComponentTrace :=
  if familyAreaOK ex cx parents posA posC then
    let aux := familyAreaAux ex cx posA tb
    let light := { cx with closure := #[], rootsC := #[], storedInC := #[] }
    traceWithPhi cfg cx width index members (phiA light posA tb aux (fun _ => (cx, posC)))
  else traceWithPositions cfg cx width index members posA posC

def familyAreaEvaluation (cfg : Config) (ex : Expanded) (cx : SCtx) (tb : TBase)
    (parents : Array (Array Nat)) (width index : Nat) (members posA posC : Array Nat) :
    ComponentTrace × Array Nat × Array Nat :=
  if localSearchOK cx then
    let posA := setPositions posA cx.area
    let trace := familyTraceArea cfg ex cx tb parents width index members posA posC
    (trace, clearPositions posA cx.area, clearPositions posC cx.closure)
  else
    (traceWithPhi cfg cx width index members cx.phiE, posA, clearPositions posC cx.closure)

def familyStepArea (cfg : Config) (limits : Limits) (ex : Expanded) (sg : UStage)
    (width : Nat) (parents : Array (Array Nat)) (tb : TBase) (acc : FamilyState)
    (members : Array Nat) : Except SharingError FamilyState := do
  let ((results, states, work), posA, posC) := acc
  let states ← bump states (familyCalls cfg members.size) limits.maxStates .states
  let (cx, posC) := mkSCtxL ex sg.f sg.up sg.cand sg.b0 sg.vis0 sg.rootCount
    sg.slack sg.theta sg.baseEv sg.widthCs sg.allTrue sg.unc parents posC members
  let work ← bump work (familyWork cfg members.size cx.closure.size) limits.maxCostEvals .costEvals
  let (trace, posA, posC) := familyAreaEvaluation cfg ex cx tb parents width results.size members posA posC
  let result ← retainedResult sg.slack trace
  return ((results.push result, states, work), posA, posC)

def familyComponentsArea (cfg : Config) (limits : Limits) (ex : Expanded) (sg : UStage)
    (width : Nat) (parents : Array (Array Nat)) : Except SharingError MeterState :=
  let tb := TBase.ofPrep sg.up.prep sg.up.w sg.up.opaq
  if tStageOK sg.up.prep sg.up.w sg.up.opaq tb then
    (sg.comps.foldlM (familyStepArea cfg limits ex sg width parents tb)
      ((#[], 0, 0), Array.replicate sg.up.prep.dag.size 0, Array.replicate ex.dag.size 0)).map (·.1)
  else familyComponents cfg limits ex sg width parents

def familyUniformArea (cfg : Config) (limits : Limits) (ex : Expanded) (p : Prep)
    (facts : GraphFacts) (parents : Array (Array Nat)) (width : Nat) :
    Except SharingError UniformSharingResult := do
  let sg := uniformStageF width ex p facts
  unless componentsChecked ex.dag sg.cls sg.opaq sg.comps (componentLabels ex.dag.size sg.comps) do
    throw (.internal "uncertain components are not a separated partition")
  let (results, states, costEvals) ← familyComponentsArea cfg limits ex sg width parents
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

def familyAtWidthArea (cfg : Config) (layout : ShareLayout) (limits : Limits) (ex : Expanded)
    (p : Prep) (facts : GraphFacts) (parents : Array (Array Nat)) (candidates width : Nat) :
    Except SharingError TieredSharingResult := do
  let uniform ← familyUniformArea cfg limits ex p facts parents width
  let allocation ← allocate layout limits ex.dag facts.deg uniform.result.tableTerms
    uniform.result.sharing uniform.result.roots
  let phase1 := layoutBytes layout uniform.result.sharing uniform.result.roots
  let materialized ← rematerializeP p layout limits ex allocation.order phase1
  return tieredResultF layout width uniform allocation materialized candidates phase1

def familyExpandedArea (cfg : Config) (layout : ShareLayout) (limits : Limits) (ex : Expanded) :
    Except SharingError TieredSharingResult := do
  uniformDagChecks ex
  let prep := Prep.ofDag ex.dag
  uniformSpineCheck ex prep
  let facts := graphFacts ex.dag ex.roots
  let parents := parentsOf ex.dag
  let candidates := tieredCandidateCount ex.dag.size prep facts
  let result ← tieredCandidates ex.dag.size
    (familyAtWidthArea cfg layout limits ex prep facts parents candidates)
  return withExpansionStats ex result

private theorem positioned_iff {xs pos : Array Nat}
    (hp : LocalSearch.PosFn xs.size (xs[·]!) (posOf pos)) (u : Nat) :
    AreaProof.InA xs u ↔ pos[u]! ≠ 0 := by
  constructor
  · rintro ⟨i, hi, hiu⟩
    have h := (hp u i).mpr ⟨hi, hiu⟩
    rw [LocalSearch.posOf_some] at h
    omega
  · intro h
    have hv : pos[u]! = (pos[u]! - 1) + 1 := by omega
    exact ⟨pos[u]! - 1, (hp u _).mp ((LocalSearch.posOf_some pos u _).mpr hv)⟩

/-- The stopped evaluator preserves the full natural cost and the original
closure-sized work field, including its per-evaluation opacity fallback. -/
theorem familyAreaPhi_eq (ex : Expanded) (sg : UStage) (members posA posC : Array Nat)
    (hst : AreaProof.StageOK ex sg.up sg.baseEv sg.widthCs sg.allTrue) (tb : TBase)
    (htb : tb = TBase.ofPrep sg.up.prep sg.up.w sg.up.opaq)
    (hstage : tStageOK sg.up.prep sg.up.w sg.up.opaq tb = true)
    (hr : LocalSearch.Ready (componentContext ex sg members) posA posC)
    (hok : familyAreaOK ex (componentContext ex sg members) (parentsOf ex.dag) posA posC = true)
    (avail : Nat → Bool) (stored : Array Nat) :
    let cx := componentContext ex sg members
    phiA { cx with closure := #[], rootsC := #[], storedInC := #[] } posA tb
      (familyAreaAux ex cx posA tb) (fun _ => (cx, posC)) avail stored = phiEL2 cx posA posC avail stored := by
  let cx := componentContext ex sg members
  change familyAreaOK ex cx (parentsOf ex.dag) posA posC = true at hok
  change LocalSearch.Ready cx posA posC at hr
  have hposA := positioned_iff hr.area
  have hposC := positioned_iff hr.closure
  obtain ⟨_, _, _, _, _, _, _, _, harea, _⟩ := LocalSearch.localSearchOK_spec hr.ok
  have hn : cx.up.prep.dag.size = ex.dag.size := by
    change sg.up.prep.dag.size = ex.dag.size
    rw [hst.prep]; rfl
  simp only [familyAreaOK, areaOK, Bool.and_eq_true] at hok
  obtain ⟨⟨hm, ⟨⟨⟨_, _⟩, hmA⟩, hclosed⟩⟩, hAC⟩ := hok
  have hmem : ∀ m, cx.members.contains m = true → AreaProof.InA cx.area m ∧ cx.up.opaq[m]! = false := by
    intro m hm'
    have h1 := Array.all_eq_true'.mp hm m (Array.contains_iff_mem.mp hm')
    have h2 := Array.all_eq_true'.mp hmA m (Array.contains_iff_mem.mp hm')
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h1
    exact ⟨(hposA m).mpr (by simpa using h2), h1.2⟩
  have hclose : ∀ y q, AreaProof.InA cx.area y → cx.up.opaq[y]! = false → q < ex.dag.size →
      y ∈ (ex.dag.node q).children → AreaProof.InA cx.area q := by
    intro y q hy ho hq hc
    have hy' := Array.mem_toList_iff.mp (AreaProof.inA_iff_mem.mp hy)
    have hp := Array.all_eq_true'.mp hclosed y hy'
    rw [ho, Bool.false_or] at hp
    have hyl : y < ex.dag.size := by
      obtain ⟨i, hi, rfl⟩ := hy
      rw [← hn]; exact harea i hi
    have hqp := (LocalSearch.mem_parentsOf ex.dag y q).mpr ⟨hyl, hq, hc⟩
    exact (hposA q).mpr (by simpa using Array.all_eq_true'.mp hp q hqp)
  have hAC' : ∀ y, AreaProof.InA cx.area y → y ∈ cx.closure.toList := by
    intro y hy
    have h := Array.all_eq_true'.mp hAC y (Array.mem_toList_iff.mp (AreaProof.inA_iff_mem.mp hy))
    exact AreaProof.inA_iff_mem.mp ((hposC y).mpr (by simpa using h))
  have hK : (familyAreaAux ex cx posA tb).K =
      ((ex.roots.toList.filter (fun r => (markTable ex.dag.size cx.closure)[r]! && posA[r]! == 0)).map
        (tb.cost[·]!)).sum +
      ((cx.closure.toList.filter (fun c => cx.up.opaq[c]! && posA[c]! == 0)).map (tb.inl[·]!)).sum := by
    simp only [familyAreaAux, familyOutsideSum, ← Array.foldl_toList, AreaProof.foldl_if_add,
      Nat.zero_add]
    simp only [cx, componentContext, mkSCtx, Array.toList_filter, List.filter_filter, Bool.and_comm]
  exact AreaProof.phiA_eq ex cx _ posA posC tb _ _ hst.dag hst.prep rfl rfl rfl
    hst.widths hst.all hst.base htb hstage hr hmem hclose hAC' rfl hK rfl rfl rfl rfl avail stored

theorem familyTraceArea_eq (cfg : Config) (ex : Expanded) (sg : UStage) (width index : Nat)
    (members posA posC : Array Nat) (hst : AreaProof.StageOK ex sg.up sg.baseEv sg.widthCs sg.allTrue)
    (tb : TBase) (htb : tb = TBase.ofPrep sg.up.prep sg.up.w sg.up.opaq)
    (hstage : tStageOK sg.up.prep sg.up.w sg.up.opaq tb = true)
    (hr : LocalSearch.Ready (componentContext ex sg members) posA posC) :
    familyTraceArea cfg ex (componentContext ex sg members) tb (parentsOf ex.dag) width index members posA posC =
      traceWithPositions cfg (componentContext ex sg members) width index members posA posC := by
  unfold familyTraceArea
  split
  · rename_i hok
    dsimp only
    have heval := funext fun avail => funext fun stored =>
      familyAreaPhi_eq ex sg members posA posC hst tb htb hstage hr hok avail stored
    rw [heval]
    unfold traceWithPositions
    have hm := hok
    simp only [familyAreaOK, areaOK, Bool.and_eq_true] at hm
    have hall := hm.1.2.1.2
    have hsome : (componentContext ex sg members).members.all (fun m => (posOf posA m).isSome) = true := by
      apply Array.all_eq_true'.mpr
      intro m hmem
      have h := Array.all_eq_true'.mp hall m hmem
      unfold posOf
      simp [show posA[m]! ≠ 0 by simpa using h]
    rw [ite_eq_left hsome]
  · rfl

theorem familyAreaEvaluation_eq (cfg : Config) (ex : Expanded) (sg : UStage) (width index : Nat)
    (members : Array Nat) (hst : AreaProof.StageOK ex sg.up sg.baseEv sg.widthCs sg.allTrue)
    (tb : TBase) (htb : tb = TBase.ofPrep sg.up.prep sg.up.w sg.up.opaq)
    (hstage : tStageOK sg.up.prep sg.up.w sg.up.opaq tb = true) :
    let cx := componentContext ex sg members
    let posA := Array.replicate sg.up.prep.dag.size 0
    let posC := setPositions (Array.replicate ex.dag.size 0) cx.closure
    familyAreaEvaluation cfg ex cx tb (parentsOf ex.dag) width index members posA posC =
      cachedEvaluation cfg cx width index members posA posC := by
  dsimp only
  unfold familyAreaEvaluation cachedEvaluation
  split
  · rename_i hok
    dsimp only
    let cx := componentContext ex sg members
    have hn : sg.up.prep.dag.size = ex.dag.size := by rw [hst.prep]; rfl
    obtain ⟨_, _, _, _, _, _, _, _, ha, hc⟩ := LocalSearch.localSearchOK_spec hok
    obtain ⟨hsa, hsc⟩ := LocalSearch.localSearchOK_inc hok
    have hr : LocalSearch.Ready cx
        (setPositions (Array.replicate sg.up.prep.dag.size 0) cx.area)
        (setPositions (Array.replicate ex.dag.size 0) cx.closure) :=
      ⟨hok, LocalSearch.setPositions_posFn _ _ hsa ha,
        LocalSearch.setPositions_posFn _ _ hsc (fun i hi => by rw [← hn]; exact hc i hi)⟩
    rw [familyTraceArea_eq cfg ex sg width index members _ _ hst tb htb hstage hr]
  · rfl

theorem familyStepArea_eq_reference (cfg : Config) (limits : Limits) (ex : Expanded) (sg : UStage)
    (width : Nat) (hst : AreaProof.StageOK ex sg.up sg.baseEv sg.widthCs sg.allTrue)
    (tb : TBase) (htb : tb = TBase.ofPrep sg.up.prep sg.up.w sg.up.opaq)
    (hstage : tStageOK sg.up.prep sg.up.w sg.up.opaq tb = true) (acc : MeterState) (members : Array Nat) :
    familyStepArea cfg limits ex sg width (parentsOf ex.dag) tb
        (acc, Array.replicate sg.up.prep.dag.size 0, Array.replicate ex.dag.size 0) members =
      (familyReferenceStep cfg limits ex sg width acc members).map
        (fun next => (next, Array.replicate sg.up.prep.dag.size 0, Array.replicate ex.dag.size 0)) := by
  rw [← familyStep_eq_reference cfg limits ex sg width hst.dag.cp]
  obtain ⟨results, states, work⟩ := acc
  unfold familyStepArea familyStep
  dsimp only
  rw [LocalSearch.mkSCtxL_eq ex sg.f sg.up sg.cand sg.b0 sg.vis0 sg.rootCount sg.slack
    sg.theta sg.baseEv sg.widthCs sg.allTrue sg.unc members hst.dag.cp]
  dsimp only
  have evaluated := familyAreaEvaluation_eq cfg ex sg width results.size members hst tb htb hstage
  dsimp only [componentContext, mkSCtx] at evaluated ⊢
  rw [evaluated]

theorem familyFoldArea_eq_reference (cfg : Config) (limits : Limits) (ex : Expanded) (sg : UStage)
    (width : Nat) (hst : AreaProof.StageOK ex sg.up sg.baseEv sg.widthCs sg.allTrue)
    (tb : TBase) (htb : tb = TBase.ofPrep sg.up.prep sg.up.w sg.up.opaq)
    (hstage : tStageOK sg.up.prep sg.up.w sg.up.opaq tb = true) (members : List (Array Nat)) (acc : MeterState) :
    members.foldlM (familyStepArea cfg limits ex sg width (parentsOf ex.dag) tb)
        (acc, Array.replicate sg.up.prep.dag.size 0, Array.replicate ex.dag.size 0) =
      (members.foldlM (familyReferenceStep cfg limits ex sg width) acc).map
        (fun next => (next, Array.replicate sg.up.prep.dag.size 0, Array.replicate ex.dag.size 0)) := by
  exact LocalSearch.foldlM_sim _ _ _
    (familyStepArea_eq_reference cfg limits ex sg width hst tb htb hstage) members acc

theorem familyComponentsArea_eq (cfg : Config) (limits : Limits) (ex : Expanded) (sg : UStage)
    (width : Nat) (hst : AreaProof.StageOK ex sg.up sg.baseEv sg.widthCs sg.allTrue) :
    familyComponentsArea cfg limits ex sg width (parentsOf ex.dag) =
      familyComponents cfg limits ex sg width (parentsOf ex.dag) := by
  unfold familyComponentsArea
  dsimp only
  split
  · rename_i hstage
    rw [familyComponents_eq_reference cfg limits ex sg width hst.dag.cp]
    unfold familyReferenceComponents
    rw [← Array.foldlM_toList, ← Array.foldlM_toList,
      familyFoldArea_eq_reference cfg limits ex sg width hst _ rfl hstage]
    cases sg.comps.toList.foldlM (familyReferenceStep cfg limits ex sg width) (#[], 0, 0) <;> rfl
  · rfl

theorem familyUniformArea_eq (cfg : Config) (limits : Limits) (ex : Expanded) (facts : GraphFacts)
    (width : Nat) (hdag : AreaProof.DagOK ex.dag) :
    familyUniformArea cfg limits ex (Prep.ofDag ex.dag) facts (parentsOf ex.dag) width =
      familyUniform cfg limits ex (Prep.ofDag ex.dag) facts (parentsOf ex.dag) width := by
  unfold familyUniformArea familyUniform
  dsimp only
  rw [familyComponentsArea_eq cfg limits ex _ width (stageOK_F width ex facts hdag)]

theorem familyAtWidthArea_eq (cfg : Config) (layout : ShareLayout) (limits : Limits) (ex : Expanded)
    (facts : GraphFacts) (candidates width : Nat) (hdag : AreaProof.DagOK ex.dag) :
    familyAtWidthArea cfg layout limits ex (Prep.ofDag ex.dag) facts (parentsOf ex.dag) candidates width =
      familyAtWidth cfg layout limits ex (Prep.ofDag ex.dag) facts (parentsOf ex.dag) candidates width := by
  unfold familyAtWidthArea familyAtWidth
  rw [familyUniformArea_eq cfg limits ex facts width hdag]

/-- The executed entry check supplies all DAG/stage facts. This replacement
preserves every error, complete result, charge and serialized output. -/
@[csimp] theorem familyExpanded_eq_area : @familyExpanded = @familyExpandedArea := by
  funext cfg layout limits ex
  unfold familyExpanded familyExpandedArea
  cases checks : uniformDagChecks ex with
  | error error => rfl
  | ok u =>
    cases u
    have widths := fun facts candidates => funext fun width =>
      familyAtWidthArea_eq cfg layout limits ex facts candidates width (dagOK_of_checks checks)
    simp only [widths]

/-- Recompile the parameterized API as well, so the captured-input benchmark
uses the same evaluator as the canonical production wrapper. -/
def normalizeFamilyArea (cfg : Config) (layout : ShareLayout) (constant : Ixon.Constant)
    (limits : Limits := {}) : Except SharingError (Ixon.Constant × TieredSharingResult) := do
  let expanded ← expand limits constant.sharing (constantInfoRoots constant.info) true
  let result ← familyExpandedArea cfg layout limits expanded
  let info ← withRoots constant.info result.result.roots
  return ({ constant with info, sharing := result.result.sharing }, result)

@[csimp] theorem normalizeFamily_eq_area : @normalizeFamily = @normalizeFamilyArea := by
  funext cfg layout constant limits
  unfold normalizeFamily normalizeFamilyArea
  rw [familyExpanded_eq_area]

end Ix.Sharing.Family

end
