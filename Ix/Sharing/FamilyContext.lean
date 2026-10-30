module

public import Ix.Sharing.FamilyNormalizeArea
public import Ix.Sharing.FamilyParallel
import all Ix.Sharing.Family
import all Ix.Sharing.FamilyParallel
import all Ix.Sharing.FamilyCached
import all Ix.Sharing.FamilyNormalize
import all Ix.Sharing.FamilyNormalizeSpec
import all Ix.Sharing.FamilyNormalizeArea
import all Ix.Sharing.Exact.UniformSearch
import all Ix.Sharing.Exact.UniformSearchLocal
import all Ix.Sharing.Exact.AreaSearch
import all Ix.Sharing.Exact.AreaCostEq
import all Ix.Sharing.Exact.AreaBlockEq
import all Ix.Sharing.Exact.AreaSearchEq
import all Ix.Sharing.Exact.TieredFast

@[expose] public section

/-! The fixed component family needs an ancestor count and a constant cost,
but its usual area evaluator does not need the sorted ancestor closure or the
reclassification tables. Keep the closure walk unsorted, and construct the full
context at most once if an opacity check requests it. Preparation checks and
state/work refusals retain the original result and ordering. -/

namespace Ix.Sharing.Family.LightContext

open Ix.Sharing.Exact
open Ix.Sharing.Exact.AreaProof (lightCx)

/-- These tables support reclassification, which the fixed family does not run. -/
def eraseUnused (context : SCtx) : SCtx :=
  { context with memberIdx := {}, areaIdx := {}, inEdges := #[], rootOcc := #[] }

theorem localSearchOK_erase (context : SCtx) :
    localSearchOK (eraseUnused context) = localSearchOK context := by
  unfold localSearchOK eraseUnused
  rfl

theorem phiA_erase (context : SCtx) (positions : Array Nat) (base : TBase) (aux : AAux)
    (fallback : Unit → SCtx × Array Nat) (avail : Nat → Bool) (stored : Array Nat) :
    phiA (eraseUnused context) positions base aux fallback avail stored =
      phiA context positions base aux fallback avail stored := by
  unfold phiA memberFlags eraseUnused
  rfl

def context (stage : UStage) (members area : Array Nat) : SCtx :=
  { up := stage.up, facts := stage.f, cand := stage.cand, bounds0 := stage.b0,
    vis0 := stage.vis0, members, memberIdx := {}, area, areaIdx := {}, inEdges := #[],
    rootOcc := #[], slack := stage.slack, theta := stage.theta, baseEv := stage.baseEv,
    widthCs := stage.widthCs, allTrue := stage.allTrue, closure := #[], rootsC := #[],
    storedInC := #[], allUnc := stage.unc }

theorem context_eq (ex : Expanded) (stage : UStage) (members : Array Nat) :
    context stage members (componentArea stage.up stage.f members) =
      eraseUnused (lightCx (componentContext ex stage members)) := by
  unfold context eraseUnused lightCx componentContext mkSCtx
  rfl

/-- The full context is constructed only when the memoizing thunk is forced. -/
@[noinline] def fullContext (ex : Expanded) (stage : UStage) (members : Array Nat) : SCtx × Array Nat :=
  let full := componentContext ex stage members
  (full, setPositions (Array.replicate ex.dag.size 0) full.closure)

@[noinline] def forceContext (cached : Thunk (SCtx × Array Nat)) (_ : Unit) : SCtx × Array Nat :=
  cached.get

def trace (cfg : Config) (width index : Nat) (members : Array Nat) (areaSize closureSize : Nat)
    (eval : (Nat → Bool) → Array Nat → Nat × Nat) : ComponentTrace :=
  let baseline := (eval (fun _ => false) #[]).1
  let cost : Cost := fun selected => ((eval selected.contains selected).1 : _root_.Int) - baseline
  let size := members.size
  let exact := size ≤ cfg.exactLimit
  { width, index, exact, members, areaSize, closureSize, rows := table cfg cost members.toList,
    evaluations := if exact then 2 ^ size else size * (size + 1) / 2 + size + 1 }

def traceParallel (cfg : Config) (width index : Nat) (members : Array Nat) (areaSize closureSize : Nat)
    (eval : (Nat → Bool) → Array Nat → Nat × Nat) : ComponentTrace :=
  let baseline := (eval (fun _ => false) #[]).1
  let cost : Cost := fun selected => ((eval selected.contains selected).1 : _root_.Int) - baseline
  let size := members.size
  let exact := size ≤ cfg.exactLimit
  { width, index, exact, members, areaSize, closureSize,
    rows := Parallel.table cfg cost members.toList,
    evaluations := if exact then 2 ^ size else size * (size + 1) / 2 + size + 1 }

@[csimp] theorem trace_eq_parallel : @trace = @traceParallel := by
  funext cfg width index members areaSize closureSize eval
  simp only [trace, traceParallel, Parallel.table_eq]

def auxiliary (ex : Expanded) (stage : UStage) (base : TBase)
    (area positions found marks : Array Nat) : AAux :=
  { csize := found.size
    K := areaK base stage.up.opaq ex.roots found marks positions
    rootsA := ex.roots.filter (fun root => positions[root]! != 0)
    storedA := area.filter (stage.up.opaq[·]!) }

theorem positioned {terms positions : Array Nat}
    (table : LocalSearch.PosFn terms.size (terms[·]!) (posOf positions)) (term : Nat) :
    positions[term]! ≠ 0 ↔ term ∈ terms.toList := by
  constructor
  · intro nonzero
    have value : positions[term]! = (positions[term]! - 1) + 1 := by omega
    have item := (table term (positions[term]! - 1)).mp
      ((LocalSearch.posOf_some positions term _).mpr value)
    exact AreaProof.inA_iff_mem.mp ⟨_, item.1, item.2⟩
  · intro member
    obtain ⟨i, hi, eq⟩ := AreaProof.inA_iff_mem.mpr member
    have entry := (table term i).mpr ⟨hi, eq⟩
    have := (LocalSearch.posOf_some positions term i).mp entry
    omega

/-- The walk's unique marks can always be cleared without sorting its output. -/
theorem clear_walk (ex : Expanded) (members marks found stack : Array Nat)
    (walk : upWalk (parentsOf ex.dag) members (Array.replicate ex.dag.size 0) = (marks, found, stack)) :
    clearPositions marks found = Array.replicate ex.dag.size 0 := by
  obtain ⟨invariant, _⟩ := LocalSearch.upWalk_spec ex.dag members
  rw [walk] at invariant
  apply LocalSearch.clearPositions_zero _ _ _ invariant.size
  intro term absent
  rw [invariant.marks term]
  have notFound : term ∉ found.toList := by
    intro member
    rw [Array.mem_toList_iff, Array.mem_iff_getElem] at member
    obtain ⟨i, hi, rfl⟩ := member
    exact absent i hi (getElem!_pos found i hi)
  rw [ite_eq_right notFound]

/-- Checked area preparation preserves the exact closure size and every
candidate cost, including the opacity fallback, without preparing the closure. -/
theorem trace_walk_eq (cfg : Config) (ex : Expanded) (stage : UStage) (width index : Nat)
    (members : Array Nat)
    (stageOK : AreaProof.StageOK ex stage.up stage.baseEv stage.widthCs stage.allTrue)
    (base : TBase) (baseEq : base = TBase.ofPrep stage.up.prep stage.up.w stage.up.opaq)
    (baseOK : tStageOK stage.up.prep stage.up.w stage.up.opaq base = true)
    (marks found stack : Array Nat)
    (walk : upWalk (parentsOf ex.dag) members (Array.replicate ex.dag.size 0) = (marks, found, stack))
    (membersOK : members.all (fun m => decide (m < ex.dag.size) && !stage.up.opaq[m]!) = true)
    (areaOK : areaOK ex.dag.size stage.up.opaq (parentsOf ex.dag) members
      (componentArea stage.up stage.f members)
      (setPositions (Array.replicate stage.up.prep.dag.size 0) (componentArea stage.up stage.f members)) = true)
    (walkOK : (stack.isEmpty && (componentArea stage.up stage.f members).all (fun y => marks[y]! != 0)) = true)
    (localOK : localSearchOK (context stage members (componentArea stage.up stage.f members)) = true) :
    let full := componentContext ex stage members
    let area := componentArea stage.up stage.f members
    let positions := setPositions (Array.replicate stage.up.prep.dag.size 0) area
    found.size = full.closure.size ∧
      trace cfg width index members area.size found.size
          (phiA (context stage members area) positions base
            (auxiliary ex stage base area positions found marks)
            (forceContext (Thunk.mk fun _ => fullContext ex stage members))) =
        component cfg ex stage width index members := by
  let full := componentContext ex stage members
  let area := componentArea stage.up stage.f members
  let positions := setPositions (Array.replicate stage.up.prep.dag.size 0) area
  change found.size = full.closure.size ∧ _
  have sameSize : stage.up.prep.dag.size = ex.dag.size := by rw [stageOK.prep]; rfl
  have fullClosure : full.closure = upClosure ex.dag ((markTable ex.dag.size members)[·]!) := rfl
  have fullRoots : full.rootsC = ex.roots.filter ((markTable ex.dag.size full.closure)[·]!) := rfl
  have fullStored : full.storedInC = full.closure.filter (stage.up.opaq[·]!) := rfl
  obtain ⟨invariant, done⟩ := LocalSearch.upWalk_spec ex.dag members
  rw [walk] at invariant done
  rw [Bool.and_eq_true] at walkOK
  obtain ⟨emptyStack, markedArea⟩ := walkOK
  have emptyList : stack.toList = [] := by
    rw [Array.isEmpty_iff] at emptyStack
    rw [emptyStack]
  have foundMembers := done emptyList
  have closureMembers := LocalSearch.mem_upClosure stageOK.dag.cp ((markTable ex.dag.size members)[·]!)
  have sameMembers : ∀ term, term ∈ found.toList ↔ term ∈ full.closure.toList :=
    fun term => (foundMembers term).trans (by rw [fullClosure]; exact (closureMembers term).symm)
  have sortedClosure : full.closure.toList.Pairwise (· < ·) := by
    rw [fullClosure]; exact LocalSearch.upClosure_sorted _ _
  have permutation : found.toList.Perm full.closure.toList :=
    (List.perm_ext_iff_of_nodup invariant.nodup (sortedClosure.imp Nat.ne_of_lt)).mpr sameMembers
  have closureSize : found.size = full.closure.size := by simpa using permutation.length_eq
  refine ⟨closureSize, ?_⟩
  have closureInc := LocalSearch.strictInc_of_sorted sortedClosure
  have closureBound : ∀ term ∈ full.closure.toList, term < ex.dag.size := by
    rw [fullClosure]
    intro term member
    exact ((closureMembers term).mp member).lt
  have closureAt : ∀ i, i < full.closure.size → full.closure[i]! < ex.dag.size :=
    fun i hi => closureBound _ (LocalSearch.mem_of_getElem! hi)
  have closureTable := LocalSearch.setPositions_posFn full.closure ex.dag.size closureInc closureAt
  let closurePositions := setPositions (Array.replicate ex.dag.size 0) full.closure
  rw [context_eq ex stage members, localSearchOK_erase] at localOK
  change localSearchOK (lightCx full) = true at localOK
  have fullOK := AreaProof.localSearchOK_full full localOK closureInc
    (fun i hi => by change full.closure[i]! < stage.up.prep.dag.size; rw [sameSize]; exact closureAt i hi)
  obtain ⟨_, _, _, _, _, _, _, _, areaBound, _⟩ := LocalSearch.localSearchOK_spec fullOK
  have areaInc := (LocalSearch.localSearchOK_inc fullOK).1
  have areaTable := LocalSearch.setPositions_posFn full.area full.up.prep.dag.size areaInc areaBound
  have ready : LocalSearch.Ready full positions closurePositions := ⟨fullOK, areaTable, closureTable⟩
  have markEq : ∀ term : Nat, (marks[term]! != 0) = (markTable ex.dag.size full.closure)[term]! := by
    intro term
    rw [invariant.marks term, LocalSearch.markTable_read]
    by_cases member : term ∈ found.toList
    · rw [ite_eq_left member]
      have memberFull := (sameMembers term).mp member
      simp [closureBound term memberFull, Array.mem_toList_iff.mp memberFull]
    · rw [ite_eq_right member]
      have notFull : term ∉ full.closure :=
        fun h => member ((sameMembers term).mpr (Array.mem_toList_iff.mpr h))
      simp [notFull]
  have positionedArea : full.area.all (fun term => closurePositions[term]! != 0) = true := by
    apply Array.all_eq_true'.mpr
    intro term member
    have marked := Array.all_eq_true'.mp markedArea term member
    have memberFound : term ∈ found.toList := by
      by_cases foundCase : term ∈ found.toList
      · exact foundCase
      · rw [invariant.marks term, ite_eq_right foundCase] at marked
        simp at marked
    have present := (positioned closureTable term).mpr ((sameMembers term).mp memberFound)
    simpa using present
  have areaReady : familyAreaOK ex full (parentsOf ex.dag) positions closurePositions = true := by
    unfold familyAreaOK
    simp only [Bool.and_eq_true]
    exact ⟨⟨membersOK, areaOK⟩, positionedArea⟩
  have constantCost : areaK base stage.up.opaq ex.roots found marks positions =
      familyOutsideSum full.rootsC positions base.cost +
        familyOutsideSum full.storedInC positions base.inl := by
    rw [AreaProof.areaK_eq, AreaProof.sum_perm (permutation.filter _), fullRoots, fullStored]
    simp only [familyOutsideSum, ← Array.foldl_toList, AreaProof.foldl_if_add, Nat.zero_add,
      Array.toList_filter, List.filter_filter, markEq, Bool.and_comm]
    exact Nat.add_comm _ _
  have sameAux : auxiliary ex stage base area positions found marks = familyAreaAux ex full positions base := by
    unfold auxiliary familyAreaAux
    rw [closureSize, constantCost]
    rfl
  have membersIn : LocalSearch.MembersIn full positions := by
    intro member present
    have memberArray := Array.contains_iff_mem.mp present
    have position := Array.all_eq_true'.mp
      (show members.all (fun m => positions[m]! != 0) = true from by
        have := areaOK
        unfold Ix.Sharing.Exact.areaOK at this
        simp only [Bool.and_eq_true] at this
        exact this.1.2) member memberArray
    unfold posOf
    have nonzero : positions[member]! ≠ 0 := by simpa using position
    simp [nonzero]
  have sameEval : phiA (context stage members area) positions base
        (auxiliary ex stage base area positions found marks)
        (forceContext (Thunk.mk fun _ => fullContext ex stage members)) = full.phiE := by
    funext avail stored
    rw [context_eq ex stage members, phiA_erase, sameAux]
    change phiA (lightCx full) positions base (familyAreaAux ex full positions base)
      (forceContext (Thunk.mk fun _ => fullContext ex stage members)) avail stored = full.phiE avail stored
    have equal := familyAreaPhi_eq ex stage members positions closurePositions stageOK base baseEq baseOK
      ready areaReady avail stored
    change phiA (lightCx full) positions base (familyAreaAux ex full positions base)
      (fun _ => (full, closurePositions)) avail stored = _ at equal
    change phiA (lightCx full) positions base (familyAreaAux ex full positions base)
      (fun _ => (full, closurePositions)) avail stored = _
    rw [equal]
    exact (LocalSearch.phiE_eq_L2 ready membersIn avail stored).symm
  rw [sameEval, closureSize]
  rfl

def step (cfg : Config) (limits : Limits) (ex : Expanded) (stage : UStage)
    (width : Nat) (parents : Array (Array Nat)) (base : TBase) (acc : FamilyState)
    (members : Array Nat) : Except SharingError FamilyState := do
  let ((results, states, work), areaPositions, closurePositions) := acc
  let nextStates ← bump states (familyCalls cfg members.size) limits.maxStates .states
  if members.all (fun m => decide (m < ex.dag.size) && !stage.up.opaq[m]!) then
    let area := componentArea stage.up stage.f members
    let areaPositions := setPositions areaPositions area
    if areaOK ex.dag.size stage.up.opaq parents members area areaPositions then
      let (marks, found, stack) := upWalk parents members closurePositions
      if stack.isEmpty && area.all (fun y => marks[y]! != 0) then
        let light := context stage members area
        if localSearchOK light then
          let nextWork ← bump work (familyWork cfg members.size found.size) limits.maxCostEvals .costEvals
          let aux := auxiliary ex stage base area areaPositions found marks
          let closurePositions := clearPositions marks found
          let cached := Thunk.mk fun _ => fullContext ex stage members
          let result ← retainedResult stage.slack
            (trace cfg width results.size members area.size found.size
              (phiA light areaPositions base aux (forceContext cached)))
          return ((results.push result, nextStates, nextWork),
            clearPositions areaPositions area, closurePositions)
        else
          familyStepArea cfg limits ex stage width parents base
            ((results, states, work), clearPositions areaPositions area, clearPositions marks found) members
      else
        familyStepArea cfg limits ex stage width parents base
          ((results, states, work), clearPositions areaPositions area, clearPositions marks found) members
    else
      familyStepArea cfg limits ex stage width parents base
        ((results, states, work), clearPositions areaPositions area, closurePositions) members
  else
    familyStepArea cfg limits ex stage width parents base
      ((results, states, work), areaPositions, closurePositions) members

theorem step_eq_area (cfg : Config) (limits : Limits) (ex : Expanded) (stage : UStage)
    (width : Nat) (stageOK : AreaProof.StageOK ex stage.up stage.baseEv stage.widthCs stage.allTrue)
    (base : TBase) (baseEq : base = TBase.ofPrep stage.up.prep stage.up.w stage.up.opaq)
    (baseOK : tStageOK stage.up.prep stage.up.w stage.up.opaq base = true)
    (acc : MeterState) (members : Array Nat) :
    step cfg limits ex stage width (parentsOf ex.dag) base
        (acc, Array.replicate stage.up.prep.dag.size 0, Array.replicate ex.dag.size 0) members =
      familyStepArea cfg limits ex stage width (parentsOf ex.dag) base
        (acc, Array.replicate stage.up.prep.dag.size 0, Array.replicate ex.dag.size 0) members := by
  have original := familyStepArea_eq_reference cfg limits ex stage width stageOK base baseEq baseOK acc members
  obtain ⟨results, states, work⟩ := acc
  have clearArea := AreaProof.clear_set_any stage.up.prep.dag.size (componentArea stage.up stage.f members)
  unfold step
  dsimp only
  cases stateCharge : bump states (familyCalls cfg members.size) limits.maxStates .states with
  | error error =>
    unfold familyStepArea
    simp only [stateCharge, Bind.bind, Except.bind]
  | ok nextStates =>
    simp only [Bind.bind, Except.bind]
    split
    · rename_i membersOK
      split
      · rename_i areaReady
        generalize walk : upWalk (parentsOf ex.dag) members (Array.replicate ex.dag.size 0) = walked
        obtain ⟨marks, found, stack⟩ := walked
        have clearClosure := clear_walk ex members marks found stack walk
        split
        · rename_i walkOK
          split
          · rename_i localOK
            obtain ⟨sameSize, sameTrace⟩ := trace_walk_eq cfg ex stage width results.size members
              stageOK base baseEq baseOK marks found stack walk membersOK areaReady walkOK localOK
            rw [sameTrace, sameSize, clearArea, clearClosure, original]
            unfold familyReferenceStep
            simp only [stateCharge, Bind.bind, Except.bind]
            cases workCharge : bump work (familyWork cfg members.size (componentContext ex stage members).closure.size)
                limits.maxCostEvals .costEvals with
            | error error => rfl
            | ok nextWork =>
              cases retainedResult stage.slack (component cfg ex stage width results.size members) <;> rfl
          · rw [clearArea, clearClosure]
        · rw [clearArea, clearClosure]
      · rw [clearArea]
    · rfl

theorem fold_eq_reference (cfg : Config) (limits : Limits) (ex : Expanded) (stage : UStage)
    (width : Nat) (stageOK : AreaProof.StageOK ex stage.up stage.baseEv stage.widthCs stage.allTrue)
    (base : TBase) (baseEq : base = TBase.ofPrep stage.up.prep stage.up.w stage.up.opaq)
    (baseOK : tStageOK stage.up.prep stage.up.w stage.up.opaq base = true)
    (members : List (Array Nat)) (acc : MeterState) :
    members.foldlM (step cfg limits ex stage width (parentsOf ex.dag) base)
        (acc, Array.replicate stage.up.prep.dag.size 0, Array.replicate ex.dag.size 0) =
      (members.foldlM (familyReferenceStep cfg limits ex stage width) acc).map
        (fun next => (next, Array.replicate stage.up.prep.dag.size 0, Array.replicate ex.dag.size 0)) := by
  exact LocalSearch.foldlM_sim _ _ _
    (fun acc members =>
      (step_eq_area cfg limits ex stage width stageOK base baseEq baseOK acc members).trans
        (familyStepArea_eq_reference cfg limits ex stage width stageOK base baseEq baseOK acc members))
    members acc

def components (cfg : Config) (limits : Limits) (ex : Expanded) (stage : UStage)
    (width : Nat) (parents : Array (Array Nat)) : Except SharingError MeterState :=
  let base := TBase.ofPrep stage.up.prep stage.up.w stage.up.opaq
  if tStageOK stage.up.prep stage.up.w stage.up.opaq base then
    (stage.comps.foldlM (step cfg limits ex stage width parents base)
      ((#[], 0, 0), Array.replicate stage.up.prep.dag.size 0, Array.replicate ex.dag.size 0)).map (·.1)
  else familyComponents cfg limits ex stage width parents

theorem components_eq (cfg : Config) (limits : Limits) (ex : Expanded) (stage : UStage)
    (width : Nat) (stageOK : AreaProof.StageOK ex stage.up stage.baseEv stage.widthCs stage.allTrue) :
    components cfg limits ex stage width (parentsOf ex.dag) =
      familyComponentsArea cfg limits ex stage width (parentsOf ex.dag) := by
  unfold components familyComponentsArea
  dsimp only
  split
  · rename_i baseOK
    rw [← Array.foldlM_toList, ← Array.foldlM_toList,
      fold_eq_reference cfg limits ex stage width stageOK _ rfl baseOK,
      familyFoldArea_eq_reference cfg limits ex stage width stageOK _ rfl baseOK]
  · rfl

def uniform (cfg : Config) (limits : Limits) (ex : Expanded) (prep : Prep)
    (facts : GraphFacts) (parents : Array (Array Nat)) (width : Nat) :
    Except SharingError UniformSharingResult := do
  let stage := uniformStageF width ex prep facts
  let (results, states, costEvals) ← components cfg limits ex stage width parents
  let (delta, chosen, lowerBracket) ← uniformKnapsack limits stage.cs.size results
  let modelInt : _root_.Int := (csBase ex prep stage : Nat) + delta + tag0Size (stage.cs.size + chosen.size)
  let model := modelInt.toNat
  if model > limits.maxOutputBytes then throw (.resourceExhausted .outputBytes limits.maxOutputBytes)
  let choice : UniformChoice :=
    { facts, certainStored := stage.cs, certainExcluded := stage.ce, uncertain := stage.unc,
      lowDegree := stage.low, components := stage.comps, stored := mergeSorted stage.cs chosen,
      model, states, costEvals, lowerBracket }
  uniformFinishF width limits ex prep facts.deg choice

theorem uniform_eq (cfg : Config) (limits : Limits) (ex : Expanded) (facts : GraphFacts)
    (width : Nat) (dagOK : AreaProof.DagOK ex.dag) :
    uniform cfg limits ex (Prep.ofDag ex.dag) facts (parentsOf ex.dag) width =
      familyUniformArea cfg limits ex (Prep.ofDag ex.dag) facts (parentsOf ex.dag) width := by
  unfold uniform familyUniformArea
  dsimp only
  rw [components_eq cfg limits ex _ width (stageOK_F width ex facts dagOK)]

def atWidth (cfg : Config) (layout : ShareLayout) (limits : Limits) (ex : Expanded)
    (prep : Prep) (facts : GraphFacts) (parents : Array (Array Nat)) (candidates width : Nat) :
    Except SharingError TieredSharingResult := do
  let uniform ← uniform cfg limits ex prep facts parents width
  let allocation ← allocate layout limits ex.dag facts.deg uniform.result.tableTerms
    uniform.result.sharing uniform.result.roots
  let phase1 := layoutBytes layout uniform.result.sharing uniform.result.roots
  let materialized ← rematerializeP prep layout limits ex allocation.order phase1
  return tieredResultF layout width uniform allocation materialized candidates phase1

theorem atWidth_eq (cfg : Config) (layout : ShareLayout) (limits : Limits) (ex : Expanded)
    (facts : GraphFacts) (candidates width : Nat) (dagOK : AreaProof.DagOK ex.dag) :
    atWidth cfg layout limits ex (Prep.ofDag ex.dag) facts (parentsOf ex.dag) candidates width =
      familyAtWidthArea cfg layout limits ex (Prep.ofDag ex.dag) facts (parentsOf ex.dag) candidates width := by
  unfold atWidth familyAtWidthArea
  rw [uniform_eq cfg limits ex facts width dagOK]

def expanded (cfg : Config) (layout : ShareLayout) (limits : Limits) (ex : Expanded) :
    Except SharingError TieredSharingResult := do
  uniformDagChecks ex
  let prep := Prep.ofDag ex.dag
  let facts := graphFacts ex.dag ex.roots
  let parents := parentsOf ex.dag
  let candidates := tieredCandidateCount ex.dag.size prep facts
  let result ← tieredCandidates ex.dag.size
    (atWidth cfg layout limits ex prep facts parents candidates)
  return withExpansionStats ex result

theorem expanded_eq : @expanded = @familyExpandedArea := by
  funext cfg layout limits ex
  unfold expanded familyExpandedArea
  cases checks : uniformDagChecks ex with
  | error error => rfl
  | ok value =>
    cases value
    have widths := fun facts candidates => funext fun width =>
      atWidth_eq cfg layout limits ex facts candidates width (dagOK_of_checks checks)
    simp only [widths]

def normalize (cfg : Config) (layout : ShareLayout) (constant : Ixon.Constant)
    (limits : Limits := {}) : Except SharingError (Ixon.Constant × TieredSharingResult) := do
  let ex ← expand limits constant.sharing (constantInfoRoots constant.info) true
  let result ← expanded cfg layout limits ex
  let info ← withRoots constant.info result.result.roots
  return ({ constant with info, sharing := result.result.sharing }, result)

theorem normalize_eq_area : @normalize = @normalizeFamilyArea := by
  funext cfg layout constant limits
  unfold normalize normalizeFamilyArea
  rw [expanded_eq]

end Ix.Sharing.Family.LightContext

namespace Ix.Sharing.Family

/-- The checked context preparation preserves the complete canonical result
and every refusal for every input, layout, family parameter and budget. -/
@[csimp] theorem familyExpandedArea_eq_lightContext :
    @familyExpandedArea = @LightContext.expanded := LightContext.expanded_eq.symm

/-- The parameterized API uses the same proved evaluator as the compiler. -/
@[csimp] theorem normalizeFamilyArea_eq_lightContext :
    @normalizeFamilyArea = @LightContext.normalize := LightContext.normalize_eq_area.symm

/-- Register the original entry directly: earlier compiler simplification
passes may already have collapsed its intermediate replacement chain. -/
@[csimp] theorem familyReferenceExpanded_eq_lightContext :
    @familyReferenceExpanded = @LightContext.expanded :=
  familyReferenceExpanded_eq_cached.trans
    (familyExpanded_eq_area.trans LightContext.expanded_eq.symm)

@[csimp] theorem familyExpanded_eq_lightContext :
    @familyExpanded = @LightContext.expanded :=
  familyExpanded_eq_area.trans LightContext.expanded_eq.symm

@[csimp] theorem normalizeFamily_eq_lightContext :
    @normalizeFamily = @LightContext.normalize :=
  normalizeFamily_eq_area.trans LightContext.normalize_eq_area.symm

end Ix.Sharing.Family
