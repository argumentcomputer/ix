module

public import Ix.Sharing.FamilyPrototypeFast
import all Ix.Sharing.Exact.UniformSearchLocal

@[expose] public section

/-! Cached preparation for all INITIAL component families of one width.
The parent table and two position buffers are allocated once. The closure is
found by `mkSCtxL`'s upward walk, and only touched positions are cleared.
Every family and complete trace remains the existing reference's value.
This module does not combine rows or normalize a constant. -/

namespace Ix.Sharing.FamilyPrototype

open Ix.Sharing.Exact

def traceWithPhi (cfg : Config) (cx : SCtx) (width index : Nat)
    (members : Array Nat) (eval : (Nat → Bool) → Array Nat → Nat × Nat) : ComponentTrace :=
  let baseline := (eval (fun _ => false) #[]).1
  let cost : Cost := fun set => ((eval set.contains set).1 : _root_.Int) - (baseline : _root_.Int)
  let m := members.size
  let exact := m ≤ cfg.experimentK
  { width, index, exact, members, areaSize := cx.area.size, closureSize := cx.closure.size,
    rows := table cfg cost members.toList,
    evaluations := if exact then 2 ^ m else m * (m + 1) / 2 + m + 1 }

private theorem traceWithPhi_spec (cfg : Config) (ex : Expanded) (sg : UStage)
    (width index : Nat) (members : Array Nat) :
    traceWithPhi cfg (componentContext ex sg members) width index members
        (componentContext ex sg members).phiE = component cfg ex sg width index members := by
  rfl

/-- Decide the evaluator outside the cost closure, once per component.
Returning a trace here avoids native eta expansion repeating the check. -/
def traceWithPositions (cfg : Config) (cx : SCtx) (width index : Nat)
    (members posA posC : Array Nat) : ComponentTrace :=
  if cx.members.all (fun m => (posOf posA m).isSome) then
    traceWithPhi cfg cx width index members (phiEL2 cx posA posC)
  else traceWithPhi cfg cx width index members cx.phiE

private theorem traceWithPositions_eq (cfg : Config) {cx : SCtx} (width index : Nat)
    (members : Array Nat) {posA posC : Array Nat}
    (hr : LocalSearch.Ready cx posA posC) :
    traceWithPositions cfg cx width index members posA posC =
      traceWithPhi cfg cx width index members cx.phiE := by
  unfold traceWithPositions
  split
  · rename_i hm
    have hmem : LocalSearch.MembersIn cx posA := by
      intro m hc
      exact Array.all_eq_true'.mp hm m (Array.contains_iff_mem.mp hc)
    have heval : phiEL2 cx posA posC = cx.phiE := by
      funext avail stored
      exact (LocalSearch.phiE_eq_L2 hr hmem avail stored).symm
    rw [heval]
  · rfl

abbrev CacheState := Array ComponentTrace × Array Nat × Array Nat

/-- Shared evaluator/clear step for the trace fold and the metered production
fold. The caller may charge closure work after preparation and before this call. -/
def cachedEvaluation (cfg : Config) (cx : SCtx) (width index : Nat)
    (members posA posC : Array Nat) : ComponentTrace × Array Nat × Array Nat :=
  if localSearchOK cx then
    let posA := setPositions posA cx.area
    let trace := traceWithPositions cfg cx width index members posA posC
    (trace, clearPositions posA cx.area, clearPositions posC cx.closure)
  else
    let trace := traceWithPhi cfg cx width index members cx.phiE
    (trace, posA, clearPositions posC cx.closure)

def cachedComponent (cfg : Config) (ex : Expanded) (sg : UStage) (width : Nat)
    (parents : Array (Array Nat)) (posA posC members : Array Nat) (index : Nat) :
    ComponentTrace × Array Nat × Array Nat :=
  let (cx, posC) := mkSCtxL ex sg.f sg.up sg.cand sg.b0 sg.vis0 sg.rootCount
    sg.slack sg.theta sg.baseEv sg.widthCs sg.allTrue sg.unc parents posC members
  cachedEvaluation cfg cx width index members posA posC

/-- One component consumes its evaluator before clearing its shared buffers.
Trace rows contain values/IDs, never a retained context or position closure. -/
def cachedStep (cfg : Config) (ex : Expanded) (sg : UStage) (width : Nat)
    (parents : Array (Array Nat)) (acc : CacheState) (item : Array Nat × Nat) : CacheState :=
  let (results, posA, posC) := acc
  let (trace, posA, posC) := cachedComponent cfg ex sg width parents posA posC item.1 item.2
  (results.push trace, posA, posC)

/-- From cleared buffers, the cached step returns the reference trace and
cleared buffers again. No stage/classification premise is added. -/
theorem cachedComponent_eq (cfg : Config) (ex : Expanded) (sg : UStage) (width : Nat)
    (hcp : childrenPrecede ex.dag.nodes = true)
    (members : Array Nat) (index : Nat) :
    cachedComponent cfg ex sg width (parentsOf ex.dag)
        (Array.replicate sg.up.prep.dag.size 0) (Array.replicate ex.dag.size 0) members index =
      (component cfg ex sg width index members,
        Array.replicate sg.up.prep.dag.size 0, Array.replicate ex.dag.size 0) := by
  unfold cachedComponent
  dsimp only
  rw [LocalSearch.mkSCtxL_eq ex sg.f sg.up sg.cand sg.b0 sg.vis0 sg.rootCount sg.slack
    sg.theta sg.baseEv sg.widthCs sg.allTrue sg.unc members hcp]
  simp only
  have hCs := LocalSearch.upClosure_sorted ex.dag ((markTable ex.dag.size members)[·]!)
  have hCmem := LocalSearch.mem_upClosure hcp ((markTable ex.dag.size members)[·]!)
  have hCinc := LocalSearch.strictInc_of_sorted hCs
  have hCin : ∀ i, i < (upClosure ex.dag ((markTable ex.dag.size members)[·]!)).size →
      (upClosure ex.dag ((markTable ex.dag.size members)[·]!))[i]! < ex.dag.size :=
    fun i hi => ((hCmem _).mp (LocalSearch.mem_of_getElem! hi)).lt
  have hzC := LocalSearch.clear_set_zero ex.dag.size
    (upClosure ex.dag ((markTable ex.dag.size members)[·]!)) hCinc hCin
  let cx := componentContext ex sg members
  have hcx : mkSCtx ex sg.f sg.up sg.cand sg.b0 sg.vis0 sg.rootCount sg.slack
      sg.theta sg.baseEv sg.widthCs sg.allTrue sg.unc members = cx := rfl
  have hcl : cx.closure = upClosure ex.dag ((markTable ex.dag.size members)[·]!) := rfl
  have hup : cx.up = sg.up := rfl
  rw [hcx]
  unfold cachedEvaluation
  rw [hcl, hzC]
  by_cases hok : localSearchOK cx = true
  · rw [ite_eq_left hok]
    dsimp only
    obtain ⟨_, _, _, _, _, _, _, _, harea, _⟩ := LocalSearch.localSearchOK_spec hok
    have hainc := (LocalSearch.localSearchOK_inc hok).1
    have hain : ∀ i, i < cx.area.size → cx.area[i]! < sg.up.prep.dag.size := by
      intro i hi
      rw [← hup]
      exact harea i hi
    have hzA := LocalSearch.clear_set_zero sg.up.prep.dag.size cx.area hainc hain
    have hr : LocalSearch.Ready cx
        (setPositions (Array.replicate sg.up.prep.dag.size 0) cx.area)
        (setPositions (Array.replicate ex.dag.size 0)
          (upClosure ex.dag ((markTable ex.dag.size members)[·]!))) :=
      ⟨hok, LocalSearch.setPositions_posFn _ _ hainc hain,
        by rw [hcl]; exact LocalSearch.setPositions_posFn _ _ hCinc hCin⟩
    rw [traceWithPositions_eq cfg width index members hr, hzA]
    exact congrArg (fun t => (t, Array.replicate sg.up.prep.dag.size 0,
      Array.replicate ex.dag.size 0)) (traceWithPhi_spec cfg ex sg width index members)
  · rw [ite_eq_right hok]
    dsimp only
    exact congrArg (fun t => (t, Array.replicate sg.up.prep.dag.size 0,
      Array.replicate ex.dag.size 0)) (traceWithPhi_spec cfg ex sg width index members)

theorem cachedStep_eq (cfg : Config) (ex : Expanded) (sg : UStage) (width : Nat)
    (hcp : childrenPrecede ex.dag.nodes = true) (results : Array ComponentTrace)
    (members : Array Nat) (index : Nat) :
    cachedStep cfg ex sg width (parentsOf ex.dag)
        (results, Array.replicate sg.up.prep.dag.size 0, Array.replicate ex.dag.size 0)
        (members, index) =
      (results.push (component cfg ex sg width index members),
        Array.replicate sg.up.prep.dag.size 0, Array.replicate ex.dag.size 0) := by
  unfold cachedStep
  dsimp only
  rw [cachedComponent_eq cfg ex sg width hcp]

/-- Whole-stage fold, with the initial classification supplied once. Non-DAG
inputs retain the reference loop; valid inputs use the proved cached walk. -/
def componentsCachedWith (cfg : Config) (ex : Expanded) (sg : UStage) (width : Nat) :
    Array ComponentTrace :=
  if childrenPrecede ex.dag.nodes then
    let parents := parentsOf ex.dag
    let init : CacheState :=
      (#[], Array.replicate sg.up.prep.dag.size 0, Array.replicate ex.dag.size 0)
    ((sg.comps.zipIdx).foldl (cachedStep cfg ex sg width parents) init).1
  else sg.comps.mapIdx fun i members => component cfg ex sg width i members

theorem componentsCachedWith_eq (cfg : Config) (ex : Expanded) (sg : UStage) (width : Nat) :
    componentsCachedWith cfg ex sg width =
      sg.comps.mapIdx (fun i members => component cfg ex sg width i members) := by
  unfold componentsCachedWith
  split
  · rename_i hcp
    let spec := fun (acc : Array ComponentTrace) (item : Array Nat × Nat) =>
      acc.push (component cfg ex sg width item.2 item.1)
    have fold : ∀ (items : List (Array Nat × Nat)) (acc : Array ComponentTrace),
        items.foldl (cachedStep cfg ex sg width (parentsOf ex.dag))
            (acc, Array.replicate sg.up.prep.dag.size 0, Array.replicate ex.dag.size 0) =
          (items.foldl spec acc, Array.replicate sg.up.prep.dag.size 0,
            Array.replicate ex.dag.size 0) := by
      intro items
      induction items with
      | nil => intro acc; rfl
      | cons item rest ih =>
        intro acc
        rw [List.foldl_cons, cachedStep_eq cfg ex sg width hcp, ih]
        rfl
    dsimp only
    rw [← Array.foldl_toList, fold]
    apply Array.ext'
    rw [Array.foldl_toList_eq_map, Array.toList_mapIdx, List.mapIdx_eq_zipIdx_map]
    simp
  · rfl

/-- One shared initial stage and one pair of buffers per width. -/
def componentsCached (cfg : Config) (ex : Expanded) (width : Nat) : Array ComponentTrace :=
  componentsCachedWith cfg ex (uniformStage width ex (Prep.ofDag ex.dag)) width

@[csimp] theorem components_eq_cached : @components = @componentsCached := by
  funext cfg ex width
  exact (componentsCachedWith_eq cfg ex (uniformStage width ex (Prep.ofDag ex.dag)) width).symm

end Ix.Sharing.FamilyPrototype
