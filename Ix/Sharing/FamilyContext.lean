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
import all Ix.Sharing.Exact.Reexpand
import all Ix.Sharing.Exact.Search
import all Ix.Sharing.Exact.Phase3
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

def areaFlagsFast (k : Nat) (posA ts : @& Array Nat) : Array Bool :=
  ts.foldl (fun f t => let q := posA[t]!; if q != 0 then f.set! (q - 1) true else f)
    (Array.replicate k false)

def allGuardFast (p : @& Prep) (tb : @& TBase) (w : Nat)
    (posA C I S storedA : @& Array Nat) : Bool :=
  storedA.all (fun c => tGuardDirect p tb w posA C I S c)

def sumRdAFast (posA arr baseArr ts : @& Array Nat) : Nat :=
  ts.foldl (fun acc x => acc + rdA posA arr baseArr x) 0

/-- `phiA` computing member flags directly from `stored` in `O(|stored|)` via
`areaFlagsFast`, and running `areaFoldDirect` and `tGuardDirect` without closure
allocations. -/
@[inline] def phiASet (cx : SCtx) (posA : Array Nat) (tb : TBase) (aux : AAux)
    (fb : Unit → SCtx × Array Nat) (avail : Nat → Bool) (stored : Array Nat) : Nat × Nat :=
  let w := cx.up.w
  match areaFoldDirect cx.up.prep cx.up.opaq tb w cx.area posA (areaFlagsFast cx.area.size posA stored) with
  | (C, I, S, _) =>
    if allGuardFast cx.up.prep tb w posA C I S aux.storedA then
      let roots := sumRdAFast posA C tb.cost aux.rootsA
      let base := sumRdAFast posA I tb.inl aux.storedA
      let entries := sumRdAFast posA I tb.inl stored
      (aux.K + roots + base + entries, aux.csize + stored.size)
    else
      match fb () with
      | (cs, posC) => phiEL2 cs posA posC avail stored

private theorem phiASet_eq_of_flags (cx : SCtx) (posA : Array Nat) (tb : TBase) (aux : AAux)
    (fb : Unit → SCtx × Array Nat) (avail : Nat → Bool) (stored : Array Nat)
    (hfl : areaFlags cx.area.size posA stored = memberFlags cx posA avail) :
    phiASet cx posA tb aux fb avail stored = phiA cx posA tb aux fb avail stored := by
  have hfast : areaFlagsFast cx.area.size posA stored = areaFlags cx.area.size posA stored := rfl
  unfold phiASet allGuardFast sumRdAFast phiA tGuardDirect tGuard
  rw [hfast, hfl, ← areaFold_eq_direct]

private theorem areaFlags_size (k : Nat) (posA ts : Array Nat) :
    (areaFlags k posA ts).size = k := by
  unfold areaFlags
  rw [← Array.foldl_toList]
  suffices ∀ (l : List Nat) (f : Array Bool), f.size = k →
      (l.foldl (fun f t => let q := posA[t]!; if q != 0 then f.set! (q - 1) true else f) f).size = k by
    exact this ts.toList _ Array.size_replicate
  intro l
  induction l with
  | nil => intro f hf; exact hf
  | cons x l ih =>
    intro f hf
    simp only [List.foldl_cons]
    split <;> apply ih <;> simp [hf]

private theorem areaFlags_congr (k : Nat) (posA ts₁ ts₂ : Array Nat)
    (h : ∀ x, x ∈ ts₁.toList ↔ x ∈ ts₂.toList) :
    areaFlags k posA ts₁ = areaFlags k posA ts₂ := by
  apply Array.ext
  · rw [areaFlags_size, areaFlags_size]
  · intro i hi₁ hi₂
    rw [← getElem!_pos _ i hi₁, ← getElem!_pos _ i hi₂]
    apply Bool.eq_iff_iff.mpr
    rw [AreaProof.areaFlags_spec, AreaProof.areaFlags_spec]
    exact and_congr_right fun _ => exists_congr fun x => and_congr_left fun _ => h x

private theorem memberFlags_eq_areaFlags_filter (cx : SCtx) (posA : Array Nat) (avail : Nat → Bool) :
    memberFlags cx posA avail = areaFlags cx.area.size posA (cx.members.filter avail) := by
  unfold memberFlags areaFlags
  rw [← Array.foldl_toList, ← Array.foldl_toList, Array.toList_filter]
  suffices ∀ (l : List Nat) (fl : Array Bool),
      l.foldl (fun fl m => match posOf posA m with
        | some j => if avail m then fl.set! j true else fl
        | none => fl) fl =
      (l.filter avail).foldl (fun f t =>
        let q := posA[t]!; if q != 0 then f.set! (q - 1) true else f) fl by
    exact this cx.members.toList _
  intro l
  induction l with
  | nil => intro fl; rfl
  | cons m l ih =>
    intro fl
    simp only [List.foldl_cons, List.filter_cons]
    have hstep : (match posOf posA m with
        | some j => if avail m then fl.set! j true else fl
        | none => fl) =
        if avail m then (let q := posA[m]!; if q != 0 then fl.set! (q - 1) true else fl) else fl := by
      unfold posOf
      by_cases hq : posA[m]! = 0 <;> by_cases ha : avail m = true <;> simp [hq, ha]
    rw [hstep]
    cases avail m <;> simp only [ite_true, Bool.false_eq_true, ite_false, List.foldl_cons] <;> exact ih _

private theorem areaFlags_empty_eq_memberFlags (cx : SCtx) (posA : Array Nat) :
    areaFlags cx.area.size posA #[] = memberFlags cx posA (fun _ => false) := by
  rw [memberFlags_eq_areaFlags_filter]
  apply areaFlags_congr
  intro x
  simp

private theorem areaFlags_subset_eq_memberFlags (cx : SCtx) (posA : Array Nat)
    (selected : Array Nat) (hsub : ∀ x ∈ selected.toList, x ∈ cx.members.toList) :
    areaFlags cx.area.size posA selected = memberFlags cx posA selected.contains := by
  rw [memberFlags_eq_areaFlags_filter]
  apply areaFlags_congr
  intro x
  rw [Array.toList_filter, List.mem_filter, Array.contains_iff_mem, ← Array.mem_toList_iff]
  exact ⟨fun hx => ⟨hsub x hx, hx⟩, fun h => h.2⟩

private theorem mem_sorted {xs : List Nat} {x : Nat} (hx : x ∈ (sorted xs).toList) : x ∈ xs := by
  unfold sorted at hx
  exact (List.Perm.mem_iff (List.mergeSort_perm xs _)).mp hx

private theorem foldChoices_congr {α : Type} (members : List Nat)
    (visit₁ visit₂ : α → Array Nat → α)
    (hvisit : ∀ a (s : Array Nat), (∀ x ∈ s.toList, x ∈ members) → visit₁ a s = visit₂ a s)
    (remaining chosen : List Nat)
    (hrem : ∀ x ∈ remaining, x ∈ members) (hch : ∀ x ∈ chosen, x ∈ members) (acc : α) :
    foldChoices visit₁ remaining chosen acc = foldChoices visit₂ remaining chosen acc := by
  induction remaining generalizing chosen acc with
  | nil =>
    unfold foldChoices
    exact hvisit acc (sorted chosen) (fun x hx => hch x (mem_sorted hx))
  | cons m rest ih =>
    unfold foldChoices
    have hm : m ∈ members := hrem m List.mem_cons_self
    have hrest : ∀ x ∈ rest, x ∈ members := fun x hx => hrem x (List.mem_cons_of_mem _ hx)
    rw [ih chosen hrest hch acc, ih (m :: chosen) hrest
      (fun x hx => by rcases List.mem_cons.mp hx with rfl | hx; exact hm; exact hch x hx) _]

private theorem score_congr (members : List Nat) (cost₁ cost₂ : Cost)
    (hcost : ∀ s : Array Nat, (∀ x ∈ s.toList, x ∈ members) → cost₁ s = cost₂ s)
    (chosen : List Nat) (hch : ∀ x ∈ chosen, x ∈ members) (m : Nat) (hm : m ∈ members) :
    score cost₁ chosen m = score cost₂ chosen m := by
  unfold score
  dsimp only
  rw [hcost (sorted (m :: chosen))]
  intro x hx
  rcases List.mem_cons.mp (mem_sorted hx) with rfl | hx
  · exact hm
  · exact hch x hx

private theorem pickTail_congr (members : List Nat) (cost₁ cost₂ : Cost)
    (hcost : ∀ s : Array Nat, (∀ x ∈ s.toList, x ∈ members) → cost₁ s = cost₂ s)
    (chosen : List Nat) (hch : ∀ x ∈ chosen, x ∈ members)
    (best : Nat × Entry) (rest : List Nat) (hrest : ∀ x ∈ rest, x ∈ members) :
    pickTail cost₁ chosen best rest = pickTail cost₂ chosen best rest := by
  induction rest generalizing best with
  | nil => rfl
  | cons m rest ih =>
    unfold pickTail
    dsimp only
    rw [score_congr members cost₁ cost₂ hcost chosen hch m (hrest m List.mem_cons_self)]
    exact ih _ (fun x hx => hrest x (List.mem_cons_of_mem _ hx))

private theorem pickTail_fst_mem (cost : Cost) (chosen : List Nat) (best : Nat × Entry)
    (rest : List Nat) :
    (pickTail cost chosen best rest).1 = best.1 ∨ (pickTail cost chosen best rest).1 ∈ rest := by
  induction rest generalizing best with
  | nil => exact Or.inl rfl
  | cons m rest ih =>
    unfold pickTail
    dsimp only
    by_cases hb : betterEntry (score cost chosen m) (some best.2) = true
    · simp only [hb, ite_true]
      rcases ih (m, score cost chosen m) with h | h
      · exact Or.inr (by rw [h]; exact List.mem_cons_self)
      · exact Or.inr (List.mem_cons_of_mem _ h)
    · simp only [hb, Bool.false_eq_true, ite_false]
      rcases ih best with h | h
      · exact Or.inl h
      · exact Or.inr (List.mem_cons_of_mem _ h)

private theorem greedyOrderAux_congr_and_mem (members : List Nat) (cost₁ cost₂ : Cost)
    (hcost : ∀ s : Array Nat, (∀ x ∈ s.toList, x ∈ members) → cost₁ s = cost₂ s)
    (fuel : Nat) (chosen pool : List Nat)
    (hch : ∀ x ∈ chosen, x ∈ members) (hpool : ∀ x ∈ pool, x ∈ members) :
    greedyOrderAux cost₁ fuel chosen pool = greedyOrderAux cost₂ fuel chosen pool ∧
      (∀ x ∈ greedyOrderAux cost₁ fuel chosen pool, x ∈ members) := by
  induction fuel generalizing chosen pool with
  | zero =>
    unfold greedyOrderAux
    exact ⟨rfl, fun _ h => nomatch h⟩
  | succ fuel ih =>
    cases pool with
    | nil =>
      unfold greedyOrderAux
      exact ⟨rfl, fun _ h => nomatch h⟩
    | cons m rest =>
      unfold greedyOrderAux
      dsimp only
      have hm : m ∈ members := hpool m List.mem_cons_self
      have hrest : ∀ x ∈ rest, x ∈ members := fun x hx => hpool x (List.mem_cons_of_mem _ hx)
      have hpick : pick cost₁ chosen m rest = pick cost₂ chosen m rest := by
        unfold pick
        rw [score_congr members cost₁ cost₂ hcost chosen hch m hm,
          pickTail_congr members cost₁ cost₂ hcost chosen hch _ rest hrest]
      have hnext_mem : pick cost₁ chosen m rest ∈ members := by
        unfold pick
        rcases pickTail_fst_mem cost₁ chosen (m, score cost₁ chosen m) rest with h | h
        · rw [h]; exact hm
        · exact hrest _ h
      have hch' : ∀ x ∈ pick cost₁ chosen m rest :: chosen, x ∈ members := by
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hnext_mem
        · exact hch x hx
      have hpool' : ∀ x ∈ (m :: rest).erase (pick cost₁ chosen m rest), x ∈ members :=
        fun x hx => hpool x (List.mem_of_mem_erase hx)
      obtain ⟨heq, hmem⟩ := ih (pick cost₁ chosen m rest :: chosen)
        ((m :: rest).erase (pick cost₁ chosen m rest)) hch' hpool'
      refine ⟨by rw [← hpick, heq], ?_⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hnext_mem
      · exact hmem x hx

private theorem table_congr_subset (cfg : Config) (members : List Nat) (cost₁ cost₂ : Cost)
    (hcost : ∀ s : Array Nat, (∀ x ∈ s.toList, x ∈ members) → cost₁ s = cost₂ s) :
    table cfg cost₁ members = table cfg cost₂ members := by
  unfold table foldFamily
  split
  · exact foldChoices_congr members _ _
      (fun tb s hs => by rw [hcost s hs])
      members [] (fun x hx => hx) (fun _ h => nomatch h) #[]
  · unfold chain greedyOrder
    obtain ⟨hord, hmem⟩ := greedyOrderAux_congr_and_mem members cost₁ cost₂ hcost
      members.length [] members (fun _ h => nomatch h) (fun x hx => hx)
    rw [hord]
    have hchain_mem : ∀ s ∈ List.map (fun k => sorted ((greedyOrderAux cost₂ members.length [] members).take k))
        (List.range (members.length + 1)), ∀ x ∈ s.toList, x ∈ members := by
      intro s hs x hx
      rcases List.mem_map.mp hs with ⟨k, _, rfl⟩
      rw [← hord] at hx
      exact hmem x (List.mem_of_mem_take (mem_sorted hx))
    generalize List.map (fun k => sorted ((greedyOrderAux cost₂ members.length [] members).take k))
      (List.range (members.length + 1)) = ch at hchain_mem
    suffices ∀ (l : List (Array Nat)), (∀ s ∈ l, ∀ x ∈ s.toList, x ∈ members) →
        ∀ tb : CTable, l.foldl (fun tb set => tb.add (cost₁ set, set)) tb =
          l.foldl (fun tb set => tb.add (cost₂ set, set)) tb by
      exact this ch hchain_mem #[]
    intro l hl tb
    induction l generalizing tb with
    | nil => rfl
    | cons s l ih =>
      simp only [List.foldl_cons]
      rw [hcost s (hl s List.mem_cons_self)]
      exact ih (fun s' hs' => hl s' (List.mem_cons_of_mem _ hs')) _

theorem trace_phiASet_eq (cfg : Config) (width index : Nat) (stage : UStage)
    (members area : Array Nat) (closureSize : Nat)
    (posA : Array Nat) (tb : TBase) (aux : AAux) (fb : Unit → SCtx × Array Nat) :
    trace cfg width index members area.size closureSize
        (phiASet (context stage members area) posA tb aux fb) =
      trace cfg width index members area.size closureSize
        (phiA (context stage members area) posA tb aux fb) := by
  let cx := context stage members area
  have hbase : phiASet cx posA tb aux fb (fun _ => false) #[] =
      phiA cx posA tb aux fb (fun _ => false) #[] :=
    phiASet_eq_of_flags cx posA tb aux fb (fun _ => false) #[]
      (areaFlags_empty_eq_memberFlags cx posA)
  have hrows : table cfg
        (fun selected => ((phiASet cx posA tb aux fb selected.contains selected).1 : _root_.Int) -
          ((phiA cx posA tb aux fb (fun _ => false) #[]).1 : _root_.Int))
        members.toList =
      table cfg
        (fun selected => ((phiA cx posA tb aux fb selected.contains selected).1 : _root_.Int) -
          ((phiA cx posA tb aux fb (fun _ => false) #[]).1 : _root_.Int))
        members.toList := by
    apply table_congr_subset
    intro selected hsub
    have hsel : phiASet cx posA tb aux fb selected.contains selected =
        phiA cx posA tb aux fb selected.contains selected :=
      phiASet_eq_of_flags cx posA tb aux fb selected.contains selected
        (areaFlags_subset_eq_memberFlags cx posA selected hsub)
    rw [hsel]
  unfold trace
  dsimp only
  rw [hbase, hrows]

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

@[noinline] def runStepTrace (cfg : Config) (ex : Expanded) (stage : UStage)
    (width index : Nat) (light : SCtx) (members area areaPositions : Array Nat)
    (base : TBase) (found marks : Array Nat) : Except SharingError CompResult :=
  let aux := auxiliary ex stage base area areaPositions found marks
  retainedResult stage.slack
    (trace cfg width index members area.size found.size
      (phiASet light areaPositions base aux (fun _ => fullContext ex stage members)))

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
          let closurePositions := clearPositions marks found
          let result ← runStepTrace cfg ex stage width results.size light
            members area areaPositions base found marks
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
  unfold step runStepTrace
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
            have hfb : (fun (_ : Unit) => fullContext ex stage members) =
                forceContext (Thunk.mk fun _ => fullContext ex stage members) := rfl
            rw [trace_phiASet_eq, hfb, sameTrace, sameSize, clearArea, clearClosure, original]
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
  if stage.comps.isEmpty then
    .ok (#[], 0, 0)
  else
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
  · rename_i hEmpty
    rw [Array.isEmpty_iff] at hEmpty
    unfold familyComponents
    simp only [hEmpty]
    split <;> rfl
  · split
    · rename_i baseOK
      rw [← Array.foldlM_toList, ← Array.foldlM_toList,
        fold_eq_reference cfg limits ex stage width stageOK _ rfl baseOK,
        familyFoldArea_eq_reference cfg limits ex stage width stageOK _ rfl baseOK]
    · rfl

def uniform (cfg : Config) (limits : Limits) (ex : Expanded) (prep : Prep)
    (facts : GraphFacts) (parents : Array (Array Nat)) (reIx : ReIndex) (width : Nat) :
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
  uniformFinishIx width limits ex prep facts.deg reIx choice

def uniformCached (cfg : Config) (limits : Limits) (ex : Expanded) (prep : Prep)
    (facts : GraphFacts) (parents : Array (Array Nat)) (reIx : ReIndex)
    (cache : EmptyCache) (width : Nat) :
    Except SharingError UniformSharingResult := do
  let stage := uniformStageCached width ex prep facts cache
  let (results, states, costEvals) ← components cfg limits ex stage width parents
  let (delta, chosen, lowerBracket) ← uniformKnapsack limits stage.cs.size results
  let modelInt : _root_.Int := (csBase ex prep stage : Nat) + delta + tag0Size (stage.cs.size + chosen.size)
  let model := modelInt.toNat
  if model > limits.maxOutputBytes then throw (.resourceExhausted .outputBytes limits.maxOutputBytes)
  let choice : UniformChoice :=
    { facts, certainStored := stage.cs, certainExcluded := stage.ce, uncertain := stage.unc,
      lowDegree := stage.low, components := stage.comps, stored := mergeSorted stage.cs chosen,
      model, states, costEvals, lowerBracket }
  uniformFinishCached width limits ex prep facts.deg reIx stage cache choice

theorem uniformCached_eq (cfg : Config) (limits : Limits) (ex : Expanded) (facts : GraphFacts)
    (parents : Array (Array Nat)) (reIx : ReIndex) (width : Nat) :
    uniformCached cfg limits ex (Prep.ofDag ex.dag) facts parents reIx
        (mkEmptyCache (Prep.ofDag ex.dag) limits ex reIx) width =
      uniform cfg limits ex (Prep.ofDag ex.dag) facts parents reIx width := by
  unfold uniformCached uniform
  simp only [uniformStageCached_eq_F, uniformFinishCached_eq_Ix]

theorem uniform_eq (cfg : Config) (limits : Limits) (ex : Expanded) (facts : GraphFacts)
    (width : Nat) (dagOK : AreaProof.DagOK ex.dag) :
    uniform cfg limits ex (Prep.ofDag ex.dag) facts (parentsOf ex.dag)
        (ReIndex.ofDag ex.dag) width =
      familyUniformArea cfg limits ex (Prep.ofDag ex.dag) facts (parentsOf ex.dag) width := by
  unfold uniform familyUniformArea
  dsimp only
  rw [components_eq cfg limits ex _ width (stageOK_F width ex facts dagOK)]
  simp only [uniformFinishIx_eq_F]

private theorem familyUniformArea_layoutBytes (cfg : Config) (layout : ShareLayout)
    (limits : Limits) (ex : Expanded) (p : Prep) (facts : GraphFacts)
    (parents : Array (Array Nat)) (width : Nat) {u : UniformSharingResult}
    (hu : familyUniformArea cfg limits ex p facts parents width = .ok u) :
    u.result.variableBytes = layoutBytes layout u.result.sharing u.result.roots := by
  unfold familyUniformArea at hu
  dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at hu
  split at hu <;> try cases hu
  split at hu <;> try cases hu
  split at hu <;> try cases hu
  exact uniformFinishF_layoutBytes layout width limits ex p facts.deg _ hu

def atWidth (cfg : Config) (layout : ShareLayout) (limits : Limits) (ex : Expanded)
    (prep : Prep) (facts : GraphFacts) (parents : Array (Array Nat))
    (reIx : ReIndex) (spines : Array (Array Nat)) (candidates width : Nat) :
    Except SharingError TieredSharingResult := do
  let uniform ← uniform cfg limits ex prep facts parents reIx width
  let allocation ← allocate layout limits ex.dag facts.deg uniform.result.tableTerms
    uniform.result.sharing uniform.result.roots
  let phase1 := uniform.result.variableBytes
  let materialized ← rematerializeIx prep reIx parents spines layout limits ex allocation.order phase1
  return tieredResultF layout width uniform allocation materialized candidates phase1

def atWidthCached (cfg : Config) (layout : ShareLayout) (limits : Limits) (ex : Expanded)
    (prep : Prep) (facts : GraphFacts) (parents : Array (Array Nat))
    (reIx : ReIndex) (spines : Array (Array Nat)) (cache : EmptyCache)
    (candidates width : Nat) :
    Except SharingError TieredSharingResult := do
  let uniform ← uniformCached cfg limits ex prep facts parents reIx cache width
  let allocation ← allocate layout limits ex.dag facts.deg uniform.result.tableTerms
    uniform.result.sharing uniform.result.roots
  let phase1 := uniform.result.variableBytes
  let materialized ← rematerializeCached prep reIx parents spines layout limits ex
    allocation.order phase1 cache
  return tieredResultF layout width uniform allocation materialized candidates phase1

theorem atWidthCached_eq (cfg : Config) (layout : ShareLayout) (limits : Limits) (ex : Expanded)
    (facts : GraphFacts) (parents : Array (Array Nat)) (reIx : ReIndex)
    (spines : Array (Array Nat)) (candidates width : Nat)
    (hchecks : uniformDagChecks ex = .ok ()) :
    atWidthCached cfg layout limits ex (Prep.ofDag ex.dag) facts parents reIx spines
        (mkEmptyCache (Prep.ofDag ex.dag) limits ex reIx) candidates width =
      atWidth cfg layout limits ex (Prep.ofDag ex.dag) facts parents reIx spines
        candidates width := by
  unfold atWidthCached atWidth
  rw [uniformCached_eq]
  cases uniform cfg limits ex (Prep.ofDag ex.dag) facts parents reIx width with
  | error e => rfl
  | ok u =>
    dsimp only [Bind.bind, Except.bind]
    cases allocate layout limits ex.dag facts.deg u.result.tableTerms u.result.sharing u.result.roots with
    | error e => rfl
    | ok a =>
      dsimp only []
      rw [rematerializeCached_eq_Ix layout limits ex reIx parents spines
        a.order u.result.variableBytes hchecks]

theorem atWidth_eq (cfg : Config) (layout : ShareLayout) (limits : Limits) (ex : Expanded)
    (facts : GraphFacts) (candidates width : Nat) (dagOK : AreaProof.DagOK ex.dag) :
    atWidth cfg layout limits ex (Prep.ofDag ex.dag) facts (parentsOf ex.dag)
        (ReIndex.ofDag ex.dag) (spineParentLists ex.dag (Prep.ofDag ex.dag).family)
        candidates width =
      familyAtWidthArea cfg layout limits ex (Prep.ofDag ex.dag) facts (parentsOf ex.dag)
        candidates width := by
  unfold atWidth familyAtWidthArea
  rw [uniform_eq cfg limits ex facts width dagOK]
  cases hu : familyUniformArea cfg limits ex (Prep.ofDag ex.dag) facts (parentsOf ex.dag) width with
  | error e => rfl
  | ok u =>
    have hpar : parentsOf ex.dag = parentEdgeLists (Prep.ofDag ex.dag).dag := by
      unfold parentsOf parentEdgeLists Prep.ofDag
      rfl
    have hsp : spineParentLists ex.dag (Prep.ofDag ex.dag).family =
        spineParentLists (Prep.ofDag ex.dag).dag (Prep.ofDag ex.dag).family := rfl
    simp only [Bind.bind, Except.bind,
      familyUniformArea_layoutBytes cfg layout limits ex (Prep.ofDag ex.dag) facts
        (parentsOf ex.dag) width hu,
      hpar, hsp, rematerializeIx_eq_P]

def expanded (cfg : Config) (layout : ShareLayout) (limits : Limits) (ex : Expanded) :
    Except SharingError TieredSharingResult := do
  uniformDagChecks ex
  let prep := Prep.ofDag ex.dag
  let facts := graphFacts ex.dag ex.roots
  let parents := parentsOf ex.dag
  let reIx : ReIndex := { parents, leaves := leafIndex ex.dag }
  let spines := spineParentLists ex.dag prep.family
  let cache := mkEmptyCache prep limits ex reIx
  let candidates := tieredCandidateCount ex.dag.size prep facts
  let result ← tieredCandidates ex.dag.size
    (atWidthCached cfg layout limits ex prep facts parents reIx spines cache candidates)
  return withExpansionStats ex result

theorem expanded_eq : @expanded = @familyExpandedArea := by
  funext cfg layout limits ex
  unfold expanded familyExpandedArea
  cases checks : uniformDagChecks ex with
  | error error => rfl
  | ok value =>
    cases value
    have hRe : ({ parents := parentsOf ex.dag, leaves := leafIndex ex.dag } : ReIndex) =
        ReIndex.ofDag ex.dag := by
      unfold ReIndex.ofDag parentsOf parentEdgeLists
      rfl
    have widths := fun facts candidates => funext fun width =>
      (atWidthCached_eq cfg layout limits ex facts (parentsOf ex.dag)
        (ReIndex.ofDag ex.dag) (spineParentLists ex.dag (Prep.ofDag ex.dag).family)
        candidates width checks).trans
      (atWidth_eq cfg layout limits ex facts candidates width (dagOK_of_checks checks))
    simp only [hRe, widths]

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
