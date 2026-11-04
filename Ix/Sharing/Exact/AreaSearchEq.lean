/-
  The area search computes the specification's search, part 6: the component
  step and the component loop. `fastStepA` from cleared position tables is
  `specStep` (`fastStepA_eq`), and `searchComponentsArea` is
  `searchComponentsWith` under the stage's facts (`searchComponentsArea_eq`).
-/
module

public import Ix.Sharing.Exact.AreaBlockEq
import all Ix.Sharing.Exact.Basic
import all Ix.Sharing.Exact.Dag
import all Ix.Sharing.Exact.Dictionary
import all Ix.Sharing.Exact.UniformSearch
import all Ix.Sharing.Exact.UniformSearchLocal
import all Ix.Sharing.Exact.AreaSearch
import all Ix.Sharing.Exact.AreaRowsRel
import all Ix.Sharing.Exact.AreaClosureRows
import all Ix.Sharing.Exact.AreaTruncRows
import all Ix.Sharing.Exact.AreaCostEq
import all Ix.Sharing.Exact.AreaBlockEq

public section

namespace Ix.Sharing.Exact.AreaProof

open Ix.Sharing.Exact
open Ix.Sharing.Exact.LocalSearch (PosFn Ready MembersIn)

/-- **Component search.** -/
theorem searchComponentA_eq {cx : SCtx} {posA posC : Array Nat} (hr : Ready cx posA posC)
    (hm : MembersIn cx posA) (tb : TBase) (aux : AAux) (fb : Unit → SCtx × Array Nat)
    (limits : Limits) (states costEvals : Nat)
    (hphi : ∀ avail stored, phiA (lightCx cx) posA tb aux fb avail stored =
      phiEL2 cx posA posC avail stored)
    (hsep : ∀ g i o, sepCheckA (lightCx cx) posA g i o = sepCheckL cx posA posC g i o) :
    searchComponentA (lightCx cx) posA tb aux fb limits states costEvals =
      searchComponent cx limits states costEvals := by
  rw [← Ix.Sharing.Exact.LocalSearch.searchComponentL_eq hr]
  unfold searchComponentA searchComponentL
  rw [ite_eq_left (show (cx.members.all fun m => (posOf posA m).isSome) = true by
    rw [Array.all_eq_true']
    intro m hmm
    exact hm m (Array.contains_iff_mem.mpr hmm))]
  simp only [(block_eq cx posA posC tb aux fb limits hphi hsep
    (fun o l u => reclassifyA_eq cx posA hr.area o l u)
    (fun o t => opaqueUnderA_eq cx posA hr.area o t)
    (fun o i t => opqArrA_eq cx posA hr.area o i t) _).1] <;> rfl

/-! ## Position tables -/

theorem setPositions_out (pos xs : Array Nat) :
    (setPositions pos xs).size = pos.size ∧
      ∀ u, (∀ i, i < xs.size → xs[i]! ≠ u) → (setPositions pos xs)[u]! = pos[u]! := by
  unfold setPositions
  have key : ∀ m, (foldRange (fun pos j => pos.set! xs[j]! (j + 1)) 0 m pos).size = pos.size ∧
      ∀ u, (∀ i, i < m → xs[i]! ≠ u) →
        (foldRange (fun pos j => pos.set! xs[j]! (j + 1)) 0 m pos)[u]! = pos[u]! := by
    intro m
    induction m with
    | zero => exact ⟨rfl, fun _ _ => rfl⟩
    | succ m ih =>
      rw [Ix.Sharing.Exact.LocalSearch.foldRange_succ, Nat.zero_add]
      refine ⟨by simpa using ih.1, fun u hu => ?_⟩
      rw [getElem!_setBang, ite_eq_right (fun ⟨h1, _⟩ => hu m (by omega) h1.symm)]
      exact ih.2 u (fun i hi => hu i (by omega))
  exact ⟨(key xs.size).1, fun u hu => (key xs.size).2 u hu⟩

/-- Clearing the positions just set leaves all-zero tables, for any terms. -/
theorem clear_set_any (n : Nat) (xs : Array Nat) :
    clearPositions (setPositions (Array.replicate n 0) xs) xs = Array.replicate n 0 := by
  obtain ⟨h1, h2⟩ := setPositions_out (Array.replicate n 0) xs
  apply Ix.Sharing.Exact.LocalSearch.clearPositions_zero _ _ n (by rw [h1]; simp)
  intro u hu
  rw [h2 u hu]
  by_cases h : u < n
  · rw [getElem!_pos _ u (by simpa using h)]; simp
  · rw [getElem!_neg _ u (by simpa using h)]; rfl

/-! ## The constant part -/

theorem foldl_if_add (P : Nat → Bool) (f : Nat → Nat) (l : List Nat) (a : Nat) :
    l.foldl (fun k x => if P x then k + f x else k) a = a + ((l.filter P).map f).sum := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih =>
    simp only [List.foldl_cons, List.filter_cons]
    cases hp : P x
    · simp only [Bool.false_eq_true, ite_false]; exact ih a
    · simp only [ite_true, List.map_cons, List.sum_cons]; rw [ih]; omega

theorem areaK_eq (tb : TBase) (opaq : Array Bool) (roots found vis posA : Array Nat) :
    areaK tb opaq roots found vis posA =
      ((found.toList.filter (fun t => opaq[t]! && posA[t]! == 0)).map (tb.inl[·]!)).sum +
      ((roots.toList.filter (fun r => vis[r]! != 0 && posA[r]! == 0)).map (tb.cost[·]!)).sum := by
  unfold areaK
  have hf : (fun (k t : Nat) => if posA[t]! != 0 then k else if opaq[t]! then k + tb.inl[t]! else k) =
      (fun (k t : Nat) => if (opaq[t]! && posA[t]! == 0) then k + tb.inl[t]! else k) := by
    funext k t
    cases h1 : opaq[t]! <;> cases h2 : (posA[t]! == 0) <;> simp_all
  simp only []
  rw [hf, ← Array.foldl_toList, ← Array.foldl_toList, foldl_if_add, foldl_if_add, Nat.zero_add]

/-! ## The component step -/

theorem localSearchOK_full (cx : SCtx) (h : localSearchOK (lightCx cx) = true)
    (hinc : strictInc cx.closure = true)
    (hlt : ∀ i, i < cx.closure.size → cx.closure[i]! < cx.up.prep.dag.size) :
    localSearchOK cx = true := by
  unfold localSearchOK at h ⊢
  simp only [Bool.and_eq_true] at h ⊢
  obtain ⟨⟨h1, _⟩, _⟩ := h
  refine ⟨⟨h1, hinc⟩, ?_⟩
  · rw [Array.all_eq_true]
    intro i hi
    have := hlt i hi
    rw [getElem!_pos _ i hi] at this
    simpa using this

theorem mkACtx_eq (ex : Expanded) (f : GraphFacts) (up : UPrep) (cand : Array Bool)
    (b0 : UBounds) (vis0 : Array Nat × Array Nat) (rootCount : Array Nat) (slack : Nat)
    (theta : _root_.Int) (baseEv : DictEval) (widthCs : Array (Option Nat)) (allTrue : Array Bool)
    (unc : Array Nat) (members : Array Nat) :
    mkACtx ex f up cand b0 vis0 rootCount slack theta baseEv widthCs allTrue unc members
        (componentArea up f members) =
      lightCx (mkSCtx ex f up cand b0 vis0 rootCount slack theta baseEv widthCs allTrue unc
        members) := by
  unfold mkACtx mkSCtx lightCx
  rfl

/-- The facts of the stage that the area search relies on. -/
structure StageOK (ex : Expanded) (up : UPrep) (baseEv : DictEval) (widthCs : Array (Option Nat))
    (allTrue : Array Bool) : Prop where
  dag : DagOK ex.dag
  prep : up.prep = Prep.ofDag ex.dag
  widths : ∀ u, widthOf widthCs u = if up.opaq[u]! then some up.w else none
  all : allTrue = Array.replicate ex.dag.size true
  base : baseEv = up.prep.eval widthCs allTrue

/-- **One component** of the area loop from cleared position tables is a step
of the specification's loop. -/
theorem fastStepA_eq (limits : Limits) (ex : Expanded) (f : GraphFacts) (up : UPrep)
    (cand : Array Bool) (b0 : UBounds) (vis0 : Array Nat × Array Nat) (rootCount : Array Nat)
    (slack : Nat) (theta : _root_.Int) (baseEv : DictEval) (widthCs : Array (Option Nat))
    (allTrue : Array Bool) (unc : Array Nat) (opaq : Array Bool)
    (hss : limits.uniformSubsetSearch = false) (hst : StageOK ex up baseEv widthCs allTrue)
    (hstage : tStageOK up.prep up.w up.opaq (TBase.ofPrep up.prep up.w up.opaq) = true)
    (a : Array CompResult × Nat × Nat) (members : Array Nat) :
    fastStepA limits ex f up cand b0 vis0 rootCount slack theta baseEv widthCs allTrue unc
        (parentsOf ex.dag) (TBase.ofPrep up.prep up.w up.opaq)
        (a, Array.replicate up.prep.dag.size 0, Array.replicate ex.dag.size 0) members =
      (specStep limits ex f up cand b0 vis0 rootCount slack theta baseEv widthCs allTrue unc opaq
        a members).map
        (fun a => (a, Array.replicate up.prep.dag.size 0, Array.replicate ex.dag.size 0)) := by
  have hn : up.prep.dag.size = ex.dag.size := by rw [hst.prep]; rfl
  have hfast := Ix.Sharing.Exact.LocalSearch.fastStep_eq limits ex f up cand b0 vis0 rootCount
    slack theta baseEv widthCs allTrue unc opaq hss hst.dag.cp a members
  obtain ⟨results, states, costEvals⟩ := a
  unfold fastStepA
  simp only []
  have hclrA := clear_set_any up.prep.dag.size (componentArea up f members)
  split
  · rename_i hmemb
    split
    · rename_i hok
      obtain ⟨hinv, hdone⟩ := Ix.Sharing.Exact.LocalSearch.upWalk_spec ex.dag members
      generalize upWalk (parentsOf ex.dag) members (Array.replicate ex.dag.size 0) = r
        at hinv hdone ⊢
      obtain ⟨vis, found, stack⟩ := r
      have hclrC : clearPositions vis found = Array.replicate ex.dag.size 0 := by
        apply Ix.Sharing.Exact.LocalSearch.clearPositions_zero _ _ _ hinv.size
        intro u hu
        rw [hinv.marks u]
        have hnot : u ∉ found.toList := by
          intro hm
          rw [Array.mem_toList_iff, Array.mem_iff_getElem] at hm
          obtain ⟨i, hi, rfl⟩ := hm
          exact hu i hi (by rw [getElem!_pos _ i hi])
        rw [ite_eq_right hnot]
      simp only []
      split
      · rename_i hwalk
        split
        · rename_i hlok
          rw [hclrA, hclrC]
          rw [mkACtx_eq] at hlok ⊢
          unfold specStep
          simp only [hss, Bool.false_eq_true, ite_false]
          generalize hcx : mkSCtx ex f up cand b0 vis0 rootCount slack theta baseEv widthCs
            allTrue unc members = cx at hlok ⊢
          have hcxUp : cx.up = up := by rw [← hcx]; unfold mkSCtx; rfl
          have hcxArea : cx.area = componentArea up f members := by rw [← hcx]; unfold mkSCtx; rfl
          have hcxClo : cx.closure = upClosure ex.dag ((markTable ex.dag.size members)[·]!) := by
            rw [← hcx]; unfold mkSCtx; rfl
          have hcxMem : cx.members = members := by rw [← hcx]; unfold mkSCtx; rfl
          have hcxRC : cx.rootsC = ex.roots.filter ((markTable ex.dag.size cx.closure)[·]!) := by
            rw [← hcx]; unfold mkSCtx; rfl
          have hcxSC : cx.storedInC = cx.closure.filter (cx.up.opaq[·]!) := by
            rw [← hcx]; unfold mkSCtx; rfl
          have hcxW : cx.widthCs = widthCs := by rw [← hcx]; unfold mkSCtx; rfl
          have hcxT : cx.allTrue = allTrue := by rw [← hcx]; unfold mkSCtx; rfl
          have hcxB : cx.baseEv = baseEv := by rw [← hcx]; unfold mkSCtx; rfl
          clear hcx hfast
          subst hcxUp hcxMem hcxW hcxT hcxB
          rw [← hcxArea] at hok hwalk hclrA ⊢
          have hpd : cx.up.prep.dag = ex.dag := by rw [hst.prep]; rfl
          have hdagP : DagOK cx.up.prep.dag := by rw [hpd]; exact hst.dag
          -- the area and its positions
          unfold areaOK at hok
          rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hok
          obtain ⟨⟨⟨hA1, hA2⟩, hA3⟩, hA4⟩ := hok
          have hA2' := Array.all_eq_true'.mp hA2
          have hA3' := Array.all_eq_true'.mp hA3
          have hA4' := Array.all_eq_true'.mp hA4
          have hareaN : ∀ i, i < cx.area.size → cx.area[i]! < cx.up.prep.dag.size := by
            intro i hi
            have := hA2' _ (Array.mem_toList_iff.mp (Ix.Sharing.Exact.LocalSearch.mem_of_getElem! hi))
            rw [hn]
            simpa using this
          have hposA := Ix.Sharing.Exact.LocalSearch.setPositions_posFn cx.area
            cx.up.prep.dag.size hA1 hareaN
          generalize setPositions (Array.replicate cx.up.prep.dag.size 0) cx.area = posA
            at hposA hA3' hA4' ⊢
          have hInA : ∀ u, InA cx.area u ↔ posA[u]! ≠ 0 := by
            intro u
            constructor
            · rintro ⟨j, hj, hju⟩
              have := (hposA u j).mpr ⟨hj, hju⟩
              rw [Ix.Sharing.Exact.LocalSearch.posOf_some] at this
              omega
            · intro hne
              obtain ⟨k, hk⟩ : ∃ k, posA[u]! = k + 1 := ⟨posA[u]! - 1, by omega⟩
              have := (hposA u k).mp ((Ix.Sharing.Exact.LocalSearch.posOf_some posA u k).mpr hk)
              exact ⟨k, this.1, this.2⟩
          have hareaLt : ∀ y, InA cx.area y → y < ex.dag.size := by
            rintro y ⟨j, hj, rfl⟩
            rw [← hn]; exact hareaN j hj
          -- the closure walk
          rw [Bool.and_eq_true] at hwalk
          obtain ⟨hstk, hAv⟩ := hwalk
          have hstk' : stack.toList = [] := by
            rw [Array.isEmpty_iff] at hstk; subst hstk; rfl
          have hfound := hdone hstk'
          have hCmem := Ix.Sharing.Exact.LocalSearch.mem_upClosure hst.dag.cp
            ((markTable ex.dag.size cx.members)[·]!)
          have hfC : ∀ t, t ∈ found.toList ↔ t ∈ cx.closure.toList := fun t =>
            (hfound t).trans (by rw [hcxClo]; exact (hCmem t).symm)
          have hCs : cx.closure.toList.Pairwise (· < ·) := by
            rw [hcxClo]; exact Ix.Sharing.Exact.LocalSearch.upClosure_sorted _ _
          have hCinc := Ix.Sharing.Exact.LocalSearch.strictInc_of_sorted hCs
          have hClt' : ∀ x ∈ cx.closure.toList, x < ex.dag.size := by
            rw [hcxClo]; intro x hx; exact ((hCmem x).mp hx).lt
          have hCin : ∀ i, i < cx.closure.size → cx.closure[i]! < ex.dag.size := fun i hi =>
            hClt' _ (Ix.Sharing.Exact.LocalSearch.mem_of_getElem! hi)
          have hposC := Ix.Sharing.Exact.LocalSearch.setPositions_posFn cx.closure
            ex.dag.size hCinc hCin
          have hlokF := localSearchOK_full cx hlok hCinc (fun i hi => by rw [hn]; exact hCin i hi)
          have hr : Ready cx posA (setPositions (Array.replicate ex.dag.size 0) cx.closure) :=
            ⟨hlokF, hposA, hposC⟩
          -- the members, the closure of the area, and the area inside the closure
          have hmem : ∀ m, cx.members.contains m = true → InA cx.area m ∧ cx.up.opaq[m]! = false := by
            intro m hm
            have hmm := Array.contains_iff_mem.mp hm
            have h1 := Array.all_eq_true'.mp hmemb m hmm
            have h3 := hA3' m hmm
            simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h1
            exact ⟨(hInA m).mpr (by simpa using h3), h1.2⟩
          have hm : MembersIn cx posA := by
            intro m hc
            have h3 := hA3' m (Array.contains_iff_mem.mp hc)
            have hne : posA[m]! ≠ 0 := by simpa using h3
            unfold posOf
            simp [hne]
          have hclose : ∀ y q, InA cx.area y → cx.up.opaq[y]! = false → q < ex.dag.size →
              y ∈ (ex.dag.node q).children → InA cx.area q := by
            intro y q hy hyo hq hc
            have hy' : y ∈ cx.area := Array.mem_toList_iff.mp (inA_iff_mem.mp hy)
            have h4 := hA4' y hy'
            rw [hyo, Bool.false_or] at h4
            have hqP : q ∈ (parentsOf ex.dag)[y]! :=
              (Ix.Sharing.Exact.LocalSearch.mem_parentsOf ex.dag y q).mpr ⟨hareaLt y hy, hq, hc⟩
            have h5 := Array.all_eq_true'.mp h4 q hqP
            exact (hInA q).mpr (by simpa using h5)
          have hAinC : ∀ y, InA cx.area y → y ∈ cx.closure.toList := by
            intro y hy
            have hy' : y ∈ cx.area := Array.mem_toList_iff.mp (inA_iff_mem.mp hy)
            have hv := Array.all_eq_true'.mp hAv y hy'
            rw [hinv.marks y] at hv
            by_cases hf : y ∈ found.toList
            · exact (hfC y).mp hf
            · rw [ite_eq_right hf] at hv; simp at hv
          -- the closure's size and the constant part
          have hperm : found.toList.Perm cx.closure.toList :=
            (List.perm_ext_iff_of_nodup hinv.nodup (hCs.imp Nat.ne_of_lt)).mpr hfC
          have hcs : found.size = cx.closure.size := by simpa using hperm.length_eq
          have hvisC : ∀ r : Nat, (vis[r]! != 0) = (markTable ex.dag.size cx.closure)[r]! := by
            intro r
            rw [hinv.marks r, Ix.Sharing.Exact.LocalSearch.markTable_read]
            by_cases hf : r ∈ found.toList
            · rw [ite_eq_left hf]
              have hc := (hfC r).mp hf
              have hlt := hClt' r hc
              simp [hlt, Array.mem_toList_iff.mp hc]
            · rw [ite_eq_right hf]
              have hnc : r ∉ cx.closure := fun h => hf ((hfC r).mpr (Array.mem_toList_iff.mpr h))
              simp [hnc]
          have hK : areaK (TBase.ofPrep cx.up.prep cx.up.w cx.up.opaq) cx.up.opaq ex.roots found
              vis posA =
              ((ex.roots.toList.filter (fun r => (markTable ex.dag.size cx.closure)[r]! &&
                posA[r]! == 0)).map ((TBase.ofPrep cx.up.prep cx.up.w cx.up.opaq).cost[·]!)).sum +
              ((cx.closure.toList.filter (fun c => cx.up.opaq[c]! && posA[c]! == 0)).map
                ((TBase.ofPrep cx.up.prep cx.up.w cx.up.opaq).inl[·]!)).sum := by
            rw [areaK_eq, sum_perm (hperm.filter _)]
            simp only [hvisC]
            omega
          have hclose' : ∀ y q, InA cx.area y → cx.up.opaq[y]! = false →
              q < cx.up.prep.dag.size → y ∈ (cx.up.prep.dag.node q).children → InA cx.area q := by
            rw [hpd]; exact hclose
          rw [searchComponentA_eq hr hm _ _ _ limits states costEvals
            (fun avail stored => phiA_eq ex cx (lightCx cx) posA _ _ _ _ hst.dag hst.prep hcxClo
              hcxRC hcxSC hst.widths hst.all hst.base rfl hstage hr hmem hclose hAinC hcs hK rfl
              rfl rfl rfl avail stored)
            (fun g i o => sepCheckA_eq hr hdagP hmem hclose'
              (fun y hy => inA_iff_mem.mpr (hAinC y hy)) g i o)]
          cases searchComponent cx limits states costEvals with
          | error e => rfl
          | ok v => rfl
        · rw [hclrA, hclrC]; exact hfast
      · rw [hclrA, hclrC]; exact hfast
    · rw [hclrA]; exact hfast
  · exact hfast

/-- **The area loop** computes the component loop, given the stage's facts. -/
theorem searchComponentsArea_eq (limits : Limits) (ex : Expanded) (f : GraphFacts) (up : UPrep)
    (cand : Array Bool) (b0 : UBounds) (vis0 : Array Nat × Array Nat) (rootCount : Array Nat)
    (slack : Nat) (theta : _root_.Int) (baseEv : DictEval) (widthCs : Array (Option Nat))
    (allTrue : Array Bool) (unc : Array Nat) (opaq : Array Bool) (comps : Array (Array Nat))
    (hst : StageOK ex up baseEv widthCs allTrue) :
    searchComponentsArea limits ex f up cand b0 vis0 rootCount slack theta baseEv widthCs allTrue
        unc opaq comps =
      searchComponentsWith limits ex f up cand b0 vis0 rootCount slack theta baseEv widthCs
        allTrue unc opaq comps := by
  unfold searchComponentsArea
  split
  · rw [← searchComponentsWith_eq_fast]
  · rename_i hg
    simp only [Bool.or_eq_true, Bool.not_eq_true', not_or, Bool.not_eq_false] at hg
    obtain ⟨hss, _⟩ := hg
    simp only []
    split
    · rw [← searchComponentsWith_eq_fast]
    · rename_i hstage
      simp only [Bool.not_eq_true', Bool.not_eq_false] at hstage
      unfold searchComponentsWith
      rw [← Array.foldlM_toList, ← Array.foldlM_toList]
      have key := Ix.Sharing.Exact.LocalSearch.foldlM_sim
        (specStep limits ex f up cand b0 vis0 rootCount slack theta baseEv widthCs allTrue unc opaq)
        (fastStepA limits ex f up cand b0 vis0 rootCount slack theta baseEv widthCs allTrue unc
          (parentsOf ex.dag) (TBase.ofPrep up.prep up.w up.opaq))
        (fun a => (a, Array.replicate up.prep.dag.size 0, Array.replicate ex.dag.size 0))
        (fastStepA_eq limits ex f up cand b0 vis0 rootCount slack theta baseEv widthCs allTrue unc
          opaq (by simpa using hss) hst (by simpa using hstage)) comps.toList
        ((#[] : Array CompResult), 0, 0)
      rw [key]
      cases List.foldlM (specStep limits ex f up cand b0 vis0 rootCount slack theta baseEv
        widthCs allTrue unc opaq) ((#[] : Array CompResult), 0, 0) comps.toList <;> rfl

end Ix.Sharing.Exact.AreaProof

end
