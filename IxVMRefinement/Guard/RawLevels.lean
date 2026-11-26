import IxVMRefinement.Nat.Levels
import IxVM.Obs.KernelGuard

/-! # Exact raw universe substitution for the guard classifier

Unlike the normalizing universe helper, these functions preserve Max/IMax syntax. Successful
parameter lookups themselves establish that every substituted parameter is in the supplied list.
No caller-supplied parameter-coverage premise is needed.
-/

namespace IxVM.Refinement.Guard

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM (F)
open Core (W)
open Core.LevelsAux
open _root_.IxVM.Refinement.KernelLevels
open Ix.Kernel (Level)

/-- Positional substitution without smart universe constructors. -/
def rawSubst (params : List Level) : Level → Level
  | .zero => .zero
  | .succ u => .succ (rawSubst params u)
  | .max u v => .max (rawSubst params u) (rawSubst params v)
  | .imax u v => .imax (rawSubst params u) (rawSubst params v)
  | .param i => params[i]?.getD (.param i)

private theorem subst_go_range (params : List Level) (i : Nat) :
    Level.subst.go (List.range params.length) params i = params[i]?.getD (.param i) := by
  have H : ∀ (k : Nat) (ps : List Level),
      Level.subst.go ((List.range ps.length).map (· + k)) ps i =
        if k ≤ i then ps[i - k]?.getD (.param i) else .param i := by
    intro k ps
    induction ps generalizing k with
    | nil => simp [Level.subst.go]
    | cons p ps ih =>
      rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
      have hmap : ((· + k) ∘ Nat.succ) = (· + (k + 1)) := by
        funext x; simp [Function.comp]; omega
      rw [hmap, Nat.zero_add]
      simp only [Level.subst.go]
      by_cases hki : k = i
      · subst hki; simp
      · simp only [hki, ↓reduceIte, ih (k + 1)]
        by_cases hle : k + 1 ≤ i
        · have hle' : k ≤ i := by omega
          have hsub : i - k = (i - (k + 1)) + 1 := by omega
          simp [hle, hle', hsub]
        · have hle' : ¬ k ≤ i := by omega
          simp [hle, hle']
  simpa using H 0 params

/-- The raw operation is the kernel's literal positional substitution, not only level equivalent. -/
theorem rawSubst_eq (params : List Level) (u : Level) :
    rawSubst params u = Level.subst (List.range params.length) params u := by
  induction u with
  | zero => rfl
  | succ u ih => simp only [rawSubst, Level.subst, ih]
  | max u v ihu ihv => simp only [rawSubst, Level.subst, ihu, ihv]
  | imax u v ihu ihv => simp only [rawSubst, Level.subst, ihu, ihv]
  | param i => exact (subst_go_range params i).symm

/-- Actual raw level instantiation returns the exact substituted syntax and produces coverage
of every parameter it visited. -/
theorem level_inst_raw_spec {p pp r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    {l : Level} {params : List Level}
    (ev : ObsFn W "KernelGuard::level_inst_raw" [p, pp] h r h' cs)
    (rep : RepKLevel h l p) (repPs : RepKLevelList h params pp) :
    ParamsLt params.length l ∧ RepKLevel h' (rawSubst params l) r := by
  cases Obs.«KernelGuard::level_inst_raw».obs ev with
  | Zero ld hr hh hc =>
    obtain rfl := zero_of_load rep ld
    subst hr hh
    exact ⟨trivial, rep⟩
  | Succ x v m cs' ld hr hh ev' hc =>
    obtain ⟨u, rfl, hu⟩ := succ_of_load rep ld
    obtain ⟨hpu, repU⟩ := level_inst_raw_spec ev' hu repPs
    subst hr hh
    exact ⟨hpu, .succ List.getElem?_concat_length (repU.mono (Heap.Extends.snoc _ _))⟩
  | Max a b va vb ma csa mb csb ld hr hh eva evb hc =>
    obtain ⟨u, v, rfl, hu, hv⟩ := max_of_load rep ld
    obtain ⟨hpu, repU⟩ := level_inst_raw_spec eva hu repPs
    obtain ⟨hpv, repV⟩ := level_inst_raw_spec evb (hv.mono eva.heap_extends)
      (repPs.mono eva.heap_extends)
    subst hr hh
    exact ⟨⟨hpu, hpv⟩, .max List.getElem?_concat_length
      (repU.mono (evb.heap_extends.trans (Heap.Extends.snoc _ _)))
      (repV.mono (Heap.Extends.snoc _ _))⟩
  | IMax a b va vb ma csa mb csb ld hr hh eva evb hc =>
    obtain ⟨u, v, rfl, hu, hv⟩ := imax_of_load rep ld
    obtain ⟨hpu, repU⟩ := level_inst_raw_spec eva hu repPs
    obtain ⟨hpv, repV⟩ := level_inst_raw_spec evb (hv.mono eva.heap_extends)
      (repPs.mono eva.heap_extends)
    subst hr hh
    exact ⟨⟨hpu, hpv⟩, .imax List.getElem?_concat_length
      (repU.mono (evb.heap_extends.trans (Heap.Extends.snoc _ _)))
      (repV.mono (Heap.Extends.snoc _ _))⟩
  | Param idx cs' ld ev' hc =>
    obtain ⟨i, rfl, hi, rfl⟩ := param_of_load rep ld
    rw [← Obs.Names.«Lists::lookup<&KernelTypes::KLevelNode>».symbol] at ev'
    obtain ⟨u, hu, hru, rfl⟩ := listsLookup_refines hi repPs ev'.erase
    refine ⟨(List.getElem?_eq_some_iff.mp hu).1, ?_⟩
    simpa only [rawSubst, hu, Option.getD_some] using hru
termination_by cs.length
decreasing_by all_goals (rw [hc]; simp only [List.length_cons, List.length_append]; omega)

/-- The exact level-list operation, with coverage produced elementwise from its run. -/
theorem levels_inst_raw_spec {p pp r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    {ls params : List Level}
    (ev : ObsFn W "KernelGuard::levels_inst_raw" [p, pp] h r h' cs)
    (rep : RepKLevelList h ls p) (repPs : RepKLevelList h params pp) :
    (∀ l ∈ ls, ParamsLt params.length l) ∧ RepKLevelList h' (ls.map (rawSubst params)) r := by
  cases Obs.«KernelGuard::levels_inst_raw».obs ev with
  | Nil ld hr hh hc =>
    rw [← Levels.klevelList_names] at ld
    obtain rfl := Lib.rep_nil_of_load rep ld
    subst hr hh
    exact ⟨by simp, rep⟩
  | Cons x rest vx vr mx csx mr csr ld hr hh evx evr hc =>
    rw [← Levels.klevelList_names] at ld
    obtain ⟨l, ls', rfl, hl, hls⟩ := Lib.rep_cons_of_load rep ld
    obtain ⟨hpl, hrl⟩ := level_inst_raw_spec evx hl repPs
    obtain ⟨hpls, hrls⟩ := levels_inst_raw_spec evr (RepKLevelList.mono hls evx.heap_extends)
      (repPs.mono evx.heap_extends)
    subst hr hh
    refine ⟨?_, ?_⟩
    · intro l' hl'
      rcases List.mem_cons.mp hl' with rfl | hmem
      · exact hpl
      · exact hpls l' hmem
    · rw [← Levels.klevelList_names]
      exact .cons List.getElem?_concat_length
        (hrl.mono (evr.heap_extends.trans (Heap.Extends.snoc _ _)))
        (RepKLevelList.mono hrls (Heap.Extends.snoc _ _))
termination_by cs.length
decreasing_by all_goals (rw [hc]; simp only [List.length_cons, List.length_append]; omega)

end IxVM.Refinement.Guard
