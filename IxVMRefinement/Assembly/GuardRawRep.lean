import IxVMRefinement.Subst.Steps
import IxVMRefinement.Levels.Smart
import IxVMRefinement.Obs.KernelGuard0

/-! # Representation preservation by the structural classifier's substitution

These lemmas only produce a represented output. They do not identify a canonical substituted
expression, assert a typing judgement, or claim that a data beta step is a licensed reduction.
-/

namespace IxVM.Refinement.Core.GuardData

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.KernelLevels (RepKLevel RepKLevelList)

set_option maxHeartbeats 2400000

private theorem level_rep_go :
    ∀ fuel : Nat, ∀ {l : KLevel} {ls : List KLevel} {p params r : SourceValue F}
      {h h' : Heap F} {cs : List (Call F)},
      cs.length ≤ fuel → RepKLevel h l p → RepKLevelList h ls params →
      ObsFn W "KernelGuard::level_inst_raw" [p, params] h r h' cs →
      ∃ l', RepKLevel h' l' r := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
    intro l ls p params r h h' cs hlen hl hp ev
    match Obs.«KernelGuard::level_inst_raw».obs ev with
    | .Zero (he21 := hr) (he22 := hh) .. =>
      subst hr hh
      exact ⟨l, hl⟩
    | .Succ (cs54 := children) (ld12 := ld) (he40 := hr) (hm39 := hh)
        (ev56 := child) (hc73 := hc) .. =>
      obtain ⟨u, -, hu⟩ := Levels.rep_succ_of_load hl ld
      have hlt : children.length < fuel := by rw [hc] at hlen; simp only [List.length_cons] at hlen; omega
      obtain ⟨u', hu'⟩ := ih children.length hlt (Nat.le_refl _) hu hp child
      subst hr hh
      exact ⟨.succ u', (RepKLevel.allocSucc hu').1⟩
    | .Max (cs110 := first) (cs138 := second) (ld12 := ld) (he95 := hr) (hm94 := hh)
        (ev112 := e1) (ev140 := e2) (hc157 := hc) .. =>
      obtain ⟨u, v, -, hu, hv⟩ := Levels.rep_max_of_load hl ld
      have h1 : first.length < fuel := by rw [hc] at hlen; simp only [List.length_cons, List.length_append] at hlen; omega
      have h2 : second.length < fuel := by rw [hc] at hlen; simp only [List.length_cons, List.length_append] at hlen; omega
      obtain ⟨u', hu'⟩ := ih first.length h1 (Nat.le_refl _) hu hp e1
      obtain ⟨v', hv'⟩ := ih second.length h2 (Nat.le_refl _)
        (hv.mono e1.heap_extends) (hp.mono e1.heap_extends) e2
      subst hr hh
      exact ⟨.max u' v', (RepKLevel.allocMax (hu'.mono e2.heap_extends) hv').1⟩
    | .IMax (cs194 := first) (cs222 := second) (ld12 := ld) (he179 := hr) (hm178 := hh)
        (ev196 := e1) (ev224 := e2) (hc241 := hc) .. =>
      obtain ⟨u, v, -, hu, hv⟩ := Levels.rep_imax_of_load hl ld
      have h1 : first.length < fuel := by rw [hc] at hlen; simp only [List.length_cons, List.length_append] at hlen; omega
      have h2 : second.length < fuel := by rw [hc] at hlen; simp only [List.length_cons, List.length_append] at hlen; omega
      obtain ⟨u', hu'⟩ := ih first.length h1 (Nat.le_refl _) hu hp e1
      obtain ⟨v', hv'⟩ := ih second.length h2 (Nat.le_refl _)
        (hv.mono e1.heap_extends) (hp.mono e1.heap_extends) e2
      subst hr hh
      exact ⟨.imax u' v', (RepKLevel.allocIMax (hu'.mono e2.heap_extends) hv').1⟩
    | .Param (ld12 := ld) (ev259 := lookup) .. =>
      obtain ⟨i, -, hi, -⟩ := Levels.rep_param_of_load' hl ld
      rw [hi] at lookup
      have ev' : ObsFn W (Instance.mk "Lists::lookup" [(.ptr (.named "KernelTypes::KLevelNode" []))]).symbol
          [params, .field (i : F)] h r h' _ := by
        simpa only [Obs.Names.«Lists::lookup<&KernelTypes::KLevelNode>».symbol] using lookup
      have hp' : RepList (Instance.mk "Lists::Node" [(.ptr (.named "KernelTypes::KLevelNode" []))]).symbol
          RepKLevel h ls params := by
        simpa only [Obs.Names.«Lists::Node<&KernelTypes::KLevelNode>».symbol] using hp
      obtain ⟨⟨l', -, hr⟩, rfl⟩ := Lib.Lists.lookup_spec ev' hp'
      exact ⟨l', hr⟩

/-- Raw level substitution preserves representation whenever its execution succeeds. -/
theorem level_inst_raw_rep {l : KLevel} {ls : List KLevel} {p params r : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)} (hl : RepKLevel h l p)
    (hp : RepKLevelList h ls params)
    (ev : ObsFn W "KernelGuard::level_inst_raw" [p, params] h r h' cs) :
    ∃ l', RepKLevel h' l' r :=
  level_rep_go cs.length (Nat.le_refl _) hl hp ev

private theorem levels_rep_go :
    ∀ fuel : Nat, ∀ {ls ps : List KLevel} {p params r : SourceValue F}
      {h h' : Heap F} {cs : List (Call F)},
      cs.length ≤ fuel → RepKLevelList h ls p → RepKLevelList h ps params →
      ObsFn W "KernelGuard::levels_inst_raw" [p, params] h r h' cs →
      ∃ ls', RepKLevelList h' ls' r := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
    intro ls ps p params r h h' cs hlen hl hp ev
    match Obs.«KernelGuard::levels_inst_raw».obs ev with
    | .Nil (he21 := hr) (he22 := hh) .. =>
      subst hr hh
      exact ⟨ls, hl⟩
    | .Cons (cs88 := children) (ld12 := ld) (he45 := hr) (hm44 := hh)
        (ev62 := e1) (ev90 := e2) (hc107 := hc) .. =>
      obtain ⟨l, rest, -, h1, h2⟩ := rep_cons_of_load hl ld
      obtain ⟨l', h1'⟩ := level_inst_raw_rep h1 hp e1
      have hlt : children.length < fuel := by rw [hc] at hlen; simp only [List.length_cons, List.length_append] at hlen; omega
      obtain ⟨rest', h2'⟩ := ih children.length hlt (Nat.le_refl _)
        (h2.mono e1.heap_extends) (hp.mono e1.heap_extends) e2
      subst hr hh
      exact ⟨l' :: rest', (RepKLevelList.allocCons (h1'.mono e2.heap_extends) h2').1⟩

/-- Raw substitution through a list of levels preserves its represented list. -/
theorem levels_inst_raw_rep {ls ps : List KLevel} {p params r : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)} (hl : RepKLevelList h ls p)
    (hp : RepKLevelList h ps params)
    (ev : ObsFn W "KernelGuard::levels_inst_raw" [p, params] h r h' cs) :
    ∃ ls', RepKLevelList h' ls' r :=
  levels_rep_go cs.length (Nat.le_refl _) hl hp ev

end IxVM.Refinement.Core.GuardData
