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
    | .Param (cs257 := lookupCalls) (ld12 := ld) (ev259 := lookup) .. =>
      obtain ⟨i, -, hi, -⟩ := Levels.rep_param_of_load' hl ld
      rw [hi] at lookup
      have ev' : ObsFn W (Instance.mk "Lists::lookup" [(.ptr (.named "KernelTypes::KLevelNode" []))]).symbol
          [params, .field (i : F)] h r h' lookupCalls := by
        simpa only [Obs.Names.«Lists::lookup<&KernelTypes::KLevelNode>».symbol] using lookup
      have hp' : RepList (Instance.mk "Lists::Node" [(.ptr (.named "KernelTypes::KLevelNode" []))]).symbol
          RepKLevel h ls params := by
        simpa only [RepKLevelList, Levels.klevelList_names,
          Obs.Names.«Lists::Node<&KernelTypes::KLevelNode>».symbol] using hp
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
      have ld' := ld
      rw [← Levels.klevelList_names] at ld'
      obtain ⟨l, rest, -, h1, h2⟩ := Lib.rep_cons_of_load hl ld'
      obtain ⟨l', h1'⟩ := level_inst_raw_rep h1 hp e1
      have hlt : children.length < fuel := by rw [hc] at hlen; simp only [List.length_cons, List.length_append] at hlen; omega
      obtain ⟨rest', h2'⟩ := ih children.length hlt (Nat.le_refl _)
        (RepKLevelList.mono h2 e1.heap_extends) (hp.mono e1.heap_extends) e2
      subst hr hh
      exact ⟨l' :: rest', by
        simpa only [Levels.klevelList_names] using
          (RepKLevelList.allocCons (h1'.mono e2.heap_extends) h2').1⟩

/-- Raw substitution through a list of levels preserves its represented list. -/
theorem levels_inst_raw_rep {ls ps : List KLevel} {p params r : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)} (hl : RepKLevelList h ls p)
    (hp : RepKLevelList h ps params)
    (ev : ObsFn W "KernelGuard::levels_inst_raw" [p, params] h r h' cs) :
    ∃ ls', RepKLevelList h' ls' r :=
  levels_rep_go cs.length (Nat.le_refl _) hl hp ev

private def rawExprName (walk : Bool) : String :=
  if walk then "KernelGuard::expr_inst_raw_walk" else "KernelGuard::expr_inst_raw"

private theorem expr_rep_go (κ : _root_.Address → KKey) :
    ∀ fuel : Nat, ∀ (walk : Bool) {d k : Nat} {Γ : Nat → KExpr} {E : KExpr}
      {ps : List KLevel} {p params r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      cs.length ≤ fuel → Tm κ d Γ h k E p → RepKLevelList h ps params →
      ObsFn W (rawExprName walk) [p, params] h r h' cs →
      ∃ E', Tm κ d Γ h' k E' r := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
    intro walk d k Γ E ps p params r h h' cs hlen hE hp ev
    cases walk with
    | false =>
      change ObsFn W "KernelGuard::expr_inst_raw" [p, params] h r h' cs at ev
      match Obs.«KernelGuard::expr_inst_raw».obs ev with
      | .Nil (he21 := hr) (he22 := hh) .. =>
        subst hr hh
        exact ⟨E, hE⟩
      | .other (cs31 := children) (ev33 := child) (hc50 := hc) .. =>
        have hlt : children.length < fuel := by rw [hc] at hlen; simp only [List.length_cons] at hlen; omega
        exact ih children.length hlt true (Nat.le_refl _) hE hp child
    | true =>
      change ObsFn W "KernelGuard::expr_inst_raw_walk" [p, params] h r h' cs at ev
      match Obs.«KernelGuard::expr_inst_raw_walk».obs ev with
      | .BVar (he27 := hr) (he28 := hh) .. | .Lit (he595 := hr) (he596 := hh) .. =>
        subst hr hh
        exact ⟨E, hE⟩
      | .Srt (ld12 := ld) (he46 := hr) (hm45 := hh) (ev62 := child) .. =>
        obtain ⟨u, rfl, l, hl, -⟩ := hE.sort_of_load ld
        obtain ⟨l', hl'⟩ := level_inst_raw_rep hl hp child
        subst hr hh
        exact ⟨.sort l', SubstAux.tm_store_sort hl' (LvEq.refl _)⟩
      | .Const (ld12 := ld) (he101 := hr) (hm100 := hh) (ev125 := child) .. =>
        obtain ⟨a, us, rfl, ha, ls, hls, -⟩ := hE.const_of_load ld
        have : Resolved (κ (ixAddr a)) := ⟨hE.const_key_ne⟩
        obtain ⟨ls', hls'⟩ := levels_inst_raw_rep hls hp child
        subst hr hh
        exact ⟨.const (κ (ixAddr a)) ls',
          SubstAux.tm_store_const (Bytes.repAddressRef_heapMono₂ addrTy child.heap_extends ha)
            hls' (LvEqList.refl _)⟩
      | .App (cs179 := first) (cs207 := second) (ld12 := ld) (he164 := hr) (hm163 := hh)
          (ev181 := e1) (ev209 := e2) (hc226 := hc) .. =>
        obtain ⟨f, a, rfl, hf, ha⟩ := hE.app_of_load ld
        have h1 : first.length < fuel := by rw [hc] at hlen; simp only [List.length_cons, List.length_append] at hlen; omega
        have h2 : second.length < fuel := by rw [hc] at hlen; simp only [List.length_cons, List.length_append] at hlen; omega
        obtain ⟨f', hf'⟩ := ih first.length h1 false (Nat.le_refl _) hf hp e1
        obtain ⟨a', ha'⟩ := ih second.length h2 false (Nat.le_refl _)
          (ha.mono e1.heap_extends) (hp.mono e1.heap_extends) e2
        subst hr hh
        exact ⟨.app f' a', Tm.store_app (hf'.mono e2.heap_extends) ha'⟩
      | .Lam (cs269 := first) (cs297 := second) (ld12 := ld) (he253 := hr) (hm252 := hh)
          (ev271 := e1) (ev299 := e2) (ev327 := e3) (hc344 := hc) .. =>
        obtain ⟨T, B, l, rfl, hT, hB, hl⟩ := hE.lam_of_load ld
        have h1 : first.length < fuel := by rw [hc] at hlen; simp only [List.length_cons, List.length_append] at hlen; omega
        have h2 : second.length < fuel := by rw [hc] at hlen; simp only [List.length_cons, List.length_append] at hlen; omega
        obtain ⟨T', hT'⟩ := ih first.length h1 false (Nat.le_refl _) hT hp e1
        obtain ⟨B', hB'⟩ := ih second.length h2 false (Nat.le_refl _)
          (hB.mono e1.heap_extends) (hp.mono e1.heap_extends) e2
        have ext := e1.heap_extends.trans e2.heap_extends
        obtain ⟨l', hl'⟩ := level_inst_raw_rep (hl.mono ext) (hp.mono ext) e3
        subst hr hh
        exact ⟨.lam T' B' (bmeta l'),
          SubstAux.tm_store_lam (hT'.mono (e2.heap_extends.trans e3.heap_extends))
            (hB'.mono e3.heap_extends) hl'⟩
      | .Forall (cs387 := first) (cs415 := second) (ld12 := ld) (he371 := hr) (hm370 := hh)
          (ev389 := e1) (ev417 := e2) (ev445 := e3) (hc462 := hc) .. =>
        obtain ⟨T, B, l, rfl, hT, hB, hl⟩ := hE.forallE_of_load ld
        have h1 : first.length < fuel := by rw [hc] at hlen; simp only [List.length_cons, List.length_append] at hlen; omega
        have h2 : second.length < fuel := by rw [hc] at hlen; simp only [List.length_cons, List.length_append] at hlen; omega
        obtain ⟨T', hT'⟩ := ih first.length h1 false (Nat.le_refl _) hT hp e1
        obtain ⟨B', hB'⟩ := ih second.length h2 false (Nat.le_refl _)
          (hB.mono e1.heap_extends) (hp.mono e1.heap_extends) e2
        have ext := e1.heap_extends.trans e2.heap_extends
        obtain ⟨l', hl'⟩ := level_inst_raw_rep (hl.mono ext) (hp.mono ext) e3
        subst hr hh
        exact ⟨.forallE T' B' (bmeta l'),
          SubstAux.tm_store_forallE (hT'.mono (e2.heap_extends.trans e3.heap_extends))
            (hB'.mono e3.heap_extends) hl'⟩
      | .Let (cs505 := first) (cs533 := second) (cs561 := third) (ld12 := ld)
          (he489 := hr) (hm488 := hh) (ev507 := e1) (ev535 := e2) (ev563 := e3) (hc580 := hc) .. =>
        obtain ⟨T, V, B, rfl, hT, hV, hB⟩ := hE.letE_of_load ld
        have h1 : first.length < fuel := by rw [hc] at hlen; simp only [List.length_cons, List.length_append] at hlen; omega
        have h2 : second.length < fuel := by rw [hc] at hlen; simp only [List.length_cons, List.length_append] at hlen; omega
        have h3 : third.length < fuel := by rw [hc] at hlen; simp only [List.length_cons, List.length_append] at hlen; omega
        obtain ⟨T', hT'⟩ := ih first.length h1 false (Nat.le_refl _) hT hp e1
        obtain ⟨V', hV'⟩ := ih second.length h2 false (Nat.le_refl _)
          (hV.mono e1.heap_extends) (hp.mono e1.heap_extends) e2
        have ext := e1.heap_extends.trans e2.heap_extends
        obtain ⟨B', hB'⟩ := ih third.length h3 false (Nat.le_refl _)
          (hB.mono ext) (hp.mono ext) e3
        subst hr hh
        exact ⟨instShift V' 0 B',
          SubstAux.tm_store_letE (hT'.mono (e2.heap_extends.trans e3.heap_extends))
            (hV'.mono e3.heap_extends) hB'⟩
      | .Proj (cs654 := children) (ld12 := ld) (he624 := hr) (hm623 := hh)
          (ev656 := child) (hc673 := hc) .. =>
        obtain ⟨a, i, E, rfl, rfl, ha, hE'⟩ := hE.proj_of_load ld
        have : Resolved (κ (ixAddr a)) := ⟨hE.proj_key_ne⟩
        have : ProjPermitted κ (ixAddr a) := hE.proj_permitted ld ha
        have hlt : children.length < fuel := by rw [hc] at hlen; simp only [List.length_cons] at hlen; omega
        obtain ⟨E', hE''⟩ := ih children.length hlt false (Nat.le_refl _) hE' hp child
        subst hr hh
        exact ⟨.proj (κ (ixAddr a)) i.val E',
          SubstAux.tm_store_proj (Bytes.repAddressRef_heapMono₂ addrTy child.heap_extends ha) hE''⟩

/-- The classifier's raw expression substitution returns a represented expression. This weak
statement deliberately does not identify the result with a canonical substituted AST. -/
theorem expr_inst_raw_rep {κ : _root_.Address → KKey} {d k : Nat} {Γ : Nat → KExpr} {E : KExpr}
    {ps : List KLevel} {p params r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hE : Tm κ d Γ h k E p) (hp : RepKLevelList h ps params)
    (ev : ObsFn W "KernelGuard::expr_inst_raw" [p, params] h r h' cs) :
    ∃ E', Tm κ d Γ h' k E' r :=
  expr_rep_go κ cs.length false (Nat.le_refl _) hE hp ev

end IxVM.Refinement.Core.GuardData
