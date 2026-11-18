import IxVMRefinement.Assembly.GuardRawRep
import IxVMRefinement.Guard.RawLevels
import IxVMRefinement.Subst.Spine
import IxVMRefinement.Core.Det

/-! # The classifier's raw level substitution, as a function at the term seam

`KernelGuard::expr_inst_raw(e, params)` replaces the positional level parameters of `e` by the
levels of `params`, with no simplification of `max` or `imax`. `expr_inst_raw_tm` names its
result: if the pointer `e` represents the kernel term `E` and `params` represents a level list
that `us` is level-equivalent to, the result represents
`E.instantiateLevelParams (List.range us.length) us`.

This is the statement `KernelLevels::expr_inst_levels` already has (`SubstAux.G.expr_inst_levels`),
with the same tolerance, which is the tolerance of the term seam and nothing more:

* `E` is any term the input pointer represents (`Tm` reads the levels of sorts and constants up
  to semantic equality, and binder data exactly);
* `us` is any list pointwise semantically equal to the represented list (`LvListRep`);
* the term is read at opening depth `0`, where it has no opened variable.

The existence-only lemma `expr_inst_raw_rep` is unchanged. -/

namespace IxVM.Refinement.Core.GuardData

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.KernelLevels (RepKLevel RepKLevelList)

set_option maxHeartbeats 2400000
set_option linter.unusedVariables false

/-- Positional substitution respects the semantic equality of levels, on the level and on the
substituted list; the right side is the syntax the raw operation builds. -/
theorem lvEq_subst_raw {u l : KLevel} {us ls : List KLevel} (hu : LvEq u l)
    (hus : LvEqList us ls) :
    LvEq (Ix.Kernel.Level.subst (List.range us.length) us u) (Guard.rawSubst ls l) := by
  rw [Guard.rawSubst_eq]
  intro φ
  exact (SubstAux.lvEq_subst hu hus φ).trans
    (SubstAux.lvEq_subst (LvEq.refl l) (LvEqList.refl ls) φ).symm

theorem lvEqList_subst_raw {us' ls' us ls : List KLevel} (h' : LvEqList us' ls')
    (hus : LvEqList us ls) :
    LvEqList (us'.map (Ix.Kernel.Level.subst (List.range us.length) us))
      (ls'.map (Guard.rawSubst ls)) := by
  have hmap : ls'.map (Guard.rawSubst ls) =
      ls'.map (Ix.Kernel.Level.subst (List.range ls.length) ls) :=
    List.map_congr_left fun l _ => Guard.rawSubst_eq ls l
  rw [hmap]
  exact (SubstAux.lvEqList_subst h' hus).trans
    (SubstAux.lvEqList_subst (LvEqList.refl ls') (LvEqList.refl ls)).symm

/-- A binder's datum after raw substitution. -/
theorem bmeta_subst_raw {ℓ : KLevel} {us ls : List KLevel} (hul : LvEqList us ls) :
    ({ bmeta ℓ with pw := Ix.Kernel.Level.substPW (List.range us.length) us (bmeta ℓ).pw } :
      Ix.Kernel.BinderMeta) = bmeta (Guard.rawSubst ls ℓ) := by
  rw [SubstAux.bmeta_subst hul]
  exact bmeta_congr fun φ =>
    (SubstAux.lvEq_subst (LvEq.refl ℓ) (LvEqList.refl ls) φ).symm.trans
      (lvEq_subst_raw (LvEq.refl ℓ) (LvEqList.refl ls) φ)

private def rawTmName (walk : Bool) : String :=
  if walk then "KernelGuard::expr_inst_raw_walk" else "KernelGuard::expr_inst_raw"

private theorem expr_tm_go (κ : _root_.Address → KKey) :
    ∀ fuel : Nat, ∀ (walk : Bool) {k : Nat} {Γ : Nat → KExpr} {E : KExpr}
      {us ls : List KLevel} {p params r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      cs.length ≤ fuel → Tm κ 0 Γ h k E p → RepKLevelList h ls params → LvEqList us ls →
      ObsFn W (rawTmName walk) [p, params] h r h' cs →
      Tm κ 0 Γ h' k (E.instantiateLevelParams (List.range us.length) us) r := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
    intro walk k Γ E us ls p params r h h' cs hlen hE hp hul ev
    cases walk with
    | false =>
      change ObsFn W "KernelGuard::expr_inst_raw" [p, params] h r h' cs at ev
      match Obs.«KernelGuard::expr_inst_raw».obs ev with
      | .Nil (ld12 := ld) (he21 := hr) (he22 := hh) .. =>
        subst hr hh
        rw [← Levels.klevelList_names] at ld
        obtain rfl := Lib.rep_nil_of_load hp ld
        obtain rfl : us = [] := by
          cases us with
          | nil => rfl
          | cons u us => exact False.elim (hul (fun _ => 0))
        simp only [List.length_nil, List.range_zero]
        rw [SubstAux.tm_ilp_nil hE]
        exact hE
      | .other (cs31 := children) (ev33 := child) (hc50 := hc) .. =>
        have hlt : children.length < fuel := by
          rw [hc] at hlen; simp only [List.length_cons] at hlen; omega
        exact ih children.length hlt true (Nat.le_refl _) hE hp hul child
    | true =>
      change ObsFn W "KernelGuard::expr_inst_raw_walk" [p, params] h r h' cs at ev
      match Obs.«KernelGuard::expr_inst_raw_walk».obs ev with
      | .BVar (ld12 := ld) (he27 := hr) (he28 := hh) .. =>
        subst hr hh
        obtain ⟨i, -, -, hcase⟩ := Tm.bvar_of_load hE ld
        rcases hcase with ⟨-, rfl⟩ | ⟨-, hd, -⟩
        · exact hE
        · omega
      | .Lit (ld12 := ld) (he595 := hr) (he596 := hh) .. =>
        subst hr hh
        rcases Tm.lit_of_load hE ld with ⟨_, _, _, _, _, rfl⟩ | ⟨_, _, _, _, _, _, rfl⟩ <;>
          exact hE
      | .Srt (ld12 := ld) (he46 := hr) (hm45 := hh) (ev62 := child) .. =>
        obtain ⟨u, rfl, l, hl, hu⟩ := hE.sort_of_load ld
        obtain ⟨-, hl'⟩ := Guard.level_inst_raw_spec child hl hp
        subst hr hh
        exact SubstAux.tm_store_sort hl' (lvEq_subst_raw hu hul)
      | .Const (ld12 := ld) (he101 := hr) (hm100 := hh) (ev125 := child) .. =>
        obtain ⟨a, us', rfl, ha, ls', hls', hus'⟩ := hE.const_of_load ld
        have : Resolved (κ (ixAddr a)) := ⟨hE.const_key_ne⟩
        obtain ⟨-, hls''⟩ := Guard.levels_inst_raw_spec child hls' hp
        subst hr hh
        exact SubstAux.tm_store_const
          (Bytes.repAddressRef_heapMono₂ addrTy child.heap_extends ha) hls''
          (lvEqList_subst_raw hus' hul)
      | .App (cs179 := first) (cs207 := second) (ld12 := ld) (he164 := hr) (hm163 := hh)
          (ev181 := e1) (ev209 := e2) (hc226 := hc) .. =>
        obtain ⟨f, a, rfl, hf, ha⟩ := hE.app_of_load ld
        have h1 : first.length < fuel := by
          rw [hc] at hlen; simp only [List.length_cons, List.length_append] at hlen; omega
        have h2 : second.length < fuel := by
          rw [hc] at hlen; simp only [List.length_cons, List.length_append] at hlen; omega
        have sf := ih first.length h1 false (Nat.le_refl _) hf hp hul e1
        have sa := ih second.length h2 false (Nat.le_refl _)
          (ha.mono e1.heap_extends) (hp.mono e1.heap_extends) hul e2
        subst hr hh
        exact Tm.store_app (sf.mono e2.heap_extends) sa
      | .Lam (cs269 := first) (cs297 := second) (ld12 := ld) (he253 := hr) (hm252 := hh)
          (ev271 := e1) (ev299 := e2) (ev327 := e3) (hc344 := hc) .. =>
        obtain ⟨T, B, ℓ, rfl, hT, hB, hl⟩ := hE.lam_of_load ld
        have h1 : first.length < fuel := by
          rw [hc] at hlen; simp only [List.length_cons, List.length_append] at hlen; omega
        have h2 : second.length < fuel := by
          rw [hc] at hlen; simp only [List.length_cons, List.length_append] at hlen; omega
        have st := ih first.length h1 false (Nat.le_refl _) hT hp hul e1
        have sb := ih second.length h2 false (Nat.le_refl _)
          (hB.mono e1.heap_extends) (hp.mono e1.heap_extends) hul e2
        have ext := e1.heap_extends.trans e2.heap_extends
        obtain ⟨-, hl'⟩ := Guard.level_inst_raw_spec e3 (hl.mono ext) (hp.mono ext)
        subst hr hh
        show Tm κ 0 Γ _ k (.lam (T.instantiateLevelParams (List.range us.length) us)
          (B.instantiateLevelParams (List.range us.length) us)
          { bmeta ℓ with
            pw := Ix.Kernel.Level.substPW (List.range us.length) us (bmeta ℓ).pw }) _
        rw [bmeta_subst_raw hul]
        exact SubstAux.tm_store_lam (st.mono (e2.heap_extends.trans e3.heap_extends))
          (sb.mono e3.heap_extends) hl'
      | .Forall (cs387 := first) (cs415 := second) (ld12 := ld) (he371 := hr) (hm370 := hh)
          (ev389 := e1) (ev417 := e2) (ev445 := e3) (hc462 := hc) .. =>
        obtain ⟨T, B, ℓ, rfl, hT, hB, hl⟩ := hE.forallE_of_load ld
        have h1 : first.length < fuel := by
          rw [hc] at hlen; simp only [List.length_cons, List.length_append] at hlen; omega
        have h2 : second.length < fuel := by
          rw [hc] at hlen; simp only [List.length_cons, List.length_append] at hlen; omega
        have st := ih first.length h1 false (Nat.le_refl _) hT hp hul e1
        have sb := ih second.length h2 false (Nat.le_refl _)
          (hB.mono e1.heap_extends) (hp.mono e1.heap_extends) hul e2
        have ext := e1.heap_extends.trans e2.heap_extends
        obtain ⟨-, hl'⟩ := Guard.level_inst_raw_spec e3 (hl.mono ext) (hp.mono ext)
        subst hr hh
        show Tm κ 0 Γ _ k (.forallE (T.instantiateLevelParams (List.range us.length) us)
          (B.instantiateLevelParams (List.range us.length) us)
          { bmeta ℓ with
            pw := Ix.Kernel.Level.substPW (List.range us.length) us (bmeta ℓ).pw }) _
        rw [bmeta_subst_raw hul]
        exact SubstAux.tm_store_forallE (st.mono (e2.heap_extends.trans e3.heap_extends))
          (sb.mono e3.heap_extends) hl'
      | .Let (cs505 := first) (cs533 := second) (cs561 := third) (ld12 := ld)
          (he489 := hr) (hm488 := hh) (ev507 := e1) (ev535 := e2) (ev563 := e3)
          (hc580 := hc) .. =>
        obtain ⟨T, V, B, rfl, hT, hV, hB⟩ := hE.letE_of_load ld
        have h1 : first.length < fuel := by
          rw [hc] at hlen; simp only [List.length_cons, List.length_append] at hlen; omega
        have h2 : second.length < fuel := by
          rw [hc] at hlen; simp only [List.length_cons, List.length_append] at hlen; omega
        have h3 : third.length < fuel := by
          rw [hc] at hlen; simp only [List.length_cons, List.length_append] at hlen; omega
        have st := ih first.length h1 false (Nat.le_refl _) hT hp hul e1
        have sv := ih second.length h2 false (Nat.le_refl _)
          (hV.mono e1.heap_extends) (hp.mono e1.heap_extends) hul e2
        have ext := e1.heap_extends.trans e2.heap_extends
        have sb := ih third.length h3 false (Nat.le_refl _) (hB.mono ext) (hp.mono ext) hul e3
        subst hr hh
        rw [SubstAux.ilp_instShift]
        exact SubstAux.tm_store_letE (st.mono (e2.heap_extends.trans e3.heap_extends))
          (sv.mono e3.heap_extends) sb
      | .Proj (cs654 := children) (ld12 := ld) (he624 := hr) (hm623 := hh)
          (ev656 := child) (hc673 := hc) .. =>
        obtain ⟨a, i, E, rfl, rfl, ha, hE'⟩ := hE.proj_of_load ld
        have : Resolved (κ (ixAddr a)) := ⟨hE.proj_key_ne⟩
        have : ProjPermitted κ (ixAddr a) := hE.proj_permitted ld ha
        have hlt : children.length < fuel := by
          rw [hc] at hlen; simp only [List.length_cons] at hlen; omega
        have se := ih children.length hlt false (Nat.le_refl _) hE' hp hul child
        subst hr hh
        exact SubstAux.tm_store_proj
          (Bytes.repAddressRef_heapMono₂ addrTy child.heap_extends ha) se

/-- **`expr_inst_raw` is positional level instantiation at the term seam.** If `p` represents
`E` at opening depth `0` and `params` represents a level list that `us` is pointwise
semantically equal to, the result represents
`E.instantiateLevelParams (List.range us.length) us`. -/
theorem expr_inst_raw_tm {κ : _root_.Address → KKey} {k : Nat} {Γ : Nat → KExpr} {E : KExpr}
    {us : List KLevel} {p params r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hE : Tm κ 0 Γ h k E p) (hus : LvListRep h us params)
    (ev : ObsFn W "KernelGuard::expr_inst_raw" [p, params] h r h' cs) :
    Tm κ 0 Γ h' k (E.instantiateLevelParams (List.range us.length) us) r := by
  obtain ⟨ls, hls, hul⟩ := hus
  exact expr_tm_go κ cs.length false (Nat.le_refl _) hE hls hul ev

end IxVM.Refinement.Core.GuardData
