import IxVMRefinement.Whnf.Basic

/-! # Step lemmas of `KernelWhnf`: the telescope scans

`type_sort_never` walks `n` `∀` nodes to a sort and asks the never-zero test of the sort at the
use's levels (`level_inst_params`, the kernel's `Level.subst (List.range n)` up to semantic
equality); `slots_never` asks the test of the first `n` `∀` binders' levels; `lams_never` of the
first `n` `λ` binders' levels, directly or at the use's levels. A nonzero answer is the
corresponding syntactic statement on the image (`piSortAt`, `forallsNever`, `lamsNeverAt`). -/

namespace IxVM.Refinement.Core

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List

set_option linter.unusedVariables false

/-- `KernelWhnf::type_sort_never`: a nonzero answer is a telescope of exactly `n` `∀`s ending
in a sort that is never zero at the levels. -/
theorem type_sort_never_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelWhnf::type_sort_never" args h r h' calls) (ih : IH c calls) :
    Specs.Whnf.type_sort_never c args h r h' calls := by
  intro ty n lvls hargs good d Γ k T m us hT hn hus hr
  subst hargs hn
  rcases Obs.«KernelWhnf::type_sort_never».obs ev with
    ⟨w20, x_body, w21, ld12, hv50, he51, he52, hc53⟩ |
    ⟨w20, x_body, w21, cs61, v65, ld12, hne54, op87, ev63, hc96⟩ |
    ⟨x_l, cs126, v129, m131, cs139, ld12, hv122, ev141, ev128, hc158⟩ |
    ⟨x_l, ld12, hne159, he163, he164, hc165⟩ |
    ⟨v1, ld12, hne97, hne166, he170, he171, hc172⟩
  · exact (hr he51).elim
  · subst hc96
    have hm : m ≠ 0 := fun e => hne54 (by rw [e])
    obtain rfl := Lib.sub_one_inv op87
    obtain ⟨T0, B, ℓ, rfl, -, hB, -⟩ := hT.forallE_of_load ld12
    obtain ⟨l, hl, hnz⟩ := ih.get (.whnf .type_sort_never) (by lt_calls) ev63 x_body _ lvls rfl
      (good.sub fun x hx => by simp [hx]) d Γ (k + 1) B (m - 1) us hB rfl hus hr
    refine ⟨l, ?_, hnz⟩
    rw [← Lib.val_sub_one hm]
    exact hl
  · subst hc158
    have hm : m = 0 := Value.field.inj hv122
    subst hm
    obtain ⟨u, rfl, l0, hl0, hul⟩ := hT.sort_of_load ld12
    obtain ⟨ls, hls, hus'⟩ := hus
    obtain ⟨-, hsub, -⟩ := ih.get (.levelOps .level_inst_params) (by lt_calls) ev141 x_l lvls rfl
      (good.sub fun x hx => by simp [hx]).2 l0 ls hl0 hls
    obtain ⟨hr1, -⟩ := ih.get (.levelOps .level_is_not_zero) (by lt_calls) ev128 v129 rfl _ hsub
    have hnz := WhnfAux.isNeverZero_of_ne_zero hr1 hr
    refine ⟨u, by rw [ZMod.val_zero]; rfl, ?_⟩
    rw [WhnfAux.isNeverZero_congr (WhnfAux.lvEq_subst_range hul hus')]
    exact hnz
  · exact (hr he163).elim
  · exact (hr he170).elim

/-- `KernelWhnf::slots_never`: a nonzero answer is `n` leading `∀`s whose data are `never`. -/
theorem slots_never_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelWhnf::slots_never" args h r h' calls) (ih : IH c calls) :
    Specs.Whnf.slots_never c args h r h' calls := by
  intro t n hargs good d Γ k T m hT hn hr
  subst hargs hn
  rcases Obs.«KernelWhnf::slots_never».obs ev with
    ⟨hv14, he15, he16, hc17⟩ |
    ⟨w41, x_body, x_bl, m58, cs69, cs87, v91, hne18, ld33, ev71, op112, ev89, hc114⟩ |
    ⟨w41, x_body, x_bl, v57, m58, cs69, hne18, ld33, ev71, hne115, he119, he120, hc121⟩ |
    ⟨v22, hne18, ld33, hne122, he126, he127, hc128⟩
  · rw [Value.field.inj hv14, ZMod.val_zero]
    exact trivial
  · subst hc114
    have hm : m ≠ 0 := fun e => hne18 (by rw [e])
    obtain rfl := Lib.sub_one_inv op112
    obtain ⟨T0, B, ℓ, rfl, -, hB, hℓ⟩ := hT.forallE_of_load ld33
    obtain ⟨hr1, e1⟩ := ih.get (.levelOps .level_is_not_zero) (by lt_calls) ev71 x_bl rfl ℓ hℓ
    subst e1
    have hnz := WhnfAux.isNeverZero_of_answer hr1
    have hrec := ih.get (.whnf .slots_never) (by lt_calls) ev89 x_body _ rfl
      (good.sub fun x hx => by simp [hx]) d Γ (k + 1) B (m - 1) hB rfl hr
    rw [← Lib.val_sub_one hm]
    show (bmeta ℓ).pw.isNever = true ∧ Specs.Whnf.forallsNever (ZMod.val (m - 1)) B
    exact ⟨by rw [bmeta_of_isNeverZero hnz]; exact nbMeta_isNever, hrec⟩
  · exact (hr he119).elim
  · exact (hr he126).elim

/-- `KernelWhnf::lams_never`: a nonzero answer is `n` leading `λ`s whose data, at the levels
(positional parameters), are `never`: either the stored level is never zero (so is every
substitution of it) or its instantiation at the levels is. -/
theorem lams_never_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelWhnf::lams_never" args h r h' calls) (ih : IH c calls) :
    Specs.Whnf.lams_never c args h r h' calls := by
  intro v n lvls hargs good d Γ k V m us hV hn hus hr
  subst hargs hn
  rcases Obs.«KernelWhnf::lams_never».obs ev with
    ⟨hv14, he15, he16, hc17⟩ |
    ⟨w41, x_body, x_bl, m58, cs69, cs87, v91, hne18, ld33, ev71, op113, ev89, hc122⟩ |
    ⟨w41, x_body, x_bl, v57, m58, cs69, m128, cs139, v142, m144, cs152, cs178, v182, hne18, ld33,
      ev71, hne123, ev154, ev141, op204, ev180, hc213⟩ |
    ⟨w41, x_body, x_bl, v57, m58, cs69, v127, m128, cs139, v142, m144, cs152, hne18, ld33, ev71,
      hne123, ev154, ev141, hne214, he218, he219, hc220⟩ |
    ⟨v22, hne18, ld33, hne221, he225, he226, hc227⟩
  · rw [Value.field.inj hv14, ZMod.val_zero]
    exact trivial
  · subst hc122
    have hm : m ≠ 0 := fun e => hne18 (by rw [e])
    obtain rfl := Lib.sub_one_inv op113
    obtain ⟨T0, B, ℓ, rfl, -, hB, hℓ⟩ := hV.lam_of_load ld33
    obtain ⟨hr1, e1⟩ := ih.get (.levelOps .level_is_not_zero) (by lt_calls) ev71 x_bl rfl ℓ hℓ
    subst e1
    have hnz := WhnfAux.isNeverZero_of_answer hr1
    have hrec := ih.get (.whnf .lams_never) (by lt_calls) ev89 x_body _ lvls rfl
      (good.sub fun x hx => by simp [hx]) d Γ (k + 1) B (m - 1) us hB rfl hus hr
    rw [← Lib.val_sub_one hm]
    show (Ix.Kernel.Level.substPW (List.range us.length) us (bmeta ℓ).pw).isNever = true ∧
      Specs.Whnf.lamsNeverAt (List.range us.length) us (ZMod.val (m - 1)) B
    exact ⟨WhnfAux.isNever_substPW_bmeta (WhnfAux.isNeverZero_subst hnz _ _), hrec⟩
  · subst hc213
    have hm : m ≠ 0 := fun e => hne18 (by rw [e])
    obtain rfl := Lib.sub_one_inv op204
    obtain ⟨T0, B, ℓ, rfl, -, hB, hℓ⟩ := hV.lam_of_load ld33
    obtain ⟨-, e1⟩ := ih.get (.levelOps .level_is_not_zero) (by lt_calls) ev71 x_bl rfl ℓ hℓ
    subst e1
    obtain ⟨ls, hls, hus'⟩ := hus
    obtain ⟨-, hsub, e2⟩ := ih.get (.levelOps .level_inst_params) (by lt_calls) ev154 x_bl lvls
      rfl (good.sub fun x hx => by simp [hx]).2 ℓ ls hℓ hls
    obtain ⟨hr1, e3⟩ := ih.get (.levelOps .level_is_not_zero) (by lt_calls) ev141 v142 rfl _ hsub
    subst e3
    have hnz := WhnfAux.isNeverZero_of_answer hr1
    have hrec := ih.get (.whnf .lams_never) (by lt_calls) ev180 x_body _ lvls rfl
      (good.sub fun x hx => by simp [hx]) d Γ (k + 1) B (m - 1) us (Tm.mono e2 hB) rfl
      ⟨ls, hls.mono e2, hus'⟩ hr
    rw [← Lib.val_sub_one hm]
    show (Ix.Kernel.Level.substPW (List.range us.length) us (bmeta ℓ).pw).isNever = true ∧
      Specs.Whnf.lamsNeverAt (List.range us.length) us (ZMod.val (m - 1)) B
    refine ⟨WhnfAux.isNever_substPW_bmeta ?_, hrec⟩
    rw [WhnfAux.isNeverZero_congr (WhnfAux.lvEq_subst_range (LvEq.refl ℓ) hus')]
    exact hnz
  · exact (hr he218).elim
  · exact (hr he225).elim

end IxVM.Refinement.Core
