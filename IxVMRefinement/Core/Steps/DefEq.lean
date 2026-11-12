import IxVMRefinement.Core.Steps.Whnf
import IxVMRefinement.Core.Det
import IxVMRefinement.Lib.Bytes
import IxVMRefinement.Obs.KernelDefEq

/-! # Step lemmas of `KernelDefEq`, on the registry: the ordered tiers' entry and spine
congruence -/

namespace IxVM.Refinement.Core

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open Ix.Kernel.Rules (Red DefEq DefEqList)

set_option linter.unusedVariables false

/-! ## Helpers -/

theorem evalBinOp_sub_inv' {x y r : SourceValue F} (h : evalBinOp .sub x y = .ok r) :
    ∃ a b, x = .field a ∧ y = .field b ∧ r = .field (a - b) := by
  cases x <;> cases y <;> simp [evalBinOp] at h
  exact ⟨_, _, rfl, rfl, h.symm⟩

/-- **Spine congruence**: equal heads and pairwise equal arguments. -/
theorem defEq_mkAppN_congr {env : Ix.Kernel.Env .anon} {d : Nat} :
    ∀ {As Bs : List KExpr}, DefEqList env d As Bs → ∀ {H H' : KExpr}, DefEq env d H H' →
      DefEq env d (Ix.Kernel.Expr.mkAppN H As) (Ix.Kernel.Expr.mkAppN H' Bs)
  | [], _, hl, _, _, hH => by cases hl; exact hH
  | _ :: _, _, hl, _, _, hH => by
    cases hl with
    | cons hab hrest => exact defEq_mkAppN_congr hrest (.app hH hab)

theorem field_ne_zero_of_eq_one {r : SourceValue F} (h : r = .field 1) : r ≠ .field 0 := by
  subst h; exact field_one_ne_zero

/-! ## The ordered tiers' entry -/

/-- `KernelDefEq::k_is_def_eq_core` is `k_is_def_eq_ordered`. -/
theorem k_is_def_eq_core_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelDefEq::k_is_def_eq_core" args h r h' calls) (ih : IH c calls) :
    Specs.DefEq.k_is_def_eq_core c args h r h' calls := by
  intro rc a b types hargs good
  subst hargs
  obtain ⟨cs4, ev6, hc39⟩ := Obs.«KernelDefEq::k_is_def_eq_core».obs ev
  subst hc39
  exact ih.get (.defEq .k_is_def_eq_ordered) (by lt_calls) ev6 rc a b types rfl
    (good.sub fun x hx => by simp [hx])

/-- `KernelDefEq::k_is_def_eq_ordered`: spine congruence, then the slow tiers. -/
theorem k_is_def_eq_ordered_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelDefEq::k_is_def_eq_ordered" args h r h' calls) (ih : IH c calls) :
    Specs.DefEq.k_is_def_eq_ordered c args h r h' calls := by
  intro rc a b types hargs good hrc d Γ htypes A B hA hB hr
  subst hargs
  rcases Obs.«KernelDefEq::k_is_def_eq_ordered».obs ev with
    ⟨m2, cs13, ev15, he52, he53, hc54⟩ | ⟨v1, m2, cs13, cs62, ev15, hne55, ev64, hc97⟩
  · subst hc54
    exact ih.get (.defEq .try_def_eq_app) (by lt_calls) ev15 rc a b types rfl
      (good.sub fun x hx => by simp [hx]) hrc d Γ htypes A B hA hB field_one_ne_zero
  · subst hc97
    have ext := ObsFn.heap_extends ev15
    exact ih.get (.defEq .k_is_def_eq_slow) (by lt_calls) ev64 rc a b types rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono ext hrc) d Γ (types_mono ext htypes) A B
      (Tm.mono ext hA) (Tm.mono ext hB) hr

/-- `KernelDefEq::de_args`: pairwise definitional equality of two argument lists. -/
theorem de_args_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelDefEq::de_args" args h r h' calls) (ih : IH c calls) :
    Specs.DefEq.de_args c args h r h' calls := by
  intro rc aa bb types hargs good hrc d Γ htypes As Bs hAs hBs hr
  subst hargs
  rcases Obs.«KernelDefEq::de_args».obs ev with
    ⟨ld12, ld31, he39, he40, hc41⟩ | ⟨v20, ld12, ld31, hne42, he46, he47, hc48⟩ |
    ⟨x_a, x_ar, ld12, ld77, he85, he86, hc87⟩ |
    ⟨x_a, x_ar, x_b, x_br, m106, cs117, ld12, ld77, ev119, he156, he157, hc158⟩ |
    ⟨x_a, x_ar, x_b, x_br, v105, m106, cs117, cs166, ld12, ld77, ev119, hne159, ev168, hc201⟩
  · obtain rfl := RepList.nil_of_load hAs ld12
    obtain rfl := RepList.nil_of_load hBs ld31
    exact .nil
  · exact absurd he46 hr
  · exact absurd he85 hr
  · exact absurd he156 hr
  · obtain ⟨A, As', rfl, hA, hAs'⟩ := RepList.cons_of_load hAs ld12
    obtain ⟨B, Bs', rfl, hB, hBs'⟩ := RepList.cons_of_load hBs ld77
    subst hc201
    have hAB := ih.get (.defEq .k_is_def_eq) (by lt_calls) ev119 rc x_a x_b types rfl
      (good.sub fun x hx => by simp [hx]) hrc d Γ htypes A B hA hB hne159
    have ext := ObsFn.heap_extends ev119
    have hrest := ih.get (.defEq .de_args) (by lt_calls) ev168 rc x_ar x_br types rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono ext hrc) d Γ (types_mono ext htypes) As' Bs'
      (tml_mono ext hAs') (tml_mono ext hBs') hr
    exact .cons hAB hrest

/-! ## Spine congruence -/

/-- `KernelDefEq::try_def_eq_app`: the same variable head, or the same constant at equal
levels, with pairwise equal arguments (`DefEq.app` along the spine). -/
theorem try_def_eq_app_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelDefEq::try_def_eq_app" args h r h' calls) (ih : IH c calls) :
    Specs.DefEq.try_def_eq_app c args h r h' calls := by
  intro rc a b types hargs good hrc d Γ htypes A B hA hB hr
  subst hargs
  have p := Obs.«KernelDefEq::try_def_eq_app».obs ev
  cases p
  case BVar_BVar_n0 m2 cs13 x_ah x_aa m41 cs52 x_bh x_bb x_i x_j cs153 ev15 ev54 ld90 ld114 op143
      ev155 hc188 =>
    subst hc188
    have g1 : Good c cs13 := good.sub fun x hx => by simp [hx]
    have g2 : Good c cs52 := good.sub fun x hx => by simp [hx]
    have g3 : Good c cs153 := good.sub fun x hx => by simp [hx]
    have e0 := ObsFn.heap_extends ev15
    have e1 := ObsFn.heap_extends ev54
    obtain ⟨ah, aa, H, As, he1, hH, hAs, rfl⟩ :=
      ih.get (.subst .collect_spine) (by lt_calls) ev15 a rfl g1 d Γ 0 A hA
    obtain ⟨bh, bb, Hb, Bs, he2, hHb, hBs, rfl⟩ :=
      ih.get (.subst .collect_spine) (by lt_calls) ev54 b rfl g2 d Γ 0 B (Tm.mono e0 hB)
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at he1 he2
    obtain ⟨rfl, rfl⟩ := he1
    obtain ⟨rfl, rfl⟩ := he2
    obtain ⟨i, rfl, -, hi⟩ := (Tm.mono e1 hH).bvar_of_load ld90
    obtain ⟨j, rfl, -, hj⟩ := hHb.bvar_of_load ld114
    obtain ⟨i', j', hi', hj', h0⟩ := evalBinOp_sub_inv' op143
    injection hi' with hi'
    injection hj' with hj'
    injection h0 with h0
    subst hi' hj'
    have hij : i = j := (sub_eq_zero.mp h0.symm)
    subst hij
    have hHH : H = Hb := by
      rcases hi with ⟨hlt, -⟩ | ⟨-, -, rfl⟩
      · omega
      rcases hj with ⟨hlt, -⟩ | ⟨-, -, rfl⟩
      · omega
      rfl
    subst hHH
    have ext := e0.trans e1
    have hl := ih.get (.defEq .de_args) (by lt_calls) ev155 rc _ _ types rfl g3
      (RCRep.mono ext hrc) d Γ (types_mono ext htypes) As Bs (tml_mono e1 hAs) hBs hr
    exact defEq_mkAppN_congr hl .refl
  case Const_Const_n0_other_n0 m2 cs13 x_ah x_aa m41 cs52 x_bh x_bb x_a_addr x_al x_b_addr x_bl
      m250 y259 cs269 v292 m293 cs304 m335 x343 y344 m345 cs354 cs368 cs386 ev15 ev54 ld90 ld231
      ev271 op265 ev306 hne330 ev356 ev370 op350 ev388 hc421 =>
    subst hc421
    have g1 : Good c cs13 := good.sub fun x hx => by simp [hx]
    have g2 : Good c cs52 := good.sub fun x hx => by simp [hx]
    have g3 : Good c cs304 := good.sub fun x hx => by simp [hx]
    have g4 : Good c cs386 := good.sub fun x hx => by simp [hx]
    have e0 := ObsFn.heap_extends ev15
    have e1 := ObsFn.heap_extends ev54
    have e2 := ObsFn.heap_extends ev271
    have e3 := ObsFn.heap_extends ev306
    have e4 := ObsFn.heap_extends ev356
    have e5 := ObsFn.heap_extends ev370
    obtain ⟨ah, aa, H, As, he1, hH, hAs, rfl⟩ :=
      ih.get (.subst .collect_spine) (by lt_calls) ev15 a rfl g1 d Γ 0 A hA
    obtain ⟨bh, bb, Hb, Bs, he2, hHb, hBs, rfl⟩ :=
      ih.get (.subst .collect_spine) (by lt_calls) ev54 b rfl g2 d Γ 0 B (Tm.mono e0 hB)
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at he1 he2
    obtain ⟨rfl, rfl⟩ := he1
    obtain ⟨rfl, rfl⟩ := he2
    obtain ⟨a1, us, rfl, ha1, hus⟩ := (Tm.mono e1 hH).const_of_load ld90
    obtain ⟨a2, us', rfl, ha2, hus'⟩ := hHb.const_of_load ld231
    obtain ⟨hy, -⟩ := Lib.address_eq_spec ev271 ha1 ha2
    obtain ⟨o, y', ho, hy', h0⟩ := evalBinOp_sub_inv' op265
    injection ho with ho
    subst hy'
    injection hy with hy
    injection h0 with h0
    have hy1 : y' = 1 := by
      have := sub_eq_zero.mp h0.symm
      rw [← ho] at this
      exact this.symm
    have ha : a1 = a2 := by
      by_contra hne
      rw [ite_eq_right hne, hy1] at hy
      exact one_ne_zero hy
    subst ha
    have hlv := ih.get (.defEq .level_list_eq) (by lt_calls) ev306 _ _ rfl g3 us us'
      (LvListRep.mono e2 hus) (LvListRep.mono e2 hus') hne330
    have ext : Heap.Extends h m335 := e0.trans (e1.trans (e2.trans (e3.trans (e4.trans e5))))
    have ext' : Heap.Extends m41 m335 := e2.trans (e3.trans (e4.trans e5))
    have hl := ih.get (.defEq .de_args) (by lt_calls) ev388 rc _ _ types rfl g4
      (RCRep.mono ext hrc) d Γ (types_mono ext htypes) As Bs (tml_mono (e1.trans ext') hAs)
      (tml_mono ext' hBs) hr
    exact defEq_mkAppN_congr hl (.const hlv)
  all_goals (subst_vars; exact absurd rfl hr)

/-! ## The entry -/

/-- `KernelDefEq::k_is_def_eq`: closed sides are compared under the empty context list (a
segment of the same ghost context); otherwise under the rebased context (`k_def_eq_rebase`). -/
theorem k_is_def_eq_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelDefEq::k_is_def_eq" args h r h' calls) (ih : IH c calls) :
    Specs.DefEq.k_is_def_eq c args h r h' calls := by
  intro rc a b types hargs good hrc d Γ htypes A B hA hB hr
  subst hargs
  rcases Obs.«KernelDefEq::k_is_def_eq».obs ev with
    ⟨m2, cs12, v15, v16, m18, cs26, m38, cs46, cs74, m103, ev28, ev48, ev14, hm111, ev76, hc115⟩ |
    ⟨v1, m2, cs12, v15, v16, m18, cs26, m38, cs46, cs123, ev28, ev48, ev14, hne116, ev125, hc166⟩
  · subst hc115 hm111
    have ext : Heap.Extends h m2 := (ObsFn.heap_extends ev28).trans
      ((ObsFn.heap_extends ev48).trans (ObsFn.heap_extends ev14))
    have ext' : Heap.Extends h (m2 ++ [.construct kexprListEnum "Nil" []]) :=
      ext.trans (Heap.Extends.snoc _ _)
    have hnil : c.types Γ (m2 ++ [.construct kexprListEnum "Nil" []]) d
        (.ptr (.enum kexprListEnum) m2.length) := ⟨.nil (by simp), htypes.2⟩
    exact ih.get (.defEq .k_is_def_eq_core) (by lt_calls) ev76 rc a b _ rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono ext' hrc) d Γ hnil A B (Tm.mono ext' hA)
      (Tm.mono ext' hB) hr
  · subst hc166
    have ext : Heap.Extends h m2 := (ObsFn.heap_extends ev28).trans
      ((ObsFn.heap_extends ev48).trans (ObsFn.heap_extends ev14))
    exact ih.get (.defEq .k_def_eq_rebase) (by lt_calls) ev125 rc a b types v1 rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono ext hrc) d Γ (types_mono ext htypes) A B
      (Tm.mono ext hA) (Tm.mono ext hB) hr

end IxVM.Refinement.Core
