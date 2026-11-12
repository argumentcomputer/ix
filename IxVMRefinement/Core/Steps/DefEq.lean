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

end IxVM.Refinement.Core
