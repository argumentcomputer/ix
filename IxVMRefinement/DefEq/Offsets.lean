import IxVMRefinement.DefEq.Basic

/-! # Step lemmas of `KernelDefEq`: string literals and η-expansion

* **String literals** (`try_string_lit_one`): a string literal reduces to its constructor form
  (`Red.strLit`, under the guard `str_lit_to_ctor` establishes), and one δ step on
  (`str_lit_delta_step`); the comparison of that reduct with the other side is carried back by
  `DefEq.redL`. `try_string_lit_pair` runs it both ways, the second by `DefEq.symm`.
* **η-expansion** (`try_eta_expand`, `DefEq.eta`): the `λ`'s body is compared under the context
  list with the left domain pushed, against `b` lifted past the new binder and applied to the
  stored `BVar 0`. One depth further in, under the ghost context extended by the left domain,
  the lifted `b` reads as `b` and the `BVar 0` as the new opened variable, so the stored
  application reads as `b` applied to it. `try_eta_swap` puts the `λ` on the left
  (`DefEq.symm` when it is on the right). -/

namespace IxVM.Refinement.Core.DefEqAux

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open Ix.Kernel.Rules (Red DefEq)

set_option linter.unusedVariables false

private theorem fval_zero : ZMod.val (0 : F) = 0 := ZMod.val_zero

private theorem fval_one : ZMod.val (1 : F) = 1 := ZMod.val_one _

/-- The constructor form of a string literal is an application of `String.ofList`. -/
private theorem strLitToConstructor_app (s : String) :
    ∃ L : KExpr, (Ix.Kernel.strLitToConstructor s : KExpr) =
      .app (.const Ix.Kernel.stringOfListName []) L :=
  ⟨_, rfl⟩

/-- **The new opened variable as IxVM stores it**: a `BVar 0` cell stored at the end of the heap
reads, one depth further in under the ghost context extended at `d`, as the opened variable
`d`. -/
private theorem tm_store_bvar0 {c : Ctx} {d : Nat} {Γ : Nat → KExpr} {T : KExpr} (h : Heap F) :
    c.tm (d + 1) (Ghost.extend Γ d T) (h ++ [.construct kexprEnum "BVar" [.field 0]])
      (.fvar d T) (.ptr (.enum kexprEnum) h.length) := by
  have hv : Tm c.κ (d + 1) (Ghost.extend Γ d T) (h ++ [.construct kexprEnum "BVar" [.field 0]]) 0
      (.fvar (fvIdx (d + 1) 0 (ZMod.val (0 : F)))
        (Ghost.extend Γ d T (fvIdx (d + 1) 0 (ZMod.val (0 : F)))))
      (.ptr (.enum kexprEnum) h.length) :=
    Tm.bvarFree (by simp) (by have := fval_zero; omega) (Nat.zero_le _)
      (by have := fval_zero; omega)
  have e : fvIdx (d + 1) 0 (ZMod.val (0 : F)) = d := by
    have := fval_zero
    show d + 1 - 1 - (ZMod.val (0 : F) - 0) = d
    omega
  rw [e, Ghost.extend_at] at hv
  exact hv

end IxVM.Refinement.Core.DefEqAux

namespace IxVM.Refinement.Core

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.KernelLevels (RepKLevel)
open Ix.Kernel.Rules (Red DefEq)
open IxVM.Refinement.Core.DefEqAux

set_option linter.unusedVariables false

/-! ## String literals -/

/-- `KernelDefEq::try_string_lit_one`: a string literal `t`, expanded to its constructor form and
δ-reduced once, compared with `s` (`Red.strLit`, the δ step, `DefEq.redL`). -/
theorem try_string_lit_one_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelDefEq::try_string_lit_one" args h r h' calls) (ih : IH c calls) :
    Specs.DefEq.try_string_lit_one c args h r h' calls := by
  intro rc a b types hargs good hrc d Γ htypes A B hA hB hr
  subst hargs
  rcases Obs.«KernelDefEq::try_string_lit_one».obs ev with
    ⟨x_bs, cs49, v53, m64, cs72, v76, m86, cs94, ld12, ev96, ev74, ev51, hc134⟩ |
    ⟨x_lit, ld12, hne135, he139, he140, hc141⟩ | ⟨v1, ld12, hne142, he146, he147, hc148⟩
  · subst hc134
    rcases hA.lit_of_load ld12 with ⟨lp, limbs, hx, -, -, -⟩ | ⟨bp, bytes, s, hx, hb, hs, rfl⟩
    · injection hx with _ hx'
      exact absurd hx' (by decide)
    · injection hx with _ _ hx'
      injection hx' with hx''
      subst hx''
      have e1 := ObsFn.heap_extends ev96
      have e2 := ObsFn.heap_extends ev74
      obtain ⟨hsup, hctor⟩ := ih.get (.nat .str_lit_to_ctor) (by lt_calls) ev96 rc _ rfl
        (good.sub fun x hx => by simp [hx]) hrc bytes s hb hs
      obtain ⟨L, hL⟩ := strLitToConstructor_app s
      rw [hL] at hctor
      obtain ⟨E', hE', hred⟩ := ih.get (.nat .str_lit_delta_step) (by lt_calls) ev74 rc v76 types
        rfl (good.sub fun x hx => by simp [hx]) (RCRep.mono e1 hrc) hsup d Γ
        (types_mono e1 htypes) L (hctor d Γ)
      have hde := ih.get (.defEq .k_is_def_eq) (by lt_calls) ev51 rc v53 b types rfl
        (good.sub fun x hx => by simp [hx]) (RCRep.mono (e1.trans e2) hrc) d Γ
        (types_mono (e1.trans e2) htypes) E' B hE' (Tm.mono (e1.trans e2) hB) hr
      have hs1 :
          Red c.env d (.lit (.strVal s)) (.app (.const Ix.Kernel.stringOfListName []) L) := by
        rw [← hL]
        exact .strLit hsup
      exact .redL (.trans hs1 hred) hde
  · exact absurd he139 hr
  · exact absurd he146 hr

/-- `KernelDefEq::try_string_lit_pair`: `try_string_lit_one` both ways (the second by
`DefEq.symm`). -/
theorem try_string_lit_pair_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelDefEq::try_string_lit_pair" args h r h' calls) (ih : IH c calls) :
    Specs.DefEq.try_string_lit_pair c args h r h' calls := by
  intro rc a b types hargs good hrc d Γ htypes A B hA hB hr
  subst hargs
  rcases Obs.«KernelDefEq::try_string_lit_pair».obs ev with
    ⟨m2, cs13, ev15, he52, he53, hc54⟩ | ⟨v1, m2, cs13, cs62, ev15, hne55, ev64, hc97⟩
  · subst hc54
    exact ih.get (.defEq .try_string_lit_one) (by lt_calls) ev15 rc a b types rfl
      (good.sub fun x hx => by simp [hx]) hrc d Γ htypes A B hA hB field_one_ne_zero
  · subst hc97
    have ext := ObsFn.heap_extends ev15
    exact .symm (ih.get (.defEq .try_string_lit_one) (by lt_calls) ev64 rc b a types rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono ext hrc) d Γ (types_mono ext htypes) B A
      (Tm.mono ext hB) (Tm.mono ext hA) hr)

/-! ## η-expansion -/

/-- `KernelDefEq::try_eta_expand`: `DefEq.eta`. `b`'s io-inferred type head-normalizes to a `∀`
of the same binder datum (`pw_eq`) whose domain compares with the `λ`'s; the `λ`'s body, opened
under the left domain, compares with `b` applied to the opened variable (the stored
`App(lift(b, 1, 0), BVar 0)` under the context list with the left domain pushed). -/
theorem try_eta_expand_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelDefEq::try_eta_expand" args h r h' calls) (ih : IH c calls) :
    Specs.DefEq.try_eta_expand c args h r h' calls := by
  intro rc ta ba la b types hargs good hrc d Γ htypes TA BA ℓ B hTA hBA hℓ hB hr
  subst hargs
  rcases Obs.«KernelDefEq::try_eta_expand».obs ev with
    ⟨v1, m2, cs12, v39, m40, cs50, x_dom_b, w96, x_lb, m113, cs124, m148, cs159, ev14, ev52, ld88,
      ev126, ev161, he198, he199, hc200⟩ |
    ⟨v1, m2, cs12, v39, m40, cs50, x_dom_b, w96, x_lb, m113, cs124, v147, m148, cs159, v205, m206,
      cs216, m242, m264, m295, cs328, ev14, ev52, ld88, ev126, ev161, hne201, ev218, hm252, hm274,
      hm305, ev330, hc363⟩ |
    ⟨v1, m2, cs12, v39, m40, cs50, x_dom_b, w96, x_lb, v112, m113, cs124, ev14, ev52, ld88, ev126,
      hne364, he368, he369, hc370⟩ |
    ⟨v1, m2, cs12, v39, m40, cs50, v77, ev14, ev52, ld88, hne371, he375, he376, hc377⟩
  · exact absurd he198 hr
  · subst hc363
    have e1 := ObsFn.heap_extends ev14
    have e2 := ObsFn.heap_extends ev52
    have e3 := ObsFn.heap_extends ev126
    have e4 := ObsFn.heap_extends ev161
    have e5 := ObsFn.heap_extends ev218
    have e6 : Heap.Extends m206 m242 := by rw [hm252]; exact Heap.Extends.snoc _ _
    have e7 : Heap.Extends m242 m264 := by rw [hm274]; exact Heap.Extends.snoc _ _
    have e8 : Heap.Extends m264 m295 := by rw [hm305]; exact Heap.Extends.snoc _ _
    have E40 : Heap.Extends h m40 := e1.trans e2
    have E113 : Heap.Extends h m113 := E40.trans e3
    have E148 : Heap.Extends h m148 := E113.trans e4
    have E264 : Heap.Extends h m264 := (E148.trans e5).trans (e6.trans e7)
    have E295 : Heap.Extends h m295 := E264.trans e8
    -- `b`'s io-inferred type, head-normalized to a `∀`
    obtain ⟨TB, hTB, hinf⟩ := ih.get (.infer .k_infer_only) (by lt_calls) ev14 rc b types rfl
      (good.sub fun x hx => by simp [hx]) hrc d Γ htypes B hB
    obtain ⟨WB, hWB, hred⟩ := ih.get (.whnf .whnf) (by lt_calls) ev52 rc v1 types rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono e1 hrc) d Γ (types_mono e1 htypes) TB hTB
    obtain ⟨D, BD, ℓb, rfl, hD, -, hℓb⟩ := hWB.forallE_of_load ld88
    -- the binder data agree
    obtain ⟨hpw, -⟩ := ih.get (.levels .pw_eq) (by lt_calls) ev126 la x_lb rfl
      (good.sub fun x hx => by simp [hx]) ℓ ℓb (hℓ.mono E40) hℓb
    have hz : ℓ.zeronessOf = ℓb.zeronessOf := of_ite_field_ne_zero hpw field_one_ne_zero
    -- the domains
    have hdom := ih.get (.defEq .k_is_def_eq) (by lt_calls) ev161 rc ta x_dom_b types rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono E113 hrc) d Γ (types_mono E113 htypes) TA D
      (Tm.mono E113 hTA) (Tm.mono e3 hD) hne201
    -- `b` lifted past the new binder: the same image, one depth further in
    have hlift := ih.get (.subst .expr_lift) (by lt_calls) ev218 b 1 0 rfl
      (good.sub fun x hx => by simp [hx]) (by have := fval_one; omega) 0 1
      (by have := fval_one; omega) d (Ghost.extend Γ d TA) B
      (by rw [fval_zero]; exact tm_extend (Tm.mono E148 hB))
    simp only [fval_zero, Nat.add_zero] at hlift
    -- the stored `App(b↑, BVar 0)`: `b` applied to the new opened variable
    have happ : c.tm (d + 1) (Ghost.extend Γ d TA) m264 (.app B (.fvar d TA))
        (.ptr (.enum kexprEnum) m242.length) := by
      have hv : c.tm (d + 1) (Ghost.extend Γ d TA) m242 (.fvar d TA)
          (.ptr (.enum kexprEnum) m206.length) := by
        rw [hm252]
        exact tm_store_bvar0 m206
      rw [hm274]
      exact Tm.store_app (Tm.mono e6 hlift) hv
    -- the context list with the left domain pushed, and the body opened under it
    have hinner : c.types (Ghost.extend Γ d TA) m295 (d + 1)
        (.ptr (.enum kexprListEnum) m264.length) := by
      rw [hm305]
      exact types_store_cons (types_mono E264 htypes) (Tm.mono E264 hTA)
    have hbody := ih.get (.defEq .k_is_def_eq) (by lt_calls) ev330 rc ba _ _ rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono E295 hrc) (d + 1) (Ghost.extend Γ d TA)
      hinner _ _ (tmk_open (Tm.mono E295 hBA)) (Tm.mono e8 happ) hr
    exact .eta hinf hred (.symm hdom) hbody (by unfold bmeta; exact hz) rfl
  · exact absurd he368 hr
  · exact absurd he375 hr

/-- `KernelDefEq::try_eta_swap`: exactly one side a `λ`, η-expanded against the other
(`try_eta_expand`; `DefEq.symm` when the `λ` is on the right). -/
theorem try_eta_swap_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelDefEq::try_eta_swap" args h r h' calls) (ih : IH c calls) :
    Specs.DefEq.try_eta_swap c args h r h' calls := by
  intro rc a b types hargs good hrc d Γ htypes A B hA hB hr
  subst hargs
  rcases Obs.«KernelDefEq::try_eta_swap».obs ev with
    ⟨x_ta, x_ba, x_la, w54, w55, w56, ld12, ld46, he72, he73, hc74⟩ |
    ⟨x_ta, x_ba, x_la, v35, cs82, ld12, ld46, hne75, ev84, hc133⟩ |
    ⟨v1, x_tb, x_bb, x_lb, cs175, ld12, hne134, ld149, ev177, hc226⟩ |
    ⟨v1, v138, ld12, hne134, ld149, hne227, he231, he232, hc233⟩
  · exact absurd he72 hr
  · subst hc133
    obtain ⟨TA, BA, ℓ, rfl, hTA, hBA, hℓ⟩ := hA.lam_of_load ld12
    exact ih.get (.defEq .try_eta_expand) (by lt_calls) ev84 rc x_ta x_ba x_la b types rfl
      (good.sub fun x hx => by simp [hx]) hrc d Γ htypes TA BA ℓ B hTA hBA hℓ hB hr
  · subst hc226
    obtain ⟨TB, BB, ℓ, rfl, hTB, hBB, hℓ⟩ := hB.lam_of_load ld149
    exact .symm (ih.get (.defEq .try_eta_expand) (by lt_calls) ev177 rc x_tb x_bb x_lb a types
      rfl (good.sub fun x hx => by simp [hx]) hrc d Γ htypes TB BB ℓ A hTB hBB hℓ hA hr)
  · exact absurd he231 hr

end IxVM.Refinement.Core
