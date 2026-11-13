import IxVMRefinement.Infer.Basic

/-! # The application spine of full-grade inference

`KernelInfer::k_infer_app_spine_loop` walks the arguments of an application, keeping the head's
type `t` under a delayed substitution `subs_rev` (the arguments consumed so far, last first):

* at a syntactic `∀` the domain is instantiated (`inst_subs`) and the argument checked against it
  (`k_check`), and the codomain is kept under one more delayed argument;
* otherwise the instantiated type is head-normalized (`whnf`) to a `∀`, the argument checked
  against its domain, and the codomain kept under the argument alone.

Each step is `Infer.app` (the head's type reduces to the `∀`, by `Red.refl` in the first case);
the delayed substitution is the kernel's `instantiateList`, whose head is the innermost argument
(`instantiateList_cons`). -/

namespace IxVM.Refinement.Core

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open Ix.Kernel.Rules (Red DefEq Infer)

set_option linter.unusedVariables false

/-- `KernelInfer::k_infer_app_spine_loop`: `Infer.app` once per argument. -/
theorem k_infer_app_spine_loop_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelInfer::k_infer_app_spine_loop" args h r h' calls) (ih : IH c calls) :
    Specs.Infer.k_infer_app_spine_loop c args h r h' calls := by
  intro rc t sp subs types hargs good hrc d Γ htypes Ss As B Fe hSs hB hAs hinf
  subst hargs
  rcases Obs.«KernelInfer::k_infer_app_spine_loop».obs ev with
    ⟨cs23, ld12, ev25, hc42⟩ |
    ⟨x_a, x_rest, x_dom, x_cod, w79, v95, m96, cs106, v125, m126, cs136, cs174, m204, ld12, ld71,
      ev108, ev138, hm212, ev176, hc239⟩ |
    ⟨x_a, x_rest, v60, v244, m245, cs255, v274, m275, cs285, x_dom, x_cod, w331, v347, m348, cs358,
      cs396, m426, m448, ld12, ld71, hne240, ev257, ev287, ld323, ev360, hm434, hm456, ev398, hc467⟩
  · -- no argument left: the head's type, instantiated
    subst hc42
    obtain rfl := RepList.nil_of_load hAs ld12
    exact ⟨_, ih.get (.infer .inst_subs) (by lt_calls) ev25 t subs rfl
      (good.sub fun x hx => by simp [hx]) d Γ Ss B hSs hB, hinf⟩
  · -- a syntactic `∀`: check the argument against the instantiated domain
    subst hc239 hm212
    obtain ⟨A, As', rfl, hA, hAs'⟩ := RepList.cons_of_load hAs ld12
    obtain ⟨D, C, ℓ, rfl, hD, hC, hℓ⟩ := hB.forallE_of_load ld71
    have hDi := ih.get (.infer .inst_subs) (by lt_calls) ev108 x_dom subs rfl
      (good.sub fun x hx => by simp [hx]) d Γ Ss D hSs hD
    have e1 := ObsFn.heap_extends ev108
    obtain ⟨TA, hTA, hdeq⟩ := ih.get (.infer .k_check) (by lt_calls) ev138 rc x_a v95 types rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono e1 hrc) d Γ (types_mono e1 htypes) A
      (D.instantiateList Ss 0) (Tm.mono e1 hA) hDi
    have e2 := e1.trans (ObsFn.heap_extends ev138)
    have e3 := e2.trans (Heap.Extends.snoc m126 (.construct kexprListEnum "Cons" [x_a, subs]))
    have hSs' : c.tml d Γ (m126 ++ [.construct kexprListEnum "Cons" [x_a, subs]]) (A :: Ss)
        (.ptr (.enum kexprListEnum) m126.length) :=
      TmL.store_cons (Tm.mono e2 hA) (TmL.mono e2 hSs)
    have hfe : Infer c.env .full d (.app Fe A) (C.instantiateList (A :: Ss) 0) := by
      rw [Ix.Kernel.Expr.instantiateList_cons]
      rw [SubstAux.iL_forallE] at hinf
      exact .app hinf .refl hTA hdeq
    exact ih.get (.infer .k_infer_app_spine_loop) (by lt_calls) ev176 rc x_cod x_rest _ types rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono e3 hrc) d Γ (types_mono e3 htypes)
      (A :: Ss) As' C (.app Fe A) hSs' (Tm.mono e3 hC) (TmL.mono e3 hAs') hfe
  · -- otherwise: head-normalize the instantiated type to a `∀`
    subst hc467 hm434 hm456
    obtain ⟨A, As', rfl, hA, hAs'⟩ := RepList.cons_of_load hAs ld12
    have hBi := ih.get (.infer .inst_subs) (by lt_calls) ev257 t subs rfl
      (good.sub fun x hx => by simp [hx]) d Γ Ss B hSs hB
    have e1 := ObsFn.heap_extends ev257
    obtain ⟨X, hX, hred⟩ := ih.get (.whnf .whnf) (by lt_calls) ev287 rc v244 types rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono e1 hrc) d Γ (types_mono e1 htypes) _ hBi
    have e2 := e1.trans (ObsFn.heap_extends ev287)
    obtain ⟨D, C, ℓ, rfl, hD, hC, hℓ⟩ := hX.forallE_of_load ld323
    obtain ⟨TA, hTA, hdeq⟩ := ih.get (.infer .k_check) (by lt_calls) ev360 rc x_a x_dom types rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono e2 hrc) d Γ (types_mono e2 htypes) A D
      (Tm.mono e2 hA) hD
    have e3 := e2.trans (ObsFn.heap_extends ev360)
    have x1 := Heap.Extends.snoc m348 (.construct kexprListEnum "Nil" [])
    have x2 := Heap.Extends.snoc (m348 ++ [(.construct kexprListEnum "Nil" [] : SourceValue F)])
      (.construct kexprListEnum "Cons" [x_a, .ptr (.enum kexprListEnum) m348.length])
    have e4 := e3.trans (x1.trans x2)
    have hSs' : c.tml d Γ ((m348 ++ [(.construct kexprListEnum "Nil" [] : SourceValue F)]) ++
        [.construct kexprListEnum "Cons" [x_a, .ptr (.enum kexprListEnum) m348.length]]) [A]
        (.ptr (.enum kexprListEnum) (m348 ++ [(.construct kexprListEnum "Nil" [] : SourceValue F)]).length) :=
      TmL.store_cons (Tm.mono (e3.trans x1) hA) (TmL.store_nil m348)
    have hfe : Infer c.env .full d (.app Fe A) (C.instantiateList [A] 0) := by
      rw [Ix.Kernel.Expr.instantiateList_cons, Ix.Kernel.Expr.instantiateList_nil]
      exact .app hinf hred hTA hdeq
    exact ih.get (.infer .k_infer_app_spine_loop) (by lt_calls) ev398 rc x_cod x_rest _ types rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono e4 hrc) d Γ (types_mono e4 htypes)
      [A] As' C (.app Fe A) hSs' (Tm.mono ((ObsFn.heap_extends ev360).trans (x1.trans x2)) hC) (TmL.mono e4 hAs') hfe

end IxVM.Refinement.Core
