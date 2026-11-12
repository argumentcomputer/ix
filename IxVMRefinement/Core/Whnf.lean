import IxVMRefinement.Core.Registry
import IxVMRefinement.Obs.KernelWhnf

/-! # The slice, on the registry: `apply_spine`

The first step lemma stated against the registry, and the pattern every package's step lemmas
follow: take the derivation's path from the generated path lemma
(`IxVMRefinement.Obs`, `«f».obs`), read the callees' specs from the induction hypothesis
(`IH.get`), and conclude the function's registered spec. -/

namespace IxVM.Refinement.Core

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List

/-- `KernelWhnf::apply_spine` applies the head to the spine, one stored `App` node per
argument. -/
theorem apply_spine_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelWhnf::apply_spine" args h r h' calls) (ih : IH c calls) :
    Specs.Whnf.apply_spine c args h r h' calls := by
  intro hd sp hargs good d Γ k H As hH hAs
  subst hargs
  rcases Obs.«KernelWhnf::apply_spine».obs ev with ⟨ld, rfl, rfl, -⟩ |
    ⟨a, rest, cs, m, ld, rfl, ev', rfl⟩
  · -- `Nil => head`
    obtain rfl := RepList.nil_of_load hAs ld
    exact hH
  · -- `Cons(a, rest) => apply_spine(&App(head, a), rest)`
    obtain ⟨A, As', rfl, hA, hAs'⟩ := RepList.cons_of_load hAs ld
    have ext : Heap.Extends h (h ++ [.construct kexprEnum "App" [hd, a]]) := Heap.Extends.snoc _ _
    have hrest : Specs.Whnf.TmLk c d Γ k (h ++ [.construct kexprEnum "App" [hd, a]]) As' rest :=
      repList_heapMono₂ kexprListEnum (by intro h₁ h₂ x y e r; exact Tm.mono e r) ext hAs'
    exact ih.get (.whnf .apply_spine) (by simp) ev' _ _ rfl
      (good.sub fun x hx => List.mem_cons_of_mem _ hx) d Γ k (.app H A) As'
      (Tm.store_app hH hA) hrest

end IxVM.Refinement.Core
