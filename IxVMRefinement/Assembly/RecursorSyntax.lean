import IxVMRefinement.Obs.KernelCheck0
import IxVMRefinement.Obs.KernelModeled0

/-! # Syntactic recursor guards from actual Source observations

Family discovery peels literal forall nodes. It does not unfold a definition alias of the
whole recursor type. These facts use the observed control flow and heap reads directly,
without a semantic environment or a caller-supplied analysis result.
-/

namespace IxVM.Refinement.Assembly

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM (F)
open Obs (W)

/-- Peeling to a forall requires a forall at the original input, even when no binder
was requested: the zero case returns the original expression and heap unchanged. -/
theorem peel_to_forall_requires_forall
    {expr count result domain body mark : SourceValue F} {heap final : Heap F}
    {calls : List (Call F)}
    (observed : ObsFn W "KernelCheck::peel_n_foralls" [expr, count] heap result final calls)
    (loaded : loadValue final result = .ok
      (.construct "KernelTypes::KExprNode" "Forall" [domain, body, mark])) :
    ∃ inputDomain inputBody inputMark, loadValue heap expr = .ok
      (.construct "KernelTypes::KExprNode" "Forall" [inputDomain, inputBody, inputMark]) := by
  cases Obs.«KernelCheck::peel_n_foralls».obs observed with
  | n0 _ output heapEq _ =>
    rw [output, heapEq] at loaded
    exact ⟨domain, body, mark, loaded⟩
  | other domain body mark _ _ _ loaded _ _ _ =>
    exact ⟨domain, body, mark, loaded⟩

/-- A whole-type constant alias cannot pass the syntactic family telescope guard. -/
theorem constant_type_cannot_peel_to_forall
    {expr count result address levels domain body mark : SourceValue F} {heap final : Heap F}
    {calls : List (Call F)}
    (constant : loadValue heap expr = .ok
      (.construct "KernelTypes::KExprNode" "Const" [address, levels]))
    (observed : ObsFn W "KernelCheck::peel_n_foralls" [expr, count] heap result final calls)
    (loaded : loadValue final result = .ok
      (.construct "KernelTypes::KExprNode" "Forall" [domain, body, mark])) : False := by
  obtain ⟨_, _, _, initial⟩ := peel_to_forall_requires_forall observed loaded
  rw [constant] at initial
  cases initial

/-- Successful family discovery exposes the actual recursor load and a literal initial
forall in its declared type. The selected load's child calls are part of the observation. -/
theorem rec_family_block_type_forall {address result : SourceValue F} {heap final : Heap F}
    {calls : List (Call F)}
    (observed : ObsFn W "KernelModeled::rec_family_block" [address] heap result final calls) :
    ∃ loadedHeap pointer loadCalls levels type parameters rest domain body mark,
      ObsFn W "Ingress::get_ci" [address] heap pointer loadedHeap loadCalls ∧
      loadValue loadedHeap pointer = .ok
        (.construct "KernelTypes::KConstantInfo" "Rec" (levels :: type :: parameters :: rest)) ∧
      loadValue loadedHeap type = .ok
        (.construct "KernelTypes::KExprNode" "Forall" [domain, body, mark]) ∧
      (∀ call ∈ loadCalls, call ∈ calls) := by
  match Obs.«KernelModeled::rec_family_block».obs observed with
  | .run (m2 := loadedHeap) (p10 := pointer) (cs16 := loadCalls)
      (w33 := levels) (x_ty := type) (x_np := parameters)
      (w34 := indices) (w35 := motives) (w36 := minors) (w37 := rules)
      (w38 := kFlag) (w39 := unsafeFlag) (w40 := block) (w41 := position)
      (ev18 := load) (ld12 := recursor) (ev110 := peel) (ld138 := head)
      (hc333 := children) .. =>
    obtain ⟨domain, body, mark, initial⟩ := peel_to_forall_requires_forall peel head
    refine ⟨loadedHeap, pointer, loadCalls, levels, type, parameters,
      [indices, motives, minors, rules, kFlag, unsafeFlag, block, position],
      domain, body, mark, load, recursor, initial, ?_⟩
    intro call member
    rw [children]
    simp [member]

end IxVM.Refinement.Assembly
