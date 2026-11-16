import IxVMRefinement.Obs.KernelCheck0
import IxVMRefinement.Obs.KernelCheck2
import IxVMRefinement.Obs.KernelCheck11
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
  simp at initial

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
      (⟨"Ingress::get_ci", [address], heap⟩ : Call F) ∈ calls ∧
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
      domain, body, mark, load, recursor, initial, ?_, ?_⟩
    · rw [children]; simp
    · intro call member
      rw [children]
      simp [member]

/-- The native parent scan independently requires a literal initial forall, regardless
of the field-valued count it computes for the major premise. -/
theorem rec_to_parent_addr_type_forall
    {type parameters motives minors indices result : SourceValue F} {heap final : Heap F}
    {calls : List (Call F)}
    (observed : ObsFn W "KernelCheck::rec_to_parent_addr"
      [type, parameters, motives, minors, indices] heap result final calls) :
    ∃ domain body mark, loadValue heap type = .ok
      (.construct "KernelTypes::KExprNode" "Forall" [domain, body, mark]) := by
  match Obs.«KernelCheck::rec_to_parent_addr».obs observed with
  | .run (ev50 := peel) (ld78 := major) .. =>
    exact peel_to_forall_requires_forall peel major

/-- The actual native member check reads the syntactic major's parent as an inductive.
The load is exposed with its exact heaps and child-call provenance; it is not assumed to
be an already installed semantic lookup. -/
theorem native_rec_parent_observed
    {rc address levels type parameters indices motives minors rules k unsafeFlag block position result : SourceValue F}
    {heap final : Heap F} {calls : List (Call F)}
    (observed : ObsFn W "KernelCheck::check_recursor_member"
      [rc, .construct "KernelTypes::KConstantInfo" "Rec"
        [levels, type, parameters, indices, motives, minors, rules, k, unsafeFlag, block, position], address]
      heap result final calls) :
    ∃ parent scanHeap pointer loadedHeap scanCalls loadCalls
        parentLevels parentType parentParams parentIndices constructors parentUnsafe parentBlock parentIndex,
      ObsFn W "KernelCheck::rec_to_parent_addr" [type, parameters, motives, minors, indices]
        heap parent scanHeap scanCalls ∧
      ObsFn W "Ingress::get_ci" [parent] scanHeap pointer loadedHeap loadCalls ∧
      loadValue loadedHeap pointer = .ok (.construct "KernelTypes::KConstantInfo" "Induct"
        [parentLevels, parentType, parentParams, parentIndices, constructors, parentUnsafe, parentBlock, parentIndex]) ∧
      (⟨"Ingress::get_ci", [parent], scanHeap⟩ : Call F) ∈ calls ∧
      (∀ call ∈ scanCalls ++ loadCalls, call ∈ calls) := by
  match Obs.«KernelCheck::check_recursor_member».obs observed with
  | .run (v72 := parent) (m73 := scanHeap) (p134 := pointer) (m127 := loadedHeap)
      (cs83 := scanCalls) (cs140 := loadCalls) (x__parent_nlvls := parentLevels)
      (w167 := parentType) (x_parent_np := parentParams) (x_parent_ni := parentIndices)
      (x_num_ctors := constructors) (w168 := parentUnsafe) (x_parent_block_addr := parentBlock)
      (x_parent_ind_idx := parentIndex) (hv15 := input) (ev85 := scan) (ev142 := load)
      (ld136 := parentInfo) (hc868 := children) .. =>
    injection input with _ _ fields
    simp only [List.cons.injEq, and_true] at fields
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := fields
    refine ⟨parent, scanHeap, pointer, loadedHeap, scanCalls, loadCalls,
      parentLevels, parentType, parentParams, parentIndices, constructors, parentUnsafe,
      parentBlock, parentIndex, scan, load, parentInfo, ?_, ?_⟩
    · rw [children]; simp
    · intro call member
      rw [children]
      rcases List.mem_append.mp member with inScan | inLoad <;> simp_all

/-- Native recursor checking tests the block of the actual major-premise parent. The
zero verdict and all of the selected call's children belong to the same observation. -/
theorem native_rec_actual_parent_route
    {rc address levels type parameters indices motives minors rules k unsafeFlag block position result : SourceValue F}
    {heap final : Heap F} {calls : List (Call F)}
    (observed : ObsFn W "KernelCheck::check_recursor_member"
      [rc, .construct "KernelTypes::KConstantInfo" "Rec"
        [levels, type, parameters, indices, motives, minors, rules, k, unsafeFlag, block, position], address]
      heap result final calls) :
    ∃ parent scanHeap pointer loadedHeap scanCalls loadCalls routedHeap routeCalls
        parentLevels parentType parentParams parentIndices constructors parentUnsafe parentBlock parentIndex,
      ObsFn W "KernelCheck::rec_to_parent_addr" [type, parameters, motives, minors, indices]
        heap parent scanHeap scanCalls ∧
      ObsFn W "Ingress::get_ci" [parent] scanHeap pointer loadedHeap loadCalls ∧
      loadValue loadedHeap pointer = .ok (.construct "KernelTypes::KConstantInfo" "Induct"
        [parentLevels, parentType, parentParams, parentIndices, constructors, parentUnsafe, parentBlock, parentIndex]) ∧
      ObsFn W "KernelModeled::block_is_modeled" [parentBlock]
        loadedHeap (.field 0) routedHeap routeCalls ∧
      (⟨"KernelModeled::block_is_modeled", [parentBlock], loadedHeap⟩ : Call F) ∈ calls ∧
      (∀ call ∈ routeCalls, call ∈ calls) := by
  match Obs.«KernelCheck::check_recursor_member».obs observed with
  | .run (v72 := parent) (m73 := scanHeap) (p134 := pointer) (m127 := loadedHeap)
      (cs83 := scanCalls) (cs140 := loadCalls) (x__parent_nlvls := parentLevels)
      (w167 := parentType) (x_parent_np := parentParams) (x_parent_ni := parentIndices)
      (x_num_ctors := constructors) (w168 := parentUnsafe) (x_parent_block_addr := parentBlock)
      (x_parent_ind_idx := parentIndex) (m223 := routedHeap) (cs231 := routeCalls)
      (hv15 := input) (ev85 := scan) (ev142 := load) (ld136 := parentInfo)
      (ev233 := route) (heq248 := native)
      (hc868 := children) .. =>
    injection input with _ _ fields
    simp only [List.cons.injEq, and_true] at fields
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := fields
    rw [native] at route
    refine ⟨parent, scanHeap, pointer, loadedHeap, scanCalls, loadCalls, routedHeap, routeCalls,
      parentLevels, parentType, parentParams, parentIndices, constructors, parentUnsafe,
      parentBlock, parentIndex, scan, load, parentInfo, route, ?_, ?_⟩
    · rw [children]; simp
    · intro call member
      rw [children]; simp [member]

end IxVM.Refinement.Assembly
