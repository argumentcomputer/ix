import IxVMRefinement.Assembly.NativeCtorInputs
import IxVMRefinement.Core.CallHeaps

/-! # Constructor load and scope observations from the native loop

The successful loop itself supplies one concrete constructor load and scope check at every
slot. These observations carry no semantic installation or typing premise.
-/

namespace IxVM.Refinement.Assembly

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)

/-- The actual load, header guards, and scope check for one constructor slot. -/
structure CtorScopeRead (block : Bytes.Address) (indIndex ctorIndex safety : F)
    (params levels : Nat) (calls : List (Call F)) where
  blockArg ptr result : SourceValue F
  before after scopeBefore scopeAfter : Heap F
  loadCalls scopeCalls : List (Call F)
  nl ty parent member slot numParams numFields unsafeFlag : SourceValue F
  loaded : ObsFn Core.W "Ingress::get_ci_cprj" [blockArg, .field indIndex, .field ctorIndex]
    before ptr after loadCalls
  blockRep : Bytes.RepAddressRef Core.addrTy before block blockArg
  tag : loadValue after ptr = .ok (.construct Core.kciEnum "Ctor"
    [nl, ty, parent, member, slot, numParams, numFields, unsafeFlag])
  memberChecked : member = .field indIndex
  slotChecked : slot = .field ctorIndex
  levelsChecked : nl = .field (levels : F)
  paramsChecked : numParams = .field (params : F)
  safetyChecked : unsafeFlag = .field safety
  extended : Heap.Extends after scopeBefore
  scoped : ObsFn Core.W "KernelCheck::validate_expr_well_scoped"
    [ty, .field 0, nl] scopeBefore result scopeAfter scopeCalls
  loadSubset : ∀ call ∈ loadCalls, call ∈ calls
  scopeMember : (⟨"KernelCheck::validate_expr_well_scoped", [ty, .field 0, nl], scopeBefore⟩ : Call F) ∈ calls

/-- Every slot covered by a successful native constructor loop has an actual guarded load
and scope check. The natural index is kept below the checked constructor-count bound. -/
theorem native_ctor_scope_reads {block : Bytes.Address} {indIndex safety : F}
    {params indices count levels : Nat} (countBound : count < 4294967296)
    {rootCalls : List (Call F)} :
    ∀ (remaining start : Nat) {rc former blockArg sortLevel result : SourceValue F}
      {h h' : Heap F} {calls : List (Call F)},
      remaining + start = count →
      Bytes.RepAddressRef Core.addrTy h block blockArg →
      (∀ call ∈ calls, call ∈ rootCalls) →
      ObsFn Core.W "KernelCheck::check_inductive_shape_ctors"
        [rc, former, .field (params : F), .field (indices : F), .field (count : F),
          .field (levels : F), blockArg, .field indIndex, sortLevel, .field safety, .field (start : F)]
        h result h' calls →
      ∀ offset < remaining, Nonempty (CtorScopeRead block indIndex ((start + offset : Nat) : F)
        safety params levels rootCalls)
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _, offset, bound => by omega
  | remaining + 1, start, rc, former, blockArg, sortLevel, result, h, h', calls,
      total, blockRep, subset, evaluated => by
    match Obs.«KernelCheck::check_inductive_shape_ctors».obs evaluated with
    | .n0 (op17 := operation) .. =>
      have zero : (.field ((0 : Nat) : F) : SourceValue F) =
          .field (((count - start : Nat) : F)) := by
        simpa using Decl.evalBinOp_sub_nat (by omega : start ≤ count) operation
      have equal := Decl.nat_eq_of_field_eq (by decide) (by omega) zero
      omega
    | .other (m34 := after) (p41 := ptr) (cs47 := loadCalls)
        (x_c_nlvls := nl) (x_cty := ty) (x_c_block := parent)
        (x_c_ind_idx := member) (x_c_cidx := slot) (x_c_np := np) (x_c_nf := nf)
        (x_c_unsafe := unsafeFlag) (v318 := scopeResult) (m144 := scopeBefore)
        (m319 := scopeAfter) (cs329 := scopeCalls) (m655 := nextHeap)
        (cs695 := nextCalls) (v708 := nextIndex)
        (ev49 := loaded) (ld43 := tag) (ev154 := addressEq)
        (heq205 := memberChecked) (heq233 := slotChecked) (heq261 := levelsChecked)
        (heq289 := paramsChecked) (heq317 := safetyChecked) (ev331 := scoped)
        (op792 := addition) (ev697 := nextRun) (hc794 := allCalls) .. =>
      have added := Decl.evalBinOp_add_nat start 1 addition
      subst nextIndex
      have nextMember : (⟨"KernelCheck::check_inductive_shape_ctors",
          [rc, former, .field (params : F), .field (indices : F), .field (count : F),
            .field (levels : F), blockArg, .field indIndex, sortLevel, .field safety,
            .field ((start + 1 : Nat) : F)], nextHeap⟩ : Call F) ∈ calls := by
        rw [allCalls]
        simp
      have nextBlock := Bytes.repAddressRef_heapMono₂ Core.addrTy
        (evaluated.call_heap_bounds nextMember).1 blockRep
      have rest := native_ctor_scope_reads countBound remaining (start + 1) (by omega)
        nextBlock (fun call member => subset call (by rw [allCalls]; simp [member])) nextRun
      have current : CtorScopeRead block indIndex (start : F) safety params levels rootCalls := {
        blockArg := blockArg, ptr := ptr, result := scopeResult
        before := h, after := after, scopeBefore := scopeBefore, scopeAfter := scopeAfter
        loadCalls := loadCalls, scopeCalls := scopeCalls
        nl := nl, ty := ty, parent := parent, member := member, slot := slot
        numParams := np, numFields := nf, unsafeFlag := unsafeFlag
        loaded := loaded, blockRep := blockRep, tag := tag
        memberChecked := memberChecked, slotChecked := slotChecked
        levelsChecked := levelsChecked, paramsChecked := paramsChecked, safetyChecked := safetyChecked
        extended := addressEq.heap_extends
        scoped := by simpa only [levelsChecked] using scoped
        loadSubset := fun call member => subset call (by rw [allCalls]; simp [member])
        scopeMember := by
          rw [levelsChecked]
          exact subset _ (by rw [allCalls]; simp) }
      intro offset bounded
      cases offset with
      | zero => simpa only [Nat.add_zero] using (⟨current⟩ : Nonempty _)
      | succ offset =>
        have picked := rest offset (by omega)
        simpa only [show start + 1 + offset = start + (offset + 1) by omega] using picked

end IxVM.Refinement.Assembly
