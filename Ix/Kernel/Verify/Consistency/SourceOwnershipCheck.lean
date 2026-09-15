/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.BlockOwnership

/-!
# Finite source ownership checks

The check reads verified source headers once, then compares only their finite
key inventories. Acceptance supplies `SourceOwnership`; neither conversion
results nor the current kernel environment are inputs.
-/

namespace Ix.Kernel.Consistency

theorem sourceOwnershipRows_mem {source : Ixon.Env} {addr : Address} {constant : Ixon.Constant}
    (verified : getConstVerified source addr true = .ok (some constant)) :
    ownershipRow addr constant ∈ sourceOwnershipRows source := by
  have present : ∃ lazy, source.consts[addr]? = some lazy := by
    cases stored : source.consts[addr]? with
    | some lazy => exact ⟨lazy, rfl⟩
    | none =>
        unfold getConstVerified at verified
        rw [stored] at verified
        cases verified
  obtain ⟨lazy, stored⟩ := present
  apply List.mem_filterMap.mpr
  refine ⟨(addr, lazy), Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr stored, ?_⟩
  simp only [verified]

/-- A successful finite inventory check discharges source ownership. Malformed
or missing source constants need no rows because verified loading cannot use them. -/
theorem SourceOwnership.ofCheck {source : Ixon.Env} (checked : sourceOwnershipCheck source = true) :
    SourceOwnership source := by
  have pair := List.all_eq_true.mp checked
  refine ⟨?_, ?_⟩
  · intro block other id left right
    obtain ⟨constant, verified, member⟩ := left
    obtain ⟨otherConstant, otherVerified, otherMember⟩ := right
    have row := List.all_eq_true.mp (pair _ (sourceOwnershipRows_mem verified))
      _ (sourceOwnershipRows_mem otherVerified)
    have key := (Array.all_eq_true_iff_forall_mem.mp (Bool.and_eq_true_iff.mp row).1) id member
    have present : (blockProjectionIds other otherConstant).contains id = true :=
      Array.contains_iff_mem.mpr otherMember
    simp only [present, Bool.not_true, Bool.false_or, ownershipRow] at key
    exact eq_of_beq key
  · intro addr constant verified standalone block projection
    obtain ⟨blockConstant, blockVerified, member⟩ := projection
    have row := List.all_eq_true.mp (pair _ (sourceOwnershipRows_mem verified))
      _ (sourceOwnershipRows_mem blockVerified)
    have absent := (Bool.and_eq_true_iff.mp row).2
    have present : (blockProjectionIds block blockConstant).contains ⟨addr, ()⟩ = true :=
      Array.contains_iff_mem.mpr member
    simp only [ownershipRow, standalone, Option.isNone_none, Bool.not_true, Bool.false_or,
      present, Bool.false_eq_true] at absent

def OwnedLazySupport.ofCheckedSource (source : Ixon.Env) (checked : sourceOwnershipCheck source = true) :
    OwnedLazySupport (TcState.newLazyAnon source) :=
  .newLazyAnon source (.ofCheck checked)

end Ix.Kernel.Consistency
