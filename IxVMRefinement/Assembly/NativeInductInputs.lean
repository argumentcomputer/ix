import IxVMRefinement.Assembly.ClaimsL1L6
import IxVMRefinement.Assembly.RawQueryCoverage
import IxVMRefinement.Assembly.NativePeerInputs
import IxVMRefinement.Decl.NativePrelude

/-! # Native inductive inputs from actual walked member checks

A walked member check already computes and hashes its projection address before loading and
checking the member. Retaining that hash identifies the actual inductive projection record
without a separately supplied projection-shape premise.
-/

namespace IxVM.Refinement.Assembly

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)

/-- The actual walked member projection hashes the canonical inductive wrapper. -/
theorem native_member_projection_hashed {base : Core.Ctx} {bindingAddr : _root_.Address}
    {block : Bytes.Address} {members : Array Ixon.MutConst} {slot : Nat} {ind : Ixon.Inductive}
    {calls : List (Call F)}
    (checked : Claim.MutsMemberCheckedAtFull calls bindingAddr base.t (Core.ixAddr block) members slot)
    (memberAt : members[slot]? = some (.indc ind)) (bounded : IxVM.Consistency.Bounded calls) :
    Hashed calls (Ixon.serConstant ⟨.iPrj ⟨slot.toUInt64, Core.ixAddr block⟩, #[], #[], #[], #[]⟩) := by
  obtain ⟨_, projectionBefore, _, _, _, _, membersPtr, blockPtr, _, _, _, _,
    projectionCalls, _, _, represented, blockRep, projected, projectionMember, projectionSubset, _⟩ := checked
  have memberCount : members.toList.length < 2 ^ 39 :=
    RomBound.bounded_length_lt bounded projectionMember (List.Mem.head _) represented
  have slotBound : slot < members.toList.length := by
    simpa only [Array.length_toList] using (Array.getElem?_eq_some_iff.mp memberAt).1
  have slotValue : ZMod.val (slot : F) = slot :=
    ZMod.val_natCast_of_lt (by
      have modulus : (2 ^ 39 : Nat) < Aiur.Library.U32.Goldilocks.modulus := by decide
      omega)
  obtain ⟨actualBlock, actualBlockRep, sameBlock⟩ := blockRep
  have same : actualBlock = block := Decl.ixAddr_inj sameBlock
  subst actualBlock
  obtain ⟨_, _, _, actualMember, _, found, _, _, hashed⟩ :=
    L1.projection_addr_hashed_spec represented actualBlockRep projected
  rw [slotValue] at found hashed
  have foundExpected : members.toList[slot]? = some (.indc ind) := by simpa using memberAt
  rw [foundExpected] at found
  injection found with sameMember
  subst actualMember
  exact Core.hashed_mono projectionSubset hashed

/-- The actual member check supplies both a checked projection invocation and its canonical
source record in the trace-backed metadata store. -/
theorem native_member_checked_source {base : Core.Ctx} {bindingAddr : _root_.Address}
    {block : Bytes.Address} {members : Array Ixon.MutConst} {slot : Nat} {ind : Ixon.Inductive}
    {calls : List (Call F)}
    (checked : Claim.MutsMemberCheckedAtFull calls bindingAddr base.t (Core.ixAddr block) members slot)
    (memberAt : members[slot]? = some (.indc ind)) (good : Core.Good base calls)
    (coverage : L1.CanonicalHashCoverage base.E calls) :
    ∃ projection : L1.CanonicalRecordAt base.E (Core.iprjAddr (Core.ixAddr block) slot),
      projection.value = ⟨.iPrj ⟨slot.toUInt64, Core.ixAddr block⟩, #[], #[], #[], #[]⟩ ∧
      Claim.CheckedAtFull calls bindingAddr base.t (Core.iprjAddr (Core.ixAddr block) slot) := by
  have hashed := native_member_projection_hashed (base := base) checked memberAt good.2
  have full : Claim.CheckedAtFull calls bindingAddr base.t (Core.iprjAddr (Core.ixAddr block) slot) :=
    mutsMemberCheckedAtFull_to_checkedAtFull good.2 checked memberAt
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, addressRep, _, loaded, _, loadSubset, _, _, _, _⟩ := full
  obtain ⟨address, represented, addressEq⟩ := addressRep
  obtain ⟨_, _, _, verified, verifiedSubset⟩ := L1.get_ci_verified_subcall loaded
  obtain ⟨source⟩ := L1.canonicalRecordAt_of_verified coverage represented verified
    (fun call member => loadSubset call (verifiedSubset call member))
  let projection := source.reindex addressEq.symm
  have bytesEq := Core.load_escape projection.stored good.1 _ hashed rfl
  have decoded := projection.decoded
  rw [← bytesEq] at decoded
  have canonical := Ixon.Verify.deConstantExact_serConstant
    (⟨.iPrj ⟨slot.toUInt64, Core.ixAddr block⟩, #[], #[], #[], #[]⟩ : Ixon.Constant)
    (L1.projConstant_wireWF_iPrj slot.toUInt64 block)
  exact ⟨projection, Except.ok.inj (decoded.symm.trans canonical), full⟩

end IxVM.Refinement.Assembly
