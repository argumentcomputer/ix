import IxVMRefinement.Assembly.NativeWalkedInputs
import IxVMRefinement.Decl.NativeShape

/-! # Native route selection before reader expression conversion

The actual member load fixes the inductive header before any semantic type is chosen. Its
checked dispatch either exposes the native shape call and unique family or retains the
modeled call. This supplies reader ordering data without assuming a typed former input first.
-/

namespace IxVM.Refinement.Assembly

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)

/-- A walked member's bounded slot has its exact field encoding. -/
theorem native_member_slot_value {base : Core.Ctx} {bindingAddr : _root_.Address}
    {block : Bytes.Address} {members : Array Ixon.MutConst} {slot : Nat} {ind : Ixon.Inductive}
    {calls : List (Call F)}
    (checked : Claim.MutsMemberCheckedAtFull calls bindingAddr base.t (Core.ixAddr block) members slot)
    (memberAt : members[slot]? = some (.indc ind)) (bounded : IxVM.Consistency.Bounded calls) :
    ZMod.val (slot : F) = slot :=
  ZMod.val_natCast_of_lt (Nat.lt_trans (native_member_slot_bound checked memberAt bounded) (by decide))

/-- The actual loaded header selects the native or modeled branch before the reader type
is supplied. Native dispatch establishes the singleton family at its actual member slot. -/
theorem native_member_shape_dispatch {base : Core.Ctx} {bindingAddr : _root_.Address}
    {block : Bytes.Address} {members : Array Ixon.MutConst} {slot : Nat} {ind : Ixon.Inductive}
    {calls : List (Call F)}
    (source : L1.CanonicalRecordAt base.E (Core.ixAddr block))
    (blockShape : source.value.info = .muts members) (memberAt : members[slot]? = some (.indc ind))
    (checked : Claim.MutsMemberCheckedAtFull calls bindingAddr base.t (Core.ixAddr block) members slot)
    (good : Core.Good base calls) (coverage : L1.CanonicalHashCoverage base.E calls) :
    ∃ (rc typePtr blockPtr : SourceValue F) (heap : Heap F),
      Bytes.RepAddressRef Core.addrTy heap block blockPtr ∧
      ((Ix.CompileCert.ReaderIndex.inductives members = #[(slot, ind)] ∧
        Nonempty (Decl.NativeInductShapeCall rc typePtr blockPtr (.field (slot : F))
          (L1.repBoolField ind.isUnsafe) ind.params.toNat ind.indices.toNat ind.ctors.size ind.lvls.toNat
          heap calls)) ∨ Decl.ModeledInductCall blockPtr heap calls) := by
  have slotBound := native_member_slot_bound checked memberAt good.2
  have slotValue := native_member_slot_value checked memberAt good.2
  have roundtrip : slot.toUInt64.toNat = slot := UInt64.toNat_ofNat_of_lt (Nat.lt_trans slotBound (by decide))
  obtain ⟨projection, projectionValue, full⟩ := native_member_checked_source checked memberAt good coverage
  obtain ⟨_, _, checkHeap, _, rc, addr, ptr, value, _, loadCalls, checkCalls,
    _, _, addressRep, _, loaded, _, loadSubset, valueAt, checkRun, _, checkSubset⟩ := full
  obtain ⟨address, addressRep, addressEq⟩ := addressRep
  let projectionAt := projection.reindex addressEq
  have projectionShape : projectionAt.value.info = .iPrj ⟨slot.toUInt64, Core.ixAddr block⟩ := by
    change projection.value.info = _
    rw [projectionValue]
  obtain ⟨parent, parentArg, _, inner, parentEq, _, parentRep, directLoad, innerSubset, _⟩ :=
    L1.get_ci_iPrj_subcall (base := base) projectionAt projectionShape addressRep (good.sub loadSubset) loaded
  have parentSame : parent = block := Decl.ixAddr_inj parentEq
  subst parent
  rw [roundtrip] at directLoad
  have memberAtField : members.toList[ZMod.val (slot : F)]? = some (.indc ind) := by
    rw [slotValue]
    simpa only [Array.getElem?_toList] using memberAt
  obtain ⟨typePtr, blockPtr, actualBlock, payload, blockRep, blockEq⟩ :=
    native_former_header_exact (base := base) source blockShape memberAtField
      (good.sub (fun call member => loadSubset call (innerSubset call member))) parentRep directLoad
  have blockSame : actualBlock = block := Decl.ixAddr_inj blockEq
  subst actualBlock
  have valueEq := Except.ok.inj (valueAt.symm.trans payload)
  subst value
  refine ⟨rc, typePtr, blockPtr, checkHeap, blockRep, ?_⟩
  rcases Decl.native_induct_dispatch checkRun with native | modeled
  · obtain ⟨native⟩ := native
    let framed := native.mono checkSubset
    have few := native_block_inductive_count (base := base) source blockShape
      (good.sub framed.modeSubset)
      (Bytes.repAddressRef_heapMono₂ Core.addrTy framed.initialToMode blockRep) framed.modeRun
    exact .inl ⟨native_inductives_singleton few memberAt, ⟨framed⟩⟩
  · obtain ⟨before, result, after, children, observed, nonzero, extended, member, included⟩ := modeled
    exact .inr ⟨before, result, after, children, observed, nonzero, extended,
      checkSubset _ member, fun call inside => checkSubset call (included call inside)⟩

/-- Admission and the actual walked closure supply raw native dispatch and the member's
canonical field embedding, without a reader expression or semantic load premise. -/
theorem admitted_native_raw_dispatch {V : IxVM.Refinement.View} {binding : Ix.Kernel.Admission.Binding}
    (witness : IxVM.Consistency.ReaderAdmissionWitness V binding)
    {trace : Ixon.Env} {calls : List (Call F)} {seeds : List _root_.Address}
    (phase : Claim.WalkedL6 calls witness.table trace seeds)
    (loaded : IxVM.Consistency.LoadedBy calls trace) (bounded : IxVM.Consistency.Bounded calls)
    (env : Ix.Kernel.Env .anon) (lim : Option Nat) (claimBytes : ByteArray)
    (noCollision : ¬ V.HashedCollision
      (claimBytes :: binding.bytes :: IxVM.Consistency.readerImages V) calls)
    {bindingAddr : _root_.Address} {block : Bytes.Address} {members : Array Ixon.MutConst}
    {slot : Nat} {ind : Ixon.Inductive}
    (source : L1.CanonicalRecordAt (nativeOriginCtx witness trace env lim).E (Core.ixAddr block))
    (shape : source.value.info = .muts members) (memberAt : members[slot]? = some (.indc ind))
    (walked : WkAll calls bindingAddr witness.table trace (Core.ixAddr block)) :
    ZMod.val (slot : F) = slot ∧
    ∃ (rc typePtr blockPtr : SourceValue F) (heap : Heap F),
      Bytes.RepAddressRef Core.addrTy heap block blockPtr ∧
      ((Ix.CompileCert.ReaderIndex.inductives members = #[(slot, ind)] ∧
        Nonempty (Decl.NativeInductShapeCall rc typePtr blockPtr (.field (slot : F))
          (L1.repBoolField ind.isUnsafe) ind.params.toNat ind.indices.toNat ind.ctors.size ind.lvls.toNat
          heap calls)) ∨ Decl.ModeledInductCall blockPtr heap calls) := by
  have good : Core.Good (nativeOriginCtx witness trace env lim) calls :=
    admittedCore_good witness (fun _ => True) env lim claimBytes loaded bounded noCollision
  have coverage := admitted_canonicalHashCoverage witness phase
  have checked := admitted_native_member_check witness env lim source shape memberAt walked good
  exact ⟨native_member_slot_value (base := nativeOriginCtx witness trace env lim) (block := block) checked memberAt bounded,
    native_member_shape_dispatch source shape memberAt checked good coverage⟩

end IxVM.Refinement.Assembly
