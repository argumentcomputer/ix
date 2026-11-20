import IxVMRefinement.Assembly.NativePeerInputs
import IxVMRefinement.Assembly.NativeReaderInputs
import IxVMRefinement.Assembly.NativeOuter

/-! # Native capability data from actual metadata queries

A selected zero-field constructor query fixes the field count in the canonical parent record.
The actual reader frames transfer that count to the shape used by nativeCapsAt. This supplies
unit-like capability evidence before the constructor itself has been installed.
-/

namespace IxVM.Refinement.Assembly

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)

/-- A successful raw zero-field query proves the canonical first constructor has zero fields.
No constructor lookup or semantic type reading is required. -/
theorem native_zero_field_metadata {context : Core.ScopedCtx} {block : Bytes.Address} {i : F}
    (source : Ingress.CanonicalRecordAt context.E (Core.ixAddr block))
    {members : Array Ixon.MutConst} {ind : Ixon.Inductive}
    (blockShape : source.value.info = .muts members)
    (memberAt : members.toList[ZMod.val i]? = some (.indc ind))
    (zero : Core.ZeroFieldCtorLoad context block i) :
    ∃ ctor, ind.ctors.toList[0]? = some ctor ∧ ctor.fields.toNat = 0 := by
  obtain ⟨_, _, _, bytes, src, ms, member, ctor, _, value, hashed, address, decoded, _,
    shape, atMember, atCtor, _, valueAt, raw⟩ :=
    Ingress.get_ci_cprj_spec zero.good.2 zero.blockRep zero.observed
  have bytesEq := Core.load_escape source.stored zero.good.1 bytes hashed address
  rw [bytesEq, source.decoded] at decoded
  injection decoded with sourceEq
  subst src
  rw [blockShape] at shape
  injection shape with membersEq
  subst ms
  rw [memberAt] at atMember
  injection atMember with memberEq
  injection memberEq with memberEq
  subst member
  obtain ⟨_, _, _, fieldsBound, _, _, _, _, _, _, valueShape, _⟩ := raw
  obtain ⟨nl, ty, parent, index, slot, params, safety, zeroPayload⟩ := zero.zeroFields
  rw [valueShape] at valueAt
  have same := Except.ok.inj (valueAt.symm.trans zeroPayload)
  simp only [Value.construct.injEq, List.cons.injEq, true_and, and_true] at same
  obtain ⟨_, _, _, _, _, _, fieldsEq, _⟩ := same
  refine ⟨ctor, by simpa only [ZMod.val_zero] using atCtor, ?_⟩
  exact Decl.nat_eq_of_field_eq_bounded (Nat.lt_trans fieldsBound (by decide)) (by decide) fieldsEq

/-- The actual reader frame transfers the observed zero-field count into the staged native
capabilities. It applies equally while the constructor key is still fresh. -/
theorem native_unitLikeCaps_of_reader {context : Core.ScopedCtx} {block : Bytes.Address} {i : F}
    (source : Ingress.CanonicalRecordAt context.E (Core.ixAddr block))
    {members : Array Ixon.MutConst} {ind : Ixon.Inductive}
    (blockShape : source.value.info = .muts members)
    (memberAt : members.toList[ZMod.val i]? = some (.indc ind))
    (zero : Core.ZeroFieldCtorLoad context block i)
    (oneCtor : ind.ctors.size = 1)
    {cx : Ix.Kernel.Reader.Ctx .anon} {mr : Ix.Kernel.Reader.MemberReader .anon}
    {rows : List NativeCtorRow}
    (frames : List.Forall₂ (NativeCtorReaderCheckedFrame cx (Core.ixAddr block) mr)
      (nativeCtorSlots [(ZMod.val i, ind)]) rows)
    {parts : Ix.Kernel.InductiveShape .anon} {isRec : Bool}
    (ctors : parts.ctors = rows.map (fun row => (row.1, row.2.2)))
    (noIndices : parts.nIdx = 0) :
    (Ix.Kernel.nativeCapsAt parts isRec).unitlike = true ∧
      (Ix.Kernel.nativeCapsAt parts isRec).unitParams = parts.nP := by
  obtain ⟨ctor, atCtor, zeroFields⟩ := native_zero_field_metadata source blockShape memberAt zero
  obtain ⟨actual, ctorArray⟩ := Ix.CompileCert.ReaderIndex.array_one ind.ctors oneCtor
  have same : actual = ctor := by simpa [ctorArray] using atCtor
  subst actual
  have frames' : List.Forall₂ (NativeCtorReaderCheckedFrame cx (Core.ixAddr block) mr)
      [(ZMod.val i, ctor, 0)] rows := by simpa [nativeCtorSlots, ctorArray] using frames
  cases frames' with
  | cons frame rest =>
    cases rest
    have fieldEq := frame.1.2.2.2.2
    simp [Ix.Kernel.nativeCapsAt, ctors, noIndices, fieldEq, zeroFields]

/-- A selected semantic stage keeps the exact native environment and caller scope. -/
abbrev NativeFormerRunInput.scopedStageCtx {base : Core.Ctx} {block : Bytes.Address} {i : F}
    {source : Ingress.CanonicalRecordAt base.E (Core.ixAddr block)}
    {members : Array Ixon.MutConst} {ind : Ixon.Inductive} {rawType : Core.KExpr} {calls : List (Call F)}
    (input : NativeFormerRunInput base block i source members ind rawType calls)
    (parts : Ix.Kernel.InductiveShape .anon) (isRec : Bool) (allowed : Call F → Prop) : Core.ScopedCtx :=
  { toCtx := input.stageCtx parts isRec, allowed := allowed }

/-- The current former's unit-like load obligation follows from actual raw metadata and
reader frames at its native capabilities. The constructor may still be fresh in this stage. -/
theorem NativeFormerRunInput.unitLikeRaw_current {base : Core.Ctx} {block : Bytes.Address} {i : F}
    {source : Ingress.CanonicalRecordAt base.E (Core.ixAddr block)}
    {members : Array Ixon.MutConst} {ind : Ixon.Inductive} {rawType : Core.KExpr} {rootCalls : List (Call F)}
    (input : NativeFormerRunInput base block i source members ind rawType rootCalls)
    (native : input.NativeCall) (rootGood : Core.Good base rootCalls) (tableWf : base.t.wf = true)
    {parts : Ix.Kernel.InductiveShape .anon} {isRec : Bool} {allowed : Call F → Prop}
    (params : parts.nP = ind.params.toNat) (indices : parts.nIdx = ind.indices.toNat)
    {cx : Ix.Kernel.Reader.Ctx .anon} {mr : Ix.Kernel.Reader.MemberReader .anon}
    {rows : List NativeCtorRow}
    (frames : List.Forall₂ (NativeCtorReaderCheckedFrame cx (Core.ixAddr block) mr)
      (nativeCtorSlots [(ZMod.val i, ind)]) rows)
    (ctors : parts.ctors = rows.map (fun row => (row.1, row.2.2)))
    (notBasis : Ix.Kernel.reservedBasisNames.contains
      (base.κ (Core.iprjAddr (Core.ixAddr block) (ZMod.val i))) = false)
    {ap ptr nl ty safety parentPtr : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    {address parent : Bytes.Address} {p j : F}
    {stored : Ix.Kernel.ConstantVal .anon} {caps : Ix.Kernel.IndCaps .anon}
    (loaded : ObsFn Core.W "Ingress::get_ci" [ap] h ptr h' calls)
    (good : Core.Good (input.stageCtx parts isRec) calls)
    (addressRep : Bytes.RepAddressRef Core.addrTy h address ap)
    (current : base.κ (Core.ixAddr address) = base.κ (Core.iprjAddr (Core.ixAddr block) (ZMod.val i)))
    (payload : loadValue h' ptr = .ok (.construct Core.kciEnum "Induct"
      [nl, ty, .field p, .field 0, .field 1, safety, parentPtr, .field j]))
    (parentRep : Bytes.RepAddressRef Core.addrTy h' parent parentPtr)
    (found : (input.stageCtx parts isRec).env.find? (base.κ (Core.ixAddr address)) = some (.indInfo stored caps))
    (zero : Core.ZeroFieldCtorLoad (input.scopedStageCtx parts isRec allowed) parent j) :
    caps.unitlike = true ∧ caps.unitParams = ZMod.val p ∧
      (Ix.Kernel.reservedBasisNames.contains (base.κ (Core.ixAddr address)) = false ∨
        (ZMod.val p = 0 ∧ ∀ us,
          Ix.Kernel.isUnitLikeTy (input.stageCtx parts isRec).env (.const (base.κ (Core.ixAddr address)) us) = true)) := by
  let context := input.scopedStageCtx parts isRec allowed
  have contextKeyed : context.TableKeyed := ⟨rfl⟩
  obtain ⟨projection, projectionShape⟩ := input.projectionSource
  have peers := native_peer_reads (raw := context) source projection projectionShape input.blockShape
    (by simpa only [Array.getElem?_toList] using input.memberAt) (input.oneFamily native rootGood) tableWf
  obtain ⟨actualType, actualSafety, actualPtr, actualParent, actualPayload, actualRep, actualParentEq⟩ :=
    peers.self_ind ap ptr h h' calls address loaded good addressRep current
  have same := Except.ok.inj (actualPayload.symm.trans payload)
  simp only [Value.construct.injEq, List.cons.injEq, true_and, and_true] at same
  obtain ⟨_, _, paramsEq, indicesEq, countEq, _, ptrEq, indexEq⟩ := same
  have noIndices : ind.indices.toNat = 0 :=
    Decl.nat_eq_of_field_eq_bounded (Nat.lt_trans input.indicesBound (by decide)) (by decide) indicesEq
  have oneCtor : ind.ctors.size = 1 :=
    Decl.nat_eq_of_field_eq_bounded (Nat.lt_trans input.ctorCountBound (by decide)) (by decide) countEq
  have pEq : ind.params.toNat = ZMod.val p := by
    have fieldValues := congrArg ZMod.val (Value.field.inj paramsEq)
    have canonicalBound : ind.params.toNat < 18446744069414584321 :=
      Nat.lt_trans input.paramsBound (by decide)
    simpa only [ZMod.val_natCast_of_lt canonicalBound] using fieldValues
  have jEq : i = j := Value.field.inj indexEq
  subst j
  have parentSame : actualParent = parent :=
    Bytes.repAddressRef_inj U32.Goldilocks.compatible (by simpa only [ptrEq] using actualRep) parentRep
  have parentBlock : parent = block := Decl.ixAddr_inj (by rw [← parentSame]; exact actualParentEq)
  rw [parentBlock] at zero
  have capability := native_unitLikeCaps_of_reader (block := block) (isRec := isRec) source input.blockShape input.memberAt zero oneCtor
    frames ctors (indices.trans noIndices)
  have currentLookup : (input.stageCtx parts isRec).env.find? (base.κ (Core.ixAddr address)) =
      some (.indInfo input.annotated (Ix.Kernel.nativeCapsAt parts isRec)) := by
    have named : input.annotated.name = base.κ (Core.iprjAddr (Core.ixAddr block) (ZMod.val i)) :=
      input.stored.1
    rw [current, ← named]
    exact Ix.Kernel.Env.find?_cons_self _ _
  have capsEq : Ix.Kernel.nativeCapsAt parts isRec = caps :=
    (Ix.Kernel.ConstantInfo.indInfo.inj (Option.some.inj (currentLookup.symm.trans found))).2
  rw [← capsEq]
  exact ⟨capability.1, capability.2.trans (params.trans pEq), .inl (by rwa [current])⟩


end IxVM.Refinement.Assembly
