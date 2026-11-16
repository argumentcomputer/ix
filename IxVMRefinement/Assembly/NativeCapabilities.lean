import IxVMRefinement.Assembly.NativePeerInputs
import IxVMRefinement.Assembly.NativeReaderInputs

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
    (source : L1.CanonicalRecordAt context.E (Core.ixAddr block))
    {members : Array Ixon.MutConst} {ind : Ixon.Inductive}
    (blockShape : source.value.info = .muts members)
    (memberAt : members.toList[ZMod.val i]? = some (.indc ind))
    (zero : Core.ZeroFieldCtorLoad context block i) :
    ∃ ctor, ind.ctors.toList[0]? = some ctor ∧ ctor.fields.toNat = 0 := by
  obtain ⟨_, _, _, bytes, src, ms, member, ctor, _, value, hashed, address, decoded, _,
    shape, atMember, atCtor, _, valueAt, raw⟩ :=
    L1.get_ci_cprj_spec zero.good.2 zero.blockRep zero.observed
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
    (source : L1.CanonicalRecordAt context.E (Core.ixAddr block))
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

end IxVM.Refinement.Assembly
