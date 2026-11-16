import IxVMRefinement.Assembly.NativeCtorOrigin
import IxVMRefinement.Assembly.NativeInductInputs

/-! # Native former inputs at actual walked owners

The walked closure supplies member checks for a mutual block. A successful direct constant
load cannot instead check the mutual block itself. This derives the former-input producer
from the actual walked owner and admitted metadata, preserving reader naming obligations.
-/

namespace IxVM.Refinement.Assembly

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)

/-- A successful direct constant check cannot load a canonical mutual-block record. -/
theorem checkedAtFull_not_muts {base : Core.Ctx} {bindingAddr address : _root_.Address}
    {calls : List (Call F)} (source : L1.CanonicalRecordAt base.E address)
    {members : Array Ixon.MutConst} (shape : source.value.info = .muts members)
    (checked : Claim.CheckedAtFull calls bindingAddr base.t address)
    (good : Core.Good base calls) : False := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, addressRep, _, loaded, _, subset, _⟩ := checked
  obtain ⟨actualAddress, addressRep, addressEq⟩ := addressRep
  let sourceAt := source.reindex addressEq
  obtain ⟨_, bytes, value, _, hashed, hashEq, decoded, _, _, _, result⟩ :=
    L1.get_ci_spec (good.sub subset).2 addressRep loaded
  have sameBytes := Core.load_escape sourceAt.stored (good.sub subset).1 bytes hashed hashEq
  rw [sameBytes, sourceAt.decoded] at decoded
  injection decoded with sameValue
  subst value
  have sourceShape : sourceAt.value.info = .muts members := shape
  simp only [L1.GetCIRawResult, sourceShape] at result

/-- A walked mutual-block owner supplies the actual check of each present inductive member. -/
theorem admitted_native_member_check {V : IxVM.Refinement.View} {binding : Ix.Kernel.Admission.Binding}
    (witness : IxVM.Consistency.ReaderAdmissionWitness V binding)
    {trace : Ixon.Env} {calls : List (Call F)} {bindingAddr : _root_.Address}
    (env : Ix.Kernel.Env .anon) (lim : Option Nat)
    {block : Bytes.Address} {members : Array Ixon.MutConst} {slot : Nat} {ind : Ixon.Inductive}
    (source : L1.CanonicalRecordAt (nativeOriginCtx witness trace env lim).E (Core.ixAddr block))
    (shape : source.value.info = .muts members) (memberAt : members[slot]? = some (.indc ind))
    (walked : WkAll calls bindingAddr witness.table trace (Core.ixAddr block))
    (good : Core.Good (nativeOriginCtx witness trace env lim) calls) :
    Claim.MutsMemberCheckedAtFull calls bindingAddr witness.table (Core.ixAddr block) members slot := by
  obtain ⟨value, stored, checked⟩ := (wkAll_closedSubwalk calls bindingAddr witness.table trace).checked _ walked
  have retained := admittedCore_trace_recordAt witness stored
  have same : value = source.value := Option.some.inj (retained.symm.trans source.recordAt)
  subst value
  rcases checked with ⟨actualMembers, actualShape, checkedMembers⟩ | checkedDirect
  · rw [shape] at actualShape
    injection actualShape with sameMembers
    subst actualMembers
    exact checkedMembers slot (Array.getElem?_eq_some_iff.mp memberAt).1
  · exact (checkedAtFull_not_muts (base := nativeOriginCtx witness trace env lim)
      source shape checkedDirect good).elim

/-- Actual claim/admission data and a walked owner construct its former input. All annotation,
projection, prelude and memory-bound witnesses are produced by the observed run. Reader key,
self-reference and blob interpretation framing remain explicit. -/
theorem admitted_native_former_input {V : IxVM.Refinement.View} {binding : Ix.Kernel.Admission.Binding}
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
    (walked : WkAll calls bindingAddr witness.table trace (Core.ixAddr block))
    {cx : Ix.Kernel.Reader.Ctx .anon}
    {self : Nat → Option (Ix.Kernel.Reader.ReadM Core.KKey)} {rawType : Core.KExpr}
    (caps : Ix.Kernel.IndCaps .anon)
    (read : (Ix.Kernel.Reader.MemberReader.mk' cx source.value id self).read ind.typ = .ok rawType)
    (keyed : ∀ address key, cx.keyAt address = .ok key → key = (nativeOriginCtx witness trace env lim).κ address)
    (selfKeyed : ∀ index address reading key,
      (L1.blockRecurAddrs (Core.ixAddr block) members.toList)[index]? = some address →
      self index = some reading → reading = .ok key → key = (nativeOriginCtx witness trace env lim).κ address)
    (blobReads : ∀ address bytes, Hashed calls bytes → Address.blake3Pure bytes = address →
      cx.blob address = some bytes) :
    Nonempty (NativeFormerRunInput (nativeOriginCtx witness trace env lim) block (slot : F)
      source members ind rawType calls) := by
  have good : Core.Good (nativeOriginCtx witness trace env lim) calls :=
    admittedCore_good witness (fun _ => True) env lim claimBytes loaded bounded noCollision
  have coverage : L1.CanonicalHashCoverage (nativeOriginCtx witness trace env lim).E calls :=
    admitted_canonicalHashCoverage witness phase
  have member := admitted_native_member_check witness env lim source shape memberAt walked good
  exact native_former_input_of_member source shape memberAt member good coverage caps read keyed selfKeyed blobReads

end IxVM.Refinement.Assembly
