import IxVMRefinement.Assembly.NativeReadOrigin
import IxVMRefinement.Assembly.NativeReaderAgreement

/-! # Native reader origins at the actual admitted context

The admitted context constructs explicit-key and literal-byte agreement. The native origin
producer therefore needs only its remaining block-member naming correspondence; it does not
ask for global blob membership or a separate explicit-key interpretation.
-/

namespace IxVM.Refinement.Assembly

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)

/-- The selected admitted reader context used by the actual native-origin adapter. -/
noncomputable abbrev admittedNativeReaderCtx {V : IxVM.Refinement.View} {binding : Ix.Kernel.Admission.Binding}
    (witness : IxVM.Consistency.ReaderAdmissionWitness V binding) (trace : Ixon.Env)
    (keepTrace : _root_.Address → Prop) (order : List _root_.Address) : Ix.Kernel.Reader.Ctx .anon :=
  ReaderStoreTransfer.readerContext witness.table witness.prelude
    (admittedOverlay witness trace keepTrace) order

/-- Actual admission constructs the native reader origin's explicit-key and blob agreement.
The block-member self-key correspondence is retained as its separate remaining naming obligation. -/
theorem admitted_native_reader_origin_in_context {V : IxVM.Refinement.View} {binding : Ix.Kernel.Admission.Binding}
    (witness : IxVM.Consistency.ReaderAdmissionWitness V binding)
    (keepTrace : _root_.Address → Prop) (order : List _root_.Address)
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
    {state : Ix.Kernel.Reader.State .anon}
    {result : Ix.Kernel.Reader.Read .anon}
    (readerSource : (admittedNativeReaderCtx witness trace keepTrace order).store (Core.ixAddr block) =
      some source.value)
    (read : Ix.Kernel.Reader.readInductive (admittedNativeReaderCtx witness trace keepTrace order) state
      (Core.ixAddr block) source.value members = .ok result)
    (selfKeyed : ∀ index address reading key,
      (L1.blockRecurAddrs (Core.ixAddr block) members.toList)[index]? = some address →
      (if index < members.size then some ((admittedNativeReaderCtx witness trace keepTrace order).memberKey (.member (Core.ixAddr block) index)) else none) =
        some reading → reading = .ok key → key = (nativeOriginCtx witness trace env lim).κ address)
    :
    ZMod.val (slot : F) = slot ∧
    ((∃ (generated : List (Ix.Kernel.Declaration .anon)) (bare : Ix.Kernel.Reader.Read .anon)
        (readerBlock : Ix.Kernel.Reader.BlockRead .anon) (row : NativeFormerRow),
        result.decls.toList = generated ++ bare.decls.toList ∧
        Ix.Kernel.Reader.lowerInductiveBare readerBlock = .ok bare ∧ readerBlock.types.toList = [row] ∧
        NativeFormerReaderFrame (admittedNativeReaderCtx witness trace keepTrace order) (Core.ixAddr block)
          (Ix.Kernel.Reader.MemberReader.mk' (admittedNativeReaderCtx witness trace keepTrace order) source.value id
            (fun index => if index < members.size then
              some ((admittedNativeReaderCtx witness trace keepTrace order).memberKey (.member (Core.ixAddr block) index)) else none))
          (slot, ind) row ∧
        List.Forall₂
          (NativeCtorReaderCheckedFrame (admittedNativeReaderCtx witness trace keepTrace order) (Core.ixAddr block)
            (Ix.Kernel.Reader.MemberReader.mk' (admittedNativeReaderCtx witness trace keepTrace order) source.value id
              (fun index => if index < members.size then
                some ((admittedNativeReaderCtx witness trace keepTrace order).memberKey (.member (Core.ixAddr block) index)) else none)))
          (nativeCtorSlots [(slot, ind)]) readerBlock.ctors.toList ∧
        readerBlock.numParams = ind.params.toNat ∧
        ∃ input : NativeFormerRunInput (nativeOriginCtx witness trace env lim) block (slot : F)
            source members ind row.1.type calls,
          ∃ native : input.NativeCall,
            Nonempty (Decl.NativeShapeCalls input.rc input.typePtr input.blockPtr (.field (slot : F))
              (L1.repBoolField ind.isUnsafe) ind.params.toNat ind.indices.toNat ind.ctors.size ind.lvls.toNat
              native.before calls)) ∨
      ∃ (blockPtr : SourceValue F) (heap : Heap F),
        Bytes.RepAddressRef Core.addrTy heap block blockPtr ∧ Decl.ModeledInductCall blockPtr heap calls) := by
  have built : ∃ records : Array (_root_.Address × Ixon.Constant),
      (admittedNativeReaderCtx witness trace keepTrace order).index =
        Ix.Kernel.Reader.buildIndex (admittedNativeReaderCtx witness trace keepTrace order).store records :=
    ⟨_, rfl⟩
  obtain ⟨records, indexBuilt⟩ := built
  have agreement := admitted_native_reader_agreement witness phase keepTrace order claimBytes loaded noCollision
  exact admitted_native_reader_dispatch_with_ctor_frames_of_blobAgreement witness phase loaded bounded
    env lim claimBytes noCollision source shape memberAt walked indexBuilt readerSource read
    agreement.1 selfKeyed agreement.2

end IxVM.Refinement.Assembly
