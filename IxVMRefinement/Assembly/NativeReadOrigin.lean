import IxVMRefinement.Assembly.NativeFormerReader
import IxVMRefinement.Assembly.NativeWalkedInputs

/-! # Native former origins from the actual reader and walked checks

The successful reader supplies the former expression read used by the Source conversion
producer. The resulting input keeps the same actual row, declaration prefix and member index.
Reader naming and blob agreement remain explicit until their support-local producers apply.
-/

namespace IxVM.Refinement.Assembly

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)

/-- Compose an actual singleton-family reader run with its admitted walked member check.
The original former expression read is extracted from the reader loop. -/
theorem admitted_native_former_input_of_reader {V : IxVM.Refinement.View} {binding : Ix.Kernel.Admission.Binding}
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
    (one : Ix.CompileCert.ReaderIndex.inductives members = #[(slot, ind)])
    {cx : Ix.Kernel.Reader.Ctx .anon} {state : Ix.Kernel.Reader.State .anon}
    {records : Array (_root_.Address × Ixon.Constant)} {result : Ix.Kernel.Reader.Read .anon}
    (indexBuilt : cx.index = Ix.Kernel.Reader.buildIndex cx.store records)
    (readerSource : cx.store (Core.ixAddr block) = some source.value)
    (read : Ix.Kernel.Reader.readInductive cx state (Core.ixAddr block) source.value members = .ok result)
    (keyed : ∀ address key, cx.keyAt address = .ok key →
      key = (nativeOriginCtx witness trace env lim).κ address)
    (selfKeyed : ∀ index address reading key,
      (L1.blockRecurAddrs (Core.ixAddr block) members.toList)[index]? = some address →
      (if index < members.size then some (cx.memberKey (.member (Core.ixAddr block) index)) else none) =
        some reading → reading = .ok key → key = (nativeOriginCtx witness trace env lim).κ address)
    (blobReads : ∀ address bytes, Hashed calls bytes → Address.blake3Pure bytes = address →
      cx.blob address = some bytes) :
    ∃ (generated : List (Ix.Kernel.Declaration .anon)) (bare : Ix.Kernel.Reader.Read .anon)
      (readerBlock : Ix.Kernel.Reader.BlockRead .anon) (row : NativeFormerRow),
      result.decls.toList = generated ++ bare.decls.toList ∧
      Ix.Kernel.Reader.lowerInductiveBare readerBlock = .ok bare ∧ readerBlock.types.toList = [row] ∧
      NativeFormerReaderFrame cx (Core.ixAddr block)
        (Ix.Kernel.Reader.MemberReader.mk' cx source.value id
          (fun index => if index < members.size then
            some (cx.memberKey (.member (Core.ixAddr block) index)) else none))
        (slot, ind) row ∧
      Nonempty (NativeFormerRunInput (nativeOriginCtx witness trace env lim) block (slot : F)
        source members ind row.1.type calls) := by
  obtain ⟨generated, bare, readerBlock, row, declarations, lowered, types, frame⟩ :=
    readInductive_one_former_frame indexBuilt readerSource shape memberAt one read
  refine ⟨generated, bare, readerBlock, row, declarations, lowered, types, frame, ?_⟩
  exact admitted_native_former_input witness phase loaded bounded env lim claimBytes noCollision
    source shape memberAt walked {} frame.2.1 keyed selfKeyed blobReads

end IxVM.Refinement.Assembly
