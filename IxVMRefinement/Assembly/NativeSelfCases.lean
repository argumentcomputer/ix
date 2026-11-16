import IxVMRefinement.Assembly.NativeSelfOrigin
import IxVMRefinement.Assembly.NativeMemberKeys

/-! # Exact naming alternatives at reached native self references

The actual admitted reader supplies either the core key of a reached recursive reference,
or the canonical address key with one unresolved bound projection. This keeps the remaining
local naming issue concrete at the native-origin boundary.
-/

namespace IxVM.Refinement.Assembly

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)

/-- Actual admitted-context data constructs the naming alternative at one reached self read.
The serialized index bound is derived from that occurrence. -/
theorem admitted_reached_self_key_cases {V : IxVM.Refinement.View} {binding : Ix.Kernel.Admission.Binding}
    (witness : IxVM.Consistency.ReaderAdmissionWitness V binding)
    {calls : List (Call F)} {trace : Ixon.Env} {seeds : List _root_.Address}
    (phase : Claim.WalkedL6 calls witness.table trace seeds)
    (keepTrace : _root_.Address → Prop) (order : List _root_.Address)
    (loaded : IxVM.Consistency.LoadedBy calls trace)
    {owner : _root_.Address} {source : Ixon.Constant} {members : Array Ixon.MutConst}
    (stored : (admittedNativeReaderCtx witness trace keepTrace order).store owner = some source)
    (shape : source.info = .muts members)
    {index : Nat} {address : _root_.Address} {expression : Ixon.Expr}
    {reading : Ix.Kernel.Reader.ReadM Core.KKey} {key : Core.KKey}
    (used : L1.RecurUsed source.sharing.toList index expression)
    (addressAt : (L1.blockRecurAddrs owner members.toList)[index]? = some address)
    (callback : (if index < members.size then
      some ((admittedNativeReaderCtx witness trace keepTrace order).memberKey (.member owner index)) else none) =
        some reading)
    (read : reading = .ok key) :
    key = Core.keyOf witness.table address ∨
      (key = .id address ∧ ∃ role, (role, address) ∈ witness.table.bound.toList ∧
        Ix.Kernel.Reader.resolve (admittedNativeReaderCtx witness trace keepTrace order).store address ≠
          some (.member owner index)) := by
  exact streamContext_block_self_key_cases rfl
    (admittedReaderStore_authentic witness keepTrace order loaded (walked_envDecoded phase))
    (check_of_admitBinding witness.admitted) stored shape used.index_lt addressAt callback read

/-- Actual native-origin data yields the native/modeled dispatch witness or identifies a reached self read whose bound projection does not resolve to that member. -/
theorem admitted_native_reader_origin_or_unresolved_self {V : IxVM.Refinement.View} {binding : Ix.Kernel.Admission.Binding}
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
    :
    (ZMod.val (slot : F) = slot ∧
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
        Bytes.RepAddressRef Core.addrTy heap block blockPtr ∧ Decl.ModeledInductCall blockPtr heap calls)) ∨
      ∃ index address reading key,
        L1.RecurUsed source.value.sharing.toList index ind.typ ∧
        (L1.blockRecurAddrs (Core.ixAddr block) members.toList)[index]? = some address ∧
        (if index < members.size then
          some ((admittedNativeReaderCtx witness trace keepTrace order).memberKey
            (.member (Core.ixAddr block) index)) else none) = some reading ∧
        reading = .ok key ∧ key = .id address ∧
        ∃ role, (role, address) ∈ witness.table.bound.toList ∧
          Ix.Kernel.Reader.resolve (admittedNativeReaderCtx witness trace keepTrace order).store address ≠
            some (.member (Core.ixAddr block) index) := by
  classical
  by_cases selfKeyed : ∀ index address reading key,
      L1.RecurUsed source.value.sharing.toList index ind.typ →
      (L1.blockRecurAddrs (Core.ixAddr block) members.toList)[index]? = some address →
      (if index < members.size then some ((admittedNativeReaderCtx witness trace keepTrace order).memberKey (.member (Core.ixAddr block) index)) else none) =
        some reading → reading = .ok key → key = (nativeOriginCtx witness trace env lim).κ address
  · exact .inl (admitted_native_reader_origin_in_context_of_selfReads witness keepTrace order phase loaded
      bounded env lim claimBytes noCollision source shape memberAt walked readerSource read selfKeyed)
  · push_neg at selfKeyed
    obtain ⟨index, address, reading, key, used, addressAt, callback, succeeded, different⟩ := selfKeyed
    rcases admitted_reached_self_key_cases witness phase keepTrace order loaded readerSource shape
      used addressAt callback succeeded with exactKey | ⟨addressKey, role, bound, unresolved⟩
    · exact (different exactKey).elim
    · exact .inr ⟨index, address, reading, key, used, addressAt, callback, succeeded,
        addressKey, role, bound, unresolved⟩

end IxVM.Refinement.Assembly
