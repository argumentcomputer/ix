import IxVMRefinement.Assembly.NativePreludePrefix
import IxVMRefinement.Assembly.NativeRoleKeys

/-! # Canonical former keys for actual prelude parents

A former emitted by the pure prelude has a concrete role binding and resolution. Admission
preserves that resolution. Authentic decoding identifies its bound address with the canonical
former projection, so its prefix presence is at the exact key used by the core checker.
-/

namespace IxVM.Refinement.Assembly

open Ix.Kernel Ix.Kernel.Reader

/-- The actual prelude former key is its canonical core key. The local binding and decoded
projection are produced by the prelude read and actual admission. -/
theorem admitted_prelude_native_former_key {V : IxVM.Refinement.View} {binding : Admission.Binding}
    (witness : IxVM.Consistency.ReaderAdmissionWitness V binding)
    {owner : _root_.Address} {source : Ixon.Constant} {members : Array Ixon.MutConst}
    {member : Nat} {ind : Ixon.Inductive}
    (present : (owner, source) ∈ witness.prelude.records) (kind : source.info = .muts members)
    (memberAt : members[member]? = some (.indc ind))
    (one : Ix.CompileCert.ReaderIndex.inductives members = #[(member, ind)])
    {key : Key .anon}
    (read : (nativePreludeReaderCtx witness.table witness.prelude).memberKey (.member owner member) = .ok key) :
    key = Core.keyOf witness.table (Core.iprjAddr owner member) := by
  obtain ⟨actual, actualRead, covered⟩ :=
    (prelude_native_member_reads witness.preludeRead present kind memberAt one).1
  have same : actual = key := Except.ok.inj (actualRead.symm.trans read)
  subst actual
  obtain ⟨role, address, keyEq, bound, resolved⟩ :=
    prelude_member_role_origin witness.preludeRead read covered
  have preludeStored : (nativePreludeReaderCtx witness.table witness.prelude).store owner = some source := by
    rw [nativePreludeReaderCtx_store]
    exact ReaderStoreTransfer.fallback_of_mem witness.preludeRead (Array.mem_append_left _ present)
  have originalStored := admitted_original_prelude_store witness preludeStored
  have originalResolved := admitted_original_prelude_resolves witness resolved
  have canonical := resolve_member_address_eq (admitted_streamStore_authentic witness)
    originalStored kind memberAt originalResolved
  change address = Core.iprjAddr owner member at canonical
  rw [canonical] at bound
  rw [keyEq, keyOf_eq_of_bound (check_of_admitBinding witness.admitted) bound]

/-- A native former whose actual parent is in the committed prelude already occurs in
the accepted reference prefix at its exact canonical core key. -/
theorem admitted_prelude_native_former_core_present {V : IxVM.Refinement.View} {binding : Admission.Binding}
    (witness : IxVM.Consistency.ReaderAdmissionWitness V binding)
    {owner : _root_.Address} {source : Ixon.Constant} {members : Array Ixon.MutConst}
    {member : Nat} {ind : Ixon.Inductive}
    (present : (owner, source) ∈ witness.prelude.records) (kind : source.info = .muts members)
    (memberAt : members[member]? = some (.indc ind))
    (one : Ix.CompileCert.ReaderIndex.inductives members = #[(member, ind)]) :
    (witness.checkedEnv.find? (Core.keyOf witness.table (Core.iprjAddr owner member))).isSome = true := by
  obtain ⟨key, read, stored⟩ :=
    admitted_prelude_native_former_present witness present kind memberAt one
  rwa [admitted_prelude_native_former_key witness present kind memberAt one read] at stored

/-- The paired annotated replay preserves the concrete prelude former's name presence.
No equality of its raw and normalized stored types is needed. -/
theorem admitted_prelude_native_former_replay_present {V : IxVM.Refinement.View} {binding : Admission.Binding}
    (witness : IxVM.Consistency.ReaderAdmissionWitness V binding)
    {fuel : Nat} {ev : Evidences .anon} {sourceStart targetStart target : Env .anon}
    {declarations : List (Declaration .anon)}
    (replay : Decl.ReferenceReplay fuel ev sourceStart targetStart declarations witness.checkedEnv target)
    {owner : _root_.Address} {source : Ixon.Constant} {members : Array Ixon.MutConst}
    {member : Nat} {ind : Ixon.Inductive}
    (present : (owner, source) ∈ witness.prelude.records) (kind : source.info = .muts members)
    (memberAt : members[member]? = some (.indc ind))
    (one : Ix.CompileCert.ReaderIndex.inductives members = #[(member, ind)]) :
    (target.find? (Core.keyOf witness.table (Core.iprjAddr owner member))).isSome = true := by
  rw [← replay.endAgreement.isSome]
  exact admitted_prelude_native_former_core_present witness present kind memberAt one

end IxVM.Refinement.Assembly
