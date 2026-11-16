import IxVMRefinement.Assembly.NativeRoleParents
import IxVMRefinement.Assembly.NativePreludeKeys

/-! # Fresh native names over the actual reference prefix

A non-trust binding of an actual native projection forces either that member's name or its
prelude parent's former name into the checked prefix. Freshness at the current native stage
excludes both cases. Compiler-trust bindings remain a distinct naming obligation.
-/

namespace IxVM.Refinement.Assembly

open Ix.Kernel Ix.Kernel.Reader
open IxVM.Consistency
open Aiur.Generic.SourceSemantics (Call)
open IxVM (F)

/-- A fresh former or constructor cannot reuse an actually admitted non-trust role binding.
The input-parent and prelude-parent branches both use concrete reader and reference evidence. -/
theorem admitted_fresh_native_bound_is_compilerTrust
    {V : IxVM.Refinement.View} {binding : Admission.Binding}
    (witness : ReaderAdmissionWitness V binding) {calls : List (Call F)} {trace : Ixon.Env}
    {seeds : List _root_.Address} (phase : Claim.WalkedL6 calls witness.table trace seeds)
    (claimBytes : ByteArray) (loaded : LoadedBy calls trace)
    (noCollision : ¬ V.HashedCollision (claimBytes :: binding.bytes :: readerImages V) calls)
    {fuel : Nat} {ev : Evidences .anon} {sourceStart targetStart roleEnv : Env .anon}
    (replay : Decl.ReferenceReplay fuel ev sourceStart targetStart
      ((Frontend.preparePrelude witness.prelude.ix witness.fullDecls).toList.map
        IxVM.Refinement.thmToOpaqueDefn) witness.checkedEnv roleEnv)
    {owner : _root_.Address}
    (source : L1.CanonicalRecordAt (admittedCore witness trace (fun _ => True)) owner)
    {members : Array Ixon.MutConst} {member : Nat} {ind : Ixon.Inductive}
    (kind : source.value.info = .muts members) (memberAt : members[member]? = some (.indc ind))
    (one : Ix.CompileCert.ReaderIndex.inductives members = #[(member, ind)])
    {role : Role} {address : _root_.Address} {bytes : ByteArray} {value : Ixon.Constant}
    {layout : Egress.ProjectionLayout} {target : ConstRef _root_.Address}
    (bound : (role, address) ∈ witness.table.bound.toList)
    (hashed : Hashed calls bytes) (hashEq : Address.blake3Pure bytes = address)
    (decoded : Ixon.deConstantExact bytes = .ok value)
    (projection : Egress.ProjectionReads value layout target)
    (nativeTarget : target = .member owner member ∨
      ∃ slot ctor, target = .ctor owner member slot ∧ ind.ctors[slot]? = some ctor)
    {env : Env .anon} (extended : EnvExt roleEnv env)
    (formerFresh : env.find? (Core.keyOf witness.table (Core.iprjAddr owner member)) = none)
    (memberFresh : env.find? (Core.keyOf witness.table address) = none) :
    IxVM.Refinement.compilerTrust role = true := by
  cases trusted : IxVM.Refinement.compilerTrust role with
  | true => rfl
  | false =>
    rcases admitted_bound_native_name_present_or_prelude witness phase claimBytes loaded noCollision
      replay.checked.storage source kind memberAt one bound trusted hashed hashEq decoded projection nativeTarget with
        present | preludeParent
    · exact (present_not_fresh_of_extension present extended memberFresh).elim
    · have present := admitted_prelude_native_former_replay_present witness replay
        preludeParent kind memberAt one
      exact (present_not_fresh_of_extension present extended formerFresh).elim

end IxVM.Refinement.Assembly
