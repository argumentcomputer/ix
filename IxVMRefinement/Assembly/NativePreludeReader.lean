import IxVMRefinement.Assembly.NativeReaderCoverage
import IxVMRefinement.Assembly.AdmittedKeys
import IxVMRefinement.Assembly.RolePreludeBridge

/-! # The actual prelude reader and its stored records

Prelude preparation performs a concrete record read before checking its pinned name shape.
Its store is the committed fallback store. The original admitted reader preserves those
lookups by its checked fallback overlap agreement, so their resolutions transport as well.
-/

namespace IxVM.Refinement.Assembly

open Ix.Kernel Ix.Kernel.Reader
open Ix.CompileCert.Loop (except_bind_ok)

abbrev nativePreludeReaderCtx (table : RoleTable) (prelude : Prelude .anon) : Ctx .anon :=
  contextOf table prelude.records [] prelude.evidence prelude.blobs

/-- Successful prelude preparation retains the actual record-reading run that produced
its state and declarations. -/
theorem preludeFor_readRecords {table : RoleTable} {prelude : Prelude .anon}
    (prepared : preludeFor table = .ok prelude) :
    readRecords (nativePreludeReaderCtx table prelude) {} prelude.records =
      .ok (prelude.state, prelude.ix.decls) := by
  have read := (preludeFor_checks prepared).1
  unfold preludeRead at read
  obtain ⟨records, _, read⟩ := except_bind_ok.mp read
  obtain ⟨evidence, _, read⟩ := except_bind_ok.mp read
  obtain ⟨blobs, _, read⟩ := except_bind_ok.mp read
  unfold readPrelude at read
  cases checked : readRecords (contextOf table records [] evidence blobs) {} records with
  | error error => simp [checked, throw, Except.error] at read
  | ok output =>
    obtain ⟨state, declarations⟩ := output
    rw [checked] at read
    simp only [pure, Except.pure, Except.ok.injEq] at read
    subst prelude
    exact checked

/-- The pure prelude reader uses exactly the committed fallback records. -/
theorem nativePreludeReaderCtx_store (table : RoleTable) (prelude : Prelude .anon) :
    (nativePreludeReaderCtx table prelude).store = Ix.Cert.EvidenceCheck.fallbackStore prelude := by
  funext address
  change ((recordMap prelude.records)[address]? <|> ((recordMap prelude.evidence)[address]? <|> none)) =
    (recordMap (prelude.records ++ prelude.evidence))[address]?
  simp [Ix.Cert.ReaderClosureKeys.recordMap_get, Array.toList_append, List.lookup_append]

/-- The pure prelude reader has no reconstruction fallback: its successful member reads
come from committed role bindings, address caches or singleton records. -/
theorem nativePreludeReaderCtx_reconstruct (table : RoleTable) (prelude : Prelude .anon)
    (ref : ConstRef _root_.Address) : (nativePreludeReaderCtx table prelude).reconstruct ref = none := rfl

/-- A prelude lookup survives in the original admitted reader, including an input overlap.
The exact overlap bytes are supplied by the actual admission witness. -/
theorem admitted_original_prelude_store {V : IxVM.Refinement.View} {binding : Admission.Binding}
    (witness : IxVM.Consistency.ReaderAdmissionWitness V binding)
    {address : _root_.Address} {value : Ixon.Constant}
    (found : (nativePreludeReaderCtx witness.table witness.prelude).store address = some value) :
    (ReaderStoreTransfer.readerContext witness.table witness.prelude witness.env witness.order).store
      address = some value := by
  rw [nativePreludeReaderCtx_store] at found
  have member : (address, value) ∈ witness.prelude.records ++ witness.prelude.evidence :=
    Array.mem_toList_iff.mp (Ix.Cert.EvidenceCheck.fallbackStore_mem found)
  have wire := (Ix.Cert.FallbackStore.fallback_authentic
    rolePreludeInputs.fallbackHashed witness.preludeRead member).2
  change ReaderStoreTransfer.store witness.table witness.prelude witness.env witness.order address = some value
  rw [ReaderStoreTransfer.lookup]
  by_cases selected : address ∈ witness.order
  · simp only [selected, ↓reduceIte]
    cases input : Ix.Cert.recordAt witness.env address with
    | none => exact found
    | some actual =>
      obtain ⟨entry, stored, decoded⟩ := ReaderFootprint.coherent_recordAt_exact witness.coherent input
      have bytes := witness.fallbackRecordsAgree address selected entry stored value member
      rw [bytes, Ixon.Verify.deConstantExact_serConstant value wire] at decoded
      have same : actual = value := (Except.ok.inj decoded).symm
      subst actual
      rfl
  · simp only [selected, ↓reduceIte]
    exact found

/-- Prelude reference resolution is preserved by the actual admitted reader store. -/
theorem admitted_original_prelude_resolves {V : IxVM.Refinement.View} {binding : Admission.Binding}
    (witness : IxVM.Consistency.ReaderAdmissionWitness V binding)
    {address : _root_.Address} {target : ConstRef _root_.Address}
    (resolved : resolve (nativePreludeReaderCtx witness.table witness.prelude).store address = some target) :
    resolve (ReaderStoreTransfer.readerContext witness.table witness.prelude witness.env witness.order).store
      address = some target := by
  have sourceRead := resolved
  unfold resolve at sourceRead
  obtain ⟨value, found, _⟩ := Option.bind_eq_some_iff.mp sourceRead
  exact ReaderStoreTransfer.resolve_of_local found (admitted_original_prelude_store witness found)
    (fun _ parentAt => admitted_original_prelude_store witness parentAt) resolved

/-- A role name actually emitted by the prelude comes from a concrete bound record
resolving to that member. Reconstruction cannot supply a conflicting cached role name. -/
theorem prelude_member_role_origin {table : RoleTable} {prelude : Prelude .anon}
    (prepared : preludeFor table = .ok prelude) {target : ConstRef _root_.Address} {key : Key .anon}
    (read : (nativePreludeReaderCtx table prelude).memberKey target = .ok key)
    (covered : ReaderInductiveKey prelude.ix.decls.toList key) :
    ∃ role address, key = .role role ∧ (role, address) ∈ table.bound.toList ∧
      resolve (nativePreludeReaderCtx table prelude).store address = some target := by
  obtain ⟨block, params, declared, named⟩ := covered
  obtain ⟨role, _, keyEq⟩ := (preludeFor_decls_roles prepared).2 (.indDecl block params) declared key named
  have roleRead : (nativePreludeReaderCtx table prelude).memberKey target = .ok (.role role) := by
    rwa [keyEq] at read
  have compatible : Ix.Cert.ReaderKeys.ReconCompatible (nativePreludeReaderCtx table prelude) (fun _ => True) := by
    intro ref address _ _ _ _ impossible _
    rw [nativePreludeReaderCtx_reconstruct] at impossible
    cases impossible
  have boundName := (Ix.Cert.ReaderKeys.memberKey_role_iff compatible (ref := target) (r := role) trivial).mp roleRead
  obtain ⟨address, bound, resolved⟩ := Ix.Cert.ReaderKeys.bindings_role_origin
    (nativePreludeReaderCtx table prelude).store table boundName
  exact ⟨role, address, keyEq, bound, resolved⟩

end IxVM.Refinement.Assembly
