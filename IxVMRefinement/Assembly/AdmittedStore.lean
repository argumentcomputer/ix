import IxVMRefinement.Assembly.AdmittedBare
import IxVMRefinement.RoleVal.CommittedData
import Ix.Cert.FallbackStore

/-! # Exact authentication of the admitted reader's actual store

The selected role records are authenticated by their byte preparation. The committed
fallback is authenticated by its own checked data. No global authenticity of the view is used.
-/

namespace IxVM.Refinement.Assembly

open Ix.Kernel Ix.Kernel.Reader

private theorem lookup_mem {α β : Type} [BEq α] [LawfulBEq α] :
    ∀ {rows : List (α × β)} {a : α} {value : β}, rows.lookup a = some value → (a, value) ∈ rows
  | [], _, _, h => nomatch h
  | (key, value) :: rest, a, found, h => by
    rw [List.lookup_cons] at h
    cases hkey : a == key with
    | true =>
      rw [hkey] at h
      cases h
      rw [beq_iff_eq.mp hkey]
      exact List.mem_cons_self
    | false =>
      rw [hkey] at h
      exact List.mem_cons_of_mem _ (lookup_mem h)

private theorem streamContext_store_mem {hash : ByteArray → _root_.Address} {table : RoleTable}
    {prelude : Prelude .anon} {records : List (_root_.Address × Ixon.Constant)}
    {blobs : Ingress.Blobs} {hint : ConstRef _root_.Address → Option ReducibilityHint}
    {a : _root_.Address} {c : Ixon.Constant}
    (h : (Admission.streamContext hash table prelude records blobs hint).store a = some c) :
    (a, c) ∈ records ∨ (a, c) ∈ prelude.records ++ prelude.evidence := by
  change ((recordMap records.toArray)[a]? <|>
    ((recordMap (prelude.records ++ prelude.evidence))[a]? <|> none)) = some c at h
  cases hinput : (recordMap records.toArray)[a]? with
  | some input =>
    rw [hinput] at h
    cases h
    rw [Ix.Cert.ReaderClosureKeys.recordMap_get, List.toList_toArray] at hinput
    exact .inl (lookup_mem hinput)
  | none =>
    rw [hinput] at h
    cases hfallback : (recordMap (prelude.records ++ prelude.evidence))[a]? with
    | none => simp [hfallback] at h
    | some fallback =>
      rw [hfallback] at h
      cases h
      rw [Ix.Cert.ReaderClosureKeys.recordMap_get] at hfallback
      exact .inr (Array.mem_toList_iff.mp (lookup_mem hfallback))

theorem admitted_streamStore_authentic {V : IxVM.Refinement.View} {b : Admission.Binding}
    (w : IxVM.Consistency.ReaderAdmissionWitness V b) :
    AuthenticExactStore
      (Admission.streamContext _root_.Address.admissionHash w.table w.prelude
        (Ix.Cert.Stream.decodedOf w.env w.order) (Ix.Cert.blobsOf w.env w.order)
        (Ix.Cert.hintsOf w.env)).store := by
  obtain ⟨_, _, hauth, hdecoded⟩ := admitted_bare_byteFacts w
  intro a c hstore
  rcases streamContext_store_mem hstore with hinput | hfallback
  · obtain ⟨record, hrecord, hread⟩ := Ix.Cert.FallbackStore.forall₂_mem_right hdecoded (a, c) hinput
    have hhash := hauth.1 record hrecord
    rw [_root_.Address.admissionHash_eq] at hhash
    exact ⟨record.2, hhash.symm.trans hread.1, hread.2.2.2⟩
  · obtain ⟨hhash, hwire⟩ := Ix.Cert.FallbackStore.fallback_authentic
      IxVM.Refinement.RoleVal.fallbackHashed w.preludeRead hfallback
    rw [_root_.Address.admissionHash_eq] at hhash
    exact ⟨Ixon.serConstant c, hhash.symm, Ixon.Verify.deConstantExact_serConstant c hwire⟩

end IxVM.Refinement.Assembly
