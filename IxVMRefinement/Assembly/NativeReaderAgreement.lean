import IxVMRefinement.Assembly.AdmittedBlobs
import IxVMRefinement.Assembly.RawQueryCoverage
import IxVMRefinement.L1.BlobAgreement

/-! # Constructed key and literal agreement for the native reader

Authentication fixes every successful explicit key lookup. Literal bytes returned by the
selected reader come from the trace, selected admitted blobs, or the committed fallback;
the actual collision alternative makes each agree with bytes the Aiur checker hashed.
Block-member self keys remain a separate obligation.
-/

namespace IxVM.Refinement.Assembly

open Ix.Kernel Ix.Kernel.Reader
open IxVM.Consistency
open Aiur.Generic.SourceSemantics (Call)
open IxVM (F)

private theorem lookup_member : ∀ {rows : List (_root_.Address × ByteArray)}
    {address : _root_.Address} {bytes : ByteArray},
    rows.lookup address = some bytes → (address, bytes) ∈ rows
  | [], _, _, found => nomatch found
  | (key, value) :: rest, address, bytes, found => by
    rw [List.lookup_cons] at found
    cases same : address == key with
    | true =>
      rw [same] at found
      cases found
      rw [beq_iff_eq.mp same]
      exact List.mem_cons_self
    | false =>
      rw [same] at found
      exact List.mem_cons_of_mem _ (lookup_member found)

/-- The actual selected reader's successful blob lookups agree with every hash of that
address in the trace, including reads supplied by the committed fallback. -/
theorem admitted_reader_blob_agreement {V : IxVM.Refinement.View} {binding : Admission.Binding}
    (witness : ReaderAdmissionWitness V binding) {calls : List (Call F)} {trace : Ixon.Env}
    (keepTrace : _root_.Address → Prop) (order : List _root_.Address) (claimBytes : ByteArray)
    (loaded : LoadedBy calls trace)
    (noCollision : ¬ V.HashedCollision (claimBytes :: binding.bytes :: readerImages V) calls) :
    L1.HashedBlobReadAgreement
      (ReaderStoreTransfer.readerContext witness.table witness.prelude
        (admittedOverlay witness trace keepTrace) order).blob calls := by
  intro address observed hashed hashEq declared read
  have agrees (held : V.Preimage address declared ∨
      (declared ∈ claimBytes :: binding.bytes :: readerImages V ∧ Address.blake3Pure declared = address) ∨
      (Hashed calls declared ∧ Address.blake3Pure declared = address)) : observed = declared := by
    by_contra different
    exact noCollision (.inl ⟨address, declared, observed, held, hashed, different, hashEq⟩)
  rw [ReaderStoreTransfer.blob_lookup] at read
  cases stream : (Ix.Cert.blobsOf (admittedOverlay witness trace keepTrace) order).lookup address with
  | some bytes =>
    rw [stream] at read
    change some bytes = some declared at read
    have same := Option.some.inj read
    subst bytes
    have stored := Ix.Cert.Stream.mem_blobsOf (lookup_member stream)
    change (addBlobSupplements trace.blobs (Ix.Cert.blobsOf witness.env witness.order)).get? address =
      some declared at stored
    rcases addBlobSupplements_get?_some_inv trace.blobs _ stored with traced | ⟨_, admitted⟩
    · exact agrees (.inr (.inr (loaded.2 address declared traced)))
    · exact agrees (.inl (admitted_role_blob witness admitted).2)
  | none =>
    rw [stream] at read
    change witness.prelude.blobs.lookup address = some declared at read
    have fallback := lookup_member read
    obtain ⟨image, imageHash⟩ := RoleVal.blob_mem_committedImages_of_fallback witness.preludeRead fallback
    exact agrees (.inr (.inl ⟨by simp [readerImages, image], imageHash⟩))

/-- Actual admission, trace decoding and the collision alternative discharge the global
explicit-key and conditional literal-agreement inputs of native conversion. -/
theorem admitted_native_reader_agreement {V : IxVM.Refinement.View} {binding : Admission.Binding}
    (witness : ReaderAdmissionWitness V binding) {calls : List (Call F)} {trace : Ixon.Env}
    {seeds : List _root_.Address}
    (phase : Claim.WalkedL6 calls witness.table trace seeds)
    (keepTrace : _root_.Address → Prop) (order : List _root_.Address) (claimBytes : ByteArray)
    (loaded : LoadedBy calls trace)
    (noCollision : ¬ V.HashedCollision (claimBytes :: binding.bytes :: readerImages V) calls) :
    (∀ address key,
      (ReaderStoreTransfer.readerContext witness.table witness.prelude
        (admittedOverlay witness trace keepTrace) order).keyAt address = .ok key →
      key = Core.keyOf witness.table address) ∧
    L1.HashedBlobReadAgreement
      (ReaderStoreTransfer.readerContext witness.table witness.prelude
        (admittedOverlay witness trace keepTrace) order).blob calls := by
  refine ⟨?_, admitted_reader_blob_agreement witness keepTrace order claimBytes loaded noCollision⟩
  intro address key found
  exact streamContext_keyAt_ok_inv
    (admittedReaderStore_authentic witness keepTrace order loaded (walked_envDecoded phase))
    (check_of_admitBinding witness.admitted) found

end IxVM.Refinement.Assembly
