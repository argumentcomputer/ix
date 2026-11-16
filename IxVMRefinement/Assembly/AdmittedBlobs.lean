import IxVMRefinement.Assembly.AdmittedKeys
import IxVMRefinement.Assembly.RecordReadBare

/-! # Literal blobs in the selected admitted reader

The selected input keeps every blob a retained record references. If the original input
did not supply that address, the committed fallback supplies it; a newly traced blob at
that address must agree by the existing collision alternative.
-/

namespace IxVM.Refinement.Assembly.ReaderStoreTransfer

open Ix.Kernel Ix.Kernel.Reader
open IxVM.Consistency
open Aiur.Generic.SourceSemantics (Call)
open IxVM (F)

private def blobStep (m : Std.HashMap _root_.Address ByteArray)
    (row : _root_.Address × ByteArray) : Std.HashMap _root_.Address ByteArray :=
  if m.contains row.1 then m else m.insert row.1 row.2

private theorem blobStep_keeps (m : Std.HashMap _root_.Address ByteArray)
    (row : _root_.Address × ByteArray) {a : _root_.Address} {bytes : ByteArray}
    (found : m[a]? = some bytes) : (blobStep m row)[a]? = some bytes := by
  unfold blobStep
  split
  · exact found
  · rename_i fresh
    rw [Std.HashMap.getElem?_insert]
    split
    · rename_i same
      have equal := beq_iff_eq.mp same
      rw [equal, Std.HashMap.contains_eq_isSome_getElem?, found] at fresh
      exact (fresh rfl).elim
    · exact found

private theorem blobFold_lookup (rows : List (_root_.Address × ByteArray))
    (m : Std.HashMap _root_.Address ByteArray) (a : _root_.Address) :
    (rows.foldl blobStep m)[a]? = (m[a]? <|> rows.lookup a) := by
  induction rows generalizing m with
  | nil => simp
  | cons row rows ih =>
    rw [List.foldl_cons, ih, List.lookup_cons]
    cases found : m[a]? with
    | some bytes => rw [blobStep_keeps m row found]; rfl
    | none =>
      by_cases same : row.1 = a
      · obtain ⟨key, bytes⟩ := row
        dsimp only at same
        subst key
        simp [blobStep, Std.HashMap.contains_eq_isSome_getElem?, found]
      · have reverse := beq_eq_false_iff_ne.mpr (Ne.symm same)
        have forward := beq_eq_false_iff_ne.mpr same
        unfold blobStep
        split <;> simp [Std.HashMap.getElem?_insert, forward, reverse, found]

private theorem lookup_member : ∀ {rows : List (_root_.Address × ByteArray)}
    {a : _root_.Address} {bytes : ByteArray}, rows.lookup a = some bytes → (a, bytes) ∈ rows
  | [], _, _, found => nomatch found
  | (key, value) :: rest, a, bytes, found => by
    rw [List.lookup_cons] at found
    cases same : a == key with
    | true =>
      rw [same] at found
      cases found
      rw [beq_iff_eq.mp same]
      exact List.mem_cons_self
    | false =>
      rw [same] at found
      exact List.mem_cons_of_mem _ (lookup_member found)

theorem blob_lookup (table : RoleTable) (prelude : Prelude .anon) (env : Ixon.Env)
    (order : List _root_.Address) (a : _root_.Address) :
    (readerContext table prelude env order).blob a =
      ((Ix.Cert.blobsOf env order).lookup a <|> prelude.blobs.lookup a) := by
  change ((Ix.Cert.blobsOf env order ++ prelude.blobs).foldl blobStep {})[a]? = _
  rw [blobFold_lookup]
  simp [List.lookup_append]

private theorem blobs_lookup_none {env : Ixon.Env} {order : List _root_.Address}
    {a : _root_.Address} (missing : env.blobs.get? a = none) :
    (Ix.Cert.blobsOf env order).lookup a = none := by
  cases found : (Ix.Cert.blobsOf env order).lookup a with
  | none => rfl
  | some bytes =>
    have stored := Ix.Cert.Stream.mem_blobsOf (lookup_member found)
    rw [missing] at stored
    cases stored

/-- A retained admitted record reads the same literal bytes in the actual selected
reader, including bytes supplied by the committed fallback. -/
theorem admitted_referenced_blob {V : IxVM.Refinement.View} {b : Admission.Binding}
    (w : ReaderAdmissionWitness V b) {calls : List (Call F)} {trace : Ixon.Env}
    (keepTrace : _root_.Address → Prop) (claimBytes : ByteArray) {order : List _root_.Address}
    (loaded : LoadedBy calls trace) (decoded : L1.EnvDecoded trace)
    (noCollision : ¬ V.HashedCollision (claimBytes :: b.bytes :: readerImages V) calls)
    {owner a : _root_.Address} {record : Ixon.Constant}
    (selected : owner ∈ w.order) (original : Ix.Cert.recordAt w.env owner = some record)
    (retained : owner ∈ order) (reference : a ∈ record.refs) {bytes : ByteArray}
    (found : (readerContext w.table w.prelude w.env w.order).blob a = some bytes) :
    (readerContext w.table w.prelude (admittedOverlay w trace keepTrace) order).blob a = some bytes := by
  have stored := admittedOverlay_recordAt w keepTrace loaded decoded noCollision selected original
  cases oldBlob : w.env.blobs.get? a with
  | some oldBytes =>
    have oldMember := mem_blobsOf_of_ref selected original reference oldBlob
    have oldRead := streamContext_blob_of_mem_blobsOf (t := w.table) (pre := w.prelude) oldMember
    have equal := Option.some.inj (oldRead.symm.trans found)
    subst oldBytes
    have kept := admittedOverlay_blob w keepTrace loaded noCollision oldMember
    exact streamContext_blob_of_mem_blobsOf (mem_blobsOf_of_ref retained stored reference kept)
  | none =>
    have oldMissing := blobs_lookup_none (order := w.order) oldBlob
    rw [blob_lookup, oldMissing] at found
    change w.prelude.blobs.lookup a = some bytes at found
    have fallbackMember := lookup_member found
    cases newBlob : (admittedOverlay w trace keepTrace).blobs.get? a with
    | none =>
      rw [blob_lookup, blobs_lookup_none (order := order) newBlob]
      exact found
    | some newBytes =>
      have equal : newBytes = bytes := by
        change (addBlobSupplements trace.blobs (Ix.Cert.blobsOf w.env w.order)).get? a = some newBytes at newBlob
        rcases addBlobSupplements_get?_some_inv trace.blobs _ newBlob with traced | ⟨_, fromRole⟩
        · rcases rolePreludeInputs.fallback_blob_agree
            (V := V) (extra := claimBytes :: b.bytes :: readerImages V)
            (fun image member => by simp [readerImages, member]) loaded w.preludeRead
            fallbackMember traced with collision | equal
          · exact (noCollision collision).elim
          · exact equal
        · have impossible := Ix.Cert.Stream.mem_blobsOf fromRole
          rw [oldBlob] at impossible
          cases impossible
      subst newBytes
      exact streamContext_blob_of_mem_blobsOf (mem_blobsOf_of_ref retained stored reference newBlob)

end IxVM.Refinement.Assembly.ReaderStoreTransfer
