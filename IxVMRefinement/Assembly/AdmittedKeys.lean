import IxVMRefinement.Assembly.AdmittedAnalysis

/-! # Actual reader key transport along used references

Both reader stores have authenticated exact bytes. Successful used-reference resolution
survives the selected closure, and each resolving address has the role table's own key.
This does not require equality of the rebuilt contexts or their recursor indexes.
-/

namespace IxVM.Refinement.Assembly.ReaderStoreTransfer

open Ix.Kernel Ix.Kernel.Reader
open IxVM.Consistency
open Aiur.Generic.SourceSemantics (Call)
open IxVM (F)

abbrev readerContext (table : RoleTable) (prelude : Prelude .anon) (env : Ixon.Env)
    (order : List _root_.Address) : Ctx .anon :=
  Admission.streamContext _root_.Address.admissionHash table prelude
    (Ix.Cert.Stream.decodedOf env order) (Ix.Cert.blobsOf env order) (Ix.Cert.hintsOf env)

/-- A reference actually used by a retained record resolves identically in the selected
reader whenever it resolved in the original admitted reader. -/
theorem admitted_used_resolve {V : IxVM.Refinement.View} {b : Admission.Binding}
    (w : ReaderAdmissionWitness V b) {calls : List (Call F)} {trace : Ixon.Env}
    (keepTrace : _root_.Address → Prop) (claimBytes : ByteArray) {order : List _root_.Address}
    (loaded : LoadedBy calls trace) (decoded : L1.EnvDecoded trace)
    (noCollision : ¬ V.HashedCollision (claimBytes :: b.bytes :: readerImages V) calls)
    {seeds : _root_.Address → Prop}
    (closure : UsedClosureOrderAt w.table (admittedOverlay w trace keepTrace) seeds order)
    {owner a : _root_.Address} {record : Ixon.Constant}
    (retained : owner ∈ order)
    (stored : Ix.Cert.recordAt (admittedOverlay w trace keepTrace) owner = some record)
    {i : Nat} (used : i ∈ usedRefIdxs record) (reference : record.refs[i]? = some a)
    {ref : ConstRef _root_.Address}
    (resolved : resolve (store w.table w.prelude w.env w.order) a = some ref) :
    resolve (store w.table w.prelude (admittedOverlay w trace keepTrace) order) a = some ref := by
  obtain ⟨value, found, _⟩ := Option.bind_eq_some_iff.mp resolved
  have kept := admitted_used_reference w keepTrace claimBytes loaded decoded noCollision
    closure retained stored used reference found
  apply resolve_of_local found kept _ resolved
  intro ownerRecord ownerFound
  exact admitted_used_owner w keepTrace claimBytes loaded decoded noCollision
    closure retained stored used reference found ownerFound

/-- Every successful used-address key lookup is preserved by the actual pruned reader.
Authentication and local collision agreement are obtained from the admitted/trace union. -/
theorem admitted_used_keyAt {V : IxVM.Refinement.View} {b : Admission.Binding}
    (w : ReaderAdmissionWitness V b) {calls : List (Call F)} {trace : Ixon.Env}
    (keepTrace : _root_.Address → Prop) (claimBytes : ByteArray) {order : List _root_.Address}
    (loaded : LoadedBy calls trace) (decoded : L1.EnvDecoded trace)
    (noCollision : ¬ V.HashedCollision (claimBytes :: b.bytes :: readerImages V) calls)
    {seeds : _root_.Address → Prop}
    (closure : UsedClosureOrderAt w.table (admittedOverlay w trace keepTrace) seeds order)
    {owner a : _root_.Address} {record : Ixon.Constant}
    (retained : owner ∈ order)
    (stored : Ix.Cert.recordAt (admittedOverlay w trace keepTrace) owner = some record)
    {i : Nat} (used : i ∈ usedRefIdxs record) (reference : record.refs[i]? = some a)
    {key : Key .anon}
    (keyed : (readerContext w.table w.prelude w.env w.order).keyAt a = .ok key) :
    (readerContext w.table w.prelude (admittedOverlay w trace keepTrace) order).keyAt a = .ok key := by
  have tableChecked := check_of_admitBinding w.admitted
  have keyEq := streamContext_keyAt_ok_inv (admitted_streamStore_authentic w) tableChecked keyed
  obtain ⟨ref, resolved, _⟩ := Ctx.keyAt_ok keyed
  have resolved' := admitted_used_resolve w keepTrace claimBytes loaded decoded noCollision
    closure retained stored used reference resolved
  rw [keyEq]
  exact streamContext_keyAt_eq_keyOf
    (admittedReaderStore_authentic w keepTrace order loaded decoded) tableChecked resolved'

end IxVM.Refinement.Assembly.ReaderStoreTransfer
