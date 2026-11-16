import IxVMRefinement.Assembly.NativeRoleRecords
import IxVMRefinement.Assembly.AdmittedKeys

/-! # Actual retained projection-record readings

The admission run validates the projection and its owner. Used-reference closure retains
that owner in the selected reader, so its projection record still reads successfully and
emits no declaration. No implicit member-name or index-order equality is needed.
-/

namespace IxVM.Refinement.Assembly.ReaderStoreTransfer

open Ix.Kernel Ix.Kernel.Reader
open IxVM.Consistency
open Aiur.Generic.SourceSemantics (Call)
open IxVM (F)

theorem readRecordBare_projection_of_resolves {cx : Ctx .anon} (state : State .anon)
    {owner : _root_.Address} {record : Ixon.Constant} (projection : IsProjInfo record.info)
    {target : ConstRef _root_.Address}
    (resolved : resolveSource cx.store owner record = some target) :
    readRecordBare cx state owner record = .ok {} := by
  cases info : record.info with
  | dPrj p | iPrj p | rPrj p | cPrj p =>
    simp only [readRecordBare, readRecord, info, resolved, Option.isNone_some,
      Bool.false_eq_true, ↓reduceIte]
    rfl
  | _ => simp [IsProjInfo, info] at projection

/-- The original successful admitted projection guard and actual owner retention construct
the new bare read; the caller need not supply a projection-resolution premise. -/
theorem admitted_projection_record {V : IxVM.Refinement.View} {binding : Admission.Binding}
    (witness : ReaderAdmissionWitness V binding) {calls : List (Call F)} {trace : Ixon.Env}
    (keepTrace : _root_.Address → Prop) (claimBytes : ByteArray) {order : List _root_.Address}
    (loaded : LoadedBy calls trace) (decoded : L1.EnvDecoded trace)
    (noCollision : ¬ V.HashedCollision (claimBytes :: binding.bytes :: readerImages V) calls)
    {seeds : _root_.Address → Prop}
    (closure : UsedClosureOrderAt witness.table (admittedOverlay witness trace keepTrace) seeds order)
    {owner : _root_.Address} {record : Ixon.Constant}
    (selected : owner ∈ witness.order) (original : Ix.Cert.recordAt witness.env owner = some record)
    (retained : owner ∈ order) (projection : IsProjInfo record.info) (state : State .anon) :
    readRecordBare
      (readerContext witness.table witness.prelude (admittedOverlay witness trace keepTrace) order)
      state owner record = .ok {} := by
  obtain ⟨target, resolved⟩ := admitted_projection_resolves witness selected original projection
  have originalStored := ReaderStoreTransfer.selected
    (table := witness.table) (prelude := witness.prelude) selected original
  have kept := admittedOverlay_recordAt witness keepTrace loaded decoded noCollision selected original
  have keptStored := ReaderStoreTransfer.selected
    (table := witness.table) (prelude := witness.prelude) retained kept
  have ownerRetained := readOrder_owner closure retained kept
  have transferred := resolve_of_local originalStored keptStored (fun value found =>
    admitted_selected witness keepTrace claimBytes order loaded decoded noCollision ownerRetained found) resolved
  have sourceResolved : resolveSource
      (readerContext witness.table witness.prelude (admittedOverlay witness trace keepTrace) order).store
      owner record = some target := by
    unfold resolve at transferred
    rw [keptStored] at transferred
    exact transferred
  exact readRecordBare_projection_of_resolves state projection sourceResolved

end IxVM.Refinement.Assembly.ReaderStoreTransfer
