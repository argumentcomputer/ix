import IxVMRefinement.Assembly.ReaderEnvSelection
import IxVMRefinement.Assembly.PrunedRead
import IxVMRefinement.Assembly.AdmittedOrder

/-! # Exact closure orders after physical record selection

A selected store may choose different implicit recursors. Its new reachability still fits
inside an order for every original stored record: implicit targets are stored, and projection
owners follow the unchanged owner edge. Filtering that order by the new reachability gives
the exact public closure without assuming that the artifact index is unchanged.
-/

namespace IxVM.Refinement.Assembly

open IxVM.Consistency
open Aiur.Generic.SourceSemantics (Call)
open IxVM (F)

theorem selectReaderRecords_contains_old {env : Ixon.Env} {keep : _root_.Address → Bool}
    {address : _root_.Address} (present : (selectReaderRecords env keep).consts.contains address = true) :
    env.consts.contains address = true := by
  rw [Std.HashMap.contains_eq_isSome_getElem?, ← Std.HashMap.get?_eq_getElem?] at present ⊢
  obtain ⟨entry, found⟩ := Option.isSome_iff_exists.mp present
  rw [(selectReaderRecords_origin found).2]
  rfl

theorem selectReaderRecords_record_old {env : Ixon.Env} {keep : _root_.Address → Bool}
    {address : _root_.Address} {record : Ixon.Constant}
    (found : Ix.Cert.recordAt (selectReaderRecords env keep) address = some record) :
    Ix.Cert.recordAt env address = some record := by
  rw [selectReaderRecords_recordAt] at found
  split at found
  · exact found
  · cases found

theorem usedRecordRef_selected {env : Ixon.Env} {keep : _root_.Address → Bool}
    {source target : _root_.Address}
    (edge : UsedRecordRef (selectReaderRecords env keep) source target) :
    UsedRecordRef env source target := by
  obtain ⟨record, found, index, used, reference, atReference, value, loaded, owner, different⟩ := edge
  exact ⟨record, selectReaderRecords_record_old found, index, used, reference, atReference,
    value, selectReaderRecords_record_old loaded, owner, different⟩

theorem selected_reach_in_all_order {table : Ix.Kernel.RoleTable} {env : Ixon.Env}
    {order : List _root_.Address}
    (allRecords : UsedClosureOrderAt table env (fun _ => True) order)
    {keep : _root_.Address → Bool} {seeds : _root_.Address → Prop} {address : _root_.Address}
    (reached : UsedCompiledReachAt table (selectReaderRecords env keep) seeds address) :
    address ∈ order := by
  induction reached with
  | seed _ present =>
    exact (allRecords.complete _).mpr (.seed trivial (selectReaderRecords_contains_old present))
  | @step source target _ edge ih =>
    obtain ⟨record, found, owner | referenced⟩ := edge
    · exact (allRecords.complete _).mpr (.step ((allRecords.complete _).mp ih)
        ⟨record, selectReaderRecords_record_old found, .inl owner⟩)
    · exact (allRecords.complete _).mpr (.seed trivial (selectReaderRecords_contains_old referenced.2))
  | ground _ edge _ =>
    exact (allRecords.complete _).mpr (.seed trivial (selectReaderRecords_contains_old edge.1))
  | recursor _ edge _ =>
    exact (allRecords.complete _).mpr (.seed trivial (selectReaderRecords_contains_old edge.1))

/-- Recompute reachability after selecting records, then retain its exact relative order.
No relation between the old and new implicit recursor choices is required. -/
theorem selected_usedClosureOrder {table : Ix.Kernel.RoleTable} {env : Ixon.Env}
    {order : List _root_.Address}
    (allRecords : UsedClosureOrderAt table env (fun _ => True) order)
    (keep : _root_.Address → Bool) (seeds : _root_.Address → Prop) :
    UsedClosureOrderAt table (selectReaderRecords env keep) seeds
      (pruneClosureOrder table (selectReaderRecords env keep) seeds order) := by
  refine ⟨allRecords.nodup.filter _, ?_, ?_⟩
  · intro address
    rw [mem_pruneClosureOrder]
    exact ⟨And.right, fun reached => ⟨selected_reach_in_all_order allRecords reached, reached⟩⟩
  · exact (allRecords.ordered.filter _).imp
      (fun _ _ ordered edge => ordered (usedRecordRef_selected edge))

/-- The admitted/walked union supplies the finite all-record order used above. -/
theorem admitted_selected_usedClosureOrder {V : IxVM.Refinement.View} {binding : Ix.Kernel.Admission.Binding}
    (witness : ReaderAdmissionWitness V binding) {calls : List (Call F)} {trace : Ixon.Env}
    (loaded : LoadedBy calls trace) (decoded : L1.EnvDecoded trace)
    {extra : List ByteArray} (noCollision : ¬ V.HashedCollision extra calls)
    (keep : _root_.Address → Bool) (seeds : _root_.Address → Prop) :
    UsedClosureOrderAt witness.table (selectReaderRecords (admittedWalkEnv witness calls trace) keep) seeds
      (pruneClosureOrder witness.table (selectReaderRecords (admittedWalkEnv witness calls trace) keep)
        seeds (admittedWalkOrder witness calls trace (fun _ => True))) :=
  selected_usedClosureOrder (admittedWalkOrder_spec witness loaded decoded noCollision (fun _ => True)) keep seeds

end IxVM.Refinement.Assembly
