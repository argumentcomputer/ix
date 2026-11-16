import IxVMRefinement.Assembly.SelectedReaderOrder
import IxVMRefinement.Assembly.ReaderSupport

/-! # Selecting physical records by their actual used closure

The selected environment keeps precisely the original closure's stored records. Its
reader index may choose different recursors, so the reading order is recomputed from
the selected environment. Used reference targets and projection owners remain available;
no equality of the old and new indexes or declaration arrays is asserted.
-/

namespace IxVM.Refinement.Assembly

open IxVM.Consistency
open Aiur.Generic.SourceSemantics (Call)
open IxVM (F)

noncomputable def readerClosureEnv (table : Ix.Kernel.RoleTable) (env : Ixon.Env)
    (seeds : _root_.Address → Prop) : Ixon.Env :=
  selectReaderRecords env fun address =>
    @decide (UsedCompiledReachAt table env seeds address) (Classical.propDecidable _)

open Classical in
theorem readerClosureEnv_recordAt (table : Ix.Kernel.RoleTable) (env : Ixon.Env)
    (seeds : _root_.Address → Prop) (address : _root_.Address) :
    Ix.Cert.recordAt (readerClosureEnv table env seeds) address =
      if UsedCompiledReachAt table env seeds address then Ix.Cert.recordAt env address else none := by
  classical
  simp only [readerClosureEnv, selectReaderRecords_recordAt, decide_eq_true_eq]

theorem readerClosureEnv_contains_iff {table : Ix.Kernel.RoleTable} {env : Ixon.Env}
    {seeds : _root_.Address → Prop} {address : _root_.Address} :
    (readerClosureEnv table env seeds).consts.contains address = true ↔
      UsedCompiledReachAt table env seeds address ∧ env.consts.contains address = true := by
  classical
  rw [Std.HashMap.contains_eq_isSome_getElem?, ← Std.HashMap.get?_eq_getElem?]
  simp only [readerClosureEnv, selectReaderRecords_get, decide_eq_true_eq]
  by_cases reached : UsedCompiledReachAt table env seeds address
  · simp only [reached, ↓reduceIte, true_and]
    rw [Std.HashMap.contains_eq_isSome_getElem?, ← Std.HashMap.get?_eq_getElem?]
  · simp only [reached, ↓reduceIte, Option.isSome_none, Bool.false_eq_true, false_and]

theorem readerClosureEnv_record_retained {table : Ix.Kernel.RoleTable} {env : Ixon.Env}
    {seeds : _root_.Address → Prop} {address : _root_.Address}
    (reached : UsedCompiledReachAt table env seeds address) :
    Ix.Cert.recordAt (readerClosureEnv table env seeds) address = Ix.Cert.recordAt env address := by
  simp only [readerClosureEnv_recordAt, reached, ↓reduceIte]

theorem readerClosureEnv_seed {table : Ix.Kernel.RoleTable} {env : Ixon.Env}
    {seeds : _root_.Address → Prop} {address : _root_.Address}
    (seed : seeds address) (present : env.consts.contains address = true) :
    (readerClosureEnv table env seeds).consts.contains address = true :=
  readerClosureEnv_contains_iff.mpr ⟨.seed seed present, present⟩

theorem readerClosureEnv_owner {table : Ix.Kernel.RoleTable} {env : Ixon.Env}
    {seeds : _root_.Address → Prop} {address : _root_.Address} {record : Ixon.Constant}
    (reached : UsedCompiledReachAt table env seeds address)
    (stored : Ix.Cert.recordAt env address = some record) :
    UsedCompiledReachAt table env seeds (Ix.Cert.ownerOf address record) := by
  by_cases same : Ix.Cert.ownerOf address record = address
  · rwa [same]
  · exact .step reached ⟨record, stored, .inl ⟨rfl, same⟩⟩

/-- A stored reference actually used by a retained record is kept physically, even if
the new artifact index chooses different implicit recursors. -/
theorem readerClosureEnv_reference {table : Ix.Kernel.RoleTable} {env : Ixon.Env}
    {seeds : _root_.Address → Prop} {address target : _root_.Address} {record : Ixon.Constant}
    (reached : UsedCompiledReachAt table env seeds address)
    (stored : Ix.Cert.recordAt env address = some record)
    {index : Nat} (used : index ∈ usedRefIdxs record) (reference : record.refs[index]? = some target)
    (present : env.consts.contains target = true) :
    (readerClosureEnv table env seeds).consts.contains target = true ∧
      Ix.Cert.recordAt (readerClosureEnv table env seeds) target = Ix.Cert.recordAt env target := by
  have targetReached : UsedCompiledReachAt table env seeds target :=
    .step reached ⟨record, stored, .inr ⟨⟨index, used, reference⟩, present⟩⟩
  exact ⟨readerClosureEnv_contains_iff.mpr ⟨targetReached, present⟩,
    readerClosureEnv_record_retained targetReached⟩

/-- Every new reachable address belongs to the old selecting closure. This holds for
any new seeds: a stored seed was selected already, and an implicit recursor edge targets
a stored selected row. Projection-owner edges use the unchanged original record. -/
theorem readerClosureEnv_reach_original {table : Ix.Kernel.RoleTable} {env : Ixon.Env}
    {keepSeeds readSeeds : _root_.Address → Prop} {address : _root_.Address}
    (reached : UsedCompiledReachAt table (readerClosureEnv table env keepSeeds) readSeeds address) :
    UsedCompiledReachAt table env keepSeeds address := by
  induction reached with
  | seed _ present => exact (readerClosureEnv_contains_iff.mp present).1
  | step _ edge ih =>
    obtain ⟨record, stored, owner | referenced⟩ := edge
    · exact .step ih ⟨record, selectReaderRecords_record_old stored, .inl owner⟩
    · exact (readerClosureEnv_contains_iff.mp referenced.2).1
  | ground _ edge _ => exact (readerClosureEnv_contains_iff.mp edge.1).1
  | recursor _ edge _ => exact (readerClosureEnv_contains_iff.mp edge.1).1

noncomputable def readerClosureOrder (table : Ix.Kernel.RoleTable) (env : Ixon.Env)
    (keepSeeds readSeeds : _root_.Address → Prop) (allOrder : List _root_.Address) :
    List _root_.Address :=
  pruneClosureOrder table (readerClosureEnv table env keepSeeds) readSeeds allOrder

theorem readerClosureOrder_spec {table : Ix.Kernel.RoleTable} {env : Ixon.Env}
    {allOrder : List _root_.Address}
    (allRecords : UsedClosureOrderAt table env (fun _ => True) allOrder)
    (keepSeeds readSeeds : _root_.Address → Prop) :
    UsedClosureOrderAt table (readerClosureEnv table env keepSeeds) readSeeds
      (readerClosureOrder table env keepSeeds readSeeds allOrder) :=
  selected_usedClosureOrder allRecords _ _

theorem readerClosureOrder_kept {table : Ix.Kernel.RoleTable} {env : Ixon.Env}
    {keepSeeds readSeeds : _root_.Address → Prop} {allOrder : List _root_.Address}
    {address : _root_.Address}
    (member : address ∈ readerClosureOrder table env keepSeeds readSeeds allOrder) :
    UsedCompiledReachAt table env keepSeeds address :=
  readerClosureEnv_reach_original (mem_pruneClosureOrder.mp member).2

theorem readerClosureOrder_records (table : Ix.Kernel.RoleTable) (env : Ixon.Env)
    (keepSeeds readSeeds : _root_.Address → Prop) (allOrder : List _root_.Address) :
    let order := readerClosureOrder table env keepSeeds readSeeds allOrder
    Ix.Cert.recordsOf (readerClosureEnv table env keepSeeds) order = Ix.Cert.recordsOf env order := by
  apply selectReaderRecords_records
  intro address member
  simpa only [@decide_eq_true_eq _ (Classical.propDecidable _)] using readerClosureOrder_kept member

/-- The concrete admitted/walked union supplies the all-record order, so choosing the
physical closure and its public reading order adds no ordering premise. -/
theorem admitted_readerClosureOrder {V : IxVM.Refinement.View} {binding : Ix.Kernel.Admission.Binding}
    (witness : ReaderAdmissionWitness V binding) {calls : List (Call F)} {trace : Ixon.Env}
    (loaded : LoadedBy calls trace) (decoded : L1.EnvDecoded trace)
    {extra : List ByteArray} (noCollision : ¬ V.HashedCollision extra calls)
    (keepSeeds readSeeds : _root_.Address → Prop) :
    let env := admittedWalkEnv witness calls trace
    UsedClosureOrderAt witness.table (readerClosureEnv witness.table env keepSeeds) readSeeds
      (readerClosureOrder witness.table env keepSeeds readSeeds
        (admittedWalkOrder witness calls trace (fun _ => True))) :=
  readerClosureOrder_spec (admittedWalkOrder_spec witness loaded decoded noCollision (fun _ => True))
    keepSeeds readSeeds

end IxVM.Refinement.Assembly
