import Ix.IxVM.Consistency.ReaderAdmission
import Ix.Cert.RecursorIndex
import Ix.Cert.ReaderUnits
import IxVMRefinement.Assembly.RecIndexOrigins

/-! # Recursor coverage from actual admitted record readings

The reader's successful finish supplies coverage in its actual stream context. Admission
therefore cannot leave an unindexed recursor payload inside a selected inductive record.
-/

namespace IxVM.Refinement.Assembly

open Ix.Kernel Ix.Kernel.Reader
open Ix.CompileCert.Loop (except_bind_ok)
open Ix.Cert.ReaderUnits (ite_ok fail_bind)

/-- Successful reading of an inductive record covers every actual recursor slot. -/
theorem readRecord_inductive_recursors_covered {md : Mode} {cx : Ctx md} {st : State md}
    {owner : _root_.Address} {c : Ixon.Constant} {ms : Array Ixon.MutConst} {r : Read md}
    (read : readRecord cx st owner c = .ok r) (info : c.info = .muts ms)
    (hasInductive : ms.any (fun | .indc _ => true | _ => false) = true)
    {j : Nat} {rc : Ixon.Recursor} (member : ms[j]? = some (.recr rc)) :
    cx.index.recs.contains (.member owner j) = true ∨
      cx.index.twins.contains (.member owner j) = true := by
  simp only [readRecord, info] at read
  split at read
  · rcases ite_ok read with bad | read
    · exact (fail_bind bad).elim
    · obtain ⟨_, _, finish⟩ := except_bind_ok.mp read
      exact finishInductiveRead_recursors_covered finish member
  · rename_i noInductive
    exact (noInductive hasInductive).elim

/-- Every selected admitted inductive record has complete recursor coverage in the actual
index used for its accepted full read. No additional admission witness field is needed. -/
theorem admitted_inductive_recursors_covered {V : IxVM.Refinement.View}
    {binding : Admission.Binding} (w : IxVM.Consistency.ReaderAdmissionWitness V binding)
    {owner : _root_.Address} {c : Ixon.Constant} {ms : Array Ixon.MutConst}
    (selected : owner ∈ w.order) (record : Ix.Cert.recordAt w.env owner = some c)
    (info : c.info = .muts ms)
    (hasInductive : ms.any (fun | .indc _ => true | _ => false) = true)
    {j : Nat} {rc : Ixon.Recursor} (member : ms[j]? = some (.recr rc)) :
    let cx := Admission.streamContext _root_.Address.admissionHash w.table w.prelude
      (Ix.Cert.Stream.decodedOf w.env w.order) (Ix.Cert.blobsOf w.env w.order)
      (Ix.Cert.hintsOf w.env)
    cx.index.recs.contains (.member owner j) = true ∨
      cx.index.twins.contains (.member owner j) = true := by
  have decoded : (owner, c) ∈ (Ix.Cert.Stream.decodedOf w.env w.order).toArray :=
    Ix.Cert.RecursorIndex.mem_decoded.mpr ⟨selected, record⟩
  obtain ⟨_, _, read, _⟩ := (readRecords_spec w.read).mem (Array.mem_toList_iff.mpr decoded)
  exact readRecord_inductive_recursors_covered read info hasInductive member

/-- Actual admission supplies a successful analysis of every recursor payload in a selected
inductive record. The result permits later canonical/twin regrouping. -/
theorem admitted_inductive_rec_analysis {V : IxVM.Refinement.View}
    {binding : Admission.Binding} (w : IxVM.Consistency.ReaderAdmissionWitness V binding)
    {owner : _root_.Address} {c : Ixon.Constant} {ms : Array Ixon.MutConst}
    (selected : owner ∈ w.order) (record : Ix.Cert.recordAt w.env owner = some c)
    (info : c.info = .muts ms)
    (hasInductive : ms.any (fun | .indc _ => true | _ => false) = true)
    {j : Nat} {rc : Ixon.Recursor} (member : ms[j]? = some (.recr rc)) :
    let cx := Admission.streamContext _root_.Address.admissionHash w.table w.prelude
      (Ix.Cert.Stream.decodedOf w.env w.order) (Ix.Cert.blobsOf w.env w.order)
      (Ix.Cert.hintsOf w.env)
    ∃ entry carriers,
      (cx.index.recs[ConstRef.member owner j]? = some entry ∨
        cx.index.twins[ConstRef.member owner j]? = some entry) ∧
      Ix.Cert.recursorAnalysis? cx.store owner c rc =
        some (entry.block, entry.motive, carriers, entry.major) := by
  let records := (Ix.Cert.Stream.decodedOf w.env w.order).toArray
  let cx := Admission.streamContext _root_.Address.admissionHash w.table w.prelude
    (Ix.Cert.Stream.decodedOf w.env w.order) (Ix.Cert.blobsOf w.env w.order)
    (Ix.Cert.hintsOf w.env)
  have covered := admitted_inductive_recursors_covered w selected record info hasInductive member
  change cx.index.recs.contains (.member owner j) = true ∨
    cx.index.twins.contains (.member owner j) = true at covered
  have indexed : ∃ entry,
      cx.index.recs[ConstRef.member owner j]? = some entry ∨
        cx.index.twins[ConstRef.member owner j]? = some entry := by
    rcases covered with canonical | twin
    · rw [Std.HashMap.contains_eq_isSome_getElem?] at canonical
      obtain ⟨entry, found⟩ := Option.isSome_iff_exists.mp canonical
      exact ⟨entry, Or.inl found⟩
    · rw [Std.HashMap.contains_eq_isSome_getElem?] at twin
      obtain ⟨entry, found⟩ := Option.isSome_iff_exists.mp twin
      exact ⟨entry, Or.inr found⟩
  obtain ⟨entry, found⟩ := indexed
  have present : (owner, c) ∈ records := Ix.Cert.RecursorIndex.mem_decoded.mpr ⟨selected, record⟩
  have keys : (records.toList.map Prod.fst).Nodup := by
    simpa only [records, List.toList_toArray] using
      (Ix.Cert.Stream.decodedOf_keys w.env w.order).nodup w.closure.nodup
  have payload : (j, rc) ∈ recursorMembers c := by
    simp only [recursorMembers, info]
    exact Array.mem_filterMap.mpr
      ⟨(.recr rc, j), Array.mk_mem_zipIdx_iff_getElem?.mpr member, rfl⟩
  obtain ⟨carriers, analysis⟩ := contextOf_member_analysis w.table w.prelude records
    (Ix.Cert.blobsOf w.env w.order) (Ix.Cert.hintsOf w.env)
    (Admission.projectionAddress _root_.Address.admissionHash) w.preludeRead keys present payload found
  exact ⟨entry, carriers, found, analysis⟩

end IxVM.Refinement.Assembly
