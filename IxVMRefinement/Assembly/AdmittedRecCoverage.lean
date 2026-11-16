import Ix.IxVM.Consistency.ReaderAdmission
import Ix.Cert.RecursorIndex
import Ix.Cert.ReaderUnits

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

end IxVM.Refinement.Assembly
