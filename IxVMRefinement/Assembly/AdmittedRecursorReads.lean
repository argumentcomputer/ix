import IxVMRefinement.Assembly.RecursorReadFrames
import Ix.IxVM.Consistency.ReaderAdmission
import Ix.Cert.RecursorIndex

/-! # Actual twin payload readings in admitted inductive records

Selected mixed inductive records run the finishing reader on every indexed twin slot.
The accepted stream therefore supplies the twin's own successful payload read and the
raw type/rule inputs retained by that read. This describes the admission context itself;
it does not assume that a later selected context has the same block order or member keys.
-/

namespace IxVM.Refinement.Assembly

open Ix.Kernel Ix.Kernel.Reader
open Ix.CompileCert.Loop (except_bind_ok)
open Ix.Cert.ReaderUnits (ite_ok fail_bind)

theorem recordTwins_of_member {index : RecIndex} {owner : _root_.Address}
    {members : Array Ixon.MutConst} {slot : Nat} {recursor : Ixon.Recursor} {entry : RecEntry}
    (member : members[slot]? = some (.recr recursor))
    (indexed : index.twins[ConstRef.member owner slot]? = some entry) :
    (ConstRef.member owner slot, entry) ∈ recordTwins index owner members := by
  apply Array.mem_toList_iff.mp
  simp only [recordTwins, List.toList_toArray]
  apply List.mem_filterMap.mpr
  refine ⟨(.recr recursor, slot), ?_, ?_⟩
  · apply List.mem_zipIdx_iff_getElem?.mpr
    simpa using member
  · simp only [indexed, Option.map_some]

theorem finishInductiveRead_rec_read {md : Mode} {cx : Ctx md} {owner : _root_.Address}
    {members : Array Ixon.MutConst} {inductiveResult result : Read md}
    (read : finishInductiveRead cx owner members inductiveResult = .ok result)
    {slot : Nat} {recursor : Ixon.Recursor} {entry : RecEntry}
    (member : members[slot]? = some (.recr recursor))
    (indexed : cx.index.twins[ConstRef.member owner slot]? = some entry) :
    ∃ blockLps row, readRecursor cx blockLps (.member owner slot) entry = .ok row := by
  have inTwins := recordTwins_of_member member indexed
  have covered := finishInductiveRead_covered read
  simp only [finishInductiveRead, covered, ↓reduceIte] at read
  split at read
  · rename_i empty
    rw [Array.isEmpty_iff.mp empty] at inTwins
    simp only [Array.not_mem_empty] at inTwins
  · obtain ⟨chunk, chunkRead, _⟩ := except_bind_ok.mp read
    exact lowerTwins_rec_read chunkRead inTwins

theorem readRecord_inductive_twin_read {md : Mode} {cx : Ctx md} {state : State md}
    {owner : _root_.Address} {source : Ixon.Constant} {members : Array Ixon.MutConst}
    {result : Read md} (read : readRecord cx state owner source = .ok result)
    (info : source.info = .muts members)
    (hasInductive : members.any (fun | .indc _ => true | _ => false) = true)
    {slot : Nat} {recursor : Ixon.Recursor} {entry : RecEntry}
    (member : members[slot]? = some (.recr recursor))
    (indexed : cx.index.twins[ConstRef.member owner slot]? = some entry) :
    ∃ blockLps row, readRecursor cx blockLps (.member owner slot) entry = .ok row := by
  simp only [readRecord, info] at read
  split at read
  · rcases ite_ok read with failed | read
    · exact (fail_bind failed).elim
    · obtain ⟨_, _, finish⟩ := except_bind_ok.mp read
      exact finishInductiveRead_rec_read finish member indexed
  · rename_i absent
    exact (absent hasInductive).elim

/-- The original admission read constructs the complete input certificate for every
actual twin in a selected mixed inductive record. -/
theorem admitted_inductive_twin_inputs {V : IxVM.Refinement.View} {binding : Admission.Binding}
    (witness : IxVM.Consistency.ReaderAdmissionWitness V binding)
    {owner : _root_.Address} {source : Ixon.Constant} {members : Array Ixon.MutConst}
    (selected : owner ∈ witness.order) (record : Ix.Cert.recordAt witness.env owner = some source)
    (info : source.info = .muts members)
    (hasInductive : members.any (fun | .indc _ => true | _ => false) = true)
    {slot : Nat} {recursor : Ixon.Recursor} {entry : RecEntry}
    (member : members[slot]? = some (.recr recursor))
    (indexed : (Admission.streamContext _root_.Address.admissionHash witness.table witness.prelude
      (Ix.Cert.Stream.decodedOf witness.env witness.order) (Ix.Cert.blobsOf witness.env witness.order)
      (Ix.Cert.hintsOf witness.env)).index.twins[ConstRef.member owner slot]? = some entry) :
    let cx := Admission.streamContext _root_.Address.admissionHash witness.table witness.prelude
      (Ix.Cert.Stream.decodedOf witness.env witness.order) (Ix.Cert.blobsOf witness.env witness.order)
      (Ix.Cert.hintsOf witness.env)
    ∃ blockLps row, readRecursor cx blockLps (.member owner slot) entry = .ok row ∧
      Nonempty (RecursorReadInputs cx blockLps (.member owner slot) entry row) := by
  have decoded : (owner, source) ∈ (Ix.Cert.Stream.decodedOf witness.env witness.order).toArray :=
    Ix.Cert.RecursorIndex.mem_decoded.mpr ⟨selected, record⟩
  obtain ⟨_, _, read, _⟩ := (readRecords_spec witness.read).mem (Array.mem_toList_iff.mpr decoded)
  obtain ⟨blockLps, row, rowRead⟩ :=
    readRecord_inductive_twin_read read info hasInductive member indexed
  exact ⟨blockLps, row, rowRead, readRecursor_inputs rowRead⟩

end IxVM.Refinement.Assembly
