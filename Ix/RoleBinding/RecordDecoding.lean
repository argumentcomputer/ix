module

public import IxC.Kernel.Admission.Bytes
public import Ix.Compile.Parallel
import all IxC.Kernel.Admission.Bytes
import Init.Data.List.Monadic

public section

namespace Ix.RoleBinding.RecordDecoding

open Ix.Kernel.Admission

/-- Decode a record under its original position and address. -/
@[expose] def entry (limits : Limits) (record : (Address × ByteArray) × Nat) :
    Except ByteError (Address × Ixon.Constant) := do
  let ((address, bytes), position) := record
  let constant ← (Ixon.Canonical.deConstant limits.maxRecordBytes
    limits.maxRecordUnivNodes bytes).mapError (.decode position address)
  pure (address, constant)

theorem decodeLoop_eq_mapM (limits : Limits) (records : Records) (position : Nat)
    (reversed : Ix.Kernel.Ingress.Constants) :
    decodeLoop limits position records reversed =
      List.mapM.loop (entry limits) (records.zipIdx position) reversed := by
  induction records generalizing position reversed with
  | nil => rfl
  | cons record rest ih =>
    obtain ⟨address, bytes⟩ := record
    simp only [decodeLoop, List.zipIdx_cons, List.mapM.loop, entry]
    cases h : Ixon.Canonical.deConstant limits.maxRecordBytes
      limits.maxRecordUnivNodes bytes <;> simp [ih]

/-- Decode independent consecutive chunks, then select successes or the first
refusal in input order. The caller still performs batch preflight, uniqueness
and authentication first. This does not replace the kernel admission entry. -/
@[expose] def parallel (tasks : Nat) (limits : Limits) (records : Records) :
    Except ByteError Ix.Kernel.Ingress.Constants :=
  (Ix.Compile.Parallel.map tasks (entry limits) records.zipIdx.toArray).toList.mapM id

/-- Bounded parallel evaluation preserves all decoded records and the exact
first refusal, including its input position, address and decoder message. -/
theorem parallel_eq (tasks : Nat) (limits : Limits) (records : Records) :
    parallel tasks limits records = decodeRecords limits records := by
  simp only [parallel, Ix.Compile.Parallel.map_eq, Array.toList_map,
    List.mapM_map, Function.comp_def, id_eq]
  exact (decodeLoop_eq_mapM limits records 0 []).symm

end Ix.RoleBinding.RecordDecoding
