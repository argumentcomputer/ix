module

public import IxC.Kernel.Admission.Bytes
public import Ix.Compile.Parallel
import all IxC.Kernel.Admission.Bytes
import Init.Data.List.Monadic

public section

namespace Ix.RoleBinding.RecordDecoding

open Ix.Kernel.Admission

/-- Check one record or blob address against `hash` of its payload bytes under
its original input position. -/
@[expose] def mismatchEntry (hash : ByteArray → Address)
    (record : (Address × ByteArray) × Nat) : Option (Nat × Address) :=
  let ((address, bytes), position) := record
  if hash bytes == address then none else some (position, address)

theorem firstMismatch_eq_findSome? (hash : ByteArray → Address) (records : Records)
    (position : Nat) :
    firstMismatch hash position records =
      ((records.zipIdx position).map (mismatchEntry hash)).findSome? id := by
  induction records generalizing position with
  | nil => rfl
  | cons record rest ih =>
    obtain ⟨address, bytes⟩ := record
    simp only [firstMismatch, List.zipIdx_cons, List.map_cons, List.findSome?_cons,
      mismatchEntry, id_eq]
    cases hash bytes == address <;> simp [ih]

/-- Bounded parallel scan for the first hash mismatch in a table. -/
@[expose] def firstMismatchParallel (tasks : Nat) (hash : ByteArray → Address)
    (records : Records) : Option (Nat × Address) :=
  (Ix.Compile.Parallel.map tasks (mismatchEntry hash) records.zipIdx.toArray).toList.findSome? id

theorem firstMismatchParallel_eq (tasks : Nat) (hash : ByteArray → Address) (records : Records) :
    firstMismatchParallel tasks hash records = firstMismatch hash 0 records := by
  simp only [firstMismatchParallel, Ix.Compile.Parallel.map_eq, Array.toList_map]
  exact (firstMismatch_eq_findSome? hash records 0).symm

/-- Authenticate record and blob payloads over bounded parallel chunks while
preserving the exact first mismatch in input order. -/
@[expose] def authenticateParallel (tasks : Nat) (hash : ByteArray → Address)
    (records blobs : Records) : Except ByteError Unit :=
  match firstMismatchParallel tasks hash records with
  | some (position, address) => .error (.mismatch .records position address)
  | none =>
    match firstMismatchParallel tasks hash blobs with
    | some (position, address) => .error (.mismatch .blobs position address)
    | none => .ok ()

theorem authenticateParallel_eq (tasks : Nat) (hash : ByteArray → Address)
    (records blobs : Records) :
    authenticateParallel tasks hash records blobs = authenticate hash records blobs := by
  simp only [authenticateParallel, authenticate, firstMismatchParallel_eq]
  rfl

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
