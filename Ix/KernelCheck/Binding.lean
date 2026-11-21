module

public import Ix.RoleBinding.Artifact

/-! Actual artifact contexts for diagnostic environment-check harnesses.
Preparation does not certify selected, filtered or per-record results. -/

@[expose] public section

namespace Ix.KernelCheck.Binding

def limits : Ix.Kernel.Admission.Limits := ⟨1 <<< 22, 1 <<< 22, 1 <<< 34, 1 <<< 28, 1 <<< 26⟩

/-- The role table and prelude a harness reads an artifact under. A bound
artifact's binding is admitted and its prelude read as `check-lean`'s
preparation (`prepareRecords`) reads them (`preludeRecords`, `readPrelude`, the
shape and fallback checks), decoding only the prelude's records: preparing every
record and ordering the whole artifact (`prepareRecordsPar`,
`CheckOrder.wholeEnv`) took longer than the check itself on a Mathlib-sized
artifact, and the harness's loader decodes the records again anyway. -/
def context (env : Ixon.Env) :
    Except String (Ix.Kernel.RoleTable × Ix.Kernel.Reader.Prelude .anon) := do
  if let some raw := env.roleBinding then
    let table ← (Ix.Kernel.Admission.admitBinding Address.admissionHash
      ⟨raw.address, raw.bytes⟩).mapError fun e => toString (Ix.Kernel.Admission.Error.binding e)
    let preRecords ← Ix.RoleBinding.preludeRecords table env.getConst? Ix.Kernel.preludeShape
    let blobs := (env.blobs.toArray.qsort fun x y => x.1.cmpBytes y.1 == .lt).toList
    let pre ← Ix.Kernel.Reader.readPrelude (md := .anon) table preRecords #[] blobs
    Ix.Kernel.Reader.checkPreludeShape pre
    Ix.Kernel.Reader.checkFallbackRecursors pre
    return (table, pre)
  let table ← Ix.Kernel.Reader.defaultTable
  let pre ← Ix.Kernel.Reader.preludeFor table
  return (table, pre)

def metaPrelude (env : Ixon.Env) (table : Ix.Kernel.RoleTable)
    (pre : Ix.Kernel.Reader.Prelude .anon) : Except String (Ix.Kernel.Reader.Prelude .meta) := do
  if env.roleBinding.isSome then
    let actual ← Ix.Kernel.Reader.readPrelude table pre.records #[] pre.blobs
    Ix.Kernel.Reader.checkPreludeShape actual
    Ix.Kernel.Reader.checkFallbackRecursors actual
    return actual
  Ix.Kernel.Reader.preludeFor table

end Ix.KernelCheck.Binding
