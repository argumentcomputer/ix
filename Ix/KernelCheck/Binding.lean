module

public import Ix.RoleBinding.Artifact

/-! Actual artifact contexts for diagnostic environment-check harnesses.
Preparation does not certify selected, filtered or per-record results. -/

@[expose] public section

namespace Ix.KernelCheck.Binding

def limits : Ix.Kernel.Admission.Limits :=
  { maxRecords := 1 <<< 22, maxBlobs := 1 <<< 22, maxTotalBytes := 1 <<< 34,
    maxRecordBytes := 1 <<< 28, maxRecordUnivNodes := 1 <<< 26 }

/-- The role table and prelude a harness reads an artifact under. A bound
artifact's binding is admitted and its prelude read as `check-lean`'s
preparation (`prepareRecords`) reads them (`preludeRecords`, `readPrelude`, the
shape and fallback checks), decoding only the prelude's records: preparing every
record and ordering the whole artifact (`prepareRecordsPar`,
`CheckOrder.wholeEnv`) took longer than the check itself on a Mathlib-sized
artifact, and the harness's loader decodes the records again anyway. Every
prelude record is depth-scanned under `limits.maxDepth` before decoding so a
deep record declines cleanly instead of overflowing the stack. -/
def context (env : Ixon.Env) (limits : Ix.Kernel.Admission.Limits := limits) :
    Except String (Ix.Kernel.RoleTable × Ix.Kernel.Reader.Prelude .anon) := do
  if let some raw := env.roleBinding then
    let table ← (Ix.Kernel.Admission.admitBinding Address.admissionHash
      ⟨raw.address, raw.bytes⟩).mapError fun e => toString (Ix.Kernel.Admission.Error.binding e)
    let lookup (a : Address) : Option Ixon.Constant :=
      env.consts[a]?.bind fun lc => (lc.getWithin limits.maxDepth a).toOption
    let preRecords ← match Ix.RoleBinding.preludeRecords table lookup Ix.Kernel.preludeShape with
      | .ok r => pure r
      | .error e =>
        for (a, lc) in env.consts do
          if lc.cache.isNone && !Ix.Kernel.Admission.Depth.within limits.maxDepth lc.rawBytes then
            throw (Ixon.depthLimitError limits.maxDepth a)
        throw e
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
