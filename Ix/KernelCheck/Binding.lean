module

public import Ix.RoleBinding.Artifact

/-! Actual artifact contexts for diagnostic environment-check harnesses.
Preparation does not certify selected, filtered or per-record results. -/

@[expose] public section

namespace Ix.KernelCheck.Binding

def limits : Ix.Kernel.Admission.Limits := ⟨1 <<< 22, 1 <<< 22, 1 <<< 34, 1 <<< 28, 1 <<< 26⟩

def context (env : Ixon.Env) :
    Except String (Ix.Kernel.RoleTable × Ix.Kernel.Reader.Prelude .anon) := do
  if env.roleBinding.isSome then
    let input ← (Ix.RoleBinding.Artifact.prepareRecords env limits).mapError toString
    return (input.prepared.table, input.prepared.pre)
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
