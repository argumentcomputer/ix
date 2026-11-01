module

public import Ix.RoleBinding.Artifact

/-! Actual artifact contexts for diagnostic environment-check harnesses.
Preparation does not certify selected, filtered or per-record results. -/

@[expose] public section

namespace Ix.KernelCheck.Binding

def limits : Ix.Kernel.Admission.Limits := ⟨1 <<< 22, 1 <<< 22, 1 <<< 34, 1 <<< 28, 1 <<< 26⟩

def context (env : Ixon.Env) :
    Except String (Ix.Kernel.RoleTable × Ix.Kernel.Reader.Prelude .anon) := do
  if let some raw := env.roleBinding then
    let binding : Ix.Kernel.Admission.Binding := ⟨raw.address, raw.bytes⟩
    let table ← (Ix.Kernel.Admission.admitBinding Address.admissionHash binding).mapError
      (fun e => toString (Ix.RoleBinding.Artifact.Error.binding e))
    let mut needed : Std.HashSet Address := {}
    for (_, address) in table.bound do
      needed := needed.insert address
    for (_, entries) in table.evidence do
      for entry in entries do
        if let .proof address := entry then
          needed := needed.insert address
    let decodeAt (pos : Nat) (address : Address) (rawBytes : ByteArray) : Except String Ixon.Constant := do
      unless decide (Address.admissionHash rawBytes = address) do
        throw (toString (Ix.RoleBinding.Artifact.Error.bytes (.mismatch .records pos address)))
      (Ixon.Canonical.deConstant limits.maxRecordBytes limits.maxRecordUnivNodes rawBytes).mapError
        (fun e => toString (Ix.RoleBinding.Artifact.Error.bytes (.decode pos address e)))
    let mut store : Benchmarks.Kernel.CheckIxeStep.RecordStore := {}
    for (address, idx) in needed.toArray.zipIdx do
      if let some lc := env.consts[address]? then
        let c ← decodeAt idx address lc.rawBytes
        store := store.insert address c
        let own := Ixon.CheckOrder.owner address c
        if own != address && !store.contains own then
          if let some ownLc := env.consts[own]? then
            let ownC ← decodeAt idx own ownLc.rawBytes
            store := store.insert own ownC
    (Ix.RoleBinding.Artifact.checkBindings table store).mapError toString
    let preRecords ← (Ix.RoleBinding.preludeRecords table (store[·]?) Ix.Kernel.preludeShape).mapError
      (fun e => toString (Ix.RoleBinding.Artifact.Error.prelude e))
    let mut preBlobAddrs : Std.HashSet Address := {}
    for (_, c) in preRecords do
      for r in c.refs do
        if env.blobs.contains r then
          preBlobAddrs := preBlobAddrs.insert r
    let blobs := (preBlobAddrs.toArray.filterMap fun a => env.blobs[a]?.map (a, ·)).qsort
      (fun x y => x.1.cmpBytes y.1 == .lt) |>.toList
    let pre : Ix.Kernel.Reader.Prelude .anon ← (Ix.Kernel.Reader.readPrelude table preRecords #[] blobs).mapError
      (fun e => toString (Ix.RoleBinding.Artifact.Error.prelude e))
    (Ix.Kernel.Reader.checkPreludeShape pre).mapError
      (fun e => toString (Ix.RoleBinding.Artifact.Error.prelude e))
    (Ix.Kernel.Reader.checkFallbackRecursors pre).mapError
      (fun e => toString (Ix.RoleBinding.Artifact.Error.prelude e))
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
