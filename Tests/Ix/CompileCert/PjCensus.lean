import Tests.Ix.Compile.Pass3
import Ix.CompileCert.Pj.RecRead
import Ix.CompileCert.CheckCompiled
import Benchmarks.Kernel.CheckIxeStep

/-! The canonical recursors consumed by O7–O12, read from their actual compiled
bytes after certified admission of their reference closure. All five firing
fixture families are required, every view/recursor is accounted for, and every
successful read has malformed-count and malformed-data controls. This is an
executable census of the reader's domain, not a proof of pass correctness. -/

namespace Tests.Ix.CompileCert.PjCensus

open _root_.Ix.CompileCert _root_.Ix.CompileCert.Pj

def require (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

structure Target where
  name : _root_.Ix.Name
  address : Address
  np : Nat
  nm : Nat
  nmin : Nat
  deriving Inhabited

/-- Extract all canonical recursors from freshly rebuilt changed-block views,
not just the recursors for which the reader happens to succeed. -/
def targetsOf (compiled : _root_.Ix.CompileM.LeanPipelineOut) : IO (Array Target) := do
  let cenv := compiled.cenv
  let inp := _root_.Ix.Compile.Pass.viewInput cenv
  let mut views : Std.HashMap _root_.Ix.Name _root_.Ix.Compile.Pass.BlockView := {}
  for (key, all) in cenv.p3Blocks do
    match _root_.Ix.Compile.Pass.buildView inp all with
    | .ok v => views := views.insert key v
    | .error e => throw (IO.userError s!"view {key.pretty}: {e}")
  let blocks := _root_.Ix.Compile.Pass.optBlocks cenv views
  let mut targets : Array Target := #[]
  let mut seen : Std.HashSet _root_.Ix.Name := {}
  for (_, block) in blocks do
    for (name, recursor) in block.ixRecs do
      unless seen.contains name do
        let some address := _root_.Ix.Compile.Pass.resolveAddr cenv name
          | throw (IO.userError s!"canonical recursor has no emitted address: {name.pretty}")
        require (compiled.env.consts.contains address)
          s!"canonical recursor address absent from emitted bytes: {name.pretty}@{address}"
        seen := seen.insert name
        targets := targets.push {
          name := name
          address := address
          np := recursor.numParams
          nm := recursor.numMotives
          nmin := recursor.numMinors }
  return targets.qsort (fun a b => a.name.pretty < b.name.pretty)

def declineText : Decline → String
  | .admission e => s!"admission: {e}"
  | .reading e => s!"reading: {e}"
  | .decoding e => s!"decoding: {repr e}"
  | .setup e => s!"setup: {e}"
  | .malformedInput e => s!"malformed input: {e}"
  | _ => "unexpected association-stage failure"

/-- Keep the actual recursors' complete reference closure, including projection
owners and the standard prelude. Unrelated fixture definitions are not inputs to
this recursor-reader census. -/
def artifactOf (bytes : ByteArray) (targets : Array Target) :
    IO ((input : ArtifactInput) × AdmittedArtifact input × Array _root_.Ix.Kernel.Name) := do
  let produced ← IO.ofExcept (Ixon.deEnv bytes)
  let mut store : Benchmarks.Kernel.CheckIxeStep.RecordStore := {}
  for (address, lazy) in produced.consts.toList do
    store := store.insert address (← IO.ofExcept lazy.get)
  let pins ← IO.ofExcept _root_.Ix.Kernel.Reader.defaultPins
  let pre ← IO.ofExcept _root_.Ix.Kernel.Reader.builtinPrelude
  let hints := Benchmarks.Kernel.CheckIxeStep.Hints.ofStore store produced.anonHints
  let setup := Benchmarks.Kernel.CheckIxeStep.setup store (produced.blobs[·]?) pins pre hints.lookup
  let roots := targets.map (·.address) ++ pre.records.map (·.1)
  let ordered := Benchmarks.Kernel.CheckIxeStep.closure setup.store setup.extra roots
  let owners : Std.HashSet Address := ordered.foldl (fun s a => s.insert a) {}
  let primaries := ordered.filterMap (fun a => (setup.store[a]?).map (a, ·))
  let projections := (setup.store.toArray.filter fun (a, c) =>
    Benchmarks.Kernel.CheckIxeStep.owner a c != a && owners.contains (Benchmarks.Kernel.CheckIxeStep.owner a c)).qsort
      (fun a b => a.1.cmpBytes b.1 == .lt)
  let constants := (primaries ++ projections).toList
  let input : ArtifactInput := {
    limits := ⟨16384, 16384, 67108864, 4194304, 1048576⟩
    records := constants.map (fun (a, c) => (a, Ixon.serConstant c))
    blobs := produced.blobs.toList
    hint := hints.lookup }
  match prepareArtifact input with
  | .ok artifact => do
    -- Resolve names in the exact admitted subset. Recursor indices depend on
    -- this context, so the larger preparation store is not interchangeable.
    let reader := _root_.Ix.Kernel.Admission.streamContext artifact.pins artifact.prelude
      artifact.constants input.blobs input.hint
    let mut names : Array _root_.Ix.Kernel.Name := #[]
    for target in targets do
      let some ref := _root_.Ix.Kernel.Reader.resolve reader.store target.address
        | throw (IO.userError s!"cannot resolve admitted recursor: {target.name.pretty}")
      names := names.push (reader.nameOf ref)
    return ⟨input, artifact, names⟩
  | .error e => throw (IO.userError (declineText e))

/-- Report the first extraction/check condition that fails, retaining the exact
recursor and counts in the caller's diagnostic. -/
def readFailure (env : _root_.Ix.Kernel.Env) (name : _root_.Ix.Kernel.Name)
    (np nm nmin : Nat) : String := Id.run do
  let some (.recInfo hdr _ _ _) := env.find? name | return "not an installed recursor"
  let some (_, t1) := hdr.type.stripPis np | return "parameter telescope"
  let some (mbs, t2) := t1.stripPis nm | return "motive telescope"
  let some motives := (mbs.mapIdx fun j b => readMotive j b).mapM id
    | return "motive extraction"
  let some (nbs, _) := t2.stripPis nmin | return "minor telescope"
  let some _ := (nbs.mapIdx fun q b => readMinor env np nm motives q b).mapM id
    | return "minor extraction / constructor lookup"
  let some r := extractRec env name np nm nmin | return "conclusion extraction"
  if !decide (r.RecOk env name) then return "rebuilt recursor type differs"
  if r.major ≥ r.nm then return "major motive out of range"
  if r.finalMetas.length != (r.majorMotive.tele r.np).length then return "final binder count"
  for m in r.motives do
    for p in m.tele r.np do
      if p.2 != ⟨.never⟩ then return "motive telescope binder annotation"
  for n in r.minors do
    if n.motive ≥ r.nm then return "minor motive out of range"
    if n.paramMetas.length != r.np then return "constructor parameter metadata count"
    if n.fieldMetas.length != n.fields.length then return "field metadata count"
    if n.ihMetas.length != n.recFields.length then return "hypothesis metadata count"
    if !(n.recFields.all (fun p => p.2.1 < r.nm)) then return "recursive field motive out of range"
    if !decide (n.CtorOk env r.np r.motives r.params) then return "rebuilt constructor type differs"
  return "unexpected failure after all extraction/check conditions"

def runUnit (path : String) : IO (Nat × Nat × Nat) := do
  let unit ← Tests.Ix.Compile.Pass3.unitOfFile path
  let compiled ← Tests.Ix.Compile.Pass3.compileUnit unit true
  let targets ← targetsOf compiled
  require (!targets.isEmpty) s!"{unit.name}: zero canonical recursors"
  let ⟨_, artifact, names⟩ ← artifactOf compiled.bytes targets
  require (names.size == targets.size) s!"{unit.name}: target coverage changed"
  let mut read := 0
  let mut controls := 0
  let mut problems := 0
  for i in [:targets.size] do
    let target := targets[i]!
    let name := names[i]!
    match readRec artifact.env name target.np target.nm target.nmin with
    | none =>
      problems := problems + 1
      IO.println s!"[pj-census] FAIL {unit.name}/{target.name.pretty} np={target.np} nm={target.nm} nmin={target.nmin}: {readFailure artifact.env name target.np target.nm target.nmin}"
    | some data =>
      read := read + 1
      require (decide (data.Check artifact.env name)) s!"{unit.name}: successful unchecked read"
      require (data.np == target.np && data.nm == target.nm && data.nmin == target.nmin)
        s!"{unit.name}: successful read changed supplied counts"
      -- Each negative uses this same successfully read neighbour.
      require ((readRec artifact.env name target.np 0 target.nmin).isNone)
        s!"{unit.name}/{target.name.pretty}: zero-motive control accepted"
      let malformed := { data with major := data.nm }
      require (!decide (malformed.Check artifact.env name))
        s!"{unit.name}/{target.name.pretty}: out-of-range major control accepted"
      controls := controls + 2
  IO.println s!"[pj-census] {unit.name}: canonical-recursor-names={targets.size} admitted-records={artifact.constants.length} read={read} controls={controls} problems={problems}"
  return (targets.size, read, problems)

def run : IO UInt32 := do
  let mut units := 0
  let mut total := 0
  let mut read := 0
  let mut problems := 0
  for path in Tests.Ix.Compile.Pass3.pjPassFiles do
    units := units + 1
    try
      let (n, r, p) ← runUnit path
      total := total + n
      read := read + r
      problems := problems + p
    catch e =>
      problems := problems + 1
      IO.println s!"[pj-census] FAIL {path}: {e}"
  IO.println s!"[pj-census] TOTAL: units={units} canonical-recursor-names={total} read={read} problems={problems}"
  return if units == 5 && total > 0 && read == total && problems == 0 then 0 else 1

end Tests.Ix.CompileCert.PjCensus
