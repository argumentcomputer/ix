import Tests.Ix.CompileCert.Compiled

/-! Bounded census of exact stored bytes. The producer is not rerun. Source
capture uses the loaded Lean environment; proposed names/addresses remain
untrusted and every selected record is read and admitted by CompileCert. -/

namespace Tests.Ix.CompileCert.Stored

open _root_.Ix.CompileCert

def roots : List Lean.Name :=
  [`id, `Function.comp, `Nat, `Nat.add, `Bool, `List, `Option, `Prod]

/-- A finite diagnostic budget, not a termination/domain claim. Following
every stored reference may include extra records, which admission checks. -/
def recordCone (produced : Ixon.Env) : Nat → List Address →
    Benchmarks.Kernel.CheckIxeStep.RecordStore → Except String Benchmarks.Kernel.CheckIxeStep.RecordStore
  | 0, _, _ => .error "record closure budget exhausted"
  | _ + 1, [], store => .ok store
  | fuel + 1, address :: rest, store => do
    if store.contains address then recordCone produced fuel rest store
    else
      let some lazy := produced.consts[address]? | throw s!"missing stored dependency {address}"
      let record ← lazy.get
      let owners := match record.info with
        | .iPrj p => [p.block]
        | .cPrj p => [p.block]
        | .rPrj p => [p.block]
        | .dPrj p => [p.block]
        | _ => []
      recordCone produced fuel (owners ++ record.refs.toList ++ rest) (store.insert address record)

def explainCorrespondence (input : Input) : IO Unit := do
  match prepareArtifact input.toArtifactInput with
  | .error _ => pure ()
  | .ok artifact =>
    let cx : ExportContext := ⟨input.source, input.map, artifact.pins⟩
    let reader := _root_.Ix.Kernel.Admission.streamContext artifact.pins artifact.prelude
      artifact.constants input.blobs input.hint
    for ci in input.source.declarations do
      unless decide (DirectMatch cx (streamEntries artifact.declarations) ci ∨
          RawSourceMatch cx reader artifact.constants ci) do
        match directExport cx ci with
        | .error reason => IO.println s!"  source export {ci.name}: {reason}"
        | .ok _ => IO.println s!"  source entry mismatch {ci.name}"

def rootInput (env : Lean.Environment) (produced : Ixon.Env) (root : Lean.Name) :
    Except String Input := do
  let captured ← captureCone env.find? [root] 256
  let seeds ← captured.source.declarations.mapM fun ci => do
    let some named := produced.named[_root_.Ix.Name.fromLeanName ci.name]?
      | throw s!"missing proposed source name {ci.name}"
    return named.addr
  let store ← recordCone produced 16384 seeds {}
  let pins ← _root_.Ix.Kernel.Reader.defaultPins
  let pre ← _root_.Ix.Kernel.Reader.builtinPrelude
  let hints := Benchmarks.Kernel.CheckIxeStep.Hints.ofStore store produced.anonHints
  let setup := Benchmarks.Kernel.CheckIxeStep.setup store (produced.blobs[·]?) pins pre hints.lookup
  let primaries := setup.ordered.filterMap (fun a => (store[a]?).map (a, ·))
  let projections := (store.toArray.filter fun (a, c) =>
    Benchmarks.Kernel.CheckIxeStep.owner a c != a).qsort (fun a b => a.1.cmpBytes b.1 == .lt)
  let map ← captured.source.declarations.mapM fun ci => do
    let some named := produced.named[_root_.Ix.Name.fromLeanName ci.name]?
      | throw s!"missing proposed source name {ci.name}"
    let some target := _root_.Ix.Kernel.Reader.resolve setup.cx.store named.addr
      | throw s!"unresolved proposed source name {ci.name}"
    return MapEntry.mk ci.name named.addr target
  return {
    source := captured.source, roots := [root], map := map
    limits := ⟨16384, 65536, 268435456, 4194304, 1048576⟩
    records := (primaries ++ projections).toList.map (fun (a, c) => (a, Ixon.serConstant c))
    blobs := produced.blobs.toList, hint := hints.lookup }

def run (path : String) : IO Unit := do
  let start ← IO.monoMsNow
  let bytes ← IO.FS.readBinFile path
  IO.println s!"input {path}; bytes {bytes.size}; Blake3 {Address.blake3 bytes}"
  let produced ← IO.ofExcept (Ixon.deEnv bytes)
  let env ← getCompileEnv #[`Init, `Std]
  let mut count := 0
  let mut unexpected := 0
  for root in roots do
    let began ← IO.monoMsNow
    match rootInput env produced root with
    | .error reason =>
      IO.println s!"BLOCKED {root}: {reason}"
      unexpected := unexpected + 1
    | .ok input =>
      let outcome : RootOutcome input := ⟨root, checkRoot input root⟩
      let reason := match outcome.result with
        | .ok _ => "checked correspondence and admission"
        | .error (.selection s) => s
        | .error (.certification e) => Compiled.declineLabel e
      IO.println s!"{repr outcome.classification} {root}: {reason}; source={input.source.declarations.length}; records={input.records.length}; ms={(← IO.monoMsNow) - began}"
      if outcome.classification == .rejected then explainCorrespondence input
      -- `Nat.add` carries `mdata` in Lean; certified under the erasure contract (M3).
      let expected := OutcomeClass.certified
      if outcome.classification != expected then unexpected := unexpected + 1
    count := count + 1
  unless count == roots.length do throw (IO.userError "incomplete root census")
  IO.println s!"COVERAGE {count}/{roots.length}; unexpected={unexpected}; total-ms={(← IO.monoMsNow) - start}"
  unless unexpected == 0 do throw (IO.userError "stored census changed an expected root outcome")

end Tests.Ix.CompileCert.Stored
