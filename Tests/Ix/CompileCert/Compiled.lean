import Ix.CompileCert.Entry
import Ix.CompileDriver
import Ix.Meta
import Benchmarks.Kernel.CheckIxeStep
import Tests.Ix.CompileCert.BlockDefs

/-! A bounded real-compiler integration probe. The existing entry-case
producer supplies bytes and proposed metadata only. Source capture, map
validation, correspondence and admission are all performed by CompileCert.
No ReaderFidelity comparison or auxiliary exemption participates. -/

namespace Tests.Ix.CompileCert.Compiled

open _root_.Ix.CompileCert

def prefixName : Lean.Name := `Tests.Ix.CompileCert.BlockDefs

def roots : List Lean.Name :=
  [`first, `firstAlias, `first_eq, `Void, `Pair, `getFst, `Node.val, `Node.kids].map (prefixName ++ ·)

def declineLabel : Decline → String
  | .admission e => s!"admission: {e}"
  | .sourceDomain => "source-domain"
  | .setup s => s!"setup: {s}"
  | .decoding _ => "decoding"
  | .reading e => s!"reading: {e}"
  | .mapMismatch => "map"
  | .correspondence => "correspondence"
  | .blockCorrespondence => "block-correspondence"

def run : IO Unit := do
  let env ← getCompileEnv #[prefixName]
  let captured ← IO.ofExcept (captureCone env.find? roots 128)
  let compiled ← match ← _root_.Ix.CompileM.compileLeanConsts
      (captured.source.declarations.map (fun ci => (ci.name, ci))) (numWorkers := 1) with
    | .ok out => pure out
    | .error e => throw (IO.userError s!"compiler failed: {e}")
  unless compiled.ungroundedCount == 0 do throw (IO.userError "compiler output contains ungrounded declarations")
  let produced ← IO.ofExcept (Ixon.deEnv compiled.bytes)
  IO.println s!"compiled bytes: {compiled.bytes.size}; Blake3: {Address.blake3 compiled.bytes}"
  if let some directory ← IO.getEnv "C1_OUTPUT_DIR" then
    IO.FS.createDirAll directory
    IO.FS.writeBinFile (System.FilePath.mk directory / "compiled.ixe") compiled.bytes
  let mut store : Benchmarks.Kernel.CheckIxeStep.RecordStore := {}
  for (address, lazy) in produced.consts.toList do
    store := store.insert address (← IO.ofExcept lazy.get)
  let pins ← IO.ofExcept _root_.Ix.Kernel.Reader.defaultPins
  let pre ← IO.ofExcept _root_.Ix.Kernel.Reader.builtinPrelude
  let hints := Benchmarks.Kernel.CheckIxeStep.Hints.ofStore store produced.anonHints
  let setup := Benchmarks.Kernel.CheckIxeStep.setup store (produced.blobs[·]?) pins pre hints.lookup
  let primaries := setup.ordered.filterMap (fun a => (store[a]?).map (a, ·))
  let projections := (store.toArray.filter fun (a, c) =>
    Benchmarks.Kernel.CheckIxeStep.owner a c != a).qsort (fun a b => a.1.cmpBytes b.1 == .lt)
  let constants := (primaries ++ projections).toList
  let map ← captured.source.declarations.mapM fun ci => do
    let some named := produced.named[_root_.Ix.Name.fromLeanName ci.name]?
      | throw (IO.userError s!"producer omitted source map entry: {ci.name}")
    let address := named.addr
    let some target := _root_.Ix.Kernel.Reader.resolve setup.cx.store address
      | throw (IO.userError s!"producer source record does not resolve: {ci.name}")
    return MapEntry.mk ci.name address target
  let input : Input := {
    source := captured.source
    roots := roots
    map := map
    limits := ⟨16384, 16384, 67108864, 4194304, 1048576⟩
    records := constants.map (fun (a, c) => (a, Ixon.serConstant c))
    blobs := produced.blobs.toList
    hint := hints.lookup }
  IO.println s!"captured {captured.source.declarations.length} source declarations; {input.records.length} records"
  let outcomes := checkRoots input
  let mut accepted := 0
  let mut unexpected := 0
  for outcome in outcomes do
    match outcome.result with
    | .ok _ =>
      accepted := accepted + 1
      IO.println s!"CERTIFIED {outcome.root}"
    | .error reason =>
      let label := match reason with
        | .selection s => s!"selection: {s}"
        | .certification e => declineLabel e
      IO.println s!"DECLINED {outcome.root}: {label}"
      unexpected := unexpected + 1
  IO.println s!"{accepted}/{outcomes.length} certified; {unexpected} unexpected declines"
  if unexpected != 0 then throw (IO.userError "real compiler C1 probe found unresolved direct cones")
  let some (.defnInfo zero) := env.find? (prefixName ++ `Node.zero)
    | throw (IO.userError "missing checked alternative projection body")
  let changed : Source := ⟨captured.source.declarations.map fun ci =>
    if ci.name == prefixName ++ `Node.val then
      match ci with
      | .defnInfo original => .defnInfo { original with value := zero.value }
      | _ => ci
    else ci⟩
  let wrong := checkRoot { input with source := changed } (prefixName ++ `Node.val)
  match wrong with
  | .error (.certification .correspondence) =>
    IO.println "PASS: normalized projection rejects an alternative checked, same-typed value"
  | .error (.selection reason) =>
    throw (IO.userError s!"wrong-value control failed during source selection: {reason}")
  | .error (.certification reason) =>
    throw (IO.userError s!"wrong-value control had unexpected result: {declineLabel reason}")
  | .ok _ => throw (IO.userError "normalized projection accepted wrong source value")
  -- Preserve admitted target bytes and mutate one independently captured
  -- source field at a time. These cover nonempty rule/member obligations
  -- absent from the empty-inductive unit fixture.
  let some (.recInfo pairRec) := env.find? (prefixName ++ `Pair.rec)
    | throw (IO.userError "missing checked Pair recursor")
  unless !pairRec.rules.isEmpty do throw (IO.userError "nonempty-rule control became vacuous")
  let some (.ctorInfo pairCtor) := env.find? (prefixName ++ `Pair.mk)
    | throw (IO.userError "missing checked Pair constructor")
  let checks : List (String × Lean.ConstantInfo × Bool) := [
    ("nonempty recursor rule field count", .recInfo { pairRec with
      rules := pairRec.rules.map fun r => { r with nfields := r.nfields + 1 } }, false),
    ("nonempty recursor rule body", .recInfo { pairRec with
      rules := pairRec.rules.map fun r => { r with rhs := .bvar 999 } }, false),
    ("omitted nonempty recursor rule", .recInfo { pairRec with rules := [] }, false),
    ("source constructor member position", .ctorInfo { pairCtor with cidx := pairCtor.cidx + 1 }, true)]
  for (label, replacement, blockFailure) in checks do
    let source : Source := ⟨input.source.declarations.map fun ci =>
      if ci.name == replacement.name then replacement else ci⟩
    match checkRoot { input with source := source } (prefixName ++ `Pair) with
    | .error (.certification reason) =>
      let correct := match reason with
        | .blockCorrespondence => blockFailure
        | .correspondence => !blockFailure
        | _ => false
      unless correct do throw (IO.userError s!"{label}: unexpected {declineLabel reason}")
      IO.println s!"PASS: {label}"
    | .error (.selection reason) => throw (IO.userError s!"{label}: selection failed: {reason}")
    | .ok _ => throw (IO.userError s!"{label}: incorrect source accepted")

end Tests.Ix.CompileCert.Compiled
