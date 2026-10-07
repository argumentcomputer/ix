import Ix.CompileCert.Bridge.RoundTrip
import Ix.CompileCert.Entry
import Ix.CompileDriver
import Ix.Meta
import Benchmarks.Kernel.CheckIxeStep
import Tests.Ix.CompileCert.BlockDefs

/-! # M7 X2: the bridge round trip (ignored runner `bridge-roundtrip`)

1. **Fixtures, through the bytes and the certified reader.** The lane's `BlockDefs` cone is compiled
   by the Lean compiler in process (as `compile-cert-c1 compiled` does), its bytes read by the
   certified reader and admitted by the certified fold (`prepareArtifact`). For every source
   declaration, `bridgeExport` (each term through the compiler's `canonExpr` and the bridge at the
   lane's naming) is compared with the lane's `directExport` and with the reader's entries.
2. **Init+Std, every constant.** `bridgeSource` of `canonExpr` of every type, value and rule
   right-hand side is compared with the lane's `exportSourceExpr` of the Lean term.
3. **Controls**, each beside its valid neighbour: a name map moved to another name, and a level
   map shifted, both make the fixture's comparison fail.

Summary lines: `[bridge-roundtrip] fixtures: …`, `[bridge-roundtrip] initstd: …`,
`[bridge-roundtrip] controls: …`, and `[bridge-roundtrip] 0 problem(s)` on success. -/

namespace Tests.Ix.CompileCert.BridgeRoundTrip

open _root_.Ix.CompileCert
open _root_.Ix.CompileCert.Bridge

def prefixName : Lean.Name := `Tests.Ix.CompileCert.BlockDefs

def roots : List Lean.Name :=
  [`first, `firstAlias, `first_eq, `Void, `Pair, `getFst, `Node.val, `Node.kids].map (prefixName ++ ·)

def entryEq (a b : DirectEntry) : Bool := a.withoutHint == b.withoutHint

/-- The fixture's input and admitted artifact, built as `Tests.Ix.CompileCert.Compiled.run` builds
them. -/
def fixtureInput : IO ((input : Input) × AdmittedArtifact input.toArtifactInput) := do
  let env ← getCompileEnv #[prefixName]
  let captured ← IO.ofExcept (captureCone env.find? roots 128)
  let compiled ← match ← _root_.Ix.CompileM.compileLeanConsts
      (captured.source.declarations.map (fun ci => (ci.name, ci))) (numWorkers := 1) with
    | .ok out => pure out
    | .error e => throw (IO.userError s!"compiler failed: {e}")
  let produced ← IO.ofExcept (Ixon.deEnv compiled.bytes)
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
    let some target := _root_.Ix.Kernel.Reader.resolve setup.cx.store named.addr
      | throw (IO.userError s!"producer source record does not resolve: {ci.name}")
    return MapEntry.mk ci.name named.addr target
  let input : Input := {
    source := captured.source
    roots := roots
    map := map
    limits := ⟨16384, 16384, 67108864, 4194304, 1048576⟩
    records := constants.map (fun (a, c) => (a, Ixon.serConstant c))
    blobs := produced.blobs.toList
    hint := hints.lookup }
  match prepareArtifact input.toArtifactInput with
  | .ok artifact => return ⟨input, artifact⟩
  | .error _ => throw (IO.userError "the certified fold refused the fixture artifact")

/-- The fixture round trip: (declarations, bridged = lane export, found among the reader's entries). -/
def fixtureRoundTrip (input : Input) (artifact : AdmittedArtifact input.toArtifactInput)
    (canon : Lean.Expr → _root_.Ix.Expr) (cxOf : ExportContext → ExportContext) :
    Nat × Nat × Nat × List String := Id.run do
  let cx : ExportContext := cxOf ⟨input.source, input.map, artifact.pins, noImages⟩
  let entries := streamEntries artifact.declarations
  let mut total := 0
  let mut equal := 0
  let mut read := 0
  let mut bad : List String := []
  for ci in input.source.declarations do
    total := total + 1
    match directExport ⟨input.source, input.map, artifact.pins, noImages⟩ ci, bridgeExport cx canon ci with
    | .ok d, .ok b =>
      if entryEq d b then
        equal := equal + 1
        if entries.any (entryEq b) then read := read + 1
      else bad := s!"{ci.name}: bridged entry differs from the lane's export" :: bad
    | .error _, .error _ => equal := equal + 1
    | .ok _, .error e => bad := s!"{ci.name}: bridge failed: {e}" :: bad
    | .error e, .ok _ => bad := s!"{ci.name}: lane export failed ({e}), bridge succeeded" :: bad
  return (total, equal, read, bad)

/-- A tree-size walk that stops at `cap` (the bridge and `er` are tree walks; the lane's export
is sharing-aware). -/
partial def treeCap (cap : Nat) (e : Lean.Expr) (acc : Nat) : Nat :=
  if acc ≥ cap then acc else
  match e with
  | .app f a => treeCap cap a (treeCap cap f (acc + 1))
  | .lam _ t b _ | .forallE _ t b _ => treeCap cap b (treeCap cap t (acc + 1))
  | .letE _ t v b _ => treeCap cap b (treeCap cap v (treeCap cap t (acc + 1)))
  | .mdata _ x | .proj _ _ x => treeCap cap x (acc + 1)
  | _ => acc + 1

/-- The tree-size cap of the Init+Std comparison (terms above it are counted, not compared). -/
def initStdCap : Nat := 1000000

/-- Init+Std: every type, value and rule right-hand side at the source naming. -/
def initStdRoundTrip (env : Lean.Environment) : Nat × Nat × Nat × Nat × List String := Id.run do
  let mut terms := 0
  let mut equal := 0
  let mut declined := 0
  let mut skipped := 0
  let mut bad : List String := []
  for (n, ci) in env.constants.toList do
    let params := ci.levelParams
    let mut exprs : Array Lean.Expr := #[ci.type]
    match ci with
    | .defnInfo v => exprs := exprs.push v.value
    | .thmInfo v => exprs := exprs.push v.value
    | .opaqueInfo v => exprs := exprs.push v.value
    | .recInfo v => exprs := exprs ++ v.rules.toArray.map (·.rhs)
    | _ => pure ()
    for e in exprs do
      terms := terms + 1
      if treeCap initStdCap e 0 ≥ initStdCap then
        skipped := skipped + 1
      else
        let lane := (exportSourceExpr params e).toOption
        let bridged := bridgeSource params (canonOf e)
        if lane == bridged then
          equal := equal + 1
          if lane.isNone then declined := declined + 1
        else if bad.length < 20 then
          bad := s!"{n}: the bridge of the compiler's term differs from the lane's export" :: bad
  return (terms, equal, declined, skipped, bad)

def run : IO UInt32 := do
  let mut problems := 0
  -- 1. the fixtures, through the bytes
  let ⟨input, artifact⟩ ← fixtureInput
  let (total, equal, read, bad) := fixtureRoundTrip input artifact canonOf id
  IO.println s!"[bridge-roundtrip] fixtures: {total} declarations, {equal} bridged = lane export, {read} found among the certified reader's entries"
  for b in bad do IO.println s!"[bridge-roundtrip] FAIL {b}"
  problems := problems + bad.length
  if read == 0 then
    IO.println "[bridge-roundtrip] FAIL no bridged declaration was found among the reader's entries"
    problems := problems + 1
  -- 3. controls on the fixture, each beside the valid neighbour above
  let target := prefixName ++ `first
  let moved : ExportContext → ExportContext := fun cx =>
    { cx with map := cx.map.map fun m =>
        if m.source == target then { m with source := prefixName ++ `getFst } else m }
  let (_, equalMoved, _, _) := fixtureRoundTrip input artifact canonOf moved
  let nameControl := equalMoved < equal
  let shiftLevels : Lean.Expr → _root_.Ix.Expr := fun e =>
    canonOf (e.replace fun x => match x with
      | .sort (.succ l) => some (.sort l)
      | _ => none)
  let (_, equalShifted, _, _) := fixtureRoundTrip input artifact shiftLevels id
  let levelControl := equalShifted < equal
  IO.println s!"[bridge-roundtrip] controls: moved name map {if nameControl then "refused" else "NOT refused"} ({equalMoved}/{total} equal), shifted levels {if levelControl then "refused" else "NOT refused"} ({equalShifted}/{total} equal); valid neighbour {equal}/{total}"
  unless nameControl do problems := problems + 1
  unless levelControl do problems := problems + 1
  -- 2. Init+Std
  let ienv ← getFileEnv "Benchmarks/Compile/CompileInitStd.lean"
  let (terms, equalI, declined, skipped, badI) := initStdRoundTrip ienv
  let differing := terms - equalI - skipped
  IO.println s!"[bridge-roundtrip] initstd: {ienv.constants.toList.length} constants, {terms} terms, {equalI} bridged = lane export ({declined} declined by both), {differing} differing, {skipped} over the tree-size cap {initStdCap} (not compared)"
  for b in badI do IO.println s!"[bridge-roundtrip] FAIL {b}"
  problems := problems + differing
  IO.println s!"[bridge-roundtrip] {problems} problem(s)"
  return if problems == 0 then 0 else 1

end Tests.Ix.CompileCert.BridgeRoundTrip
