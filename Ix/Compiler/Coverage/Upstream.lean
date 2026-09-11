import Ix.Compiler.Coverage.Run
import Ix.Compiler.Coverage.HeapSnapshot
import Ix.Compiler.Coverage.StdContact

/-! Byte-exact exports from the pinned upstream Lean-to-Ixon writer. Every
positive case enters the public checked pipeline with its complete original
constant closure. The observations follow constructor identities through both
address maps and reclaim the actual returned heaps. -/

namespace Ix.Compiler.Coverage.Upstream

open Lean Ix.Compiler.Ixon

def directory : String := "Tests/Fixtures/Compiler/ixon-upstream"

def writerPin : String := "git:ix@6f18ea907b78d06f7dc0917c43beb385561c35f4"

inductive Expected where
  | nat (number : Nat)
  | missingCovered (address : String)

structure Fixture where
  name : String
  pieceBytes : Nat
  pieceHash : String
  root : String
  count : Nat
  expected : Expected

def fixtures : List Fixture := [
  ⟨"applyClosed", 662, "2e4873546afd7558d5c02b244d2713229c02f6f684c298739f0b7431e7b8df02",
    "b81b754f02c1b63279a609ab4b55b609fd6f87fab7b14879f4021c3327c2eb40", 6, .nat 3⟩,
  ⟨"captureClosed", 666, "280ab6f15706a3c0ed76511604abd5653a524dba4b5893b193c904db2f66f852",
    "5628cfe1b4f959fb116661fc50ae8e9e4bfa470ac5d0e639a75b9d23aed12953", 6, .nat 2⟩,
  ⟨"letClosed", 670, "717c04ee467799465d08c0e624f312fe619badbe7394c7fa0637f1b0c975744b",
    "6c737171f1a3c482ba96cbe4998ea660fda824c578fe668ab9fdc4aae1b9754f", 6, .nat 4⟩,
  ⟨"addClosed", 3072, "ce2cc4e16ffbe9166b9be201c524cbc7530705fdc5b8ff7602627aba70f5f4d0",
    "799b7939dcc3c158620a49e645c9fee367674251e5298594bf8801747e49f990", 19,
    .missingCovered "1ce12e12485a4793aa5baf4f197f5d5ceb5fb8e166f1a06640b87f9c91dad725"⟩,
  ⟨"recClosed", 796, "4c0c64ad2997001a63b5d6a70475f656cd27eb8dd30ba8c3acb8bd87564b3f49",
    "1248f5d1b9eb3c50a6818d4d6d1e2413a7e9587e0990de2421e997d756da7aa1", 6,
    .missingCovered "1248f5d1b9eb3c50a6818d4d6d1e2413a7e9587e0990de2421e997d756da7aa1"⟩]

def policy : Policy :=
  { sourcePolicy with
    limits := { sourcePolicy.limits with
      maxConstants := 32, maxExpressionUnits := 4096, maxExpandedExpressionUnits := 8192
      maxLayer1NodeVisits := 262144, maxErasedDeclarations := 256
      maxErasureAppendCells := 16384, maxCertificateCandidates := 64
      maxCertificateSourceNodeWork := 2097152 }
    evalFuel := 10000, controlFuel := 10000, heapFuel := 10000 }

structure Input where
  source : Source
  snapshot : Json
  provenance : Json
  expected : Expected

def load (path : System.FilePath) (fixture : Fixture) : IO (Except String Input) := do
  let manifest ← CatalogContactFixture.readHexAt path s!"{fixture.name}.manifest.hex"
  let piece ← CatalogContactFixture.readHexAt path s!"{fixture.name}.ixe.hex"
  if (← (path / "CompilatrixUpstream.lean").metadata).byteSize > 4096 then
    return .error "upstream source module exceeds the 4 KiB fixture limit"
  let moduleBytes ← IO.FS.readBinFile (path / "CompilatrixUpstream.lean")
  return do
    let manifest ← manifest
    let piece ← piece
    if piece.size != fixture.pieceBytes || (Address.blake3 piece).toHex != fixture.pieceHash then
      throw "upstream original piece bytes drifted"
    let loaded ← (Catalog.load manifest #[piece]).mapError (fun error => reprStr error)
    let some member := loaded.manifest.members[0]? | throw "upstream member missing"
    let some stored := loaded.pieces[0]? | throw "upstream piece missing"
    let some root := stored.main | throw "upstream MAIN missing"
    if member.label != s!"CompilatrixUpstream.{fixture.name}" ||
        member.toolchain != "leanprover/lean4:v4.33.1" || member.sourcePin != writerPin ||
        root.toHex != fixture.root || loaded.constants.length != fixture.count ||
        !stored.assumptions.isEmpty || loaded.manifest.members.size != 1 then
      throw "upstream provenance, root, or complete closure drifted"
    if CatalogContactFixture.dependencyClosure loaded.constants root != loaded.constants then
      throw "upstream pack is not the exact reachable dependency closure"
    let constants ← stored.constants.toList.mapM fun record => do
      if ser record.constant != record.bytes then throw "upstream constant bytes changed after decoding"
      return Json.mkObj [("key", toJson record.address), ("bytes", byteJson record.bytes)]
    let provenance := Json.mkObj [
      ("members_root", toJson loaded.manifest.membersRoot),
      ("content_root", toJson loaded.manifest.contentRoot), ("piece_hash", toJson fixture.pieceHash),
      ("toolchain", toJson member.toolchain), ("source_pin", toJson member.sourcePin),
      ("source_module_hash", toJson (Address.blake3 moduleBytes)),
      ("source_module", byteJson moduleBytes)]
    let source : Source :=
      { name := s!"upstream-{fixture.name}", constants := loaded.constants
        root, literals := [], policy, expected := .scalar 0 false }
    return {
      source, provenance, expected := fixture.expected
      snapshot := Json.mkObj [
        ("root", toJson root), ("constants", toJson constants),
        ("manifest_bytes", byteJson manifest), ("piece_bytes", byteJson piece),
        ("blob_inputs", toJson (loaded.blobs.map fun (address, bytes) =>
          Json.mkObj [("key", toJson address), ("bytes", byteJson bytes)])),
        ("policy", toJson policy), ("provenance", provenance)] }

structure NatIds where
  block : Address
  zero : Address
  succ : Address

def natIds (source : Source) : Except String NatIds := do
  let some zero := source.constants.find? (fun (_, constant) => match constant.info with
    | .cPrj projection => projection.idx == 0 && projection.cidx == 0
    | _ => false)
    | throw "missing upstream Nat.zero"
  let some succ := source.constants.find? (fun (_, constant) => match constant.info with
    | .cPrj projection => projection.idx == 0 && projection.cidx == 1
    | _ => false)
    | throw "missing upstream Nat.succ"
  let .cPrj zeroInfo := zero.2.info | throw "Nat.zero projection changed"
  let .cPrj succInfo := succ.2.info | throw "Nat.succ projection changed"
  if zeroInfo.block != succInfo.block then throw "upstream Nat constructor blocks disagree"
  return { block := zeroInfo.block, zero := zero.1, succ := succ.1 }

private def sourceNat? (ids : NatIds) : Nat → Ixon.Eval.Value → Option Nat
  | 0, _ => none
  | fuel + 1, .ctorV block 0 tag fields =>
    if block != ids.block then none else
      match tag, fields with
      | 0, [] => some 0
      | 1, [tail] => (· + 1) <$> sourceNat? ids fuel tail
      | _, _ => none
  | _, _ => none

private def nat0? (zero succ : Address) : Nat → IxIR0.Value → Option Nat
  | 0, _ => none
  | fuel + 1, .ctor address tag fields =>
    if address == zero && tag == 0 && fields.isEmpty then some 0
    else if address == succ && tag == 1 then
      match fields with
      | [tail] => (· + 1) <$> nat0? zero succ fuel tail
      | _ => none
    else none
  | _, _ => none

private def nat1? (zero succ : Address) : Nat → IxIR1.Store → IxIR1.RVal → Option Nat
  | 0, _, _ => none
  | fuel + 1, store, .loc location => do
    let box ← store.get? location
    if box.world != .shared then none else do
      let .ctorN identity fields := box.node | none
      if identity == IxIR1.Lower.ctorIdOf zero 0 && fields.isEmpty then some 0
      else if identity == IxIR1.Lower.ctorIdOf succ 1 then
        match fields.toList with
        | [tail] => (· + 1) <$> nat1? zero succ fuel store tail
        | _ => none
      else none
  | _, _, _ => none

private def agree (stage : String) (expected : Nat) (actual : Option Nat) : Except String Unit :=
  if actual == some expected then .ok ()
  else .error s!"{stage}: expected Nat {expected}, observed {repr actual}"

private def counters (store : IxIR1.Store) : Json :=
  Json.mkObj [("allocs", toJson store.allocs), ("frees", toJson store.frees),
    ("rcops", toJson store.rcops), ("live", toJson store.live), ("reuses", toJson store.reuses)]

def observe (source : Source) (attached : source.Attached) (number : Nat) :
    Except String Observation := do
  let ids ← natIds source
  let value ← (Ixon.Eval.eval (Pipeline.validatedEvalCtx source.constants source.config)
    policy.evalFuel (Pipeline.validatedMainFrame source.root) [] Pipeline.validatedMainSource).mapError
      (fun error => s!"Ixon: {repr error}")
  agree "Ixon" number (sourceNat? ids policy.evalFuel value)
  let artifact := attached.source.artifact
  let rename0 := IxIR0.MutualBlock.Renaming.apply attached.source.erasure.result.addressMap
  let rename1 := IxIR1.Readdress.Renaming.apply artifact.targetAddressMap
  let mut stages := [("ixon", toJson number)]
  for (stage, declarations, main, zero, succ) in [
      ("raw_ixir0", artifact.rawErasedDecls, IxIR0.Expr.ref source.root, ids.zero, ids.succ),
      ("ixir0", artifact.erasedDecls, attached.source.erasure.result.main, rename0 ids.zero, rename0 ids.succ)] do
    let value ← (IxIR0.eval { env := IxIR0.Env.ofList declarations } policy.evalFuel [] main).mapError
      (fun error => s!"{stage}: {repr error}")
    agree stage number (nat0? zero succ policy.evalFuel value)
    stages := stages ++ [(stage, toJson number)]
  let mut stores : List IxIR1.Store := []
  let mut released : List IxIR1.Store := []
  for (stage, declarations, main, zero, succ) in [
      ("raw_ixir1", attached.source.lowering.raw, attached.source.lowering.mainCode,
        rename0 ids.zero, rename0 ids.succ),
      ("ixir1", artifact.targetDecls, artifact.main, rename1 (rename0 ids.zero), rename1 (rename0 ids.succ))] do
    let context : IxIR1.Ctx := { decls := IxIR1.Env.ofList declarations }
    let (store, value) ← (IxIR1.runOwnedMain context .shared main policy.evalFuel).mapError
      (fun error => s!"{stage}: {repr error}")
    agree stage number (nat1? zero succ policy.evalFuel store value)
    let reclaimed ← (IxIR1.dropVal context policy.heapFuel store value).mapError
      (fun error => s!"{stage} reclamation: {repr error}")
    stores := stores ++ [store]
    released := released ++ [reclaimed]
    stages := stages ++ [(stage, Json.mkObj [("nat", toJson number),
      ("value", toJson value), ("store", toJson store), ("reclaimed", toJson reclaimed)])]
  let program := attached.target.artifact.program
  let context := IxIR2.Eval.Context.ofProgram program attached.target.artifact.validationContext.schemas
  let mut physicalStores : List Json := []
  let mut summary := Json.null
  for (stage, mode) in [("logical_ixir2", IxIR2.Eval.Interpretation.logical), ("physical_ixir2", .physical)] do
    let result ← (IxIR2.Eval.runMain context mode program policy.controlFuel policy.heapFuel).mapError
      (fun error => s!"{stage}: {repr error}")
    agree stage number (nat1? (rename1 (rename0 ids.zero)) (rename1 (rename0 ids.succ))
      policy.evalFuel result.store.heap result.value)
    let (reclaimed, remaining) ← (IxIR2.Eval.releaseShared policy.heapFuel result.store result.value).mapError
      (fun error => s!"{stage} reclamation: {repr error}")
    stores := stores ++ [result.store.heap]
    released := released ++ [reclaimed.heap]
    let stageObservation := Json.mkObj [("nat", toJson number), ("value", toJson result.value),
      ("store", toJson result.store), ("reclaimed", toJson reclaimed),
      ("control_remaining", toJson result.controlRemaining), ("heap_remaining", toJson result.heapRemaining),
      ("reclamation_remaining", toJson remaining)]
    physicalStores := physicalStores ++ [stageObservation]
    stages := stages ++ [(stage, stageObservation)]
    summary := Json.mkObj [("nat", toJson number), ("heap", counters result.store.heap),
      ("reclaimed", counters reclaimed.heap), ("peak_live_nodes", toJson result.store.peakLiveNodes),
      ("control_steps", toJson (policy.controlFuel - result.controlRemaining)),
      ("heap_work", toJson (policy.heapFuel - result.heapRemaining))]
  if stores.any (fun store => store.allocs != store.frees + store.live) ||
      released.any (fun store => store.live != 0 || store.allocs != store.frees) ||
      (stores.map counters).any (· != (stores.map counters).head!) ||
      (released.map counters).any (· != (released.map counters).head!) ||
      physicalStores[0]? != physicalStores[1]? then
    throw "upstream stage counters, complete baseline stores, budgets, or reclamation disagree"
  return { summary, stages := Json.mkObj stages }

def result (input : Input) (stage : String) (failure observation : Json)
    (compiled : Option input.source.Attached := none) (stages : Json := Json.null)
    (partialCompilation : Json := Json.null) (native : Json := Json.null)
    (object : Option ByteArray := none) : CaseResult :=
  let source := input.source
  { name := source.name
    row := Json.mkObj [
      ("name", toJson source.name), ("origin", toJson "upstream-lean"), ("root_kind", toJson "constant"),
      ("root", toJson source.root), ("source_constants", toJson source.constants.length),
      ("last_accepted_stage", toJson stage), ("rejection", failure), ("observation", observation),
      ("optimization_policy", toJson (if object.isSome then "baseline-ixir2; " ++
        (native.getObjValAs? String "selector").toOption.getD "unknown" else "baseline-only")),
      ("provenance", input.provenance),
      ("ir1_root", match compiled with
        | none => Json.null
        | some attached => toJson (IxIR1.Optimizer.graphRoot
            attached.source.artifact.targetArtifacts attached.source.artifact.main)),
      ("hpt_roots", match compiled with | none => Json.null | some attached => toJson attached.hpt.result.addresses),
      ("features", match compiled with | none => Json.null | some attached => toJson (features attached.target.artifact.program)),
      ("snapshot", toJson s!"{source.name}.json"),
      ("object", if object.isSome then toJson s!"{source.name}.o" else Json.null)]
    snapshot := Json.mkObj ([("format", toJson "compilatrix/source-case/1"), ("input", input.snapshot),
      ("compilation", match compiled with | none => partialCompilation | some attached => source.compilationSnapshot attached),
      ("observations", if compiled.isSome then stages else failure)] ++
      (if native == Json.null then [] else [("native", native)]))
    object }

def run (input : Input) : Except String CaseResult := do
  let source := input.source
  match source.compile, input.expected with
  | .ok attached, .nat number =>
    let observation ← observe source attached number
    let code ← match X86.Select.select attached.target.artifact.program with
      | .error .unsupportedScalarShape => pure "unsupportedScalarShape"
      | .error (.invalidSource (.invalid _ .schema "missing constructor schema")) =>
        pure "missingConstructorSchema"
      | .error error => throw s!"upstream native selection diagnostic drifted: {repr error}"
      | .ok _ => throw "upstream constructor graph unexpectedly passed scalar selection"
    let failure := Json.mkObj [("stage", toJson "x86-selection"), ("code", toJson code),
      ("root", toJson source.root), ("message", Json.null)]
    return result input "ixir2" failure observation.summary (some attached) observation.stages
  | .error (.pipeline (.validate address message)), .missingCovered expectedAddress =>
    if address.toHex != expectedAddress || message != "reference lacks a Covered certificate" then
      throw "upstream Covered diagnostic drifted"
    let partialCompilation ← addressedSnapshot source.constants source.root source.config source.policy.eraseFuel
    return result input "addressed-ixir0" (Json.mkObj [
      ("stage", toJson "validated-erasure"), ("code", toJson "missingCovered"),
      ("root", toJson address), ("message", toJson message)]) Json.null
      (partialCompilation := partialCompilation)
  | .error error, _ => throw s!"unexpected upstream compilation error: {repr error}"
  | .ok _, _ => throw "upstream negative case unexpectedly compiled"

def cases (path : System.FilePath := directory) : IO (Except String (List CaseResult)) := do
  let mut results := []
  for fixture in fixtures do
    match (← load path fixture).bind run with
    | .error message => return .error s!"{fixture.name}: {message}"
    | .ok result => results := results ++ [result]
  return .ok results

end Ix.Compiler.Coverage.Upstream
