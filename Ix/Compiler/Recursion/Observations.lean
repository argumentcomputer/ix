import Ix.Compiler.Recursion.Sources
import Ix.Compiler.Recursion.Pipeline
import Ix.Compiler.Coverage.HeapSnapshot

/-! Execute the actual source and compiler outputs. Constructor observations
check full identities; final reclamation visits the returned heaps. The
three-element hot/cold measurements retain the earlier IxIR₀ witness's counts.
-/

namespace Ix.Compiler.Recursion.Examples

open Lean Ix.Compiler.Ixon

deriving instance ToJson for IxIR0.Recursion.Schema
deriving instance ToJson for IxIR0.Recursion.Plan
deriving instance ToJson for IxIR2.Reuse.Report

inductive Observation where
  | list (values : List Nat)
  | pair (reversed original : List Nat)
  deriving BEq, Repr, ToJson

private def sourceList? (source : Source) : Nat → Ixon.Eval.Value → Option (List Nat)
  | 0, _ => none
  | fuel + 1, .ctorV block 1 tag fields =>
      if block != source.dataBlock then none
      else match tag, fields with
        | 0, [] => some []
        | 1, [.litV (.natL n), tail] => (n :: ·) <$> sourceList? source fuel tail
        | _, _ => none
  | _, _ => none

private def sourceObservation? (source : Source) (value : Ixon.Eval.Value) : Option Observation :=
  if source.aliased then
    match value with
    | .ctorV block 3 0 [left, right] => do
        if block != source.dataBlock then none
        else return .pair (← sourceList? source 1000 left) (← sourceList? source 1000 right)
    | _ => none
  else .list <$> sourceList? source 1000 value

private def list0? (source : Source) : Nat → IxIR0.Value → Option (List Nat)
  | 0, _ => none
  | fuel + 1, .ctor address tag fields =>
      if address == source.nil && tag == 0 && fields.isEmpty then some []
      else if address == source.cons && tag == 1 then
        match fields with
        | [.lit (.nat n), tail] => (n :: ·) <$> list0? source fuel tail
        | _ => none
      else none
  | _, _ => none

private def observation0? (source : Source) (value : IxIR0.Value) : Option Observation :=
  if source.aliased then
    match value with
    | .ctor address 0 [left, right] => do
        if address != source.pair then none
        else return .pair (← list0? source 1000 left) (← list0? source 1000 right)
    | _ => none
  else .list <$> list0? source 1000 value

private def list1? (source : Source) : Nat → IxIR1.Store → IxIR1.RVal → Option (List Nat)
  | 0, _, _ => none
  | fuel + 1, store, .loc location => do
      let box ← store.get? location
      let .ctorN identity fields := box.node | none
      if identity == IxIR1.Lower.ctorIdOf source.nil 0 && fields.isEmpty then some []
      else if identity == IxIR1.Lower.ctorIdOf source.cons 1 then
        match fields.toList with
        | [.lit (.nat n), tail] => (n :: ·) <$> list1? source fuel store tail
        | _ => none
      else none
  | _, _, _ => none

private def observation1? (source : Source) (store : IxIR1.Store)
    (value : IxIR1.RVal) : Option Observation :=
  if source.aliased then do
    let .loc location := value | none
    let box ← store.get? location
    let .ctorN identity fields := box.node | none
    if identity != IxIR1.Lower.ctorIdOf source.pair 0 then none
    else match fields.toList with
      | [left, right] => return .pair (← list1? source 1000 store left) (← list1? source 1000 store right)
      | _ => none
  else .list <$> list1? source 1000 store value

private def expected (source : Source) : Observation :=
  if source.aliased then .pair source.values.reverse source.values
  else .list source.values.reverse

private def agree (source : Source) (stage : String) (actual : Option Observation) : Except String Unit :=
  if actual == some (expected source) then .ok ()
  else .error s!"{stage}: expected {repr (expected source)}, got {repr actual}"

private def observe0 (source : Source) (stage : String) (declarations : List (Address × IxIR0.Decl))
    (main : IxIR0.Expr) : Except String Unit := do
  let value ← (IxIR0.eval { env := IxIR0.Env.ofList declarations } 10000 [] main).mapError
    (fun error => s!"{stage}: {repr error}")
  agree source stage (observation0? source value)

private def observe1 (source : Source) (stage : String) (context : IxIR1.Ctx)
    (main : IxIR1.Code) : Except String (IxIR1.Store × IxIR1.RVal × Json) := do
  let (store, value) ← (IxIR1.runOwnedMain context .shared main 10000).mapError
    (fun error => s!"{stage}: {repr error}")
  agree source stage (observation1? source store value)
  if store.live + store.frees != store.allocs then
    throw s!"{stage} terminal allocation balance disagrees"
  let reclaimed ← (IxIR1.dropVal context 10000 store value).mapError
    (fun error => s!"{stage} reclamation: {repr error}")
  if reclaimed.live != 0 || reclaimed.allocs != reclaimed.frees then
    throw s!"{stage} did not reclaim every allocation"
  return (store, value, Json.mkObj [
    ("value", toJson (expected source)), ("store", toJson store),
    ("reclaimed", toJson reclaimed)])

private def observe2 (source : Source) (stage : String) (context : IxIR2.Validate.Context)
    (program : IxIR2.Program) (mode : IxIR2.Eval.Interpretation) :
    Except String (IxIR2.Eval.Result × IxIR2.Eval.Store × Json) := do
  let result ← (IxIR2.Eval.runMain (IxIR2.Eval.Context.ofProgram program context.schemas)
    mode program 10000 10000).mapError (fun error => s!"{stage}: {repr error}")
  agree source stage (observation1? source result.store.heap result.value)
  if result.store.live + result.store.counters.frees != result.store.counters.allocs then
    throw s!"{stage} terminal allocation balance disagrees"
  let (reclaimed, remaining) ← (IxIR2.Eval.releaseShared 10000 result.store result.value).mapError
    (fun error => s!"{stage} reclamation: {repr error}")
  if reclaimed.live != 0 || reclaimed.counters.allocs != reclaimed.counters.frees then
    throw s!"{stage} did not reclaim every allocation"
  return (result, reclaimed, Json.mkObj [
    ("value", toJson (expected source)), ("store", toJson result.store),
    ("control_remaining", toJson result.controlRemaining), ("heap_remaining", toJson result.heapRemaining),
    ("reclaimed", toJson reclaimed), ("reclamation_remaining", toJson remaining)])

private def heapCounters (store : IxIR1.Store) : Json :=
  Json.mkObj [("allocs", toJson store.allocs), ("frees", toJson store.frees),
    ("rcops", toJson store.rcops), ("reuses", toJson store.reuses), ("live", toJson store.live)]

private def costGate (source : Source) (baseline logical physical : IxIR2.Eval.Result)
    (baselineReleased physicalReleased : IxIR2.Eval.Store) : Except String Unit := do
  let b := baseline.store.counters
  let l := logical.store.counters
  let p := physical.store.counters
  if b.reuses != 0 || b.allocs != p.allocs + p.reuses || b.frees != p.frees + p.reuses then
    throw "physical baseline/selected terminal allocation laws disagree"
  if p.rcops > b.rcops || p.peakLiveNodes > b.peakLiveNodes then
    throw "physical baseline/selected terminal RC or peak-live bound disagrees"
  let br := baselineReleased.counters
  let pr := physicalReleased.counters
  if br.reuses != 0 || br.allocs != pr.allocs + pr.reuses || br.frees != pr.frees + pr.reuses then
    throw "physical baseline/selected reclaimed allocation laws disagree"
  if pr.rcops > br.rcops || pr.peakLiveNodes > br.peakLiveNodes then
    throw "physical baseline/selected reclaimed RC or peak-live bound disagrees"
  if l.allocs != p.allocs + p.reuses || l.frees != p.frees + p.reuses ||
      l.rcops != p.rcops || logical.store.live != physical.store.live ||
      l.resetAttempts != p.resetAttempts || l.hotResets != p.hotResets || l.coldResets != p.coldResets then
    throw "logical/physical terminal accounting disagreement"
  let n := source.values.length
  if p.resetAttempts != n || (if source.aliased then p.coldResets != n || p.hotResets != 0 || p.reuses != 0
      else p.hotResets != n || p.coldResets != 0 || p.reuses != n || p.reusedPayloadUnits != 2 * n) then
    throw "one reset per input cons was not observed"
  if n == 3 then
    if source.aliased then
      if b.allocs != 9 || b.frees != 0 || b.rcops != 8 || p.allocs != 9 || p.frees != 0 ||
          p.rcops != 8 || p.peakLiveNodes != 9 then throw "three-cons cold witness counters drifted"
    else
      if b.allocs != 8 || b.frees != 4 || b.rcops != 10 || p.allocs != 5 || p.frees != 1 ||
          p.rcops != 1 || p.peakLiveNodes != 5 then throw "three-cons hot witness counters drifted"

private def graphSnapshot (result : IxIR1.ReaddressAll.Result)
    (raw : List (Address × IxIR1.Decl)) (rawMain : IxIR1.Code) : Json :=
  Json.mkObj [
    ("root", toJson (IxIR1.Optimizer.graphRoot result.artifacts result.main)),
    ("raw_declarations", Coverage.ir1Entries raw), ("raw_main", Coverage.byteJson rawMain.bytes),
    ("artifacts", toJson (result.artifacts.map Coverage.ir1Artifact)),
    ("declarations", Coverage.ir1Entries (result.artifacts.flatMap IxIR1.ReaddressAll.Artifact.declarations)),
    ("main", Coverage.byteJson result.main.bytes), ("address_map", toJson result.addressMap),
    ("reserved", toJson result.reserved)]

structure CaseResult where
  name : String
  summary : Json
  snapshot : Json

def runCase (name : String) (values : List Nat) (aliased : Bool) : Except String CaseResult := do
  let source ← Examples.source values aliased
  let sourceValue ← (Ixon.Eval.eval (Pipeline.validatedEvalCtx source.constants source.config) 10000
    (Pipeline.validatedMainFrame source.root) [] Pipeline.validatedMainSource).mapError
      (fun error => s!"Ixon: {repr error}")
  agree source "Ixon" (sourceObservation? source sourceValue)
  let compilation ← (compileValidated source.constants source.root source.config).mapError
    (fun error => s!"validated source compilation: {repr error}")
  let .recovered recovery lowered := compilation.outcome
    | throw s!"{name}: recovery did not reach the checked backend"
  let .optimized optimized _ := lowered.reuse | throw "reuse was unexpectedly skipped"
  let plan := recovery.checked.plan
  let erasure := compilation.source.erasure.result
  let oldLowering := compilation.source.lowering
  let newLowering := lowered.lowering
  let baseline := lowered.attached.target
  observe0 source "literal raw IxIR0" erasure.raw (.ref source.root)
  observe0 source "literal addressed IxIR0" erasure.declarations erasure.main
  observe0 source "recovered IxIR0" (IxIR0.Recursion.targetDeclarations plan recovery.address)
    (plan.directMain recovery.address)
  let (oldRaw, _, oldRawJson) ← observe1 source "literal raw IxIR1"
    { decls := IxIR1.Env.ofList oldLowering.raw } oldLowering.mainCode
  let (oldFinal, _, oldFinalJson) ← observe1 source "literal addressed IxIR1"
    { decls := compilation.source.artifact.targetDeclEnv } oldLowering.result.main
  if toJson oldRaw != toJson oldFinal then throw "literal IxIR1 addressing changed the complete terminal store"
  let (raw, _, rawJson) ← observe1 source "recovered raw IxIR1"
    { decls := IxIR1.Env.ofList newLowering.raw } newLowering.mainCode
  let (final, _, finalJson) ← observe1 source "recovered addressed IxIR1"
    { decls := IxIR1.HPT.programDeclEnv newLowering.result.artifacts } newLowering.result.main
  let (baseLogical, _, baseLogicalJson) ← observe2 source "baseline logical IxIR2"
    baseline.artifact.validationContext baseline.artifact.program .logical
  let (basePhysical, baseReleased, basePhysicalJson) ← observe2 source "baseline physical IxIR2"
    baseline.artifact.validationContext baseline.artifact.program .physical
  if toJson raw != toJson final || toJson final != toJson baseLogical.store.heap ||
      toJson baseLogical.store != toJson basePhysical.store ||
      baseLogical.controlRemaining != basePhysical.controlRemaining ||
      baseLogical.heapRemaining != basePhysical.heapRemaining then
    throw "recovered addressing or baseline interpretation changed stores/counters/budgets"
  let (logical, _, logicalJson) ← observe2 source "reuse logical IxIR2"
    baseline.artifact.validationContext optimized.target .logical
  let (physical, physicalReleased, physicalJson) ← observe2 source "reuse physical IxIR2"
    baseline.artifact.validationContext optimized.target .physical
  costGate source basePhysical logical physical baseReleased physicalReleased
  let loop := loopAddress newLowering.result recovery.address
  let some (_, .fn function) := baseline.artifact.program.declarations.find? (fun entry => entry.1 == loop)
    | throw "derived recursor is missing from the addressed target"
  let tailSelf := function.blocks.countP fun block => match block.terminator with
    | .tailCallSelf _ => true | _ => false
  if tailSelf != 1 || optimized.report.rewritten != 1 || optimized.report.helperBlocks != 2 then
    throw "checked lowering did not produce one recursive tail and one reset diamond"
  let rerun := IxIR2.Reuse.rewriteProgram baseline.artifact.validationContext optimized.target
  if rerun.program != optimized.target || rerun.report.rewritten != 0 then
    throw "reuse is not idempotent on the selected target"
  let summary := Json.mkObj [
    ("name", toJson name), ("snapshot", toJson s!"{name}.json"),
    ("source_root", toJson source.root), ("source_constants", toJson source.constants.length),
    ("input", toJson values), ("aliased", toJson aliased), ("value", toJson (expected source)),
    ("literal_ixir1_root", toJson (IxIR1.Optimizer.graphRoot oldLowering.result.artifacts oldLowering.result.main)),
    ("recovered_recursion_root", toJson recovery.address),
    ("recovered_ixir1_root", toJson (IxIR1.Optimizer.graphRoot newLowering.result.artifacts newLowering.result.main)),
    ("hpt_roots", toJson (lowered.attached.hpt.result.artifacts.map (·.address))),
    ("loop", toJson loop), ("tail_self_calls", toJson tailSelf),
    ("literal_ixir1", heapCounters oldFinal), ("recovered_ixir1", heapCounters final),
    ("baseline", toJson baseLogical.store.counters), ("logical", toJson logical.store.counters),
    ("physical", toJson physical.store.counters), ("reuse", toJson optimized.report),
    ("all_heaps_reclaimed", toJson true)]
  let context := lowered.attached.loweringContext
  let attached := lowered.attached
  let common := attached.source
  let sidecars := attached.sidecars
  let constructors := (IxIR0.Recursion.targetDeclarations plan recovery.address).filterMap fun
    | (address, .ctor tag _) => some (IxIR1.Lower.ctorIdOf address tag)
    | _ => none
  let snapshot := Json.mkObj [
    ("format", toJson "compilatrix/source-recursion-case/2"), ("summary", summary),
    ("source", Json.mkObj [
      ("root", toJson source.root), ("limits", toJson source.config.limits),
      ("fuel", Json.mkObj [("usage", toJson (1000 : Nat)), ("erasure", toJson (1000 : Nat)),
        ("validation", toJson (1000 : Nat)), ("ownership_lowering", toJson (1000 : Nat)),
        ("evaluation", toJson (10000 : Nat)), ("control", toJson (10000 : Nat)),
        ("heap", toJson (10000 : Nat)), ("reclamation", toJson (10000 : Nat))]),
      ("constants", toJson (source.constants.map fun (address, constant) =>
        Json.mkObj [("key", toJson address), ("bytes", Coverage.byteJson (ser constant))])),
      ("literals", toJson (values.map fun n =>
        Json.mkObj [("key", toJson (X86.ValidatedScalar.literalAddress n)), ("nat", toJson n)]))]),
    ("literal_ixir0", Json.mkObj [
      ("raw", Coverage.ir0Entries erasure.raw), ("raw_main", Coverage.byteJson (IxIR0.Expr.ref source.root).bytes),
      ("groups", toJson (erasure.groups.map Coverage.ir0Group)),
      ("declarations", Coverage.ir0Entries erasure.declarations), ("main", Coverage.byteJson erasure.main.bytes),
      ("blocks", toJson (erasure.addressed.blocks.map Coverage.ir0Block)), ("address_map", toJson erasure.addressMap)]),
    ("literal_ixir1", graphSnapshot oldLowering.result oldLowering.raw oldLowering.mainCode),
    ("recovery", Json.mkObj [
      ("plan", toJson plan), ("derived_key", toJson recovery.address),
      ("declarations", Coverage.ir0Entries (IxIR0.Recursion.targetDeclarations plan recovery.address)),
      ("main", Coverage.byteJson (plan.directMain recovery.address).bytes)]),
    ("recovered_ixir1", graphSnapshot newLowering.result newLowering.raw newLowering.mainCode),
    ("ownership_lowering", Json.mkObj [
      ("declarations", Coverage.ir0Entries common.declarations),
      ("main", Coverage.byteJson common.main.bytes),
      ("source_rows_selected", toJson (Pipeline.sourceRowsSelected common.declarations)),
      ("source_externs_rejected", toJson (Pipeline.firstValidatedExtern? common.declarations).isNone),
      ("target_externs_rejected", toJson (Pipeline.firstValidatedTargetExtern? common.targetDecls).isNone)]),
    ("hpt", Json.mkObj [
      ("producer_limits", toJson IxIR1.HPT.defaultProducerLimits),
      ("producer_stats", toJson attached.hpt.stats),
      ("candidate", toJson (attached.hpt.certificate.artifacts.map Coverage.hptCandidate)),
      ("artifacts", toJson (attached.hpt.result.artifacts.map Coverage.hptArtifact))]),
    ("sidecars", Json.mkObj [
      ("input_declarations", Coverage.ir1Entries sidecars.input.declarations),
      ("input_main", Coverage.byteJson sidecars.input.main.bytes),
      ("main_world", toJson sidecars.input.mainResult),
      ("parameter_worlds", toJson sidecars.parameterEntries),
      ("constructors", toJson sidecars.constructors),
      ("recursor_origins", toJson sidecars.recursorOrigins),
      ("hpt_certificate", toJson (sidecars.hptCertificate.artifacts.map Coverage.hptCandidate))]),
    ("ixir2_diagnostic", Json.mkObj [
      ("baseline", toJson baseline.artifact.program), ("baseline_stats", toJson baseline.stats),
      ("selected", toJson optimized.target), ("selected_stats", toJson optimized.targetStats),
      ("parameters", toJson [(loop, context.parameterWorlds loop)]),
      ("schemas", toJson (constructors.map fun c => (c, context.schemas .shared c))),
      ("case_constructors", toJson [context.caseCtors { owner := .declaration loop } 0,
        context.caseCtors { owner := .declaration loop } 1]),
      ("max_depth", toJson lowered.maxDepth), ("reuse", toJson optimized.report)]),
    ("observations", Json.mkObj [
      ("literal_raw_ixir1", oldRawJson), ("literal_ixir1", oldFinalJson),
      ("recovered_raw_ixir1", rawJson), ("recovered_ixir1", finalJson),
      ("baseline_logical", baseLogicalJson), ("baseline_physical", basePhysicalJson),
      ("reuse_logical", logicalJson), ("reuse_physical", physicalJson)])]
  return { name, summary, snapshot }

def cases : List (String × List Nat × Bool) :=
  [("empty-hot", [], false), ("empty-cold", [], true),
    ("singleton-hot", [17], false), ("singleton-cold", [17], true),
    ("three-hot", [1, 2, 3], false), ("three-cold", [1, 2, 3], true),
    ("mixed-hot", [0, 3, 3, UInt64.size, 1, 42, 0], false),
    ("mixed-cold", [0, 3, 3, UInt64.size, 1, 42, 0], true)]

end Ix.Compiler.Recursion.Examples
