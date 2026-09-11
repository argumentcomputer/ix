import Ix.Compiler.CallReuse.Sources
import Ix.Compiler.CallReuse.Provenance
import Ix.Compiler.Coverage.HeapSnapshot
import Ix.Compiler.IxIR2.ReservationOwnership

/-! Source-driven map execution, full heap release, and actual prefix
observations. Every constructor observation checks its complete identity. -/

namespace Ix.Compiler.CallReuse.Examples

open Lean Ix.Compiler.Ixon

deriving instance ToJson for IxIR2.CallReuse.Report
deriving instance ToJson for IxIR0.MapRecovery.Schema
deriving instance ToJson for IxIR0.MapRecovery.Plan

inductive Observation where
  | list (values : List Nat)
  | pair (mapped retained : List Nat)
  deriving BEq, Repr, ToJson

private def need (condition : Bool) (message : String) : Except String Unit :=
  if condition then .ok () else .error message

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
    | .ctorV block 2 0 [left, right] => do
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
  let mapped := source.values.map (fun _ => source.replacement)
  if source.aliased then .pair mapped (source.values.drop source.uniquePrefix) else .list mapped

private def agree (source : Source) (stage : String) (actual : Option Observation) : Except String Unit :=
  need (actual == some (expected source)) s!"{stage}: expected {repr (expected source)}, got {repr actual}"

private def observe0 (source : Source) (stage : String) (declarations : List (Address × IxIR0.Decl))
    (main : IxIR0.Expr) : Except String Unit := do
  let value ← (IxIR0.eval { env := IxIR0.Env.ofList declarations } 10000 [] main).mapError
    (fun error => s!"{stage}: {repr error}")
  agree source stage (observation0? source value)

private def observe1 (source : Source) (stage : String) (context : IxIR1.Ctx)
    (main : IxIR1.Code) : Except String (IxIR1.Store × Json) := do
  let (store, value) ← (IxIR1.runOwnedMain context .shared main 10000).mapError
    (fun error => s!"{stage}: {repr error}")
  agree source stage (observation1? source store value)
  need (store.live + store.frees == store.allocs) s!"{stage}: terminal allocation balance"
  let reclaimed ← (IxIR1.dropVal context 10000 store value).mapError (fun error => s!"{stage}: {repr error}")
  need (reclaimed.live == 0 && reclaimed.allocs == reclaimed.frees) s!"{stage}: incomplete reclamation"
  return (store, Json.mkObj [("value", toJson (expected source)), ("store", toJson store),
    ("reclaimed", toJson reclaimed)])

private def observe2 (source : Source) (stage : String) (context : IxIR2.Validate.Context)
    (program : IxIR2.Program) (policy : IxIR2.CreditPolicy) (mode : IxIR2.Eval.Interpretation) :
    Except String (IxIR2.Eval.Result × IxIR2.Eval.Store × Json) := do
  let result ← (IxIR2.Eval.Policy.runMain policy (IxIR2.Eval.Context.ofProgram program context.schemas)
    mode program 10000 10000).mapError (fun error => s!"{stage}: {repr error}")
  agree source stage (observation1? source result.store.heap result.value)
  need (result.store.live + result.store.heap.frees == result.store.heap.allocs) s!"{stage}: terminal allocation balance"
  let (reclaimed, remaining) ← (IxIR2.Eval.releaseShared 10000 result.store result.value).mapError
    (fun error => s!"{stage} reclamation: {repr error}")
  need (reclaimed.live == 0 && reclaimed.heap.allocs == reclaimed.heap.frees) s!"{stage}: incomplete reclamation"
  return (result, reclaimed, Json.mkObj [
    ("value", toJson (expected source)), ("store", toJson result.store),
    ("control_remaining", toJson result.controlRemaining), ("heap_remaining", toJson result.heapRemaining),
    ("reclaimed", toJson reclaimed), ("reclamation_remaining", toJson remaining)])

/-- Inspect every actual physical prefix, including the states between reset,
call entry, nested return, and credit consumption. -/
def prefixObservations (context : IxIR2.Validate.Context) (program : IxIR2.Program)
    (policy : IxIR2.CreditPolicy) (baseline final : IxIR2.Eval.Result) :
    Except String (Array Json × Nat × Nat) := do
  let context := IxIR2.Eval.Context.ofProgram program context.schemas
  let mut machine := IxIR2.Eval.initialMachine program.main #[] 10000
  let mut rows := #[]
  let mut maximum := 0
  let mut suspendedCalls := 0
  for index in [:10001] do
    let (active, saved, creditCounts) : List Nat × List (List Nat) × List Nat := match machine.control with
      | .halted _ => ([], [], [])
      | .running frame stack => (frame.reservations, stack.map IxIR2.Eval.Continuation.reservations,
          frame.liveCredits.length :: stack.map (fun (continuation : IxIR2.Eval.Continuation) => match continuation with
            | .resume frame | .applyMore _ frame => frame.liveCredits.length))
    let reservations := active ++ saved.flatten
    let emptySlots := (List.range machine.store.heap.nodes.size).filter fun location =>
      match machine.store.heap.nodes[location]? with | some none => true | _ => false
    need (reservations.eraseDups.length == reservations.length && reservations.all emptySlots.contains)
      "prefix reservation duplicated or aliases a live heap slot"
    need (machine.store.live + machine.store.heap.frees + reservations.length == machine.store.heap.allocs)
      "prefix physical allocation balance"
    need (machine.store.heap.rcops ≤ baseline.store.heap.rcops &&
      machine.store.peakLiveNodes ≤ baseline.store.peakLiveNodes &&
      machine.store.live ≤ machine.store.peakLiveNodes) "prefix RC or peak-live bound"
    maximum := max maximum creditCounts.sum
    rows := rows.push (Json.mkObj [("step", toJson index), ("counters", toJson machine.store.counters),
      ("live", toJson machine.store.live), ("owners", toJson (active :: saved)),
      ("empty_slots", toJson emptySlots), ("credit_counts", toJson creditCounts)])
    match machine.control with
    | .halted value =>
        need (toJson machine.store == toJson final.store && value == final.value &&
          machine.heapFuel == final.heapRemaining) "prefix traversal disagrees with runMain"
        return (rows, maximum, suspendedCalls)
    | .running frame _ =>
        let next ← (IxIR2.Eval.Policy.step policy context .physical machine).mapError reprStr
        if (IxIR2.Eval.Policy.directCall? frame).isSome then
          let .running callee (.resume caller :: _) := next.control
            | throw "direct call did not suspend exactly one caller"
          need (callee.credits.isEmpty && caller.credits == frame.credits &&
            toJson machine.store == toJson next.store) "direct-call credit ownership changed"
          if !frame.liveCredits.isEmpty then suspendedCalls := suspendedCalls + 1
        machine := next
  throw "prefix traversal exceeded execution budget"

private def costGate (source : Source) (baseline logical physical : IxIR2.Eval.Result)
    (baselineReleased physicalReleased : IxIR2.Eval.Store) : Except String Unit := do
  for (label, base, selected) in [("terminal", baseline.store, physical.store),
      ("reclaimed", baselineReleased, physicalReleased)] do
    let b := base.counters
    let p := selected.counters
    need (b.reuses == 0 && b.allocs == p.allocs + p.reuses && b.frees == p.frees + p.reuses)
      s!"{label}: baseline/selected allocation or free law"
    need (p.rcops ≤ b.rcops && p.peakLiveNodes ≤ b.peakLiveNodes) s!"{label}: RC or peak-live bound"
  let l := logical.store.counters
  let p := physical.store.counters
  need (l.allocs == p.allocs + p.reuses && l.frees == p.frees + p.reuses && l.rcops == p.rcops &&
    logical.store.live == physical.store.live && l.resetAttempts == p.resetAttempts &&
    l.hotResets == p.hotResets && l.coldResets == p.coldResets) "logical/physical allocation accounting"
  let hot := if source.aliased then source.uniquePrefix else source.values.length
  need (p.resetAttempts == source.values.length && p.hotResets == hot &&
    p.coldResets == source.values.length - hot && p.reuses == hot && p.reusedPayloadUnits == 2 * hot)
    "reset/reuse count differs from source alias structure"

structure CaseResult where
  name : String
  summary : Json
  snapshot : Json

def runCase (name : String) (values : List Nat) (replacement : Nat) (aliased : Bool)
    (uniquePrefix : Nat := 0) : Except String CaseResult := do
  let source ← Examples.source values replacement aliased uniquePrefix
  let sourceValue ← (Ixon.Eval.eval (Pipeline.validatedEvalCtx source.constants source.config) 10000
    (Pipeline.validatedMainFrame source.root) [] Pipeline.validatedMainSource).mapError
      (fun error => s!"Ixon: {repr error}")
  agree source "Ixon" (sourceObservation? source sourceValue)
  let compilation ← source.compile.mapError (fun error => s!"validated compilation: {repr error}")
  let .recovered recovery lowered := compilation.outcome
    | throw s!"map specialization did not reach the checked backend"
  let attached := lowered.attached
  let baseline := attached.target
  let context := baseline.artifact.validationContext
  let selected := lowered.reuse
  let .optimized output _ := selected | throw "ordinary source unexpectedly used baseline fallback"
  let report := IxIR2.CallReuse.report IxIR2.Validate.defaultLimits context baseline.artifact.program
  need (report.rewritten == 1 && report.suspendedCallSites == 2) "compiler did not expose both map calls"
  need (match IxIR2.Validate.validate context selected.target with | .error _ => true | .ok _ => false)
    "v0 accepted live credits across map calls"
  let erasure := compilation.source.erasure.result
  let lowering := lowered.lowering
  observe0 source "raw IxIR0" erasure.raw (.ref source.root)
  observe0 source "addressed IxIR0" erasure.declarations erasure.main
  observe0 source "specialized IxIR0"
    (IxIR0.MapRecovery.targetDeclarations recovery.checked.plan recovery.address)
    (recovery.checked.plan.directMain recovery.address)
  let (_, literalRawJson) ← observe1 source "literal raw IxIR1"
    { decls := IxIR1.Env.ofList compilation.source.lowering.raw } compilation.source.lowering.mainCode
  let (_, literalJson) ← observe1 source "literal IxIR1"
    { decls := compilation.source.artifact.targetDeclEnv } compilation.source.artifact.main
  let (rawStore, rawJson) ← observe1 source "raw IxIR1" { decls := IxIR1.Env.ofList lowering.raw } lowering.mainCode
  let (store, ir1Json) ← observe1 source "addressed IxIR1"
    { decls := IxIR1.HPT.programDeclEnv lowering.result.artifacts } lowering.result.main
  let (baseLogical, _, baseLogicalJson) ← observe2 source "baseline logical" context baseline.artifact.program .callLocalV0 .logical
  let (base, baseReleased, baseJson) ← observe2 source "baseline physical" context baseline.artifact.program .callLocalV0 .physical
  need (toJson rawStore == toJson store && toJson store == toJson base.store.heap &&
    toJson baseLogical.store == toJson base.store) "ordinary lowering or baseline interpretation drifted"
  let (logical, _, logicalJson) ← observe2 source "selected logical" context selected.target selected.policy .logical
  let (physical, released, physicalJson) ← observe2 source "selected physical" context selected.target selected.policy .physical
  costGate source base logical physical baseReleased released
  let (prefixes, maximumCredits, suspendedCalls) ← prefixObservations context selected.target selected.policy base physical
  need (suspendedCalls == 2 * values.length && maximumCredits == values.length)
    "nested calls did not suspend the expected independent caller credits"
  need (IxIR2.CallReuse.rewriteProgram IxIR2.Validate.defaultLimits context selected.target == selected.target)
    "call reuse is not idempotent"
  let provenance := lowered.provenance source.root
  need (({ provenance with execution := .callLocalV0 }).bytes != provenance.bytes &&
    ({ provenance with execution := .callLocalV0 }).identity != provenance.identity)
    "execution policy did not change provenance"
  let summary := Json.mkObj [
    ("name", toJson name), ("snapshot", toJson s!"{name}.json"),
    ("source_root", toJson source.root), ("source_constants", toJson source.constants.length),
    ("input", toJson values), ("replacement", toJson replacement),
    ("aliased", toJson aliased), ("unique_prefix", toJson uniquePrefix), ("value", toJson (expected source)),
    ("ixir1_root", toJson provenance.ir1Root), ("provenance", toJson provenance.identity),
    ("map_specialization", toJson recovery.address),
    ("literal_ixir1_root", toJson (IxIR1.Optimizer.graphRoot
      compilation.source.lowering.result.artifacts compilation.source.lowering.result.main)),
    ("policy", toJson selected.policy.tag), ("pass", toJson IxIR2.CallReuse.policyTag),
    ("hpt_roots", toJson provenance.hptRoots), ("reuse", toJson report),
    ("baseline", toJson base.store.counters), ("logical", toJson logical.store.counters),
    ("physical", toJson physical.store.counters), ("maximum_credits", toJson maximumCredits),
    ("suspended_calls", toJson suspendedCalls), ("prefixes", toJson prefixes.size),
    ("all_heaps_reclaimed", toJson true)]
  let sidecars := attached.sidecars
  let common := attached.source
  let snapshot := Json.mkObj [
    ("format", toJson "compilatrix/source-call-reuse-case/1"), ("summary", summary),
    ("source", Json.mkObj [("root", toJson source.root), ("limits", toJson source.config.limits),
      ("fuel", Json.mkObj [("usage", toJson (1000 : Nat)), ("erasure", toJson (1000 : Nat)),
        ("validation", toJson (1000 : Nat)), ("ownership_lowering", toJson (1000 : Nat)),
        ("evaluation", toJson (10000 : Nat)), ("control", toJson (10000 : Nat)),
        ("heap", toJson (10000 : Nat)), ("reclamation", toJson (10000 : Nat))]),
      ("constants", toJson (source.constants.map fun (address, constant) =>
        Json.mkObj [("key", toJson address), ("bytes", Coverage.byteJson (ser constant))])),
      ("literals", toJson ((replacement :: values).eraseDups.map fun n =>
        Json.mkObj [("key", toJson (X86.ValidatedScalar.literalAddress n)), ("nat", toJson n)]))]),
    ("ixir0", Json.mkObj [("raw", Coverage.ir0Entries erasure.raw),
      ("raw_main", Coverage.byteJson (IxIR0.Expr.ref source.root).bytes),
      ("groups", toJson (erasure.groups.map Coverage.ir0Group)),
      ("declarations", Coverage.ir0Entries erasure.declarations), ("main", Coverage.byteJson erasure.main.bytes),
      ("blocks", toJson (erasure.addressed.blocks.map Coverage.ir0Block)), ("address_map", toJson erasure.addressMap)]),
    ("ixir1", Json.mkObj [("root", toJson provenance.ir1Root),
      ("raw_declarations", Coverage.ir1Entries lowering.raw), ("raw_main", Coverage.byteJson lowering.mainCode.bytes),
      ("artifacts", toJson (lowering.result.artifacts.map Coverage.ir1Artifact)),
      ("declarations", Coverage.ir1Entries common.targetDecls),
      ("main", Coverage.byteJson lowering.result.main.bytes), ("address_map", toJson lowering.result.addressMap),
      ("reserved", toJson lowering.result.reserved)]),
    ("literal_ixir1", Json.mkObj [
      ("root", toJson (IxIR1.Optimizer.graphRoot compilation.source.lowering.result.artifacts
        compilation.source.lowering.result.main)),
      ("raw_declarations", Coverage.ir1Entries compilation.source.lowering.raw),
      ("raw_main", Coverage.byteJson compilation.source.lowering.mainCode.bytes),
      ("artifacts", toJson (compilation.source.lowering.result.artifacts.map Coverage.ir1Artifact)),
      ("declarations", Coverage.ir1Entries compilation.source.artifact.targetDecls),
      ("main", Coverage.byteJson compilation.source.artifact.main.bytes),
      ("address_map", toJson compilation.source.lowering.result.addressMap),
      ("reserved", toJson compilation.source.lowering.result.reserved)]),
    ("map_specialization", Json.mkObj [("policy", toJson IxIR0.MapRecovery.policyTag),
      ("plan", toJson recovery.checked.plan), ("derived_key", toJson recovery.address),
      ("declarations", Coverage.ir0Entries (IxIR0.MapRecovery.targetDeclarations recovery.checked.plan recovery.address)),
      ("main", Coverage.byteJson (recovery.checked.plan.directMain recovery.address).bytes)]),
    ("ownership_lowering", Json.mkObj [("declarations", Coverage.ir0Entries common.declarations),
      ("main", Coverage.byteJson common.main.bytes),
      ("source_rows_selected", toJson (Pipeline.sourceRowsSelected common.declarations)),
      ("source_externs_rejected", toJson (Pipeline.firstValidatedExtern? common.declarations).isNone),
      ("target_externs_rejected", toJson (Pipeline.firstValidatedTargetExtern? common.targetDecls).isNone)]),
    ("hpt", Json.mkObj [("producer_limits", toJson IxIR1.HPT.defaultProducerLimits),
      ("producer_stats", toJson attached.hpt.stats),
      ("candidate", toJson (attached.hpt.certificate.artifacts.map Coverage.hptCandidate)),
      ("artifacts", toJson (attached.hpt.result.artifacts.map Coverage.hptArtifact))]),
    ("sidecars", Json.mkObj [("input_declarations", Coverage.ir1Entries sidecars.input.declarations),
      ("input_main", Coverage.byteJson sidecars.input.main.bytes), ("main_world", toJson sidecars.input.mainResult),
      ("parameter_worlds", toJson sidecars.parameterEntries), ("constructors", toJson sidecars.constructors),
      ("recursor_origins", toJson sidecars.recursorOrigins),
      ("hpt_certificate", toJson (sidecars.hptCertificate.artifacts.map Coverage.hptCandidate))]),
    ("provenance", Json.mkObj [("kind", toJson "ixir1-plus-policy"), ("identity", toJson provenance.identity),
      ("bytes", Coverage.byteJson provenance.bytes), ("lowering_version", toJson provenance.loweringVersion),
      ("pass", toJson provenance.pass), ("execution_policy", toJson provenance.execution.tag),
      ("specialization", toJson provenance.specialization),
      ("optimized", toJson provenance.optimized)]),
    ("ixir2_diagnostic", Json.mkObj [("baseline", toJson baseline.artifact.program),
      ("baseline_stats", toJson baseline.stats), ("selected", toJson output.target),
      ("selected_stats", toJson output.targetChecked.stats), ("reuse", toJson report),
      ("max_depth", toJson attached.maxDepth),
      ("schemas", toJson (sidecars.constructors.map fun c =>
        (c.identity, attached.loweringContext.schemas .shared c.identity)))]),
    ("observations", Json.mkObj [("literal_raw_ixir1", literalRawJson), ("literal_ixir1", literalJson),
      ("raw_ixir1", rawJson), ("ixir1", ir1Json),
      ("baseline_logical", baseLogicalJson), ("baseline_physical", baseJson),
      ("selected_logical", logicalJson), ("selected_physical", physicalJson)]),
    ("prefixes", toJson prefixes)]
  return { name, summary, snapshot }

def cases : List (String × List Nat × Nat × Bool × Nat) :=
  [("empty-hot", [], 42, false, 0), ("empty-cold", [], 42, true, 0),
    ("singleton-hot", [17], 42, false, 0), ("singleton-cold", [17], 42, true, 0),
    ("three-hot", [1, 2, 3], 42, false, 0), ("three-cold", [1, 2, 3], 42, true, 0),
    ("mixed-values-hot", [0, 3, 3, UInt64.size, 1, 42, 0], UInt64.size + 7, false, 0),
    ("mixed-values-cold", [0, 3, 3, UInt64.size, 1, 42, 0], UInt64.size + 7, true, 0),
    ("mixed-ownership", [5, 4, 3, 2, 1], 0, true, 2)]

end Ix.Compiler.CallReuse.Examples
