import Ix.Compiler.UniqueReuse.Sources
import Ix.Compiler.UniqueReuse.Provenance
import Ix.Compiler.Coverage.HeapSnapshot
import Ix.Compiler.IxIR2.ReservationOwnership

namespace Ix.Compiler.UniqueReuse.Examples

open Lean Ix.Compiler.Ixon

deriving instance ToJson for IxIR0.UniqueReverse.Schema
deriving instance ToJson for IxIR0.UniqueReverse.Plan
deriving instance ToJson for IxIR2.Validate.Limits

def need (condition : Bool) (message : String) : Except String Unit :=
  if condition then .ok () else .error message

def sourceList? (source : Source) : Nat → Ixon.Eval.Value → Option (List Nat)
  | 0, _ => none
  | fuel + 1, .ctorV block 1 tag fields =>
      if block != source.dataBlock then none else match tag, fields with
        | 0, [] => some []
        | 1, [.litV (.natL n), tail] => (n :: ·) <$> sourceList? source fuel tail
        | _, _ => none
  | _, _ => none

def list0? (source : Source) : Nat → IxIR0.Value → Option (List Nat)
  | 0, _ => none
  | fuel + 1, .ctor address tag fields =>
      if address == source.nil && tag == 0 && fields.isEmpty then some []
      else if address == source.cons && tag == 1 then match fields with
        | [.lit (.nat n), tail] => (n :: ·) <$> list0? source fuel tail
        | _ => none
      else none
  | _, _ => none

def list1? (source : Source) : Nat → IxIR1.Store → IxIR1.RVal → Option (List Nat)
  | 0, _, _ => none
  | fuel + 1, store, .loc location => do
      let box ← store.get? location
      if box.world != .unique || box.rc != 1 then none else
        let .ctorN identity fields := box.node | none
        if identity == IxIR1.Lower.ctorIdOf source.nil 0 && fields.isEmpty then some []
        else if identity == IxIR1.Lower.ctorIdOf source.cons 1 then match fields.toList with
          | [.lit (.nat n), tail] => (n :: ·) <$> list1? source fuel store tail
          | _ => none
        else none
  | _, _, _ => none

private def observe0 (source : Source) (entries : List (Address × IxIR0.Decl)) (main : IxIR0.Expr) :
    Except String Unit := do
  let value ← (IxIR0.eval { env := IxIR0.Env.ofList entries } 10000 [] main).mapError reprStr
  need (list0? source 1000 value == some source.values.reverse) "IxIR0 value disagreement"

def observe1 (source : Source) (plan : IxIR0.UniqueReverse.Plan) : Except String Json := do
  let context : IxIR1.Ctx := { decls := IxIR1.Env.ofList (declarations plan.schema) }
  let (store, value) ← (IxIR1.runOwnedMain context .unique (mainCode plan) 10000).mapError reprStr
  need (list1? source 1000 store value == some source.values.reverse) "IxIR1 unique value disagreement"
  let reclaimed ← (IxIR1.dropUVal context (3 * source.values.length + 2) store value).mapError reprStr
  need (store.allocs == 2 * source.values.length + 2 && store.frees == source.values.length + 1 &&
    store.reuses == 0 && store.rcops == 0 && store.live == source.values.length + 1) "IxIR1 counter disagreement"
  need (reclaimed.live == 0 && reclaimed.allocs == reclaimed.frees && reclaimed.rcops == 0 && reclaimed.reuses == 0)
    "IxIR1 reclamation disagreement"
  return Json.mkObj [("value", toJson source.values.reverse), ("result", toJson value),
    ("store", toJson store), ("reclaimed", toJson reclaimed)]

private def observe2 (source : Source) (plan : IxIR0.UniqueReverse.Plan) (reuse : Bool)
    (mode : IxIR2.Eval.Interpretation) : Except String (IxIR2.Eval.Result × Json) := do
  let program := IxIR2.UniqueLower.program plan reuse
  let context := IxIR2.Eval.Context.ofProgram program (IxIR2.UniqueLower.schemas plan.schema)
  let result ← (IxIR2.Eval.runMain context mode program 10000 0).mapError reprStr
  need (list1? source 1000 result.store.heap result.value == some source.values.reverse) "IxIR2 unique value disagreement"
  let (reclaimed, remaining) ← (IxIR2.Eval.dropUnique (2 * source.values.length + 1) result.store result.value).mapError reprStr
  let count := source.values.length
  let reused := if reuse && mode == .physical then count else 0
  let counters := result.store.counters
  need (counters.allocs + reused == 2 * count + 2 && counters.frees + reused == count + 1 &&
    counters.reuses == reused && counters.rcops == 0 && counters.resetAttempts == 0 && counters.hotResets == 0 &&
    counters.coldResets == 0 && counters.reusedPayloadUnits == 2 * reused &&
    counters.peakLiveNodes == count + 2 && result.store.live == count + 1) "IxIR2 FIP counter disagreement"
  need (result.controlRemaining + (if reuse then 5 else 6) * count + 7 == 10000 && result.heapRemaining == 0)
    "IxIR2 independent budget disagreement"
  need (remaining == 0 && reclaimed.live == 0 && reclaimed.heap.allocs == reclaimed.heap.frees &&
    reclaimed.heap.rcops == 0 && reclaimed.heap.reuses == reused &&
    reclaimed.peakLiveNodes == counters.peakLiveNodes && reclaimed.reusedPayloadUnits == 2 * reused)
    "IxIR2 reclamation disagreement"
  return (result, Json.mkObj [("value", toJson source.values.reverse), ("result", toJson result.value), ("store", toJson result.store),
    ("reclaimed", toJson reclaimed), ("control_remaining", toJson result.controlRemaining),
    ("heap_remaining", toJson result.heapRemaining), ("reclamation_remaining", toJson remaining)])

private def prefixes (plan : IxIR0.UniqueReverse.Plan) (reuse : Bool) (final : IxIR2.Eval.Result) :
    Except String (Array Json) := do
  let program := IxIR2.UniqueLower.program plan reuse
  let context := IxIR2.Eval.Context.ofProgram program (IxIR2.UniqueLower.schemas plan.schema)
  let mut machine := IxIR2.Eval.initialMachine program.main #[] 0
  let mut rows := #[]
  for index in [:10001] do
    let owners := machine.reservations
    let emptySlots := (List.range machine.store.heap.nodes.size).filter fun location =>
      match machine.store.heap.nodes[location]? with | some none => true | _ => false
    need (owners.eraseDups.length == owners.length && owners.all emptySlots.contains)
      "prefix reservation duplicated or aliases a live slot"
    need (machine.store.live + machine.store.heap.frees + owners.length == machine.store.heap.allocs)
      "prefix allocation accounting disagreement"
    need (machine.store.heap.rcops == 0 && machine.store.live ≤ machine.store.peakLiveNodes &&
      machine.store.peakLiveNodes ≤ plan.values.length + 2 && machine.heapFuel == 0) "prefix RC, peak, or budget disagreement"
    rows := rows.push (Json.mkObj [("step", toJson index), ("counters", toJson machine.store.counters),
      ("live", toJson machine.store.live), ("owners", toJson owners), ("empty_slots", toJson emptySlots)])
    match machine.control with
    | .halted value =>
        need (toJson machine.store == toJson final.store && value == final.value) "prefix endpoint differs from runMain"
        return rows
    | .running _ stack =>
        need stack.isEmpty "unique tail recursion unexpectedly suspended a caller"
        machine ← (IxIR2.Eval.step context .physical machine).mapError reprStr
  throw "unique prefix traversal exceeded its execution budget"

structure CaseResult where
  name : String
  summary : Json
  snapshot : Json

def runCase (name : String) (values : List Nat) (policy : IxIR2.UniqueLower.ReusePolicy := {}) :
    Except String CaseResult := do
  let source ← Examples.source values
  for (address, constant) in source.constants do
    need (Address.blake3 (ser constant) == address &&
      (de (ser constant) : Except String Constant).toOption == some constant) "source codec or content address disagreement"
  let sourceValue ← (Ixon.Eval.eval (Pipeline.validatedEvalCtx source.constants source.config)
    10000 source.mainFrame [] Source.main).mapError reprStr
  need (sourceList? source 1000 sourceValue == some values.reverse) "Ixon value disagreement"
  let compilation ← (compile source.constants source.entry source.config 1000 1000 1000
    IxIR2.Validate.defaultLimits policy).mapError reprStr
  let plan := compilation.plan
  let recovery := compilation.lowered.checked.recovery
  let .translated target := compilation.backend | throw "unique target unexpectedly unavailable"
  need (plan.values == values && target.selection.reused == (policy.enabled && policy.maxRewrites > 0))
    "source plan or selection disagreement"
  let erased := compilation.source.erasure.result
  observe0 source erased.raw compilation.source.rawMain
  observe0 source erased.declarations erased.main
  observe0 source (IxIR0.UniqueReverse.targetDeclarations plan recovery.address) (plan.directMain recovery.address)
  let owned ← observe1 source plan
  let (baselineLogical, baselineLogicalJson) ← observe2 source plan false .logical
  let (baseline, baselineJson) ← observe2 source plan false .physical
  let (logical, logicalJson) ← observe2 source plan target.selection.reused .logical
  let (physical, physicalJson) ← observe2 source plan target.selection.reused .physical
  need (baselineLogical.store.counters == baseline.store.counters && logical.store.counters == baseline.store.counters)
    "logical baseline/selected counters differ"
  let prefixes ← prefixes plan target.selection.reused physical
  let provenance := compilation.provenance
  let summary := Json.mkObj [("name", toJson name), ("input", toJson values), ("value", toJson values.reverse),
    ("source_root", toJson source.root), ("source_identity", toJson provenance.source),
    ("ixir1_root", toJson provenance.graph), ("source_instance", toJson provenance.recursorInstance),
    ("specialized_instance", toJson provenance.specializedInstance), ("provenance", toJson provenance.identity),
    ("optimized", toJson target.selection.reused), ("baseline", toJson baseline.store.counters),
    ("logical", toJson logical.store.counters), ("physical", toJson physical.store.counters),
    ("prefixes", toJson prefixes.size), ("snapshot", toJson s!"{name}.json")]
  let instanceJson := fun (inst : IxIR0.RecursorInstance) => Json.mkObj [
    ("identity", toJson inst.address), ("bytes", Coverage.byteJson inst.bytes),
    ("declaration", Coverage.byteJson inst.declaration.preimage), ("arguments", toJson inst.arguments),
    ("fields", toJson inst.fields), ("result", toJson inst.result), ("well_shaped", toJson inst.wellShaped)]
  let snapshot := Json.mkObj [("format", toJson "compilatrix/source-unique-reuse-case/1"), ("summary", summary),
    ("source", Json.mkObj [("root", toJson source.root), ("identity", toJson provenance.source),
      ("input_bytes", Coverage.byteJson (sourceBytes source.constants source.entry)), ("limits", toJson source.config.limits),
      ("constants", toJson (source.constants.map fun (address, constant) => Json.mkObj [
        ("key", toJson address), ("bytes", Coverage.byteJson (ser constant))])),
      ("literals", toJson (values.eraseDups.map fun value => (X86.ValidatedScalar.literalAddress value, value))),
      ("entry", Coverage.byteJson (ser source.entry.source)), ("entry_refs", toJson source.entry.refs),
      ("entry_univs", toJson (source.entry.univs.toList.map fun univ => Coverage.byteJson (ser univ)))]),
    ("ixir0", Json.mkObj [("raw", Coverage.ir0Entries erased.raw), ("raw_main", Coverage.byteJson compilation.source.rawMain.bytes),
      ("declarations", Coverage.ir0Entries erased.declarations), ("main", Coverage.byteJson erased.main.bytes),
      ("groups", toJson (erased.groups.map Coverage.ir0Group)), ("blocks", toJson (erased.addressed.blocks.map Coverage.ir0Block)),
      ("address_map", toJson erased.addressMap)]),
    ("specialization", Json.mkObj [("plan", toJson plan), ("policy", toJson IxIR0.UniqueReverse.policyTag),
      ("source_instance", instanceJson IxIR0.UniqueReverse.sourceInstance),
      ("direct_instance", instanceJson (IxIR0.UniqueReverse.directInstance plan.schema)),
      ("declarations", Coverage.ir0Entries (IxIR0.UniqueReverse.targetDeclarations plan recovery.address)),
      ("main", Coverage.byteJson (plan.directMain recovery.address).bytes)]),
    ("ixir1", Json.mkObj [("root", toJson provenance.graph), ("main", Coverage.byteJson (mainCode plan).bytes),
      ("declarations", Coverage.ir1Entries (declarations plan.schema)),
      ("artifacts", toJson ((artifacts plan.schema).map Coverage.ir1Artifact))]),
    ("provenance", Json.mkObj [("kind", toJson "ixir1-plus-policy"), ("identity", toJson provenance.identity),
      ("bytes", Coverage.byteJson provenance.bytes), ("usage", toJson Ixon.RecursorUsage.policyTag),
      ("lowering", toJson IxIR2.UniqueLower.policyTag), ("reuse", toJson IxIR2.UniqueLower.reusePolicyTag),
      ("execution", toJson IxIR2.CreditPolicy.callLocalV0.tag), ("outcome", toJson provenance.outcome),
      ("check_fuel", toJson provenance.checkFuel), ("erase_fuel", toJson provenance.eraseFuel)]),
    ("ixir2_diagnostic", Json.mkObj [("baseline", toJson (IxIR2.UniqueLower.program plan false)),
      ("selected", toJson target.selection.program), ("baseline_stats", toJson target.translation.checked.stats),
      ("selected_stats", toJson target.selection.checked.stats), ("limits", toJson IxIR2.Validate.defaultLimits),
      ("schemas", toJson ([nilId plan.schema, consId plan.schema].map fun cid =>
        (cid, IxIR2.UniqueLower.schemas plan.schema .unique cid)))]),
    ("observations", Json.mkObj [("ixir1", owned), ("baseline_logical", baselineLogicalJson),
      ("baseline_physical", baselineJson), ("selected_logical", logicalJson), ("selected_physical", physicalJson)]),
    ("prefixes", toJson prefixes)]
  return { name, summary, snapshot }

def cases : List (String × List Nat × IxIR2.UniqueLower.ReusePolicy) :=
  [("empty", [], {}), ("singleton", [17], {}), ("three", [1, 2, 3], {}),
    ("mixed-values", [0, UInt64.size, 3, 3, 0, UInt64.size + 7, 42], {}),
    ("sixty-four", List.range 64, {}), ("disabled", [1, 2, 3], { enabled := false }),
    ("rewrite-budget", [1, 2, 3], { maxRewrites := 0 })]

end Ix.Compiler.UniqueReuse.Examples
