import Ix.Compiler.UniqueReuse.RuntimeNativeSim
import Ix.Compiler.UniqueReuse.NativeObservations
import Ix.Compiler.X86.RuntimeReject

/-! Compile and emit once, then apply the resulting source function and target
functions to independent runtime arguments. Caller-side input construction is
kept outside the exported native code and the artifact identity. -/

namespace Ix.Compiler.UniqueReuse.Runtime.Native.Examples

open Lean Ix.Compiler.Ixon Ix.Compiler.X86 Ix.Compiler.X86.UniqueABI
open Ix.Compiler.UniqueReuse.Examples (need sourceList? list0? list1?)
open Ix.Compiler.UniqueReuse.Native.Examples (headerValues heapSnapshot nativeList boundary prefixSnapshot)

private def argument (source : Runtime.Source) : List Nat → Ixon.Eval.Value
  | [] => .ctorV source.dataBlock 1 0 []
  | head :: tail => .ctorV source.dataBlock 1 1 [.litV (.natL head), argument source tail]

private def rejectionInputs (layout : Layout) (length : Nat) (initial : Core) : List (String × Core) :=
  let changed := fun name slot value => (name, { initial with memory := initial.memory.write64 (layout.address slot) value })
  [("length-sixty-five", initial.setReg .rsi 65), ("length-word-max", initial.setReg .rsi 0xffffffffffffffff),
   ("null-descriptor", initial.setReg .rdi 0), ("misaligned-descriptor", initial.setReg .rdi (layout.base + 1)),
   changed "wrong-cursor" 0 1,
   changed "insufficient-capacity" 1 (UInt64.ofNat (32 * (length + 1))), changed "zero-capacity" 1 0,
   changed "excess-capacity" 1 2144, changed "misaligned-capacity" 1 (UInt64.ofNat (32 * (length + 2) + 1))] ++
  ([("allocs", 2), ("frees", 3), ("reuses", 4), ("live", 5), ("peak", 6),
    ("rcops", 7), ("payload", 8), ("reservations", 9)].map fun (name, slot) =>
    changed s!"wrong-{name}" slot (initial.memory.read64 (layout.address slot) + 1)) ++
  ([("nil-tag", 0), ("nil-head", 1), ("nil-tail", 2), ("nil-padding", 3)].map fun (name, field) =>
    changed name (cellSlot 0 field) 1) ++
  (if length == 0 then [] else
    [changed "cons-tag" (cellSlot length 0) 0,
     changed "cons-self-tail" (cellSlot length 2) (layout.cell length),
     changed "cons-null-tail" (cellSlot length 2) 0,
     changed "cons-outside-tail" (cellSlot length 2) 0xffffffffffffffff,
     changed "cons-padding" (cellSlot length 3) 1])

private def observeNative (values : List Word) (bound : values.length ≤ maxLength)
    (foldCounters : Bool) : Except String Json := do
  let layout := RuntimeExecution.canonicalLayout values bound
  let initial : Core :=
    { registers := ((Registers.zero.set .rsp 0x8008).set .rdi layout.base).set .rsi (UInt64.ofNat values.length)
      memory := RuntimeExecution.inputMemory layout values Memory.unmapped }
  need ((← nativeList layout initial.memory values.length (layout.cell values.length)) == values.map UInt64.toNat)
    "caller input graph disagreement"
  let input ← heapSnapshot layout initial.memory
  let checked := RuntimeTarget.checked foldCounters
  let cost := RuntimeTarget.controlCost values.length foldCounters
  let mut machine := Machine.initial checked initial
  let mut prefixes := #[]
  for count in [:cost + 1] do
    need (machine.core.readReg .rsp == 0x8008 && machine.core.readReg .rdi == layout.base &&
      machine.core.calleeSavedSnapshot == initial.calleeSavedSnapshot) "runtime ABI register disagreement"
    match machine.status with
    | .trapped fault => throw s!"runtime byte evaluator trapped: {repr fault}"
    | _ => pure ()
    -- The folded reserve/reuse pair is one operation boundary. Its cancelled
    -- counter updates do not expose the old intermediate reservation state.
    if boundary machine && !(foldCounters && machine.pc.block == 5 && machine.pc.offset == 10) then
      prefixes := prefixes.push (← prefixSnapshot layout machine count)
    if count < cost then
      need (machine.status == .running) "runtime entry halted before its control cost"
      machine := step X86.Runtime.rejecting checked machine
  need (machine.status == .halted (layout.cell 1)) "runtime entry did not return its owned root"
  let observed ← nativeList layout machine.core.memory values.length (machine.core.readReg .rax)
  need (observed == (values.map UInt64.toNat).reverse) "runtime reversal disagreement"
  let returned ← heapSnapshot layout machine.core.memory
  let dropped := runFrom X86.Runtime.rejecting RuntimeTarget.releaseChecked (UniqueTarget.releaseCost values.length) machine.core
  need (dropped.status == .halted 0 && dropped.core.readReg .rsp == initial.readReg .rsp &&
    dropped.core.calleeSavedSnapshot == initial.calleeSavedSnapshot) "runtime release status or ABI disagreement"
  let reclaimed ← heapSnapshot layout dropped.core.memory
  let after := headerValues layout dropped.core.memory
  need (after[2]! == after[3]! && after[5]! == 0 && after[7]! == 0 && after[9]! == 0) "runtime release leaked"
  let mut failures := #[]
  for (label, before) in rejectionInputs layout values.length initial do
    let failed := runFrom X86.Runtime.rejecting checked cost before
    need (failed.status == .halted 0 && failed.core.readReg .rsp == before.readReg .rsp &&
      failed.core.calleeSavedSnapshot == before.calleeSavedSnapshot) s!"runtime guard did not reject {label}"
    for byte in [:8 * layout.slots] do
      let address := layout.base + UInt64.ofNat byte
      need (failed.core.memory.bytes address == before.memory.bytes address)
        s!"runtime rejection modified arena memory: {label}"
    failures := failures.push (toJson label)
  return Json.mkObj [("value", toJson observed), ("root", toJson (1 : Nat)), ("input", input),
    ("returned", returned), ("reclaimed", reclaimed), ("prefixes", Json.arr prefixes), ("rejections", Json.arr failures)]

private def observe2 (view : UniqueReuse.Examples.Source) (schema : IxIR0.UniqueReverse.Schema)
    (reuse : Bool) (mode : IxIR2.Eval.Interpretation) : Except String Json := do
  let (input, argument) := Target.makeInput schema view.values
  let cost := Target.controlCost reuse view.values.length
  let result ← (IxIR2.Eval.runFunction (Target.context schema reuse) mode (targetEntry schema) #[argument] cost 0 input).mapError reprStr
  need (list1? view 1000 result.store.heap result.value == some view.values.reverse) "runtime IxIR2 value disagreement"
  let (reclaimed, remaining) ← (IxIR2.Eval.dropUnique (2 * view.values.length + 1) result.store result.value).mapError reprStr
  let count := view.values.length
  let reused := if reuse && mode == .physical then count else 0
  let counters := result.store.counters
  need (counters.allocs + reused == 2 * count + 2 && counters.frees + reused == count + 1 &&
    counters.reuses == reused && counters.rcops == 0 && counters.resetAttempts == 0 && counters.hotResets == 0 &&
    counters.coldResets == 0 && counters.reusedPayloadUnits == 2 * reused &&
    counters.peakLiveNodes == count + 2 && result.store.live == count + 1) "runtime IxIR2 counter disagreement"
  need (result.controlRemaining == 0 && result.heapRemaining == 0 && remaining == 0 &&
    reclaimed.live == 0 && reclaimed.heap.allocs == reclaimed.heap.frees && reclaimed.heap.rcops == 0)
    "runtime IxIR2 budget or reclamation disagreement"
  return Json.mkObj [("value", toJson view.values.reverse), ("input", toJson input), ("argument", toJson argument),
    ("result", toJson result.value), ("store", toJson result.store), ("reclaimed", toJson reclaimed),
    ("control_cost", toJson cost), ("control_remaining", toJson result.controlRemaining),
    ("heap_remaining", toJson result.heapRemaining), ("reclamation_remaining", toJson remaining)]

private def objectJson (object : Object) : Json :=
  Json.mkObj [("file", toJson s!"{object.role.name}.o"), ("role", toJson object.role.name),
    ("symbol", toJson object.role.symbol), ("identity", toJson (Address.blake3 object.bytes)),
    ("size", toJson object.bytes.size), ("policy_identity", toJson object.policyIdentity),
    ("policy_bytes", Coverage.byteJson object.policyBytes), ("provenance", Coverage.byteJson object.provenance.bytes),
    ("lowering_version", toJson loweringVersion.toNat), ("role_version", toJson (object.role.policyVersion object.foldCounters).toNat),
    ("text", Coverage.byteJson object.encoded.text), ("blocks", toJson object.encoded.blockOffsets),
    ("relocations", toJson object.encoded.relocations.size),
    ("typed_program_diagnostic", toJson (reprStr (object.role.checked object.foldCounters).program))]

structure Result where
  pipeline : Json
  cases : List (String × Json)
  report : Json
  mainObject : ByteArray
  releaseObject : ByteArray

def run (foldCounters : Bool := false) : Except String Result := do
  let source ← Runtime.source
  for (address, constant) in source.constants do
    need (Address.blake3 (ser constant) == address &&
      (de (ser constant) : Except String Constant).toOption == some constant) "runtime source codec disagreement"
  let compilation ← Runtime.compile source.constants source.entry
  let .native output := Native.select compilation foldCounters | throw "runtime source skipped native selection"
  let main ← output.emit .main
  let release ← output.emit .release
  let sourceContext := Pipeline.validatedEvalCtx source.constants {}
  let sourceFunction ← (Ixon.Eval.eval sourceContext 10000 source.entry.frame [] source.entry.source).mapError reprStr
  let erased := compilation.erased.erasure.result
  let context0 : IxIR0.Ctx := { env := IxIR0.Env.ofList erased.raw }
  let function0 ← (IxIR0.eval context0 10000 [] compilation.erased.rawMain).mapError reprStr
  let schema := compilation.schema
  let mut rows := []
  let mut cases := []
  for (name, values) in UniqueReuse.Native.Examples.cases do
    let words ← ofNats values
    let bound : PLift (words.length ≤ maxLength) ←
      if bounded : words.length ≤ maxLength then pure ⟨bounded⟩ else throw "runtime length bound lost"
    let view : UniqueReuse.Examples.Source :=
      { constants := source.constants, root := source.root, dataBlock := source.dataBlock,
        nil := source.nil, cons := source.cons, recursor := schema.recursor, builder := schema.builder, values }
    let sourceValue ← (Ixon.Eval.apply sourceContext 10000 sourceFunction (argument source values)).mapError reprStr
    need (sourceList? view 1000 sourceValue == some values.reverse) "runtime Ixon result disagreement"
    let value0 ← (IxIR0.apply context0 10000 function0 (IxIR0.UniqueReverse.listValue schema values)).mapError reprStr
    need (list0? view 1000 value0 == some values.reverse) "runtime IxIR0 result disagreement"
    let context1 : IxIR1.Ctx :=
      { decls := IxIR1.Env.ofList ((entryAddress schema, .fn (entryFunction schema)) :: UniqueReuse.declarations schema) }
    let (input1, argument1) := Target.makeInput schema values
    let (store1, value1) ← (IxIR1.invoke context1 10000 (entryAddress schema) [argument1] input1.heap).mapError reprStr
    need (list1? view 1000 store1 value1 == some values.reverse) "runtime IxIR1 result disagreement"
    let reclaimed1 ← (IxIR1.dropUVal context1 (3 * values.length + 2) store1 value1).mapError reprStr
    need (reclaimed1.live == 0 && reclaimed1.allocs == reclaimed1.frees && reclaimed1.rcops == 0)
      "runtime IxIR1 reclamation disagreement"
    let baselineLogical ← observe2 view schema false .logical
    let baselinePhysical ← observe2 view schema false .physical
    let selectedLogical ← observe2 view schema compilation.selection.reuse .logical
    let selectedPhysical ← observe2 view schema compilation.selection.reuse .physical
    let native ← observeNative words bound.down foldCounters
    let row := Json.mkObj [("name", toJson name), ("input", toJson values), ("value", toJson values.reverse),
      ("snapshot", toJson s!"{name}.json"), ("main_steps", toJson (RuntimeTarget.controlCost values.length foldCounters)),
      ("release_steps", toJson (UniqueTarget.releaseCost values.length)),
      ("prefixes", toJson (← (← native.getObjVal? "prefixes").getArr?).size),
      ("rejections", ← native.getObjVal? "rejections")]
    rows := rows ++ [row]
    cases := cases ++ [(name, Json.mkObj [("format", toJson "compilatrix/source-native-runtime-case/1"),
      ("summary", row), ("source", toJson values.reverse), ("ixir0", toJson values.reverse),
      ("ixir1", Json.mkObj [("value", toJson values.reverse), ("input", toJson input1.heap),
        ("argument", toJson argument1), ("result", toJson value1), ("store", toJson store1), ("reclaimed", toJson reclaimed1)]),
      ("baseline_logical", baselineLogical), ("baseline_physical", baselinePhysical),
      ("selected_logical", selectedLogical), ("selected_physical", selectedPhysical), ("native", native)])]
  let mut rejections := #[]
  for (name, values) in [("word-overflow", [UInt64.size]), ("word-overflow-mixed", [7, UInt64.size + 7]),
      ("length-sixty-five", List.range 65)] do
    let .error reason := ofNats values | throw s!"{name}: runtime adapter accepted"
    rejections := rejections.push (Json.mkObj [("name", toJson name), ("reason", toJson reason)])
  for (name, policy) in [("disabled", ({ enabled := false } : IxIR2.UniqueLower.ReusePolicy)),
      ("rewrite-budget", { maxRewrites := 0 })] do
    let selected ← Runtime.select schema IxIR2.Validate.defaultLimits policy
    need (!selected.reuse) s!"{name}: runtime selector accepted"
    let .skipped reason := Native.select { compilation with selection := selected } foldCounters
      | throw s!"{name}: native selector accepted the consuming fallback"
    rejections := rejections.push (Json.mkObj [("name", toJson name), ("reason", toJson reason)])
  let .error limitReason := Runtime.select schema { IxIR2.Validate.defaultLimits with maxDeclarations := 0 } {}
    | throw "runtime target limit accepted"
  rejections := rejections.push (Json.mkObj [("name", toJson "target-limit-zero"), ("reason", toJson limitReason)])
  let baseline ← Runtime.select schema IxIR2.Validate.defaultLimits { enabled := false }
  let pipeline := Json.mkObj [("format", toJson "compilatrix/source-native-runtime-pipeline/1"),
    ("source", Json.mkObj [("root", toJson source.root), ("identity", toJson (Address.blake3 (sourceBytes source.constants source.entry))),
      ("input_bytes", Coverage.byteJson (sourceBytes source.constants source.entry)),
      ("constants", toJson (source.constants.map fun (address, constant) => Json.mkObj [
        ("key", toJson address), ("bytes", Coverage.byteJson (ser constant))])),
      ("entry", Coverage.byteJson (ser source.entry.source)), ("entry_refs", toJson source.entry.refs),
      ("entry_univs", toJson (source.entry.univs.toList.map fun univ => Coverage.byteJson (ser univ))),
      ("argument_worlds", toJson ["unique"]), ("result_world", toJson "unique")]),
    ("ixir0", Json.mkObj [("raw", Coverage.ir0Entries erased.raw), ("raw_main", Coverage.byteJson compilation.erased.rawMain.bytes),
      ("declarations", Coverage.ir0Entries erased.declarations), ("main", Coverage.byteJson erased.main.bytes),
      ("groups", toJson (erased.groups.map Coverage.ir0Group)), ("blocks", toJson (erased.addressed.blocks.map Coverage.ir0Block)),
      ("address_map", toJson erased.addressMap)]),
    ("schema", toJson schema), ("entry_address", toJson (entryAddress schema)), ("worker_address", toJson (functionAddress schema)),
    ("ixir1", Json.mkObj [("root", toJson output.graph),
      ("main", Coverage.byteJson (UniqueReuse.mainCode { schema, values := [] }).bytes),
      ("artifacts", toJson ((Runtime.artifacts schema).map Coverage.ir1Artifact))]),
    ("policies", Json.mkObj [("source", toJson Runtime.policyTag), ("usage", toJson Ixon.RecursorUsage.policyTag),
      ("lowering", toJson IxIR2.UniqueLower.policyTag), ("reuse", toJson IxIR2.UniqueLower.reusePolicyTag),
      ("execution", toJson IxIR2.CreditPolicy.callLocalV0.tag), ("check_fuel", toJson (1000 : Nat)), ("erase_fuel", toJson (1000 : Nat))]),
    ("ixir2_diagnostic", Json.mkObj [("baseline", toJson (Runtime.program schema false)),
      ("selected", toJson (Runtime.program schema compilation.selection.reuse)),
      ("baseline_stats", toJson baseline.checked.stats), ("selected_stats", toJson compilation.selection.checked.stats),
      ("limits", toJson IxIR2.Validate.defaultLimits)]),
    ("abi", Json.mkObj [("policy", toJson RuntimeTarget.abiTag), ("selector", toJson (RuntimeTarget.policyTag foldCounters)),
      ("max_length", toJson maxLength), ("header_words", toJson headerWords), ("cell_words", toJson cellWords)]),
    ("main", objectJson main), ("release", objectJson release)]
  let report := Json.mkObj [("format", toJson "compilatrix/source-native-runtime-report/1"),
    ("pipeline", toJson "pipeline.json"), ("pipeline_identity", toJson (Address.blake3 pipeline.compress.toUTF8)),
    ("source_identity", toJson (Address.blake3 (sourceBytes source.constants source.entry))), ("ixir1_root", toJson output.graph),
    ("main_identity", toJson (Address.blake3 main.bytes)), ("release_identity", toJson (Address.blake3 release.bytes)),
    ("main_policy", toJson main.policyIdentity), ("release_policy", toJson release.policyIdentity),
    ("cases", toJson rows), ("adapter_and_selection_rejections", Json.arr rejections)]
  return { pipeline, cases, report, mainObject := main.bytes, releaseObject := release.bytes }

end Ix.Compiler.UniqueReuse.Runtime.Native.Examples
