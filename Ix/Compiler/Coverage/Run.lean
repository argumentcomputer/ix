import Ix.Compiler.Coverage.Snapshot
import Ix.Compiler.X86.ELFValidate

/-! Run each fixed Ixon input through the actual compiler and independently
observe each executable stage. Expected rejection is part of the coverage
matrix; any other rejection or observation drift fails the gate. -/

namespace Ix.Compiler.Coverage

open Lean Ix.Compiler.Ixon

structure Features where
  directCalls : Nat := 0
  tailCalls : Nat := 0
  papps : Nat := 0
  applies : Nat := 0
  constructorSwitches : Nat := 0
  natSwitches : Nat := 0
  deriving ToJson

def features (program : IxIR2.Program) : Features := Id.run do
  let functions := program.main :: program.declarations.filterMap fun
    | (_, .fn function) => some function
    | _ => none
  let mut result : Features := {}
  for function in functions do
    for block in function.blocks do
      for instruction in block.instructions do
        result := match instruction with
          | .call .. | .callSelf .. => { result with directCalls := result.directCalls + 1 }
          | .papp .. => { result with papps := result.papps + 1 }
          | .apply .. => { result with applies := result.applies + 1 }
          | _ => result
      result := match block.terminator with
        | .tailCall .. | .tailCallSelf .. => { result with tailCalls := result.tailCalls + 1 }
        | .switchValue _ constructors natPeel =>
            { result with
              constructorSwitches := result.constructorSwitches + (if constructors.isEmpty then 0 else 1)
              natSwitches := result.natSwitches + (if natPeel.isSome then 1 else 0) }
        | _ => result
  return result

private def scalar0 (name : String) : Except IxIR0.Err IxIR0.Value → Except String Nat
  | .ok (.lit (.nat number)) => .ok number
  | .ok _ => .error s!"{name} returned a non-Nat value"
  | .error error => .error s!"{name} failed: {repr error}"

private def scalar1 (name : String) (value : IxIR1.RVal) : Except String Nat :=
  match value with
  | .lit (.nat number) => .ok number
  | _ => .error s!"{name} returned a non-Nat value"

private def heapCounters (store : IxIR1.Store) : Json :=
  Json.mkObj [("allocs", toJson store.allocs), ("frees", toJson store.frees),
    ("rcops", toJson store.rcops), ("reuses", toJson store.reuses), ("live", toJson store.live)]

private def sameCounters (first second : IxIR1.Store) : Bool :=
  first.allocs == second.allocs && first.frees == second.frees &&
    first.rcops == second.rcops && first.reuses == second.reuses && first.live == second.live

private def sameStore (first second : IxIR2.Eval.Store) : Bool :=
  first.counters == second.counters && first.heap.nodes.size == second.heap.nodes.size &&
    (first.heap.nodes.zip second.heap.nodes).all fun
      | (none, none) => true
      | (some left, some right) =>
          left.world == right.world && left.rc == right.rc && left.node == right.node
      | _ => false

private def physicalObservation (source : Source) (number : Nat)
    (result : IxIR2.Eval.Result) : Json :=
  Json.mkObj [
    ("nat", toJson number), ("heap", heapCounters result.store.heap),
    ("peak_live_nodes", toJson result.store.peakLiveNodes),
    ("control_steps", toJson (source.policy.controlFuel - result.controlRemaining)),
    ("heap_work", toJson (source.policy.heapFuel - result.heapRemaining)),
    ("reset_attempts", toJson result.store.resetAttempts),
    ("hot_resets", toJson result.store.hotResets), ("cold_resets", toJson result.store.coldResets),
    ("reused_payload_units", toJson result.store.reusedPayloadUnits)]

structure Observation where
  summary : Json
  stages : Json

def Source.observe (source : Source) (attached : source.Attached)
    (number : Nat) : Except String Observation := do
  let sourceNumber ←
    match Ixon.Eval.eval (Pipeline.validatedEvalCtx source.constants source.config)
        source.policy.evalFuel (Pipeline.validatedMainFrame source.root) [] Pipeline.validatedMainSource with
    | .ok (.litV (.natL number)) => pure number
    | .ok _ => throw "Ixon returned a non-Nat value"
    | .error error => throw s!"Ixon execution failed: {repr error}"
  let artifact := attached.source.artifact
  let raw0 ← scalar0 "raw IxIR0" (IxIR0.eval { env := IxIR0.Env.ofList artifact.rawErasedDecls }
    source.policy.evalFuel [] (.ref source.root))
  let addressed0 ← scalar0 "addressed IxIR0" (IxIR0.eval { env := IxIR0.Env.ofList artifact.erasedDecls }
    source.policy.evalFuel [] attached.source.erasure.result.main)
  let (rawStore, rawValue) ←
    (IxIR1.runOwnedMain { decls := IxIR1.Env.ofList attached.source.lowering.raw }
      .shared attached.source.lowering.mainCode source.policy.evalFuel).mapError
        (fun error => s!"raw IxIR1 failed: {repr error}")
  let raw1 ← scalar1 "raw IxIR1" rawValue
  let (store, value) ←
    (IxIR1.runOwnedMain { decls := artifact.targetDeclEnv } .shared artifact.main source.policy.evalFuel).mapError
      (fun error => s!"addressed IxIR1 failed: {repr error}")
  let addressed1 ← scalar1 "addressed IxIR1" value
  let context := IxIR2.Eval.Context.ofProgram attached.target.artifact.program
    attached.target.artifact.validationContext.schemas
  let logical ← (IxIR2.Eval.runMain context .logical attached.target.artifact.program
    source.policy.controlFuel source.policy.heapFuel).mapError (fun error => s!"logical IxIR2 failed: {repr error}")
  let physical ← (IxIR2.Eval.runMain context .physical attached.target.artifact.program
    source.policy.controlFuel source.policy.heapFuel).mapError (fun error => s!"physical IxIR2 failed: {repr error}")
  let logicalNumber ← scalar1 "logical IxIR2" logical.value
  let physicalNumber ← scalar1 "physical IxIR2" physical.value
  if [sourceNumber, raw0, addressed0, raw1, addressed1, logicalNumber, physicalNumber].any (· != number) then
    throw "source and intermediate Nat observations disagree"
  if !sameCounters rawStore store || !sameCounters store logical.store.heap ||
      !sameCounters store physical.store.heap || !sameStore logical.store physical.store ||
      logical.controlRemaining != physical.controlRemaining || logical.heapRemaining != physical.heapRemaining ||
      store.live != 0 then
    throw "intermediate counters, complete baseline stores, or execution budgets disagree"
  let summary := physicalObservation source number physical
  return {
    summary
    stages := Json.mkObj [
      ("ixon", toJson sourceNumber), ("raw_ixir0", toJson raw0), ("ixir0", toJson addressed0),
      ("raw_ixir1", Json.mkObj [("nat", toJson raw1), ("heap", heapCounters rawStore)]),
      ("ixir1", Json.mkObj [("nat", toJson addressed1), ("heap", heapCounters store)]),
      ("logical_ixir2", physicalObservation source logicalNumber logical),
      ("physical_ixir2", summary)] }

structure CaseResult where
  name : String
  row : Json
  snapshot : Json
  object : Option ByteArray := none

private def rejection (stage code : String) (root : Address)
    (message : Option String := none) : Json :=
  Json.mkObj [("stage", toJson stage), ("code", toJson code),
    ("root", toJson root), ("message", toJson message)]

private def sourceRow (source : Source) (stage : String) (failure observation : Json)
    (compiled : Option source.Attached := none) (hasObject : Bool := false) : Json :=
  Json.mkObj [
    ("name", toJson source.name), ("origin", toJson "synthetic-ixon"),
    ("root_kind", toJson "constant"), ("root", toJson source.root),
    ("source_constants", toJson source.constants.length), ("last_accepted_stage", toJson stage),
    ("rejection", failure), ("observation", observation),
    ("ir1_root", match compiled with
      | none => Json.null
      | some attached => toJson (IxIR1.Optimizer.graphRoot attached.source.artifact.targetArtifacts
          attached.source.artifact.main)),
    ("hpt_roots", match compiled with | none => Json.null | some attached => toJson attached.hpt.result.addresses),
    ("features", match compiled with | none => Json.null | some attached => toJson (features attached.target.artifact.program)),
    ("snapshot", toJson s!"{source.name}.json"),
    ("object", if hasObject then toJson s!"{source.name}.o" else Json.null)]

private def caseSnapshot (source : Source) (compilation observations : Json) : Json :=
  Json.mkObj [("format", toJson "compilatrix/source-case/1"),
    ("input", source.inputSnapshot), ("compilation", compilation), ("observations", observations)]

def runSource (source : Source) : Except String CaseResult := do
  match source.compile with
  | .error (.pipeline (.usage root .freezeNeeded)) =>
      if source.expected != .usageFreeze || root != source.root then
        throw "unexpected source freezeNeeded rejection"
      let failure := rejection "usage" "freezeNeeded" root
      return { name := source.name, row := sourceRow source "ixon" failure Json.null
               snapshot := caseSnapshot source Json.null failure }
  | .error (.pipeline (.validate root message)) =>
      if source.expected != .externRejected || root != source.root ||
          message != "validated extern ownership ABI rejects this declaration" then
        throw s!"unexpected erasure-validation rejection: {root}: {message}"
      let failure := rejection "validated-erasure" "extern-ownership" root (some message)
      return { name := source.name, row := sourceRow source "usage" failure Json.null
               snapshot := caseSnapshot source Json.null failure }
  | .error error => throw s!"compiler rejected {source.name}: {repr error}"
  | .ok attached =>
      let .scalar number shouldSelect := source.expected | throw "compiler accepted a negative source case"
      let observation ← source.observe attached number
      let compilation := source.compilationSnapshot attached
      match X86.Select.select attached.target.artifact.program with
      | .error .unsupportedScalarShape =>
          if shouldSelect then throw "source scalar failed selection"
          let failure := rejection "x86-selection" "unsupportedScalarShape" source.root
          return { name := source.name
                   row := sourceRow source "ixir2" failure observation.summary (some attached)
                   snapshot := caseSnapshot source compilation observation.stages }
      | .error (.invalidSource (.invalid _ .schema "missing constructor schema")) =>
          if shouldSelect || !(source.name.startsWith "ctor-" || source.name.startsWith "nat-") then
            throw "unexpected constructor-schema boundary in scalar selection"
          let failure := rejection "x86-selection" "missingConstructorSchema" source.root
          return { name := source.name
                   row := sourceRow source "ixir2" failure observation.summary (some attached)
                   snapshot := caseSnapshot source compilation observation.stages }
      | .error error => throw s!"unexpected selector error: {repr error}"
      | .ok selected =>
          if !shouldSelect || selected.word.toNat != number then
            throw "selector accepted an unexpected graph or truncated its Nat"
          let targetRun := X86.runFrom X86.Runtime.rejecting selected.target 2 (X86.Core.empty 0x1008)
          if targetRun.status != .halted selected.word || targetRun.core.readReg .rsp != 0x1008 then
            throw "typed x86 observation disagrees with the source"
          let stream ← (X86.Stream.encode selected.target).mapError (fun error => reprStr error)
          let encoded := stream.output
          let provenance : X86.ELF.Provenance :=
            .ixir1Policy (IxIR1.Optimizer.graphRoot attached.source.artifact.targetArtifacts
              attached.source.artifact.main) X86.ValidatedScalar.loweringVersion X86.ValidatedScalar.passPolicyVersion
          let object ← (X86.ELF.writeChecked
            { encoded, entryBlock := selected.target.program.entry, provenance }).mapError (fun error => reprStr error)
          return {
            name := source.name
            row := sourceRow source "elf" Json.null observation.summary (some attached) true
            snapshot := caseSnapshot source compilation
              (Json.mkObj [("intermediate", observation.stages), ("typed_x86", toJson selected.word),
                ("text", byteJson encoded.text), ("provenance", byteJson provenance.bytes)])
            object := some object.bytes }

end Ix.Compiler.Coverage
