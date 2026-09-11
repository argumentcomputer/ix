import Ix.Compiler.Coverage.Upstream
import Ix.Compiler.X86.NatCallsSim

namespace Ix.Compiler.Coverage.UpstreamNative
open Lean Ix.Compiler.X86 Ix.Compiler.X86.NatCalls

def policy : String := "upstream-closed-nat/2"

def schema (source : Source) (attached : source.Attached) : Except String NatCalls.Schema := do
  let ids ← Upstream.natIds source
  let rename0 := IxIR0.MutualBlock.Renaming.apply attached.source.erasure.result.addressMap
  let rename1 := IxIR1.Readdress.Renaming.apply attached.source.artifact.targetAddressMap
  return {
    zero := IxIR1.Lower.ctorIdOf (rename1 (rename0 ids.zero)) 0
    succ := IxIR1.Lower.ctorIdOf (rename1 (rename0 ids.succ)) 1 }

def expressionJson : NatCalls.Expr → Json
  | .argument => Json.mkObj [("op", toJson "argument")]
  | .constant value => Json.mkObj [("op", toJson "constant"), ("value", toJson value.toNat)]
  | .successor value => Json.mkObj [("op", toJson "successor"), ("value", expressionJson value)]
  | .call function value => Json.mkObj [("op", toJson "call"), ("function", toJson function), ("value", expressionJson value)]

def parameterJson : NatCalls.Param → Json
  | .nat => Json.mkObj [("kind", toJson "nat")]
  | .closure address none => Json.mkObj [("kind", toJson "known-capture-free-pap"), ("function", toJson address)]
  | .closure address (some expression) => Json.mkObj [("kind", toJson "known-static-capture-pap"),
      ("function", toJson address), ("capture", expressionJson expression)]
  | .staticNat expression => Json.mkObj [("kind", toJson "static-nat"), ("value", expressionJson expression)]
  | .erased => Json.mkObj [("kind", toJson "erased")]

def residualJson (residual : NatCalls.Residual) : Json :=
  Json.mkObj [("entry", toJson residual.entry), ("functions", toJson (residual.functions.map fun function =>
    Json.mkObj [("origin", toJson function.origin), ("parameters", toJson (function.parameters.map parameterJson)),
      ("body", expressionJson function.body)]))]

/-- A finite readable stack, with writes confined below the caller's return
slot. Distinct saved registers and nonzero initial bytes expose frame errors. -/
def core (stack : Word) (seed : Word) (capacity : Word := 64) : Core :=
  let registers := fun register => seed + (SysV.calleeSaved.toList.idxOf register + 1).toUInt64 * 0x102030405060708
  let memory : Memory := {
    bytes := fun address => (address ^^^ seed).toUInt8
    readable := fun address => decide (stack - capacity ≤ address && address < stack + 8)
    writable := fun address => decide (stack - capacity ≤ address && address < stack) }
  { registers := Registers.set registers .rsp stack, memory := memory.write64 stack 0x12345678 }

def executionJson {source context schema} (object : NatCalls.Object source context schema)
    (stack seed base : Word) : Except String Json := do
  let initial := core stack seed
  let execution ← certifyExecution object initial 100
  let mut machine := Machine.initial object.selected.target initial
  let mut steps := 0
  let mut calls := 0
  let mut minimum := stack
  for _ in [:100] do
    if machine.status != .running then break
    if let some block := object.selected.target.program.blocks[machine.pc.block.toNat]? then
      if let some (.call _) := block.instructions[machine.pc.offset.toNat]? then calls := calls + 1
    machine := X86.step Runtime.rejecting object.selected.target machine
    minimum := min minimum (machine.core.readReg .rsp)
    steps := steps + 1
  let final ← (ObjectEval.run object.object.bytes object.input.exportName base steps initial).mapError reprStr
  if final.rip != execution.returnAddress || final.core.readReg .rax != object.selected.word ||
      final.core.readReg .rsp != stack + 8 ||
      !final.core.calleeSavedMatch initial.calleeSavedSnapshot then
    throw "actual object-byte execution disagrees with typed execution"
  return Json.mkObj [("stack", toJson stack.toNat), ("seed", toJson seed.toNat), ("text_base", toJson base.toNat),
    ("value", toJson (final.core.readReg .rax).toNat), ("return_address", toJson final.rip.toNat),
    ("typed_steps", toJson steps), ("byte_steps", toJson steps), ("direct_calls", toJson calls),
    ("stack_written_bytes", toJson (stack - minimum).toNat), ("stack_capacity_bytes", toJson (64 : Nat)),
    ("saved_registers_preserved", toJson true), ("stack_restored_before_ret", toJson true),
    ("call_trace_certified", toJson true), ("object_entry_certified", toJson true)]

def snapshot {source context schema} (object : NatCalls.Object source context schema) : Except String Json := do
  let mut executions := #[]
  for (stack, seed, base) in [(0x4008, 0xabcdef01, 0x100000), (0x8008, 0x12345678, 0x400000),
      (0x100000008, 0xffffffffffffffff, 0x100000000), (0x7fffffffe008, 0x1020304050607080, 0x7fff00000000)] do
    executions := executions.push (← executionJson object stack seed base)
  let selected := object.selected
  let mut fallback := #[]
  for (name, limits) in [("zero-depth", { depth := 0 : NatCalls.Limits }),
      ("zero-functions", { functions := 0 : NatCalls.Limits }),
      ("zero-instructions", { instructions := 0 : NatCalls.Limits })] do
    match NatCalls.select source context schema limits selected.captureMode with
    | .error (.lowering .budget) => fallback := fallback.push (Json.mkObj [
        ("name", toJson name), ("reason", toJson "budget"), ("path", toJson "checked-baseline-ixir2")])
    | _ => throw "native budget fallback changed"
  if selected.captureMode == .staticNat then
    match NatCalls.select source context schema { captureFuel := 0 } .staticNat with
    | .error (.lowering .budget) => fallback := fallback.push (Json.mkObj [
        ("name", toJson "zero-capture-fuel"), ("reason", toJson "budget"), ("path", toJson "checked-baseline-ixir2")])
    | _ => throw "native capture budget fallback changed"
    match NatCalls.select source context schema with
    | .error (.lowering .capturedPap) => fallback := fallback.push (Json.mkObj [
        ("name", toJson "capture-free-policy"), ("reason", toJson "capturedPap"), ("path", toJson "checked-baseline-ixir2")])
    | _ => throw "capture-free policy boundary changed"
  for (name, initial) in [("misaligned-stack", core 0x8000 1), ("insufficient-stack", core 0x8008 1 32)] do
    match certifyExecution object initial 100 with
    | .error _ => fallback := fallback.push (Json.mkObj [("name", toJson name),
        ("reason", toJson "execution-condition"), ("path", toJson "no-native-execution-certificate")])
    | .ok _ => throw "invalid native stack admitted"
  return Json.mkObj [
    ("format", toJson "compilatrix/upstream-native/1"), ("selector", toJson selected.captureMode.policy),
    ("representation", toJson "closed shared unary Nat constructors to exact UInt64"),
    ("runtime_arguments", toJson (0 : Nat)), ("schema", Json.mkObj [("zero", toJson schema.zero), ("succ", toJson schema.succ)]),
    ("residual", residualJson selected.residual), ("typed_program_diagnostic", toJson (reprStr selected.target.program)),
    ("value", toJson selected.number), ("word_exact", toJson true),
    ("physical_store", toJson selected.physical.store), ("physical_value", toJson selected.physical.value),
    ("reclaimed_store", toJson selected.reclaimed),
    ("native_heap", Json.mkObj [("allocs", toJson (0 : Nat)), ("frees", toJson (0 : Nat)),
      ("rcops", toJson (0 : Nat)), ("result_bytes", toJson (8 : Nat)), ("result_release", toJson "unboxed word; no heap root")]),
    ("text", byteJson object.stream.output.text), ("text_bytes", toJson object.stream.output.text.size),
    ("block_offsets", toJson (object.stream.output.blockOffsets.map id)),
    ("symbol", toJson object.input.exportName), ("lowering_version", toJson selected.captureMode.loweringVersion.toNat), ("pass_policy_version", toJson (1 : Nat)),
    ("object", byteJson object.object.bytes), ("object_bytes", toJson object.object.bytes.size),
    ("object_identity", toJson (Ixon.Address.blake3 object.object.bytes)),
    ("executions", Json.arr executions), ("fallbacks_and_rejections", Json.arr fallback)]

def run (input : Upstream.Input) : Except String CaseResult := do
  let source := input.source
  match source.compile, input.expected with
  | .ok attached, .nat number =>
    let observed ← Upstream.observe source attached number
    let schema ← schema source attached
    let selected := match NatCalls.select attached.target.artifact.program attached.target.artifact.validationContext schema with
      | .error (.lowering .capturedPap) => NatCalls.select attached.target.artifact.program attached.target.artifact.validationContext schema {} .staticNat
      | result => result
    match selected with
    | .error error => throw s!"upstream computational native selection failed: {repr error}"
    | .ok selected =>
      if selected.number != number || !["upstream-applyClosed", "upstream-captureClosed", "upstream-letClosed"].contains source.name then
        throw "upstream native accepted inventory or source value drifted"
      let root := IxIR1.Optimizer.graphRoot attached.source.artifact.targetArtifacts attached.source.artifact.main
      let object ← selected.emit root "compilatrix_main"
      let native ← snapshot object
      return Upstream.result input "elf" Json.null observed.summary (some attached) observed.stages
        (native := native) (object := some object.object.bytes)
  | _, _ => Upstream.run input

def cases (path : System.FilePath := Upstream.directory) : IO (Except String (List CaseResult)) := do
  let mut results := []
  for fixture in Upstream.fixtures do
    match (← Upstream.load path fixture).bind run with
    | .error message => return .error s!"{fixture.name}: {message}"
    | .ok result => results := results ++ [result]
  return .ok results

end Ix.Compiler.Coverage.UpstreamNative
