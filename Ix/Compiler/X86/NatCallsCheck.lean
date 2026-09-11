import Ix.Compiler.X86.NatCalls
import Ix.Compiler.IxIR2.EvalFuel
import Ix.Compiler.X86.ObjectExecution
import Ix.Compiler.X86.StreamDecidable

/-! Closed translation validation connects the structurally selected call
program to the actual physical run, its complete release, and certified ELF
bytes. Execution certificates expose their stack/state conditions explicitly;
they do not establish N3's later open-function or branch/join domain. -/
namespace Ix.Compiler.X86.NatCalls
open Ix.Compiler

def heapNat (schema : Schema) : Nat → IxIR1.Store → IxIR1.RVal → Option Nat
  | 0, _, _ => none
  | fuel + 1, store, .loc location => do
      let box ← store.get? location
      if box.world != .shared then none else do
        let .ctorN cid fields := box.node | none
        if cid == schema.zero && fields.isEmpty then some 0
        else if cid == schema.succ then
          let #[tail] := fields | none
          (· + 1) <$> heapNat schema fuel store tail
        else none
  | _, _, .lit (.nat number) => some number
  | _, _, _ => none

def evalContext (source : IxIR2.Program) (context : IxIR2.Validate.Context) : IxIR2.Eval.Context :=
  IxIR2.Eval.Context.ofProgram source context.schemas

structure Output (source : IxIR2.Program) (context : IxIR2.Validate.Context) (schema : Schema) where
  limits : Limits
  captureMode : CaptureMode
  sourceStats : IxIR2.Validate.Stats
  sourceAccepted : IxIR2.Validate.validate context source = .ok sourceStats
  arity : source.main.signature.params.size = 0
  nonempty : source.main.blocks.isEmpty = false
  residual : Residual
  lowered : lower source schema limits captureMode = .ok residual
  number : Nat
  evaluated : residual.evaluate 1024 = .ok number
  word : Word
  exactWord : word.toNat = number
  physical : IxIR2.Eval.Result
  physicalRun : IxIR2.Eval.runMain (evalContext source context) .physical source 10000 10000 = .ok physical
  observation : heapNat schema 10000 physical.store.heap physical.value = some number
  reclaimed : IxIR2.Eval.Store
  remaining : Nat
  releaseRun : IxIR2.Eval.releaseShared 10000 physical.store physical.value = .ok (reclaimed, remaining)
  empty : reclaimed.heap.live = 0
  balanced : reclaimed.heap.allocs = reclaimed.heap.frees
  target : X86.Checked
  targetProduced : target.program = residual.target

inductive CheckError where
  | source (error : IxIR2.Validate.Error)
  | lowering (error : Error)
  | physical (error : IxIR2.Eval.Error)
  | arity
  | emptyMain
  | representation
  | reclamation
  | target
  deriving Repr

def select (source : IxIR2.Program) (context : IxIR2.Validate.Context) (schema : Schema)
    (limits : Limits := {}) (captureMode : CaptureMode := .captureFree) : Except CheckError (Output source context schema) := do
  match sourceAccepted : IxIR2.Validate.validate context source with
  | .error error => throw (.source error)
  | .ok sourceStats =>
    if arity : source.main.signature.params.size = 0 then
      if nonempty : source.main.blocks.isEmpty = false then
        match lowered : lower source schema limits captureMode with
        | .error error => throw (.lowering error)
        | .ok residual =>
          match evaluated : residual.evaluate 1024 with
          | .error error => throw (.lowering error)
          | .ok number =>
            let word := UInt64.ofNat number
            if exactWord : word.toNat = number then
              match physicalRun : IxIR2.Eval.runMain (evalContext source context) .physical source 10000 10000 with
              | .error error => throw (.physical error)
              | .ok physical =>
                if observation : heapNat schema 10000 physical.store.heap physical.value = some number then
                  match releaseRun : IxIR2.Eval.releaseShared 10000 physical.store physical.value with
                  | .error error => throw (.physical error)
                  | .ok (reclaimed, remaining) =>
                    if empty : reclaimed.heap.live = 0 then
                      if balanced : reclaimed.heap.allocs = reclaimed.heap.frees then
                        if valid : residual.target.wellFormed = true then
                          return {
                            limits, captureMode, sourceStats, sourceAccepted, arity, nonempty, residual, lowered,
                            number, evaluated, word, exactWord, physical, physicalRun, observation,
                            reclaimed, remaining, releaseRun, empty, balanced,
                            target := ⟨residual.target, valid⟩, targetProduced := rfl }
                        else throw .target
                      else throw .reclamation
                    else throw .reclamation
                else throw .representation
            else throw .representation
      else throw .emptyMain
    else throw .arity

/-- The value and entire physical store are independent of successful run
budgets. The endpoint is a Nat observation, not equality to an unboxed physical
literal: the baseline still returns its actual shared constructor heap. -/
theorem Output.refinesSuccessfulRun {source context schema} (output : Output source context schema)
    {control heap : Nat} {result : IxIR2.Eval.Result}
    (execution : IxIR2.Eval.runMain (evalContext source context) .physical source control heap = .ok result) :
    heapNat schema 10000 result.store.heap result.value = some output.word.toNat ∧
      result.store = output.physical.store ∧ result.value = output.physical.value := by
  obtain ⟨stores, values⟩ := IxIR2.Eval.runMain_success_unique output.arity output.nonempty execution output.physicalRun
  refine ⟨?_, stores, values⟩
  rw [stores, values, output.exactWord]
  exact output.observation

/-- Every successful physical run has the same complete result release,
including the captured PAP and its retained constructor graph. -/
theorem Output.reclaimsSuccessfulRun {source context schema} (output : Output source context schema)
    {control heap : Nat} {result : IxIR2.Eval.Result}
    (execution : IxIR2.Eval.runMain (evalContext source context) .physical source control heap = .ok result) :
    IxIR2.Eval.releaseShared 10000 result.store result.value = .ok (output.reclaimed, output.remaining) ∧
      output.reclaimed.heap.live = 0 ∧ output.reclaimed.heap.allocs = output.reclaimed.heap.frees := by
  obtain ⟨_, stores, values⟩ := output.refinesSuccessfulRun execution
  exact ⟨by rw [stores, values]; exact output.releaseRun, output.empty, output.balanced⟩

structure Object (source : IxIR2.Program) (context : IxIR2.Validate.Context) (schema : Schema) where
  selected : Output source context schema
  stream : Stream.Certified selected.target
  input : ELF.Input
  encoded : input.encoded = stream.output
  entry : input.entryBlock = selected.target.program.entry
  object : ELF.Certified input

def CaptureMode.policy : CaptureMode → String
  | .captureFree => "closed-unary-nat-calls/1"
  | .staticNat => "closed-static-capture-nat-calls/1"

def CaptureMode.loweringVersion : CaptureMode → UInt32
  | .captureFree => 4
  | .staticNat => 8

def Output.emit {source context schema} (output : Output source context schema)
    (root : Ixon.Address) (name : String) : Except String (Object source context schema) := do
  let stream ← (Stream.encode output.target).mapError reprStr
  let input : ELF.Input := {
    encoded := stream.output, entryBlock := output.target.program.entry, exportName := name,
    provenance := .ixir1Policy root output.captureMode.loweringVersion 1 }
  let object ← (ELF.writeChecked input).mapError reprStr
  return { selected := output, stream, input, encoded := rfl, entry := rfl, object }

/-- Explicit, executable certification of a complete terminating typed trace
including call alignment, return slots, saved registers, and the final RET.
It can be checked for any supplied initial machine state. -/
structure Execution {source context schema} (object : Object source context schema) (core : Core) (fuel : Nat) where
  after : Machine
  run : X86.runFrom Runtime.rejecting object.selected.target fuel core = after
  halted : after.status = .halted object.selected.word
  value : after.core.readReg .rax = object.selected.word
  safe : Stream.SafeTrace Runtime.rejecting object.selected.target fuel (fun _ => False)
    (Machine.initial object.selected.target core)
  stack : after.core.readReg .rsp = core.readReg .rsp
  saved : after.core.calleeSavedMatch (core.calleeSavedSnapshot) = true
  returnAddress : Word
  slot : after.core.memory.read64? (after.core.readReg .rsp) = .ok returnAddress

def certifyExecution {source context schema} (object : Object source context schema)
    (core : Core) (fuel : Nat := 4096) : Except String (Execution object core fuel) := do
  let after := X86.runFrom Runtime.rejecting object.selected.target fuel core
  if halted : after.status = .halted object.selected.word then
   if value : after.core.readReg .rax = object.selected.word then
    if safe : Stream.SafeTrace Runtime.rejecting object.selected.target fuel (fun _ => False)
        (Machine.initial object.selected.target core) then
      if stack : after.core.readReg .rsp = core.readReg .rsp then
        if saved : after.core.calleeSavedMatch core.calleeSavedSnapshot = true then
          match slot : after.core.memory.read64? (after.core.readReg .rsp) with
          | .error _ => throw "unreadable native return slot"
          | .ok returnAddress => return { after, run := rfl, halted, value, safe, stack, saved, returnAddress, slot }
        else throw "native callee-saved register mismatch"
      else throw "native stack pointer mismatch"
    else throw "native call/stack trace rejected"
   else throw "native result register disagrees"
  else throw "native return value or termination disagrees"

theorem Execution.objectRun {source context schema} {object : Object source context schema}
    {core : Core} {fuel : Nat} (execution : Execution object core fuel) (base : Word) (flags : ByteEval.Flags) :
    ∃ count holes finalState, 0 < count ∧ count ≤ 3 * fuel ∧
      ObjectEval.run object.object.bytes object.input.exportName base count core flags = .ok finalState ∧
      finalState.rip = execution.returnAddress ∧
      Stream.CoreRelated object.selected.target.program base holes []
        (execution.after.core.setReg .rsp (execution.after.core.readReg .rsp + 8)) finalState.core := by
  have stream : Stream.Valid object.selected.target.program object.input.encoded := by
    rw [object.encoded]
    exact object.stream.valid
  exact ObjectEval.run_with_calls stream object.object.valid object.entry Runtime.rejecting base fuel core flags
    execution.safe execution.run execution.halted execution.slot

theorem Execution.objectReturns {source context schema} {object : Object source context schema}
    {core : Core} {fuel : Nat} (execution : Execution object core fuel) (base : Word) (flags : ByteEval.Flags) :
    ∃ count finalState, 0 < count ∧ count ≤ 3 * fuel ∧
      ObjectEval.run object.object.bytes object.input.exportName base count core flags = .ok finalState ∧
      finalState.rip = execution.returnAddress ∧ finalState.core.readReg .rax = object.selected.word := by
  obtain ⟨count, holes, finalState, positive, bounded, run, returned, related⟩ := execution.objectRun base flags
  refine ⟨count, finalState, positive, bounded, run, returned, ?_⟩
  have equal := related.readReg .rax
  simpa [Core.readReg, Core.setReg, Registers.set] using equal.symm.trans (by simpa [Core.readReg, Core.setReg, Registers.set] using execution.value)

end Ix.Compiler.X86.NatCalls
