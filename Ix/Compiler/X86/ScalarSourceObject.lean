import Ix.Compiler.X86.ScalarSourceApply
import Ix.Compiler.IxIR1.Optimizer

namespace Ix.Compiler.X86.Scalar.Source
open Ix.Compiler.Ixon (Address Constant)
open Ix.Compiler.IxIR0.NatArithmetic (Represents)

def policy : String := "source-scalar-runtime/1"

/-- The source certificate, selected runtime graph, instruction stream, and
actual ELF bytes are attached once, independently of runtime arguments. -/
structure Compiled {constants : List (Address × Constant)} {root : Address} {config : Pipeline.Config}
    {eraseFuel lowerFuel : Nat}
    (source : Pipeline.ValidatedCompilation constants root config .shared eraseFuel lowerFuel) where
  selected : Selected source.erasure.result.raw root
  native : Output selected.scalar
  stream : Stream.Certified native.target
  input : ELF.Input
  encoded : input.encoded = stream.output
  entry : input.entryBlock = native.target.program.entry
  object : ELF.Certified input

def compile {constants : List (Address × Constant)} {root : Address} {config : Pipeline.Config}
    {eraseFuel lowerFuel : Nat}
    (source : Pipeline.ValidatedCompilation constants root config .shared eraseFuel lowerFuel)
    (name : String := "compilatrix_scalar") : Except String (Compiled source) := do
  let selected ← select source.erasure.result.raw root
  let native ← Scalar.compile selected.scalar
  let stream ← (Stream.encode native.target).mapError reprStr
  let graphRoot := IxIR1.Optimizer.graphRoot source.artifact.targetArtifacts source.artifact.main
  let input : ELF.Input := {
    encoded := stream.output, entryBlock := native.target.program.entry, exportName := name
    provenance := .ixir1Policy graphRoot 5 1 }
  let object ← (ELF.writeChecked input).mapError reprStr
  return { selected, native, stream, input, encoded := rfl, entry := rfl, object }

theorem Compiled.nativeReturns
    {constants : List (Address × Constant)} {root : Address} {config : Pipeline.Config} {eraseFuel lowerFuel : Nat}
    {source : Pipeline.ValidatedCompilation constants root config .shared eraseFuel lowerFuel}
    (compiled : Compiled source) (left right : Word) (stack : Stack)
    (depth : compiled.selected.scalar.program.entry < stack.depth) (core : Core)
    (stackPointer : core.readReg .rsp = stack.layout.address stack.frame.top)
    (arguments : ArgumentsAt #[left, right] ⟨core.registers, fun index => core.memory.read64 (stack.layout.address index)⟩)
    (readable : ∀ index < stack.layout.slots, Memory.rangeAllowed core.memory.readable (stack.layout.address index) 8 = true)
    (writable : ∀ index < stack.layout.slots, Memory.rangeAllowed core.memory.writable (stack.layout.address index) 8 = true)
    (base : Word) (flags : ByteEval.Flags) :
    ∃ result, Evaluates compiled.selected.scalar.program.functions compiled.selected.entryFunction.body #[left, right] result ∧
      Nonempty (ObjectResult compiled.object.bytes compiled.input.exportName base flags core stack result) := by
  have arity : #[left, right].size = compiled.selected.entryFunction.parameters := by simp [compiled.selected.binary]
  obtain ⟨result, evaluated⟩ := compiled.selected.scalar.function_total _ _ compiled.selected.functionFound _ arity
  obtain ⟨executed⟩ := compiled.native.root_run compiled.selected.functionFound arity evaluated stack depth core
    stackPointer arguments readable writable
  have stream : Stream.Valid compiled.native.target.program compiled.input.encoded := by
    rw [compiled.encoded]
    exact compiled.stream.valid
  exact ⟨result, evaluated, executed.objectResult stream compiled.object.valid compiled.entry base flags⟩

/-- A successful source call and the existing source/raw value relation.
These are source obligations; no scalar, typed x86, or byte run is assumed. -/
structure Invocation {constants : List (Address × Constant)} {root : Address} {config : Pipeline.Config}
    {eraseFuel lowerFuel : Nat}
    (source : Pipeline.ValidatedCompilation constants root config .shared eraseFuel lowerFuel)
    (selected : Selected source.erasure.result.raw root) (a b : Nat) (result : Ixon.Eval.Value) where
  function : Ixon.Eval.Value
  left : Ixon.Eval.Value
  right : Ixon.Eval.Value
  intermediate : Ixon.Eval.Value
  rawLeft : IxIR0.Value
  rawRight : IxIR0.Value
  fuel : Nat
  firstFuel : Nat
  secondFuel : Nat
  oracles : @Sim.OracleRel source.memberScope (Pipeline.validatedEvalCtx constants config).inlineSharing
    { env := IxIR0.Env.ofList source.erasure.result.raw }
  contextWF : (Pipeline.validatedEvalCtx constants config).SharingWF
  functionWF : function.SharingWF
  leftWF : left.SharingWF
  rightWF : right.SharingWF
  entry : Ixon.Eval.eval (Pipeline.validatedEvalCtx constants config) fuel
    (Pipeline.validatedMainFrame root) [] Pipeline.validatedMainSource = .ok function
  first : Ixon.Eval.apply (Pipeline.validatedEvalCtx constants config) firstFuel function left = .ok intermediate
  second : Ixon.Eval.apply (Pipeline.validatedEvalCtx constants config) secondFuel intermediate right = .ok result
  leftRel : @Sim.InlinedValRel (Pipeline.validatedEvalCtx constants config)
    { env := IxIR0.Env.ofList source.erasure.result.raw } left rawLeft source.memberScope
  rightRel : @Sim.InlinedValRel (Pipeline.validatedEvalCtx constants config)
    { env := IxIR0.Env.ofList source.erasure.result.raw } right rawRight source.memberScope
  leftRep : Represents selected.primitives.arithmetic rawLeft a
  rightRep : Represents selected.primitives.arithmetic rawRight b

/-- Every compiled binary source function returns safely from its actual
ELF for every pair of runtime Words and every sufficiently mapped stack.
Success refines the source Nat; overflow returns the explicit fallback tag. -/
theorem Compiled.sourceReturns
    {constants : List (Address × Constant)} {root : Address} {config : Pipeline.Config} {eraseFuel lowerFuel : Nat}
    {source : Pipeline.ValidatedCompilation constants root config .shared eraseFuel lowerFuel}
    (compiled : Compiled source) (left right : Word) {sourceResult : Ixon.Eval.Value}
    (invocation : Invocation source compiled.selected left.toNat right.toNat sourceResult)
    (stack : Stack) (depth : compiled.selected.scalar.program.entry < stack.depth) (core : Core)
    (stackPointer : core.readReg .rsp = stack.layout.address stack.frame.top)
    (arguments : ArgumentsAt #[left, right] ⟨core.registers, fun index => core.memory.read64 (stack.layout.address index)⟩)
    (readable : ∀ index < stack.layout.slots, Memory.rangeAllowed core.memory.readable (stack.layout.address index) 8 = true)
    (writable : ∀ index < stack.layout.slots, Memory.rangeAllowed core.memory.writable (stack.layout.address index) 8 = true)
    (base : Word) (flags : ByteEval.Flags) :
    ∃ result, Nonempty (ObjectResult compiled.object.bytes compiled.input.exportName base flags core stack result) ∧
      ∀ word, result = some word → ∃ rawResult,
        @Sim.InlinedValRel (Pipeline.validatedEvalCtx constants config)
          { env := IxIR0.Env.ofList source.erasure.result.raw } sourceResult rawResult source.memberScope ∧
        Represents compiled.selected.primitives.arithmetic rawResult word.toNat := by
  obtain ⟨result, evaluated, native⟩ := compiled.nativeReturns left right stack depth core stackPointer arguments readable writable base flags
  refine ⟨result, native, ?_⟩
  intro word success
  have exactNat := evaluated.exact word success
  apply compiled.selected.sourceApplies source invocation.oracles invocation.contextWF invocation.functionWF
    invocation.leftWF invocation.rightWF invocation.entry invocation.first invocation.second
    invocation.leftRel invocation.rightRel invocation.leftRep invocation.rightRep
  simpa using exactNat

end Ix.Compiler.X86.Scalar.Source
