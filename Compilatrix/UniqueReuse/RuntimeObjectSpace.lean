import Compilatrix.UniqueReuse.RuntimeObjectSim
import Compilatrix.X86.ArenaSpace

/-! A byte-budget input contract for the emitted native object pair. -/

namespace Compilatrix.UniqueReuse.Runtime.Native

open Compilatrix.Ixon (Address Constant)
open Compilatrix.X86 Compilatrix.X86.UniqueABI Compilatrix.X86.UniqueExecution

variable {constants : List (Address × Constant)} {entry : Pipeline.ClosedEntry}
  {config : Pipeline.Config} {checkFuel eraseFuel : Nat} {limits : IxIR2.Validate.Limits}

structure ByteArgumentRel (compilation : Compilation constants entry config checkFuel eraseFuel limits)
    (argument : Ixon.Eval.Value) (values : List Word) (layout : Layout) (state : State) (outside memory : Memory) : Prop where
  sourceWF : argument.SharingWF
  source : @Sim.InlinedValRel (Pipeline.validatedEvalCtx constants config)
    { env := IxIR0.Env.ofList compilation.erased.erasure.result.raw }
    argument (IxIR0.UniqueReverse.listValue compilation.schema (values.map UInt64.toNat)) compilation.erased.memberScope
  input : RuntimeExecution.Input layout values state
  capacity : requiredBytes values.length ≤ layout.bytes
  represented : Realizes layout outside state.words memory

theorem ByteArgumentRel.toArgumentRel {compilation : Compilation constants entry config checkFuel eraseFuel limits}
    {argument : Ixon.Eval.Value} {values : List Word} {layout : Layout} {state : State} {outside memory : Memory}
    (relation : ByteArgumentRel compilation argument values layout state outside memory) :
    ArgumentRel compilation argument values layout state outside memory :=
  ⟨relation.sourceWF, relation.source, relation.input,
    (layout.enough_bytes_iff _).mp relation.capacity, relation.represented⟩

/-- Exactly `80 + 32 * (n + 2)` admitted arena bytes suffice for source
refinement, actual ELF execution and complete release. The caller's return
slot remains a separate eight-byte stack requirement. -/
theorem Output.sourceRefinesObjects_of_bytes {compilation : Compilation constants entry config checkFuel eraseFuel limits}
    (output : Output compilation) {functionFuel applyFuel : Nat} {function argument sourceResult : Ixon.Eval.Value}
    {values : List Word} {layout : Layout} {state : State} {outside memory : Memory}
    (relation : ByteArgumentRel compilation argument values layout state outside memory)
    (oracles : @Sim.OracleRel compilation.erased.memberScope (Pipeline.validatedEvalCtx constants config).inlineSharing
      { env := IxIR0.Env.ofList compilation.erased.erasure.result.raw })
    (contextWF : (Pipeline.validatedEvalCtx constants config).SharingWF)
    (evaluated : Ixon.Eval.eval (Pipeline.validatedEvalCtx constants config) functionFuel entry.frame [] entry.source = .ok function)
    (applied : Ixon.Eval.apply (Pipeline.validatedEvalCtx constants config) applyFuel function argument = .ok sourceResult)
    (runtime : X86.Runtime) (main release : Object)
    (mainEmitted : output.emit .main = .ok main) (releaseEmitted : output.emit .release = .ok release)
    (base returnAddress : Word) (flags : ByteEval.Flags)
    (caller : CallerSlot layout (state.registers .rsp) memory returnAddress) :
    ObjectResult output sourceResult values layout state outside memory runtime main release base returnAddress flags :=
  output.sourceRefinesObjects relation.toArgumentRel oracles contextWF evaluated applied runtime main release
    mainEmitted releaseEmitted base returnAddress flags caller

end Compilatrix.UniqueReuse.Runtime.Native
