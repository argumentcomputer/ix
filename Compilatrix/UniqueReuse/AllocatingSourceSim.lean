import Compilatrix.UniqueReuse.AllocatingObjectSim
import Compilatrix.UniqueReuse.RuntimeObjectSpace

namespace Compilatrix.UniqueReuse.Runtime.AllocatingNative

open Compilatrix.Ixon (Address Constant)
open Compilatrix.X86 Compilatrix.X86.UniqueABI Compilatrix.X86.UniqueExecution

variable {constants : List (Address × Constant)} {entry : Pipeline.ClosedEntry}
  {config : Pipeline.Config} {checkFuel eraseFuel : Nat} {limits : IxIR2.Validate.Limits}

structure ObjectResult {compilation : Compilation constants entry config checkFuel eraseFuel limits}
    (output : Output compilation) (sourceResult : Ixon.Eval.Value) (values : List Word)
    (layout : Layout) (before : State) (outside memory : Memory) (stack : Allocating.Stack layout)
    (main release : Object) (base returnAddress : Word) (flags : ByteEval.Flags) : Prop where
  source : @Sim.InlinedValRel (Pipeline.validatedEvalCtx constants config)
    { env := IxIR0.Env.ofList compilation.erased.erasure.result.raw }
    sourceResult (IxIR0.UniqueReverse.listValue compilation.schema ((values.map UInt64.toNat).reverse)) compilation.erased.memberScope
  target : ∀ (before : IxIR2.Eval.Store) (argument : IxIR1.RVal) (heapFuel : Nat),
    Target.Input compilation.schema (values.map UInt64.toNat) before argument →
    ∃ result,
      IxIR2.Eval.runFunction (Target.context compilation.schema true) .physical (targetEntry compilation.schema) #[argument]
        (Target.controlCost true values.length) heapFuel before = .ok result ∧
      UniqueReuse.Target.MainResult { schema := compilation.schema, values := values.map UInt64.toNat } true .physical
        result.store result.value ∧ result.controlRemaining = 0 ∧ result.heapRemaining = heapFuel
  mainProvenance : (ELFRead.parse main.bytes).map ELFRead.View.provenance =
    some (ELF.expectedProvenance (.ixir1Policy output.base.graph Native.loweringVersion (policyVersion .main output.base.foldCounters)))
  releaseProvenance : (ELFRead.parse release.bytes).map ELFRead.View.provenance =
    some (ELF.expectedProvenance (.ixir1Policy output.base.graph Native.loweringVersion (policyVersion .release output.base.foldCounters)))
  mainIdentity : main.policyBytes = output.policyBytes .main ∧ main.policyIdentity = output.identity .main
  releaseIdentity : release.policyBytes = output.policyBytes .release ∧ release.policyIdentity = output.identity .release
  native : ∃ returned reclaimed returnedMemory reclaimedMemory mainCount releaseCount byteReturned byteReclaimed,
    ByteExecution main release layout values before memory outside stack base returnAddress flags
      returned reclaimed returnedMemory reclaimedMemory mainCount releaseCount byteReturned byteReclaimed

/-- A successful ordinary source application reaches the actual emitted ELF
pair for every admitted runtime Word list. The arena budget includes the live
caller reservation and callee allocation; the separate finite stack has 16
bytes below the external return slot. Release consumes the actual byte result. -/
theorem Output.sourceRefinesObjects {compilation : Compilation constants entry config checkFuel eraseFuel limits}
    (output : Output compilation) {functionFuel applyFuel : Nat} {function argument sourceResult : Ixon.Eval.Value}
    {values : List Word} {layout : Layout} {state : State} {outside memory : Memory}
    (relation : Native.ByteArgumentRel compilation argument values layout state outside memory)
    (oracles : @Sim.OracleRel compilation.erased.memberScope (Pipeline.validatedEvalCtx constants config).inlineSharing
      { env := IxIR0.Env.ofList compilation.erased.erasure.result.raw })
    (contextWF : (Pipeline.validatedEvalCtx constants config).SharingWF)
    (evaluated : Ixon.Eval.eval (Pipeline.validatedEvalCtx constants config) functionFuel entry.frame [] entry.source = .ok function)
    (applied : Ixon.Eval.apply (Pipeline.validatedEvalCtx constants config) applyFuel function argument = .ok sourceResult)
    (stack : Allocating.Stack layout) (pointer : state.registers .rsp = stack.top) (available : stack.Available memory)
    (main release : Object) (mainEmitted : output.emit .main = .ok main) (releaseEmitted : output.emit .release = .ok release)
    (base returnAddress : Word) (flags : ByteEval.Flags) (caller : memory.read64? stack.top = .ok returnAddress) :
    ObjectResult output sourceResult values layout state outside memory stack main release base returnAddress flags := by
  have mainSpec := output.emit_spec .main mainEmitted
  have releaseSpec := output.emit_spec .release releaseEmitted
  refine ⟨compilation.sourceRefines oracles contextWF evaluated relation.sourceWF relation.source applied, ?_,
    ?_, ?_, ⟨mainSpec.2.2.1, mainSpec.2.2.2.1⟩, ⟨releaseSpec.2.2.1, releaseSpec.2.2.2.1⟩, ?_⟩
  · intro before targetArgument heapFuel input
    have result := compilation.targetRuns (values.map UInt64.toNat) before targetArgument heapFuel input .physical
    simpa [output.base.reuseSelected] using result
  · simpa [mainSpec.2.1] using main.provenance_parsed
  · simpa [releaseSpec.2.1] using release.provenance_parsed
  · exact byte_execution layout values state relation.input ((layout.enough_bytes_iff _).mp relation.capacity)
      stack pointer outside memory relation.represented available returnAddress caller main release mainSpec.1 releaseSpec.1 base flags

end Compilatrix.UniqueReuse.Runtime.AllocatingNative
