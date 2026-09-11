import Ix.Compiler.UniqueReuse.RuntimeNative
import Ix.Compiler.UniqueReuse.RuntimeSourceSim
import Ix.Compiler.UniqueReuse.RuntimeTarget
import Ix.Compiler.X86.RuntimeInput

namespace Ix.Compiler.UniqueReuse.Runtime.Native

open Ix.Compiler.Ixon (Address Constant)
open Ix.Compiler.X86
open Ix.Compiler.X86.UniqueABI
open Ix.Compiler.X86.UniqueExecution

variable {constants : List (Address × Constant)} {entry : Pipeline.ClosedEntry}
  {config : Pipeline.Config} {checkFuel eraseFuel : Nat} {limits : IxIR2.Validate.Limits}

/-- The source argument and the native input denote the same finite list.
`Word` payloads state exact representation, `Layout` states alignment and
nonwrapping bounds, and `Realizes` supplies permissions and the memory frame.
The caller transfers exclusive ownership of the admitted arena's list cells. -/
structure ArgumentRel (compilation : Compilation constants entry config checkFuel eraseFuel limits)
    (argument : Ixon.Eval.Value) (values : List Word) (layout : Layout) (state : State) (outside memory : Memory) : Prop where
  sourceWF : argument.SharingWF
  source : @Sim.InlinedValRel (Pipeline.validatedEvalCtx constants config)
    { env := IxIR0.Env.ofList compilation.erased.erasure.result.raw }
    argument (IxIR0.UniqueReverse.listValue compilation.schema (values.map UInt64.toNat)) compilation.erased.memberScope
  input : RuntimeExecution.Input layout values state
  capacity : values.length + 2 ≤ layout.capacity
  represented : Realizes layout outside state.words memory

theorem ArgumentRel.graph {compilation : Compilation constants entry config checkFuel eraseFuel limits}
    {argument : Ixon.Eval.Value} {values : List Word} {layout : Layout} {state : State} {outside memory : Memory}
    (relation : ArgumentRel compilation argument values layout state outside memory) :
    NativeList memory (values.map UInt64.toNat) (layout.cell values.length) (RuntimeExecution.downNodes layout values.length) :=
  RuntimeExecution.down_native relation.input.chain relation.represented (by have := relation.capacity; omega)

structure Result {compilation : Compilation constants entry config checkFuel eraseFuel limits}
    (output : Output compilation) (sourceResult : Ixon.Eval.Value) (values : List Word)
    (layout : Layout) (state : State) (outside memory : Memory) (runtime : X86.Runtime) : Prop where
  source : @Sim.InlinedValRel (Pipeline.validatedEvalCtx constants config)
    { env := IxIR0.Env.ofList compilation.erased.erasure.result.raw }
    sourceResult (IxIR0.UniqueReverse.listValue compilation.schema ((values.map UInt64.toNat).reverse)) compilation.erased.memberScope
  target : ∀ (before : IxIR2.Eval.Store) (argument : IxIR1.RVal) (heapFuel : Nat),
    Target.Input compilation.schema (values.map UInt64.toNat) before argument →
    ∃ result,
      IxIR2.Eval.runFunction (Target.context compilation.schema true) .physical (targetEntry compilation.schema) #[argument]
        (Target.controlCost true values.length) heapFuel before = .ok result ∧
      UniqueReuse.Target.MainResult { schema := compilation.schema, values := values.map UInt64.toNat } true .physical
        result.store result.value ∧
      result.controlRemaining = 0 ∧ result.heapRemaining = heapFuel
  native : ∃ returned returnedMemory reclaimed reclaimedMemory,
    RuntimeExecution.Execution layout values state memory outside runtime returned returnedMemory reclaimed reclaimedMemory output.foldCounters

/-- A successful source call refines to the selected physical function and
the single selected native function on every admitted runtime argument. -/
theorem Output.sourceRefines {compilation : Compilation constants entry config checkFuel eraseFuel limits}
    (output : Output compilation) {functionFuel applyFuel : Nat} {function argument sourceResult : Ixon.Eval.Value}
    {values : List Word} {layout : Layout} {state : State} {outside memory : Memory}
    (relation : ArgumentRel compilation argument values layout state outside memory)
    (oracles : @Sim.OracleRel compilation.erased.memberScope (Pipeline.validatedEvalCtx constants config).inlineSharing
      { env := IxIR0.Env.ofList compilation.erased.erasure.result.raw })
    (contextWF : (Pipeline.validatedEvalCtx constants config).SharingWF)
    (evaluated : Ixon.Eval.eval (Pipeline.validatedEvalCtx constants config) functionFuel entry.frame [] entry.source = .ok function)
    (applied : Ixon.Eval.apply (Pipeline.validatedEvalCtx constants config) applyFuel function argument = .ok sourceResult)
    (runtime : X86.Runtime) : Result output sourceResult values layout state outside memory runtime := by
  refine ⟨compilation.sourceRefines oracles contextWF evaluated relation.sourceWF relation.source applied, ?_,
    RuntimeExecution.executes layout values state relation.input relation.capacity outside memory relation.represented runtime⟩
  intro before targetArgument heapFuel input
  have result := compilation.targetRuns (values.map UInt64.toNat) before targetArgument heapFuel input .physical
  simpa [output.reuseSelected] using result

def targetCounts (store : IxIR2.Eval.Store) : Counts :=
  { allocs := store.heap.allocs, frees := store.heap.frees, reuses := store.heap.reuses
    live := store.live, peak := store.peakLiveNodes, payload := store.reusedPayloadUnits }

theorem costsAgree {schema : IxIR0.UniqueReverse.Schema} {values : List Word} {layout : Layout} {before after : State}
    (native : LoopResult layout values.reverse (mainCounts values.length) before after)
    {store : IxIR2.Eval.Store} {value : IxIR1.RVal}
    (target : UniqueReuse.Target.MainResult { schema, values := values.map UInt64.toNat } true .physical store value) :
    CountsAt layout (targetCounts store) after.words := by
  have equal : targetCounts store = mainCounts values.length := by
    simp [targetCounts, target.allocs, target.frees, target.reuses, target.live, target.peak, target.payload,
      UniqueReuse.Target.freshPerCons, UniqueReuse.Target.reusesPerCons, UniqueReuse.Target.inPlace, mainCounts]
  rw [equal]
  exact native.countsAt

end Ix.Compiler.UniqueReuse.Runtime.Native
