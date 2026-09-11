import Ix.Compiler.PipelineSound
import Ix.Compiler.SimApply

/-! Runtime application contracts derived from a validated compilation.
The stored function graph and source application trace supply the semantic
inputs; compiler-owned value, progress, and ownership contracts are closed
from the retained lowering run. -/

namespace Ix.Compiler.Pipeline.ValidatedCompilation
open Ix.Compiler.Ixon (Address Constant Owned)
open Ix.Compiler.IxIR1 Ix.Compiler.IxIR1.Lower Ix.Compiler.IxIR1.LowerSim

variable {constants : List (Address × Constant)} {root : Address} {config : Config}
  {world : Owned} {eraseFuel lowerFuel : Nat}

private theorem runtimeLowerRun
    (source : ValidatedCompilation constants root config world eraseFuel lowerFuel) :
    (lowerAllAction source.erasure.result.declarations source.erasure.result.main world lowerFuel).run {} =
      .ok (source.lowering.raw, source.lowering.mainCode) source.lowering.finalState := by
  simpa only [lowerAllIndexedAction_eq_lowerAllAction] using source.lowering.lowerRun

theorem runtimeValueContracts
    (source : ValidatedCompilation constants root config world eraseFuel lowerFuel) :
    CompilerValueContracts source.functionRel source.addressedSourceCtx
      (IxIR0.Env.ofList source.erasure.result.declarations) (source.exactTargetCtx (fun _ _ => none)) :=
  lowerAllAction_compilerValueContracts rfl source.runtimeLowerRun
    (fun member => source.exactTargetCtx_decls_of_mem (fun _ _ => none) member)
    (source.exactExtraRepresented (fun _ _ => none))
    (source.exactCompilerContracts (fun _ _ => none)).1
    (source.externValueContract (fun _ _ => none))

theorem runtimeProgressContracts
    (source : ValidatedCompilation constants root config world eraseFuel lowerFuel) :
    CompilerTraceProgressContracts source.functionRel source.addressedSourceCtx
      (IxIR0.Env.ofList source.erasure.result.declarations) (source.exactTargetCtx (fun _ _ => none)) :=
  lowerAllAction_compilerTraceProgressContracts rfl source.runtimeLowerRun
    (fun member => source.exactTargetCtx_decls_of_mem (fun _ _ => none) member)
    (source.exactExtraRepresented (fun _ _ => none))
    (source.exactCompilerContracts (fun _ _ => none)).1 source.runtimeValueContracts
    (source.externTraceProgressContract (fun _ _ => none))

/-- Runtime closure/application traces cross the same mutual-block address
map as the compiled module entry. -/
theorem runtimeTraceRenames
    (source : ValidatedCompilation constants root config world eraseFuel lowerFuel) :
    IxIR0.Readdress.Ctx.TraceRenames
      (IxIR0.MutualBlock.Renaming.apply source.erasure.result.addressMap)
      source.rawCtx source.addressedSourceCtx := by
  have audit := EraseAddressed.semanticAudit_of_run_eq_ok source.erasure.runEq
  have raw := source.erasure.result.raw_eq_grouped audit
  have contexts := source.erasure.result.addressed.traceRenames_rawCtx
    (source.erasure.result.addressed_audit audit)
    (fun _ _ => none)
    (IxIR0.Readdress.Oracle.readdress source.erasure.result.addressMap (fun _ _ => none))
    (IxIR0.Readdress.Oracle.readdress_compatible
      (IxIR0.Readdress.Oracle.Readdressable.empty source.erasure.result.addressMap))
  simpa only [rawCtx, addressedSourceCtx, EraseAddressed.Result.rawCtx, EraseAddressed.Result.addressMap,
    IxIR0.Readdress.Result.rawCtx, raw] using contexts

/-- Apply a source-related runtime function through the actual compiled
IxIR₁ context. Successful source application implies target termination and
value agreement, while the compiler supplies complete root ownership. -/
theorem runtimeApply
    (source : ValidatedCompilation constants root config world eraseFuel lowerFuel)
    {limit : Nat} {store : Store} {function : RVal} {arguments : List RVal}
    {sourceFunction sourceResult : IxIR0.Value} {sourceArguments : List IxIR0.Value}
    (functionGraph : Sim.ValueGraph source.functionRel store sourceFunction function)
    (argumentsGraph : Sim.ValuesGraph source.functionRel store sourceArguments arguments)
    (trace : IxIR0.ProjectionSafe.AppliesBelow source.addressedSourceCtx limit
      sourceFunction sourceArguments sourceResult)
    (nonempty : sourceArguments ≠ [])
    (ownership : Sim.RootOwnership store (⟨.shared, function⟩ :: Sim.rootsFor .shared arguments)) :
    ∃ fuel output value,
      applyGo (source.exactTargetCtx (fun _ _ => none)) fuel store function arguments = .ok (output, value) ∧
      Sim.ValueGraph source.functionRel output sourceResult value ∧
      Sim.RootOwnership output [⟨.shared, value⟩] := by
  obtain ⟨fuel, output, value, run⟩ := source.runtimeProgressContracts.apply.progresses limit
    functionGraph argumentsGraph trace nonempty Sim.RootsGraph.nil (by simpa using ownership)
  have related := source.runtimeValueContracts.apply.preserves functionGraph argumentsGraph
    (SourceAppliesSafelyBelow.sourceApplies trace) Sim.RootsGraph.nil (by simpa using ownership) run
  have owned := (source.exactCompilerContracts (fun _ _ => none)).1.apply.preserves
    (rest := []) (by simpa using ownership) run
  exact ⟨fuel, output, value, run, related.1, owned⟩

end Ix.Compiler.Pipeline.ValidatedCompilation
