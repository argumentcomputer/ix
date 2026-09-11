import Ix.Compiler.IxIR2.PipelineSim
import Ix.Compiler.IxIR2.Interpretation

/-! The validated baseline's exact logical-to-physical execution boundary. -/

namespace Ix.Compiler.IxIR2.Pipeline

/-- The emitted baseline has identical successful main runs under both
interpretations. The attachment supplies the complete instruction inventory
and entry facts; callers supply only the run being transported. -/
theorem CompiledAttachment.mainInterpretation
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    {first second : Eval.Interpretation} {controlFuel heapFuel : Nat}
    {result : Eval.Result}
    (run : Eval.runMain attached.simulationTargetContext first
      attached.target.artifact.program controlFuel heapFuel = .ok result) :
    Eval.runMain attached.simulationTargetContext second
      attached.target.artifact.program controlFuel heapFuel = .ok result :=
  Eval.runMain_creditFree attached.target.creditFree
    attached.target.artifact.mainArity attached.target.artifact.mainNonempty run

/-- Compose the existing logical whole-main theorem with exact baseline
interpretation independence. The source heap and value remain unchanged. -/
theorem CompiledAttachment.successfulPhysicalMainSimulation
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    {sourceFuel : Nat} {sourceOut : IxIR1.Store × IxIR1.RVal}
    (run : IxIR1.runOwnedMain attached.simulationSourceContext
      attached.target.artifact.source.mainResult
      attached.target.artifact.source.main sourceFuel = .ok sourceOut) :
    ∃ controlFuel heapFuel targetOut,
      Eval.runMain attached.simulationTargetContext .physical
        attached.target.artifact.program controlFuel heapFuel = .ok targetOut ∧
      Lower.Sim.OutcomeRel sourceOut targetOut := by
  obtain ⟨controlFuel, heapFuel, targetOut, logicalRun, related⟩ :=
    attached.successfulCanonicalMainSimulation run
  exact ⟨controlFuel, heapFuel, targetOut, attached.mainInterpretation logicalRun, related⟩


/-! Existing theorem names remain available for direct application. -/
namespace Attached
export CompiledAttachment (
  mainInterpretation
  successfulPhysicalMainSimulation)
end Attached

end Ix.Compiler.IxIR2.Pipeline
