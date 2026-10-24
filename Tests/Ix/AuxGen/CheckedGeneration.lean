import Tests.Ix.AuxGen.GenerationRetry
import Tests.Ix.AuxGen.ExplicitKernel

namespace Tests.Ix.AuxGen.CheckedGeneration

/-- The retained M7 boundaries in one CI entry. The dependency evaluator
runs the production factory controls and the nine-target replay once;
PlanCache remains its own registered entry. Exceptions fail the runner. -/
def run : IO UInt32 := do
  IO.println "[checked-generation] original baseline and immutable-state controls"
  GenerationOnlySpike.evaluate
  IO.println "[checked-generation] production factory, dependencies and nine actual retries"
  GenerationOnlyDependencies.evaluate
  IO.println "[checked-generation] driver retry boundary and retained SourceFamily provider"
  GenerationRetry.evaluate
  IO.println "[checked-generation] explicit callers and missing capabilities"
  ExplicitKernel.evaluate
  return 0

end Tests.Ix.AuxGen.CheckedGeneration
