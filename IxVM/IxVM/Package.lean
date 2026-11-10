import IxVM
import IxVM.FunctionGroups
import Aiur.Artifact
import Aiur.Trace.Export

/-! The compiled IxVM claim program, as the exporter (`ixvm export-claim-trace`)
writes it and as `ix` compiles it in process on a cache miss
(`Ix.FormalCompiler`). Both call `compilePackage`, so they produce the same
bytes for the same program, groups and compiler. -/

namespace IxVM
open Aiur

/-- The claim entry's compiled package (`Aiur.Artifact.package`): its bytecode
and, with `trace`, its certified circuits and population plans, with the
function groups `groups`. -/
def compilePackage (groups : List (String × List String) := IxVM.functionGroups)
    (trace : Bool := true) : IO ByteArray := do
  let entries := [IxVM.entry]
  let exported ← IO.ofExcept (IxVM.source.exportExecution entries)
  let (exported, circuits) ← if trace then do
      let (exported, circuits) ←
        Trace.exportPlanParallel IxVM.modulus ZMod.val IxVM.source entries exported groups
      pure (exported, some circuits)
    else pure (exported, none)
  IO.ofExcept (Artifact.package exported IxVM.modulus ZMod.val circuits)

end IxVM
