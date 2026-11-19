import MultiStark.Program
import MultiStark.FunctionGroups
import MultiStark.Modules.AiurExec
import Aiur.Artifact
import Aiur.Trace.Export

/-! The `aiurExec` aggregator: the recursive verifier's modules and `Aggregation`'s
helpers, with entry point `AiurExec::aiur_exec` (`Modules/AiurExec.lean`). It is a
program of its own, so `aggregateProgram` (`MultiStark::ix_aggr`), its key and
every existing proof are untouched. -/

namespace MultiStark
open Aiur

def aiurExecSource : Modules.Program Nat :=
  [Source.proofDeserialize, Source.systemDeserialize, Source.pcs, Source.aggregation,
    Source.starkIO, Source.starkHash, Source.mmcs, Source.starkVerifier, Source.transcript,
    Source.aiurExec].foldl Modules.Program.append {}

#aiur_check libraries.append aiurExecSource

def aiurExecProgram : Modules.Program F := withLibraries aiurExecSource

def aiurExecEntry : String := "AiurExec::aiur_exec"

def aiurExecDigest : String := aiur_eval% hexDigest (reprStr aiurExecProgram)

/-- The verifier's function groups, restricted to functions the program has, plus one group
for this module's own functions. -/
def aiurExecGroups (names : List String) : List (String × List String) :=
  (functionGroups.map fun (g, fs) => (g, fs.filter names.contains)).filter (!·.2.isEmpty)

/-- The compiled package, as `compilePackage` compiles `ix_aggr`. -/
def compileAiurExecPackage (grouped : Bool := true) : IO ByteArray := do
  let prepared ← IO.ofExcept (Modules.prepare aiurExecProgram [aiurExecEntry])
  let exported ← IO.ofExcept prepared.exportExecution
  let names := exported.bytecode.functions.map (·.name) ++ exported.bytecode.maps.map (·.name)
  let groups := if grouped then aiurExecGroups names else []
  let (exported, circuits) ← Trace.exportPlanParallel MultiStark.modulus ZMod.val
    prepared.environment.source prepared.entries exported groups
  IO.ofExcept (Artifact.package exported MultiStark.modulus ZMod.val (some circuits))

end MultiStark
