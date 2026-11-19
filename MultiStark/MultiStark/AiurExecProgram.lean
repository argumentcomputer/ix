import MultiStark.Program
import MultiStark.FunctionGroups
import MultiStark.Modules.AiurExec
import MultiStark.Modules.AiurExecBlock
import MultiStark.Modules.AiurExecTrain
import Aiur.Artifact
import Aiur.Trace.Export

/-! The `aiurExec` aggregator: the recursive verifier's modules and `Aggregation`'s
helpers, with entry point `AiurExec::aiur_exec` (`Modules/AiurExec.lean`). It is a
program of its own, so `aggregateProgram` (`MultiStark::ix_aggr`), its key and
every existing proof are untouched. -/

namespace MultiStark
open Aiur

/-- The aggregator over `module`, an instance of `AiurExec` for one program's claim shape. -/
def aiurExecSourceWith (module : Modules.Program Nat) : Modules.Program Nat :=
  [Source.proofDeserialize, Source.systemDeserialize, Source.pcs, Source.aggregation,
    Source.starkIO, Source.starkHash, Source.mmcs, Source.starkVerifier, Source.transcript,
    module].foldl Modules.Program.append {}

def aiurExecSource : Modules.Program Nat := aiurExecSourceWith Source.aiurExec

/-- The aggregator for `Fixed::train_block` claims. -/
def aiurExecBlockSource : Modules.Program Nat := aiurExecSourceWith Source.aiurExecBlock

/-- The aggregator for `FixedTree::train_tree` claims, the whole run in one execution. -/
def aiurExecTrainSource : Modules.Program Nat := aiurExecSourceWith Source.aiurExecTrain

#aiur_check libraries.append aiurExecSource
#aiur_check libraries.append aiurExecBlockSource
#aiur_check libraries.append aiurExecTrainSource

def aiurExecProgram : Modules.Program F := withLibraries aiurExecSource

def aiurExecBlockProgram : Modules.Program F := withLibraries aiurExecBlockSource

def aiurExecTrainProgram : Modules.Program F := withLibraries aiurExecTrainSource

def aiurExecEntry : String := "AiurExec::aiur_exec"

def aiurExecDigest : String := aiur_eval% hexDigest (reprStr aiurExecProgram)

def aiurExecBlockDigest : String := aiur_eval% hexDigest (reprStr aiurExecBlockProgram)

def aiurExecTrainDigest : String := aiur_eval% hexDigest (reprStr aiurExecTrainProgram)

/-- The verifier's function groups, restricted to functions the program has, plus one group
for this module's own functions. -/
def aiurExecGroups (names : List String) : List (String × List String) :=
  (functionGroups.map fun (g, fs) => (g, fs.filter names.contains)).filter (!·.2.isEmpty)

/-- The compiled package of `program` (`aiurExecProgram` unless given), as `compilePackage`
compiles `ix_aggr`. -/
def compileAiurExecPackage (grouped : Bool := true) (program : Modules.Program F := aiurExecProgram) :
    IO ByteArray := do
  let prepared ← IO.ofExcept (Modules.prepare program [aiurExecEntry])
  let exported ← IO.ofExcept prepared.exportExecution
  let names := exported.bytecode.functions.map (·.name) ++ exported.bytecode.maps.map (·.name)
  let groups := if grouped then aiurExecGroups names else []
  let (exported, circuits) ← Trace.exportPlanParallel MultiStark.modulus ZMod.val
    prepared.environment.source prepared.entries exported groups
  IO.ofExcept (Artifact.package exported MultiStark.modulus ZMod.val (some circuits))

end MultiStark
