import MultiStark
import MultiStark.FunctionGroups
import Aiur.Artifact
import Aiur.Trace.Export

/-! The compiled recursive verifier and aggregation programs, as the exporter
(`stark-export export-trace [--aggregate]`) writes them and as `ix` compiles
them in process on a cache miss (`Ix.FormalCompiler`). Both call
`compilePackage`, so they produce the same bytes for the same program, groups
and compiler. -/

namespace MultiStark
open Aiur

/-- The recursive verifier's entry point. -/
def recursionEntry : String := "MultiStark::verify_multi_stark_proof"
/-- The aggregator's entry point. -/
def aggregateEntry : String := "MultiStark::ix_aggr"
/-- The root compression wrapper's entry point. -/
def compressWrapEntry : String := "CompressWrap::verify_root"

/-- The program (`aggregateProgram` with `aggregate`, else
`recursionProgram`), its entry point and its identity digest. -/
def selected (aggregate : Bool) : Modules.Program MultiStark.F × String × String :=
  if aggregate then
    (MultiStark.aggregateProgram, MultiStark.aggregateEntry, MultiStark.aggregateDigest)
  else (MultiStark.recursionProgram, MultiStark.recursionEntry, MultiStark.recursionDigest)

/-- A program's compiled package (`Aiur.Artifact.package`): its
bytecode and, with `trace`, its certified circuits and population plans, with
the function groups `groups`. -/
private def compileSource (source : Modules.Program MultiStark.F) (entry : String)
    (groups : List (String × List String)) (trace : Bool) : IO ByteArray := do
  let prepared ← IO.ofExcept (Modules.prepare source [entry])
  let exported ← IO.ofExcept prepared.exportExecution
  let (exported, circuits) ← if trace then do
      let (exported, circuits) ← Trace.exportPlanParallel MultiStark.modulus ZMod.val
        prepared.environment.source prepared.entries exported groups
      pure (exported, some circuits)
    else pure (exported, none)
  IO.ofExcept (Artifact.package exported MultiStark.modulus ZMod.val circuits)

/-- Compile the selected recursive or aggregation program. -/
def compilePackage (aggregate : Bool)
    (groups : List (String × List String) := MultiStark.functionGroups)
    (trace : Bool := true) : IO ByteArray := do
  let (source, entry, _) := MultiStark.selected aggregate
  compileSource source entry groups trace

/-- Compile the compression wrapper with the same verifier groups and depth pass. -/
def compileCompressWrapPackage
    (groups : List (String × List String) := MultiStark.functionGroups)
    (trace : Bool := true) : IO ByteArray :=
  compileSource compressWrapProgram compressWrapEntry groups trace

end MultiStark
