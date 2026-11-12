import MultiStark.Program
import MultiStark.FunctionGroups
import Aiur.Library.Blake3.BN254
import Aiur.Library.Field.Goldilocks.Emulated
import Aiur.Artifact
import Aiur.Trace.Export

/-! The generic Goldilocks root verifier compiled over BN254 Fr. The root key
and claims are data authenticated by the same domain-separated statement as
CompressWrap; only the arithmetic provider and outer proving field change. -/
namespace MultiStark.CompressGL
open Aiur

abbrev F := Library.Field.BN254.F
abbrev modulus := Library.Field.BN254.modulus

def entry : String := "CompressGL::verify_root"

def source : Modules.Program Nat :=
  MultiStark.compressWrapSource.append (aiur⟦ module CompressGL = CompressWrap; ⟧)

def libraries : Modules.Program Nat :=
  Library.Blake3.templates.append Library.Option.declarations
    |>.append Library.Field.Goldilocks.Emulated.declarations

#aiur_check libraries.append source

def program : Modules.Program F :=
  Library.Blake3.BN254.program.append (Library.Option.declarations.toField F)
    |>.append Library.Field.Goldilocks.Emulated.program
    |>.append (source.toField F)

def compilePackage (trace : Bool := true)
    (groups : List (String × List String) := MultiStark.functionGroups) : IO ByteArray := do
  let prepared ← IO.ofExcept (Modules.prepare program [entry])
  let exported ← IO.ofExcept prepared.exportExecution
  let (exported, circuits) ← if trace then do
      let (exported, circuits) ← Trace.exportPlanParallelWide modulus ZMod.val
        prepared.environment.source prepared.entries exported groups
      pure (exported, some circuits)
    else pure (exported, none)
  IO.ofExcept (Artifact.packageWide exported modulus ZMod.val circuits)

end MultiStark.CompressGL
