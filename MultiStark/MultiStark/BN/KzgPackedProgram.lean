import MultiStark.BN.Program
import MultiStark.BN.KzgPackedDeserialize
import MultiStark.BN.KzgPackedShape
import MultiStark.BN.KzgPcsPacked
import MultiStark.BN.KzgPackedVerifier
import MultiStark.BN.CompressBNPacked

/-! The column KZG verifier program extended with the packed-SHPLONK
verifier and the packed accumulator fold. Shared parsing, transcript, algebra
and MSM modules are the column verifier's own. -/
namespace MultiStark.BN.Packed
open Aiur

def verifierEntry := "KzgPackedVerifier::verify_deferred"

def source : Modules.Program Nat :=
  Source.kzgPackedDeserialize.append Source.kzgPackedShape |>.append Source.kzgPcsPacked
    |>.append Source.kzgPackedVerifier |>.append Source.compressBNPacked

#aiur_check MultiStark.BN.libraries.append MultiStark.BN.source |>.append source

def program : Modules.Program MultiStark.BN.F :=
  MultiStark.BN.program.append (source.toField MultiStark.BN.F)

def compilePackage (trace : Bool := true) (entries : List String := [verifierEntry])
    (groups : List (String × List String) := []) (base : Modules.Program MultiStark.BN.F := program) :
    IO ByteArray := do
  let prepared ← IO.ofExcept (Modules.prepare base entries)
  let exported ← IO.ofExcept prepared.exportExecution
  let (exported, circuits) ← if trace then do
      let (exported, circuits) ← Trace.exportPlanParallelWide MultiStark.BN.modulus ZMod.val
        prepared.environment.source prepared.entries exported groups
      pure (exported, some circuits)
    else pure (exported, none)
  IO.ofExcept (Artifact.packageWide exported MultiStark.BN.modulus ZMod.val circuits)

end MultiStark.BN.Packed
