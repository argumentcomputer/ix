import MultiStark.BN.KzgBlake3
import MultiStark.BN.KzgIO
import MultiStark.BN.KzgTranscript
import MultiStark.BN.KzgDeserialize
import MultiStark.BN.KzgShape
import MultiStark.BN.KzgAlgebra
import MultiStark.BN.KzgMsm
import MultiStark.BN.KzgPcs
import MultiStark.BN.KzgAccumulator
import MultiStark.BN.KzgVerifier
import MultiStark.BN.CompressBN
import Aiur.Library.Blake3.BN254
import Aiur.Library.Field.BN254.G1
import Aiur.Library.Field.BN254.G1Encoding
import Aiur.Artifact
import Aiur.Trace.Export

/-! Compiler entry points for native-Fr KZG verification and recursive
compression. Pairing operands remain explicit outputs until a terminal
program checks them against the policy's trusted G2 anchors. -/
namespace MultiStark.BN
open Aiur

abbrev F := Library.Field.BN254.F
abbrev modulus := Library.Field.BN254.modulus

def verifierEntry := "KzgVerifier::verify_deferred"
def compressionEntry := "CompressBN::compress_v1"

def source : Modules.Program Nat :=
  Source.kzgBlake3.append Source.kzgIO |>.append Source.kzgTranscript
    |>.append Source.kzgDeserialize |>.append Source.kzgShape |>.append Source.kzgAlgebra
    |>.append Source.kzgMsm |>.append Source.kzgPcs |>.append Source.kzgAccumulator
    |>.append Source.kzgVerifier |>.append Source.compressBN

def libraries : Modules.Program Nat :=
  Library.Blake3.templates.append Library.Field.BN254.Fq.declarations
    |>.append Library.Field.BN254.G1.declarations
    |>.append Library.Field.BN254.G1Encoding.declarations

#aiur_check libraries.append source

def program : Modules.Program F :=
  Library.Blake3.BN254.program.append (Library.Field.BN254.Fq.declarations.toField F)
    |>.append (Library.Field.BN254.G1.declarations.toField F)
    |>.append (Library.Field.BN254.G1Encoding.declarations.toField F)
    |>.append (source.toField F)

def compilePackage (trace : Bool := true) (entries : List String := [compressionEntry]) : IO ByteArray := do
  let prepared ← IO.ofExcept (Modules.prepare program entries)
  let exported ← IO.ofExcept prepared.exportExecution
  let (exported, circuits) ← if trace then do
      let (exported, circuits) ← Trace.exportPlanParallelWide modulus ZMod.val
        prepared.environment.source prepared.entries exported
      pure (exported, some circuits)
    else pure (exported, none)
  IO.ofExcept (Artifact.packageWide exported modulus ZMod.val circuits)

end MultiStark.BN
