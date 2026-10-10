import Ix.CompileCert.Publication
import IxC.Fixtures.IxonFixtures

/-! Controls for anonymous publication compatibility. These are finite
controls for the checked store boundary, not compiler/source correctness. -/

namespace Tests.Ix.CompileCert.Publication

open _root_.Ix.CompileM _root_.Ix.CompileCert.Publication
open Tests.Ix.Kernel.IxonFixtures

private def payload : ByteArray := Ixon.ser identity
private def changedPayload : ByteArray := Ixon.ser sharedIdentity
private def key : Address := address 17
private def otherKey : Address := address 18
private def sourceName : Ix.Name := .anonymous (address 19)

private def result : BlockResult :=
  { block := identity, blockBytes := payload, blockAddr := key }

private def empty : DriverAcc := { cenv := default }
private def matching : DriverAcc :=
  { cenv := { empty.cenv with constants := ({} : Store).insert key payload } }
private def conflicting : DriverAcc :=
  { cenv := { empty.cenv with constants := ({} : Store).insert key changedPayload } }

#guard payload != changedPayload
#guard checkPublication empty result {}
#guard checkPublication matching result {}
#guard !checkPublication conflicting result {}
#guard (mergeCompiledBlock matching sourceName result {}).cenv.constants[key]? == some payload

-- Name-claim validation does not establish anonymous content compatibility.
#guard (checkBlockClaims conflicting.cenv (primaryClaims sourceName result) {}).isOk
#guard (mergeCompiledBlock conflicting sourceName result {}).cenv.constants[key]? == some payload

-- Repeated identical content is allowed; a conflicting write inside the
-- same unit is rejected even when the old store did not contain the key.
#guard checkWrites {} [(key, payload), (key, payload)]
#guard !checkWrites {} [(key, payload), (key, changedPayload)]
#guard checkPublication empty result { auxConsts := #[(key, identity)] }
#guard !checkPublication empty result { auxConsts := #[(key, sharedIdentity)] }
#guard checkPublication empty result { auxConsts := #[(otherKey, sharedIdentity)] }

-- Constants and literal blobs are separate address spaces.
#guard checkPublication matching result
  { blockBlobs := ({} : Store).insert key changedPayload }
#guard !checkPublication
  { cenv := { matching.cenv with blobs := ({} : Store).insert key payload } } result
  { blockBlobs := ({} : Store).insert key changedPayload }
#guard checkPublication
  { cenv := { matching.cenv with blobs := ({} : Store).insert key payload } } result
  { blockBlobs := ({} : Store).insert key payload }

-- Presentation-only output does not add an anonymous record write.
#guard recordWrites result { auxNamed := #[(sourceName, { addr := otherKey })] } ==
  recordWrites result {}

end Tests.Ix.CompileCert.Publication
