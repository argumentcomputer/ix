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

-- The production guard keeps the name check and rejects the content conflict.
#guard (checkCompiledBlock empty.cenv sourceName result {}).isOk
#guard (checkCompiledBlock matching.cenv sourceName result {}).isOk
#guard !(checkCompiledBlock conflicting.cenv sourceName result {}).isOk
#guard !(checkCompiledBlock empty.cenv sourceName result
  { auxConsts := #[(key, sharedIdentity)] }).isOk

private def refused :=
  applyAuxBlockOutcome conflicting sourceName (({} : Ix.Set Ix.Name).insert sourceName) (.compiled result {})
#guard refused.2.2
#guard refused.2.1.isEmpty
#guard refused.1.cenv.constants[key]? == some changedPayload
#guard !refused.1.cenv.nameToAddr.contains sourceName
#guard refused.1.cenv.ungrounded.contains sourceName

private def accepted :=
  applyAuxBlockOutcome matching sourceName (({} : Ix.Set Ix.Name).insert sourceName) (.compiled result {})
#guard !accepted.2.2
#guard accepted.1.cenv.constants[key]? == some payload
#guard accepted.1.cenv.nameToAddr[sourceName]? == some key

-- Cross-SCC publication also goes through the same guard.
private def refusedCross := applyAuxBlockOutcome conflicting sourceName {}
  (.promoted (some (sourceName, result, {})) #[sourceName] none none none)
#guard refusedCross.1.cenv.constants[key]? == some changedPayload
#guard !refusedCross.1.cenv.nameToAddr.contains sourceName

-- Original-form promotion stores blobs even though its constants are ephemeral.
private def withBlob : DriverAcc :=
  { cenv := { matching.cenv with blobs := ({} : Store).insert key payload } }
#guard !(promoteOriginalBlock withBlob sourceName result
  { blockBlobs := ({} : Store).insert key changedPayload }).isOk
#guard (promoteOriginalBlock withBlob sourceName result
  { blockBlobs := ({} : Store).insert key payload }).isOk

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
