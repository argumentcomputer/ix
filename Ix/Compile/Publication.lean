module
public import Ix.CompileM
public section

/-! # Anonymous publication

A compiled block's records and blobs are published into content-keyed tables
(`CompileEnv.constants`, `CompileEnv.blobs`). A reused address must hold
exactly the same bytes: digest injectivity is not assumed, and identical
payloads may share an address. The drivers check a block's writes against the
published tables before merging it (`Ix.CompileM.checkCompiledBlock`), as the
Rust compiler compares and inserts under one map entry
(`CompileState::store_const`, `store_blob`). -/

namespace Ix.CompileM

/-- Exact anonymous writes made by the aux-aware driver's block merge. -/
def blockRecordWrites (result : BlockResult) (cache : BlockState) :
    List (Address × ByteArray) :=
  (result.blockAddr, result.blockBytes) ::
    (result.projections.toList.map fun (_, projection, _) =>
      (Address.admissionHash (Ixon.ser projection), Ixon.ser projection)) ++
    (cache.auxConsts.toList.map fun (address, constant) => (address, Ixon.ser constant))

/-- Check successive writes against a small store of already-seen payloads. -/
def checkContentWrites (seen : Std.HashMap Address ByteArray) :
    List (Address × ByteArray) → Bool
  | [] => true
  | (key, bytes) :: rest =>
    contentMatches seen key bytes && checkContentWrites (seen.insert key bytes) rest

/-- Read the prior store without inserting into it: inserting would copy the
whole live map while the driver retains it for the later merge. Only this
unit's writes populate the fresh consistency-check map. -/
def checkAnonymousWrites (before : Std.HashMap Address ByteArray)
    (writes : List (Address × ByteArray)) : Bool :=
  writes.all (fun (key, bytes) => contentMatches before key bytes) &&
    checkContentWrites {} writes

/-- A block's blobs agree with the published ones. -/
def checkBlobContent (cenv : CompileEnv) (cache : BlockState) : Except CompileError Unit :=
  if checkAnonymousWrites cenv.blobs cache.blockBlobs.toList then .ok ()
  else .error (.invalidMutualBlock "anonymous publication: conflicting blob payload")

/-- A block's records and blobs agree with the published ones. -/
def checkBlockContent (cenv : CompileEnv) (result : BlockResult)
    (cache : BlockState) : Except CompileError Unit :=
  if checkAnonymousWrites cenv.constants (blockRecordWrites result cache) then
    checkBlobContent cenv cache
  else .error (.invalidMutualBlock "anonymous publication: conflicting constant payload")

end Ix.CompileM

end
