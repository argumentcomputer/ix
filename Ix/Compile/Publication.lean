module
public import Ix.CompileM
public section

namespace Ix.CompileM

/-- Exact anonymous writes made by the aux-aware driver's block merge. -/
def blockRecordWrites (result : BlockResult) (cache : BlockState) :
    List (Address × ByteArray) :=
  (result.blockAddr, result.blockBytes) ::
    (result.projections.toList.map fun (_, projection, _) =>
      (Address.blake3 (Ixon.ser projection), Ixon.ser projection)) ++
    (cache.auxConsts.toList.map fun (address, constant) => (address, Ixon.ser constant))

/-- A reused address must contain exactly the same bytes. Digest injectivity
is not assumed, and identical aliases are allowed. -/
def contentMatches (store : Std.HashMap Address ByteArray)
    (key : Address) (bytes : ByteArray) : Bool :=
  match store[key]? with
  | none => true
  | some old => decide (old = bytes)

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

def checkBlobContent (cenv : CompileEnv) (cache : BlockState) : Except CompileError Unit :=
  if checkAnonymousWrites cenv.blobs cache.blockBlobs.toList then .ok ()
  else .error (.invalidMutualBlock "anonymous publication: conflicting blob payload")

def checkBlockContent (cenv : CompileEnv) (result : BlockResult)
    (cache : BlockState) : Except CompileError Unit :=
  if checkAnonymousWrites cenv.constants (blockRecordWrites result cache) then
    checkBlobContent cenv cache
  else .error (.invalidMutualBlock "anonymous publication: conflicting constant payload")

end Ix.CompileM
