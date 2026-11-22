module

public import Ix.Address

public section

namespace Iroh.Connect

structure PutResponse where
  message: String
  hash: String
  deriving Inhabited

structure GetResponse where
  message: String
  hash: String
  bytes: ByteArray
  deriving Inhabited

/-- Parse `hash` as a canonical 64-character lowercase hexadecimal `Address`.
Rejects any path separators, relative segments, or non-canonical hex strings. -/
def parseCanonicalAddress (hash : String) : Except String Address :=
  match Address.fromString hash with
  | some addr =>
    if toString addr == hash then .ok addr
    else .error s!"invalid hash (expected canonical 64-character lowercase hex): {hash}"
  | none =>
    .error s!"invalid hash (expected canonical 64-character lowercase hex): {hash}"

@[never_extract, extern "rs_iroh_put"]
private opaque putBytes' : @& String → @& Array String → @& String → @& String → Except String PutResponse

def putBytes (nodeId : @& String) (addrs : @& Array String) (relayUrl : @& String) (input : @& String) : IO Unit := do
  match putBytes' nodeId addrs relayUrl input with
  | .ok response => IO.println s!"Pinned hash {response.hash}"
  | .error e => throw (IO.userError e)

@[never_extract, extern "rs_iroh_get"]
private opaque getBytes' : @& String → @& Array String → @& String → @& String → Except String GetResponse

def getBytes (nodeId : @& String) (addrs : @& Array String) (relayUrl : @& String) (hash : @& String) (writeToDisk : Bool): IO Unit := do
  let expectedAddr ← match parseCanonicalAddress hash with
    | .ok addr => pure addr
    | .error e => throw (IO.userError e)
  let canonicalHash := toString expectedAddr
  match getBytes' nodeId addrs relayUrl canonicalHash with
  | .ok response =>
    let actualAddr := Address.blake3 response.bytes
    if actualAddr != expectedAddr then
      throw (IO.userError s!"hash mismatch: expected {canonicalHash}, got {actualAddr}")
    if writeToDisk then
      IO.println s!"Writing bytes to ./{canonicalHash}"
      IO.FS.writeBinFile canonicalHash response.bytes
    else
      match String.fromUTF8? response.bytes with
      | some string => IO.print string
      | none => throw (IO.userError "response bytes are not valid UTF-8")
  | .error e => throw (IO.userError e)

end Iroh.Connect

end
