module

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

@[never_extract, extern "c_rs_iroh_put"]
private opaque putBytes' : @& String → @& Array String → @& String → @& String → Except String PutResponse

def putBytes (nodeId : @& String) (addrs : @& Array String) (relayUrl : @& String) (input : @& String) : IO Unit := do
  match putBytes' nodeId addrs relayUrl input with
  | .ok response => IO.println s!"Pinned hash {response.hash}"
  | .error e => throw (IO.userError e)

@[never_extract, extern "c_rs_iroh_get"]
private opaque getBytes' : @& String → @& Array String → @& String → @& String → Except String GetResponse

def getBytes (nodeId : @& String) (addrs : @& Array String) (relayUrl : @& String) (hash : @& String) (writeToDisk : Bool): IO Unit := do
  match getBytes' nodeId addrs relayUrl hash with
  | .ok response =>
    IO.println s!"Received bytes for hash {response.hash}"
    if writeToDisk then
      IO.println s!"Writing bytes to ./{response.hash}"
      let string := String.fromUTF8! response.bytes
      IO.FS.writeFile response.hash string
  | .error e => throw (IO.userError e)

end Iroh.Connect

end
