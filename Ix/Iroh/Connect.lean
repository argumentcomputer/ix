namespace Iroh.Connect

-- inductive Request where
-- | put (filePath : String)
-- | get (hash: String)

@[never_extract, extern "c_rs_iroh_put"]
private opaque putBytes' : @& String → @& String → @& String → @& String → Except String Unit
--private opaque putBytes' : @& String → @& Array String → @& String → @& String → Except String Unit

--def putBytes (nodeId : @& String) (addrs : @& Array String) (relayUrl : @& String) (filePath : @& String) : IO Unit := do
def putBytes (nodeId : @& String) (addrs : @& String) (relayUrl : @& String) (filePath : @& String) : IO Unit := do
  match putBytes' nodeId addrs relayUrl filePath with
  | .ok () => return
  | .error e => throw (IO.userError e)

@[never_extract, extern "c_rs_iroh_get"]
--private opaque getBytes' : @& String → @& Array String → @& String → @& String → Except String Unit
private opaque getBytes' : @& String → @& String → @& String → @& String → Except String Unit

--def getBytes (nodeId : @& String) (addrs : @& Array String) (relayUrl : @& String) (hash : @& String) : IO Unit := do
def getBytes (nodeId : @& String) (addrs : @& String) (relayUrl : @& String) (hash : @& String) : IO Unit := do
  match getBytes' nodeId addrs relayUrl hash with
  | .ok () => return
  | .error e => throw (IO.userError e)

end Iroh.Connect
