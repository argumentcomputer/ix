namespace Iroh.Transfer

@[never_extract, extern "c_rs_iroh_send"]
opaque sendBytes' : @& ByteArray → Except String Unit

def sendBytes (bytes: @&ByteArray) : IO Unit :=
  match sendBytes' bytes with
  | .ok () => return
  | .error e => throw (IO.userError e)

@[never_extract, extern "c_rs_iroh_recv"]
private opaque recvBytes' : (ticket : @& String) → (bufferCapacity : USize) → Except String ByteArray

def recvBytes (ticket : @& String) (bufferCapacity : USize) : IO ByteArray :=
  match recvBytes' ticket bufferCapacity with
  | .ok bytes => pure bytes
  | .error e => throw (IO.userError e)

end Iroh.Transfer
