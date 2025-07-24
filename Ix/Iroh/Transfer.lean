namespace Iroh.Transfer

@[never_extract, extern "c_rs_iroh_send"]
opaque sendBytes : @& ByteArray → IO Unit

@[never_extract, extern "c_rs_iroh_recv"]
opaque recvBytes : (ticket : @& String) → (bufferCapacity : USize) → IO ByteArray

end Iroh.Transfer
