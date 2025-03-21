namespace Iroh

namespace Transfer

@[never_extract, extern "c_rs_iroh_send"]
opaque sendBytes : @& ByteArray → Except String Unit

@[never_extract, extern "c_rs_iroh_recv"]
opaque recvBytes : (ticket : @& String) → (bufferCapacity : USize) → Except String ByteArray

end Transfer
end Iroh
