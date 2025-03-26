import Cli

namespace Iroh

namespace Transfer

@[never_extract, extern "c_rs_iroh_send"]
opaque sendBytes : @& ByteArray → IO Unit

@[never_extract, extern "c_rs_iroh_recv"]
opaque recvBytes : (ticket : @& String) → (bufferCapacity : USize) → IO ByteArray

end Transfer
end Iroh
