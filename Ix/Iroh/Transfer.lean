namespace Iroh

namespace Transfer

@[extern "c_rs_iroh_send"]
opaque sendFile : @& String → USize

@[extern "c_rs_iroh_recv"]
opaque recvFile : @& String → @& String → USize

end Transfer
end Iroh
