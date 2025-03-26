namespace Iroh

namespace Transfer

@[never_extract, extern "c_rs_iroh_send"]
opaque sendBytes : @& ByteArray → IO Unit

@[never_extract, extern "c_rs_iroh_recv"]
opaque recvBytes : (ticket : @& String) → (bufferCapacity : USize) → IO ByteArray

end Transfer
end Iroh

def main : IO Unit := do
  let bytes := ByteArray.mk #[1, 2, 3, 4, 5]
  Iroh.Transfer.sendBytes bytes
  --let bytes' ← Iroh.Transfer.recvBytes "ticket" 5
  --IO.println bytes'
