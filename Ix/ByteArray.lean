namespace ByteArray

def beqNoFFI (a b : ByteArray) : Bool :=
  a.data == b.data

@[extern "rs_byte_array_beq"]
def beq : @& ByteArray → @& ByteArray → Bool :=
  beqNoFFI

instance : BEq ByteArray := ⟨ByteArray.beq⟩

@[extern "rs_byte_array_zeros"]
opaque zeros : USize → ByteArray

end ByteArray
