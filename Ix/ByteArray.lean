namespace ByteArray

def beqNoFFI (a b : ByteArray) : Bool :=
  a.data == b.data

@[extern "lean_byte_array_beq"]
def beq : @& ByteArray → @& ByteArray → Bool :=
  beqNoFFI

instance : BEq ByteArray := ⟨ByteArray.beq⟩

end ByteArray
