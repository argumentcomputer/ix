namespace Keccak

private opaque GenericNonempty : NonemptyType

def Hasher : Type := GenericNonempty.type

instance : Nonempty Hasher := GenericNonempty.property

namespace Hasher

@[extern "c_rs_keccak256_hasher_init"]
opaque init : Unit → Hasher

@[extern "c_rs_keccak256_hasher_update"]
opaque update : (hasher: Hasher) → (input: @& ByteArray) → Hasher

@[extern "c_rs_keccak256_hasher_finalize"]
opaque finalize : (hasher: Hasher) → ByteArray

end Hasher

end Keccak
