namespace Keccak

private opaque GenericNonempty : NonemptyType

def Hasher : Type := GenericNonempty.type

instance : Nonempty Hasher := GenericNonempty.property

namespace Hasher

@[never_extract, extern "c_rs_keccak256_hash"]
opaque hash : (input: @& ByteArray) → ByteArray

@[never_extract, extern "c_rs_keccak256_hasher_init"]
opaque init : Unit → Hasher

@[never_extract, extern "c_rs_keccak256_hasher_update"]
opaque update : (hasher: Hasher) → (input: @& ByteArray) → Hasher

@[never_extract, extern "c_rs_keccak256_hasher_finalize"]
opaque finalize : (hasher: Hasher) → ByteArray

end Hasher

end Keccak
