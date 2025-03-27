namespace Keccak

@[never_extract, extern "c_rs_keccak256_hash"]
opaque hash : (input: @& ByteArray) → ByteArray

end Keccak
