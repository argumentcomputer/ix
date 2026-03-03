use lean_sys::object::LeanByteArray;

/// `@& ByteArray → @& ByteArray → Bool`
/// Efficient implementation for `BEq ByteArray`
#[unsafe(no_mangle)]
extern "C" fn rs_byte_array_beq(a: LeanByteArray, b: LeanByteArray) -> bool {
  a.as_bytes() == b.as_bytes()
}
