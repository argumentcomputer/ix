use lean_ffi::object::{LeanBorrowed, LeanByteArray};

/// `@& ByteArray → @& ByteArray → Bool`
/// Efficient implementation for `BEq ByteArray`
#[unsafe(no_mangle)]
extern "C" fn rs_byte_array_beq(
  a: LeanByteArray<LeanBorrowed<'_>>,
  b: LeanByteArray<LeanBorrowed<'_>>,
) -> bool {
  a.as_bytes() == b.as_bytes()
}
