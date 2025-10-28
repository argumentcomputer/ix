use crate::lean::sarray::LeanSArrayObject;

/// `@& ByteArray → @& ByteArray → Bool`
/// Efficient implementation for `BEq ByteArray`
#[unsafe(no_mangle)]
extern "C" fn rs_byte_array_beq(
  a: &LeanSArrayObject,
  b: &LeanSArrayObject,
) -> bool {
  a.data() == b.data()
}
