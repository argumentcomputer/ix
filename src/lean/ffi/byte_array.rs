use crate::lean::sarray::LeanSArrayObject;

/// `USize → ByteArray`
/// This function showcases how we create a Lean `ByteArray` from Rust.
#[unsafe(no_mangle)]
extern "C" fn rs_byte_array_zeros(len: usize) -> *const LeanSArrayObject {
    LeanSArrayObject::from_slice(&vec![0; len])
}

/// `@& ByteArray → @& ByteArray → Bool`
/// Efficient implementation for `BEq ByteArray`
#[unsafe(no_mangle)]
extern "C" fn rs_byte_array_beq(a: &LeanSArrayObject, b: &LeanSArrayObject) -> bool {
    a.data() == b.data()
}
