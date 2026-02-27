use std::ffi::c_void;

use crate::lean::lean_sarray_data;

/// `@& ByteArray → @& ByteArray → Bool`
/// Efficient implementation for `BEq ByteArray`
#[unsafe(no_mangle)]
extern "C" fn rs_byte_array_beq(a: *const c_void, b: *const c_void) -> bool {
  lean_sarray_data(a) == lean_sarray_data(b)
}
