use super::sarray::LeanSArrayObject;

/// `UInt32 → UInt32 → UInt32`
#[no_mangle]
extern "C" fn add_u32s(a: u32, b: u32) -> u32 {
    a + b
}

/// `@& ByteArray → UInt8`
#[no_mangle]
extern "C" fn byte_array_sum(o: &LeanSArrayObject) -> u8 {
    o.data().iter().fold(0, |acc, x| x.overflowing_add(acc).0)
}

/// `USize → ByteArray`
#[no_mangle]
extern "C" fn byte_array_zeros(len: usize) -> *const LeanSArrayObject {
    LeanSArrayObject::from_slice(&vec![0; len])
}

/// `@& ByteArray → @& ByteArray → Bool`
#[no_mangle]
extern "C" fn byte_array_beq(a: &LeanSArrayObject, b: &LeanSArrayObject) -> bool {
    a.data() == b.data()
}
