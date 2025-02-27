use crate::lean::sarray::LeanSArrayObject;

#[no_mangle]
extern "C" fn rs_usize_to_le_bytes(u: usize) -> *const LeanSArrayObject {
    LeanSArrayObject::from_slice(&u.to_le_bytes())
}
