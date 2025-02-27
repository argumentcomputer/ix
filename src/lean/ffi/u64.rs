use crate::lean::sarray::LeanSArrayObject;

#[no_mangle]
extern "C" fn rs_u64_to_le_bytes(u: u64) -> *const LeanSArrayObject {
    LeanSArrayObject::from_slice(&u.to_le_bytes())
}
