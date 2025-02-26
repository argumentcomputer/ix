use super::{drop_raw, to_raw};

#[no_mangle]
extern "C" fn rs_u128_free(ptr: *mut u128) {
    drop_raw(ptr);
}

#[no_mangle]
extern "C" fn rs_u128_of_hi_lo(hi: u64, lo: u64) -> *const u128 {
    to_raw(((hi as u128) << 64) | (lo as u128))
}
