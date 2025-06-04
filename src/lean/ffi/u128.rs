use binius_field::{BinaryField64b as B64, BinaryField128b as B128, Field};

use super::to_raw;

#[unsafe(no_mangle)]
extern "C" fn rs_add_u128_in_binary_field(a: &u128, b: &u128) -> *const u128 {
    let a = B128::new(*a);
    let b = B128::new(*b);
    let c = a + b;
    to_raw(c.val())
}

#[unsafe(no_mangle)]
extern "C" fn rs_mul_u128_in_binary_field(a: &u128, b: &u128) -> *const u128 {
    let a = B128::new(*a);
    let b = B128::new(*b);
    let c = a * b;
    to_raw(c.val())
}

#[unsafe(no_mangle)]
extern "C" fn rs_mul_u64_in_binary_field(a: u64, b: u64) -> u64 {
    let a = B64::new(a);
    let b = B64::new(b);
    let c = a * b;
    c.val()
}

#[unsafe(no_mangle)]
extern "C" fn rs_pow_u64_in_binary_field(a: u64, b: u64) -> u64 {
    let a = B64::new(a);
    let c = a.pow([b]);
    c.val()
}

#[unsafe(no_mangle)]
extern "C" fn rs_inv_u64_in_binary_field(a: u64) -> u64 {
    let a = B64::new(a);
    let c = a.invert().unwrap_or(B64::new(0));
    c.val()
}
