use binius_field::BinaryField128b as B128;

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
