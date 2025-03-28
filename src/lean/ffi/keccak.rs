use crate::lean::sarray::LeanSArrayObject;
use tiny_keccak::{Hasher, Keccak};

use super::{drop_raw, to_raw};

#[unsafe(no_mangle)]
extern "C" fn rs_keccak256_hash(input: &LeanSArrayObject, output: &mut LeanSArrayObject) {
    let input = input.data();
    let mut res = [0; 32];
    let mut hasher = Keccak::v256();
    hasher.update(input);
    hasher.finalize(&mut res);
    output.set_data(&res);
}

#[unsafe(no_mangle)]
extern "C" fn rs_keccak256_hasher_init() -> *const Keccak {
    let hasher = Keccak::v256();
    to_raw(hasher)
}

#[unsafe(no_mangle)]
extern "C" fn rs_keccak256_hasher_free(hasher: *mut Keccak) {
    println!("Hasher freed");
    drop_raw(hasher);
}

#[unsafe(no_mangle)]
extern "C" fn rs_keccak256_hasher_update(
    hasher: &Keccak,
    input: &LeanSArrayObject,
) -> *const Keccak {
    let mut hasher = hasher.clone();
    hasher.update(input.data());
    to_raw(hasher)
}

#[unsafe(no_mangle)]
extern "C" fn rs_keccak256_hasher_finalize(hasher: &Keccak, output: &mut LeanSArrayObject) {
    let mut data = [0u8; 32];
    // FIXME: This panics with an out of bounds error
    hasher.clone().finalize(&mut data);
    output.set_data(&data);
}
