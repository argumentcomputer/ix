use crate::lean::sarray::LeanSArrayObject;
use tiny_keccak::{Hasher, Keccak};

use super::{drop_raw, to_raw};

#[unsafe(no_mangle)]
extern "C" fn rs_keccak256_hasher_init() -> *const Keccak {
    let hasher = Keccak::v256();
    to_raw(hasher)
}

#[unsafe(no_mangle)]
extern "C" fn rs_keccak256_hasher_free(hasher: *mut Keccak) {
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
    hasher.clone().finalize(&mut data);
    output.set_data(&data);
}
