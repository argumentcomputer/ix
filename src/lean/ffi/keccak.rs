use crate::lean::sarray::LeanSArrayObject;
use tiny_keccak::{Hasher, Keccak};

#[unsafe(no_mangle)]
extern "C" fn rs_keccak256_hash(input: &LeanSArrayObject, output: &mut LeanSArrayObject) {
    let input = input.data();
    let mut res = [0; 32];
    let mut hasher = Keccak::v256();
    hasher.update(input);
    hasher.finalize(&mut res);
    output.set_data(&res);
}
