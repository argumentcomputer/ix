use sha2::{Digest, Sha256};
use std::ffi::c_void;

use crate::lean::{as_mut_unsafe, lean_alloc_sarray, sarray::LeanSArrayObject};

#[unsafe(no_mangle)]
extern "C" fn rs_sha256(bytes: &LeanSArrayObject) -> *mut c_void {
  let mut hasher = Sha256::new();
  hasher.update(bytes.data());
  let digest = hasher.finalize();
  let digest_slice = digest.as_slice();
  assert_eq!(digest_slice.len(), 32);
  let arr_ptr = unsafe { lean_alloc_sarray(1, 32, 32) };
  let arr: &mut LeanSArrayObject = as_mut_unsafe(arr_ptr.cast());
  arr.set_data(digest_slice);
  arr_ptr
}
