use sha2::{Digest, Sha256};
use std::ffi::c_void;

use crate::lean::{
  lean::lean_alloc_sarray, lean_sarray_data, lean_sarray_set_data,
};

#[unsafe(no_mangle)]
extern "C" fn rs_sha256(bytes: *const c_void) -> *mut c_void {
  let mut hasher = Sha256::new();
  hasher.update(lean_sarray_data(bytes));
  let digest = hasher.finalize();
  let digest_slice = digest.as_slice();
  assert_eq!(digest_slice.len(), 32);
  let arr_ptr = unsafe { lean_alloc_sarray(1, 32, 32) };
  unsafe { lean_sarray_set_data(arr_ptr.cast(), digest_slice) };
  arr_ptr.cast()
}
