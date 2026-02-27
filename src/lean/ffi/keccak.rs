use std::ffi::c_void;
use std::sync::OnceLock;

use tiny_keccak::{Hasher, Keccak};

use crate::lean::{
  as_mut_unsafe, as_ref_unsafe, external::LeanExternalObject,
  lean_alloc_external, lean_alloc_sarray, lean_register_external_class,
  noop_foreach, sarray::LeanSArrayObject,
};

use super::{ExternalClassPtr, drop_raw, to_raw};

static KECCAK_CLASS: OnceLock<ExternalClassPtr> = OnceLock::new();

fn get_keccak_class() -> *mut c_void {
  KECCAK_CLASS
    .get_or_init(|| {
      ExternalClassPtr(unsafe {
        lean_register_external_class(keccak_finalizer, noop_foreach)
      })
    })
    .0
}

extern "C" fn keccak_finalizer(ptr: *mut c_void) {
  drop_raw(ptr as *mut Keccak);
}

/// `Keccak.Hasher.init : Unit → Hasher`
#[unsafe(no_mangle)]
extern "C" fn c_rs_keccak256_hasher_init(_unit: *const c_void) -> *mut c_void {
  let hasher = Keccak::v256();
  let ptr = to_raw(hasher) as *mut c_void;
  unsafe { lean_alloc_external(get_keccak_class(), ptr) }
}

/// `Keccak.Hasher.update : (hasher: Hasher) → (input: @& ByteArray) → Hasher`
#[unsafe(no_mangle)]
extern "C" fn c_rs_keccak256_hasher_update(
  hasher_obj: *mut c_void,
  input: &LeanSArrayObject,
) -> *mut c_void {
  let external: &LeanExternalObject = as_ref_unsafe(hasher_obj.cast());
  let hasher: &Keccak = as_ref_unsafe(external.cast_data());
  let mut new_hasher = hasher.clone();
  new_hasher.update(input.data());
  let ptr = to_raw(new_hasher) as *mut c_void;
  unsafe { lean_alloc_external(get_keccak_class(), ptr) }
}

/// `Keccak.Hasher.finalize : (hasher: Hasher) → ByteArray`
#[unsafe(no_mangle)]
extern "C" fn c_rs_keccak256_hasher_finalize(
  hasher_obj: *mut c_void,
) -> *mut c_void {
  let external: &LeanExternalObject = as_ref_unsafe(hasher_obj.cast());
  let hasher: &Keccak = as_ref_unsafe(external.cast_data());
  let mut data = [0u8; 32];
  hasher.clone().finalize(&mut data);
  let arr_ptr = unsafe { lean_alloc_sarray(1, 32, 32) };
  let arr: &mut LeanSArrayObject = as_mut_unsafe(arr_ptr.cast());
  arr.set_data(&data);
  arr_ptr
}
