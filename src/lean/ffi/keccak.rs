use std::ffi::c_void;
use std::sync::OnceLock;

use tiny_keccak::{Hasher, Keccak};

use crate::lean::{
  lean::{
    lean_alloc_external, lean_alloc_sarray, lean_get_external_data,
    lean_register_external_class,
  },
  lean_sarray_data, lean_sarray_set_data, noop_foreach,
};

use super::{ExternalClassPtr, drop_raw, to_raw};

static KECCAK_CLASS: OnceLock<ExternalClassPtr> = OnceLock::new();

fn get_keccak_class() -> *mut c_void {
  KECCAK_CLASS
    .get_or_init(|| {
      ExternalClassPtr(
        unsafe {
          lean_register_external_class(
            Some(keccak_finalizer),
            Some(noop_foreach),
          )
        }
        .cast(),
      )
    })
    .0
}

extern "C" fn keccak_finalizer(ptr: *mut c_void) {
  drop_raw(ptr.cast::<Keccak>());
}

/// `Keccak.Hasher.init : Unit → Hasher`
#[unsafe(no_mangle)]
extern "C" fn rs_keccak256_hasher_init(_unit: *const c_void) -> *mut c_void {
  let hasher = Keccak::v256();
  let ptr = to_raw(hasher) as *mut c_void;
  unsafe { lean_alloc_external(get_keccak_class().cast(), ptr) }.cast()
}

/// `Keccak.Hasher.update : (hasher: Hasher) → (input: @& ByteArray) → Hasher`
#[unsafe(no_mangle)]
extern "C" fn rs_keccak256_hasher_update(
  hasher_obj: *mut c_void,
  input: *const c_void,
) -> *mut c_void {
  let hasher: &Keccak =
    unsafe { &*lean_get_external_data(hasher_obj.cast()).cast() };
  let mut new_hasher = hasher.clone();
  new_hasher.update(lean_sarray_data(input));
  let ptr = to_raw(new_hasher) as *mut c_void;
  unsafe { lean_alloc_external(get_keccak_class().cast(), ptr) }.cast()
}

/// `Keccak.Hasher.finalize : (hasher: Hasher) → ByteArray`
#[unsafe(no_mangle)]
extern "C" fn rs_keccak256_hasher_finalize(
  hasher_obj: *mut c_void,
) -> *mut c_void {
  let hasher: &Keccak =
    unsafe { &*lean_get_external_data(hasher_obj.cast()).cast() };
  let mut data = [0u8; 32];
  hasher.clone().finalize(&mut data);
  let arr_ptr = unsafe { lean_alloc_sarray(1, 32, 32) };
  unsafe { lean_sarray_set_data(arr_ptr.cast(), &data) };
  arr_ptr.cast()
}
