//! Ixon.Univ build/decode/roundtrip FFI.

use std::ffi::c_void;
use std::sync::Arc;

use crate::ix::ixon::univ::Univ as IxonUniv;
use crate::lean::{
  as_ref_unsafe, lean_alloc_array, lean_alloc_ctor, lean_array_set_core, lean_box_fn,
  lean_ctor_get, lean_ctor_set, lean_is_scalar, lean_obj_tag,
};

/// Build Ixon.Univ
pub fn build_ixon_univ(univ: &IxonUniv) -> *mut c_void {
  unsafe {
    match univ {
      IxonUniv::Zero => lean_box_fn(0),
      IxonUniv::Succ(inner) => {
        let inner_obj = build_ixon_univ(inner);
        let obj = lean_alloc_ctor(1, 1, 0);
        lean_ctor_set(obj, 0, inner_obj);
        obj
      }
      IxonUniv::Max(a, b) => {
        let a_obj = build_ixon_univ(a);
        let b_obj = build_ixon_univ(b);
        let obj = lean_alloc_ctor(2, 2, 0);
        lean_ctor_set(obj, 0, a_obj);
        lean_ctor_set(obj, 1, b_obj);
        obj
      }
      IxonUniv::IMax(a, b) => {
        let a_obj = build_ixon_univ(a);
        let b_obj = build_ixon_univ(b);
        let obj = lean_alloc_ctor(3, 2, 0);
        lean_ctor_set(obj, 0, a_obj);
        lean_ctor_set(obj, 1, b_obj);
        obj
      }
      IxonUniv::Var(idx) => {
        let obj = lean_alloc_ctor(4, 0, 8);
        let base = obj.cast::<u8>();
        *base.add(8).cast::<u64>() = *idx;
        obj
      }
    }
  }
}

/// Build an Array of Ixon.Univ.
pub fn build_ixon_univ_array(univs: &[Arc<IxonUniv>]) -> *mut c_void {
  unsafe {
    let arr = lean_alloc_array(univs.len(), univs.len());
    for (i, univ) in univs.iter().enumerate() {
      let univ_obj = build_ixon_univ(univ);
      lean_array_set_core(arr, i, univ_obj);
    }
    arr
  }
}

// =============================================================================
// Decode Functions
// =============================================================================

/// Decode Ixon.Univ (recursive enum).
/// | zero -- tag 0 (no fields)
/// | succ (u : Univ) -- tag 1
/// | max (a b : Univ) -- tag 2
/// | imax (a b : Univ) -- tag 3
/// | var (idx : UInt64) -- tag 4 (scalar field)
pub fn decode_ixon_univ(ptr: *const c_void) -> IxonUniv {
  unsafe {
    // Note: .zero is a nullary constructor with tag 0, represented as lean_box(0)
    if lean_is_scalar(ptr) {
      return IxonUniv::Zero;
    }
    let tag = lean_obj_tag(ptr as *mut _);
    match tag {
      0 => IxonUniv::Zero,
      1 => {
        let inner_ptr = lean_ctor_get(ptr as *mut _, 0);
        IxonUniv::Succ(Arc::new(decode_ixon_univ(inner_ptr)))
      }
      2 => {
        let a_ptr = lean_ctor_get(ptr as *mut _, 0);
        let b_ptr = lean_ctor_get(ptr as *mut _, 1);
        IxonUniv::Max(Arc::new(decode_ixon_univ(a_ptr)), Arc::new(decode_ixon_univ(b_ptr)))
      }
      3 => {
        let a_ptr = lean_ctor_get(ptr as *mut _, 0);
        let b_ptr = lean_ctor_get(ptr as *mut _, 1);
        IxonUniv::IMax(Arc::new(decode_ixon_univ(a_ptr)), Arc::new(decode_ixon_univ(b_ptr)))
      }
      4 => {
        // scalar field: UInt64 at offset 8 (after header)
        let base = ptr.cast::<u8>();
        let idx = *(base.add(8).cast::<u64>());
        IxonUniv::Var(idx)
      }
      _ => panic!("Invalid Ixon.Univ tag: {}", tag),
    }
  }
}

/// Decode Array Ixon.Univ.
pub fn decode_ixon_univ_array(ptr: *const c_void) -> Vec<Arc<IxonUniv>> {
  let arr: &crate::lean::array::LeanArrayObject = as_ref_unsafe(ptr.cast());
  arr.to_vec(|u| Arc::new(decode_ixon_univ(u)))
}

// =============================================================================
// FFI Exports
// =============================================================================

/// Round-trip Ixon.Univ.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ixon_univ(ptr: *const c_void) -> *mut c_void {
  let univ = decode_ixon_univ(ptr);
  build_ixon_univ(&univ)
}
