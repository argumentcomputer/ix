//! Ixon.Univ build/decode/roundtrip FFI.

use std::ffi::c_void;
use std::sync::Arc;

use crate::ix::ixon::univ::Univ as IxonUniv;
use crate::lean::{
  lean::{
    lean_alloc_array, lean_alloc_ctor, lean_array_set_core, lean_ctor_get,
    lean_ctor_set, lean_obj_tag,
  },
  lean_box_fn, lean_is_scalar,
};

/// Build Ixon.Univ
pub fn build_ixon_univ(univ: &IxonUniv) -> *mut c_void {
  unsafe {
    match univ {
      IxonUniv::Zero => lean_box_fn(0),
      IxonUniv::Succ(inner) => {
        let inner_obj = build_ixon_univ(inner);
        let obj = lean_alloc_ctor(1, 1, 0);
        lean_ctor_set(obj, 0, inner_obj.cast());
        obj.cast()
      },
      IxonUniv::Max(a, b) => {
        let a_obj = build_ixon_univ(a);
        let b_obj = build_ixon_univ(b);
        let obj = lean_alloc_ctor(2, 2, 0);
        lean_ctor_set(obj, 0, a_obj.cast());
        lean_ctor_set(obj, 1, b_obj.cast());
        obj.cast()
      },
      IxonUniv::IMax(a, b) => {
        let a_obj = build_ixon_univ(a);
        let b_obj = build_ixon_univ(b);
        let obj = lean_alloc_ctor(3, 2, 0);
        lean_ctor_set(obj, 0, a_obj.cast());
        lean_ctor_set(obj, 1, b_obj.cast());
        obj.cast()
      },
      IxonUniv::Var(idx) => {
        let obj = lean_alloc_ctor(4, 0, 8);
        let base = obj.cast::<u8>();
        *base.add(8).cast::<u64>() = *idx;
        obj.cast()
      },
    }
  }
}

/// Build an Array of Ixon.Univ.
pub fn build_ixon_univ_array(univs: &[Arc<IxonUniv>]) -> *mut c_void {
  unsafe {
    let arr = lean_alloc_array(univs.len(), univs.len());
    for (i, univ) in univs.iter().enumerate() {
      let univ_obj = build_ixon_univ(univ);
      lean_array_set_core(arr, i, univ_obj.cast());
    }
    arr.cast()
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
    let tag = lean_obj_tag((ptr as *mut c_void).cast());
    match tag {
      0 => IxonUniv::Zero,
      1 => {
        let inner_ptr = lean_ctor_get((ptr as *mut c_void).cast(), 0);
        IxonUniv::Succ(Arc::new(decode_ixon_univ(inner_ptr.cast())))
      },
      2 => {
        let a_ptr = lean_ctor_get((ptr as *mut c_void).cast(), 0);
        let b_ptr = lean_ctor_get((ptr as *mut c_void).cast(), 1);
        IxonUniv::Max(
          Arc::new(decode_ixon_univ(a_ptr.cast())),
          Arc::new(decode_ixon_univ(b_ptr.cast())),
        )
      },
      3 => {
        let a_ptr = lean_ctor_get((ptr as *mut c_void).cast(), 0);
        let b_ptr = lean_ctor_get((ptr as *mut c_void).cast(), 1);
        IxonUniv::IMax(
          Arc::new(decode_ixon_univ(a_ptr.cast())),
          Arc::new(decode_ixon_univ(b_ptr.cast())),
        )
      },
      4 => {
        // scalar field: UInt64 at offset 8 (after header)
        let base = ptr.cast::<u8>();
        let idx = *(base.add(8).cast::<u64>());
        IxonUniv::Var(idx)
      },
      _ => panic!("Invalid Ixon.Univ tag: {}", tag),
    }
  }
}

/// Decode Array Ixon.Univ.
pub fn decode_ixon_univ_array(ptr: *const c_void) -> Vec<Arc<IxonUniv>> {
  crate::lean::lean_array_data(ptr)
    .iter()
    .map(|&u| Arc::new(decode_ixon_univ(u)))
    .collect()
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
