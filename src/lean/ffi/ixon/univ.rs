//! Ixon.Univ build/decode/roundtrip FFI.

use std::sync::Arc;

use crate::ix::ixon::univ::Univ;
use crate::lean::obj::{IxonUniv, LeanArray, LeanCtor, LeanObj};

impl IxonUniv {
  /// Build Ixon.Univ
  pub fn build(univ: &Univ) -> Self {
    let obj = match univ {
      Univ::Zero => LeanObj::box_usize(0),
      Univ::Succ(inner) => {
        let ctor = LeanCtor::alloc(1, 1, 0);
        ctor.set(0, Self::build(inner));
        *ctor
      },
      Univ::Max(a, b) => {
        let ctor = LeanCtor::alloc(2, 2, 0);
        ctor.set(0, Self::build(a));
        ctor.set(1, Self::build(b));
        *ctor
      },
      Univ::IMax(a, b) => {
        let ctor = LeanCtor::alloc(3, 2, 0);
        ctor.set(0, Self::build(a));
        ctor.set(1, Self::build(b));
        *ctor
      },
      Univ::Var(idx) => {
        let ctor = LeanCtor::alloc(4, 0, 8);
        ctor.set_u64(0, *idx);
        *ctor
      },
    };
    Self::new(obj)
  }

  /// Build an Array of Ixon.Univ.
  pub fn build_array(univs: &[Arc<Univ>]) -> LeanArray {
    let arr = LeanArray::alloc(univs.len());
    for (i, univ) in univs.iter().enumerate() {
      arr.set(i, Self::build(univ));
    }
    arr
  }

  /// Decode Ixon.Univ (recursive enum).
  pub fn decode(self) -> Univ {
    let obj: LeanObj = *self;
    if obj.is_scalar() {
      return Univ::Zero;
    }
    let ctor = unsafe { LeanCtor::from_raw(obj.as_ptr()) };
    match ctor.tag() {
      0 => Univ::Zero,
      1 => Univ::Succ(Arc::new(Self::new(ctor.get(0)).decode())),
      2 => Univ::Max(
        Arc::new(Self::new(ctor.get(0)).decode()),
        Arc::new(Self::new(ctor.get(1)).decode()),
      ),
      3 => Univ::IMax(
        Arc::new(Self::new(ctor.get(0)).decode()),
        Arc::new(Self::new(ctor.get(1)).decode()),
      ),
      4 => Univ::Var(ctor.scalar_u64(0, 0)),
      tag => panic!("Invalid Ixon.Univ tag: {tag}"),
    }
  }

  /// Decode Array Ixon.Univ.
  pub fn decode_array(obj: LeanObj) -> Vec<Arc<Univ>> {
    let arr = unsafe { LeanArray::from_raw(obj.as_ptr()) };
    arr.map(|elem| Arc::new(Self::new(elem).decode()))
  }
}

// =============================================================================
// FFI Exports
// =============================================================================

/// Round-trip Ixon.Univ.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ixon_univ(obj: LeanObj) -> LeanObj {
  let univ = IxonUniv::new(obj).decode();
  IxonUniv::build(&univ).into()
}
