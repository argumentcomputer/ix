//! Ixon.Univ build/decode/roundtrip FFI.

use std::sync::Arc;

use crate::ix::ixon::univ::Univ;
use crate::lean::LeanIxonUniv;
use lean_ffi::object::{LeanArray, LeanBorrowed, LeanOwned, LeanRef};

impl LeanIxonUniv<LeanOwned> {
  /// Build Ixon.Univ
  pub fn build(univ: &Univ) -> Self {
    match univ {
      Univ::Zero => Self::new(LeanOwned::box_usize(0)),
      Univ::Succ(inner) => {
        let ctor = LeanIxonUniv::alloc(1);
        ctor.set_obj(0, Self::build(inner));
        ctor
      },
      Univ::Max(a, b) => {
        let ctor = LeanIxonUniv::alloc(2);
        ctor.set_obj(0, Self::build(a));
        ctor.set_obj(1, Self::build(b));
        ctor
      },
      Univ::IMax(a, b) => {
        let ctor = LeanIxonUniv::alloc(3);
        ctor.set_obj(0, Self::build(a));
        ctor.set_obj(1, Self::build(b));
        ctor
      },
      Univ::Var(idx) => {
        let ctor = LeanIxonUniv::alloc(4);
        ctor.set_num_64(0, *idx);
        ctor
      },
    }
  }

  /// Build an Array of Ixon.Univ.
  pub fn build_array(univs: &[Arc<Univ>]) -> LeanArray<LeanOwned> {
    let arr = LeanArray::alloc(univs.len());
    for (i, univ) in univs.iter().enumerate() {
      arr.set(i, Self::build(univ));
    }
    arr
  }
}

impl<R: LeanRef> LeanIxonUniv<R> {
  /// Decode Ixon.Univ (recursive enum).
  pub fn decode(&self) -> Univ {
    if self.inner().is_scalar() {
      return Univ::Zero;
    }
    let ctor = self.as_ctor();
    match ctor.tag() {
      0 => Univ::Zero,
      1 => Univ::Succ(Arc::new(LeanIxonUniv(ctor.get(0)).decode())),
      2 => Univ::Max(
        Arc::new(LeanIxonUniv(ctor.get(0)).decode()),
        Arc::new(LeanIxonUniv(ctor.get(1)).decode()),
      ),
      3 => Univ::IMax(
        Arc::new(LeanIxonUniv(ctor.get(0)).decode()),
        Arc::new(LeanIxonUniv(ctor.get(1)).decode()),
      ),
      4 => Univ::Var(self.get_num_64(0)),
      tag => panic!("Invalid Ixon.Univ tag: {tag}"),
    }
  }
}

impl LeanIxonUniv<LeanBorrowed<'_>> {
  /// Decode Array Ixon.Univ.
  pub fn decode_array(obj: &LeanArray<LeanBorrowed<'_>>) -> Vec<Arc<Univ>> {
    obj.map(|elem| Arc::new(LeanIxonUniv(elem).decode()))
  }
}

// =============================================================================
// FFI Exports
// =============================================================================

/// Round-trip Ixon.Univ.
#[cfg(feature = "test-ffi")]
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ixon_univ(
  obj: LeanIxonUniv<LeanBorrowed<'_>>,
) -> LeanIxonUniv<LeanOwned> {
  let univ = obj.decode();
  LeanIxonUniv::build(&univ)
}
