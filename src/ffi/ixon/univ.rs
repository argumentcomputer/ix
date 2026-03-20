//! Ixon.Univ build/decode/roundtrip FFI.

use std::sync::Arc;

use crate::ix::ixon::univ::Univ;
use crate::lean::LeanIxonUniv;
use lean_ffi::object::{LeanArray, LeanBorrowed, LeanCtor, LeanOwned, LeanRef};

impl LeanIxonUniv<LeanOwned> {
  /// Build Ixon.Univ
  pub fn build(univ: &Univ) -> Self {
    let obj = match univ {
      Univ::Zero => LeanOwned::box_usize(0),
      Univ::Succ(inner) => {
        let ctor = LeanCtor::alloc(1, 1, 0);
        ctor.set(0, Self::build(inner));
        ctor.into()
      },
      Univ::Max(a, b) => {
        let ctor = LeanCtor::alloc(2, 2, 0);
        ctor.set(0, Self::build(a));
        ctor.set(1, Self::build(b));
        ctor.into()
      },
      Univ::IMax(a, b) => {
        let ctor = LeanCtor::alloc(3, 2, 0);
        ctor.set(0, Self::build(a));
        ctor.set(1, Self::build(b));
        ctor.into()
      },
      Univ::Var(idx) => {
        let ctor = LeanCtor::alloc(4, 0, 8);
        ctor.set_u64(0, 0, *idx);
        ctor.into()
      },
    };
    Self::new(obj)
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
      4 => Univ::Var(ctor.get_u64(0, 0)),
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
