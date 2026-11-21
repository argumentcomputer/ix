//! Ixon resource modes (`IxC/Ixon/Types/Modes.lean`) build/decode.
//!
//! Lean representations:
//! - `BinderMode`, `ResultMode`, `FieldMode`, `AllocAssert`: enums of
//!   nullary constructors, so `uint8` scalars in a structure and `lean_box`ed
//!   in an `Array` or an object field; the value is the constructor index,
//!   which is the wire code.
//! - `AllMode` (`input`, `result`) and `DefAsserts` (`alloc`, `boundedStack`):
//!   a constructor object with no object field and two `uint8` scalars, in
//!   declaration order.
//! - `LetMode`: `value m` is constructor 0 with one `uint8` scalar (`m`);
//!   `borrow` is `lean_box(1)`.
//! - `FieldModes n`: `inherited` is `lean_box(0)`; `listed modes _` is
//!   constructor 1 with one object field, the `Vector`'s `Array` of boxed
//!   `FieldMode`s (the proof is erased).

use crate::lean::{
  LeanIxonAllMode, LeanIxonDefAsserts, LeanIxonFieldModes, LeanIxonLetMode,
};
use ixon::modes::{
  AllMode, AllocAssert, BinderMode, DefAsserts, FieldMode, FieldModes, LetMode,
  ResultMode,
};
use lean_ffi::object::{LeanArray, LeanOwned, LeanRef};

impl LeanIxonAllMode<LeanOwned> {
  pub fn build(m: &AllMode) -> Self {
    let ctor = Self::alloc(0);
    ctor.set_num_8(0, m.input.to_code());
    ctor.set_num_8(1, m.result.to_code());
    ctor
  }
}

impl<R: LeanRef> LeanIxonAllMode<R> {
  pub fn decode(&self) -> AllMode {
    AllMode {
      input: BinderMode::of_code(self.get_num_8(0))
        .expect("invalid Ixon.BinderMode tag"),
      result: ResultMode::of_code(self.get_num_8(1))
        .expect("invalid Ixon.ResultMode tag"),
    }
  }
}

impl LeanIxonLetMode<LeanOwned> {
  pub fn build(m: &LetMode) -> Self {
    match m {
      LetMode::Value(b) => {
        let ctor = Self::alloc(0);
        ctor.set_num_8(0, b.to_code());
        ctor
      },
      LetMode::Borrow => Self::new(LeanOwned::box_usize(1)),
    }
  }
}

impl<R: LeanRef> LeanIxonLetMode<R> {
  pub fn decode(&self) -> LetMode {
    if self.inner().is_scalar() {
      return match self.inner().as_raw() as usize >> 1 {
        1 => LetMode::Borrow,
        tag => panic!("Invalid scalar Ixon.LetMode tag: {tag}"),
      };
    }
    match self.as_ctor().tag() {
      0 => LetMode::Value(
        BinderMode::of_code(self.get_num_8(0))
          .expect("invalid Ixon.BinderMode tag"),
      ),
      tag => panic!("Invalid Ixon.LetMode tag: {tag}"),
    }
  }
}

impl LeanIxonFieldModes<LeanOwned> {
  pub fn build(m: &FieldModes) -> Self {
    match m {
      FieldModes::Inherited => Self::new(LeanOwned::box_usize(0)),
      FieldModes::Listed(modes) => {
        let arr = LeanArray::alloc(modes.len());
        for (i, mode) in modes.iter().enumerate() {
          arr.set(i, LeanOwned::box_usize(usize::from(mode.to_code())));
        }
        let ctor = Self::alloc(1);
        ctor.set_obj(0, arr);
        ctor
      },
    }
  }
}

impl<R: LeanRef> LeanIxonFieldModes<R> {
  pub fn decode(&self) -> FieldModes {
    if self.inner().is_scalar() {
      return match self.inner().as_raw() as usize >> 1 {
        0 => FieldModes::Inherited,
        tag => panic!("Invalid scalar Ixon.FieldModes tag: {tag}"),
      };
    }
    match self.as_ctor().tag() {
      1 => FieldModes::Listed(
        self
          .get_obj(0)
          .as_array()
          .iter()
          .map(|elem| {
            u8::try_from(elem.unbox_usize())
              .ok()
              .and_then(FieldMode::of_code)
              .expect("invalid Ixon.FieldMode tag")
          })
          .collect(),
      ),
      tag => panic!("Invalid Ixon.FieldModes tag: {tag}"),
    }
  }
}

impl LeanIxonDefAsserts<LeanOwned> {
  pub fn build(a: &DefAsserts) -> Self {
    let ctor = Self::alloc(0);
    ctor.set_num_8(0, a.alloc.to_code());
    ctor.set_num_8(1, u8::from(a.bounded_stack));
    ctor
  }
}

impl<R: LeanRef> LeanIxonDefAsserts<R> {
  pub fn decode(&self) -> DefAsserts {
    DefAsserts {
      alloc: AllocAssert::of_code(self.get_num_8(0))
        .expect("invalid Ixon.AllocAssert tag"),
      bounded_stack: self.get_num_8(1) != 0,
    }
  }
}
