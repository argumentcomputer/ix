//! Semantic usage, ownership, locality, and let-kind contracts.

use crate::lean::{
  LeanIxonBinderContract, LeanIxonLetContract, LeanIxonValueContract,
};
use ixon::contract::{
  BinderContract, LetContract, LetKind, Locality, ValueContract,
};
use ixon::expr::{Owned, Uses};
use lean_ffi::object::{LeanOwned, LeanRef};

impl LeanIxonValueContract<LeanOwned> {
  pub fn build(v: &ValueContract) -> Self {
    let ctor = Self::alloc(0);
    ctor.set_num_8(0, v.owned.to_bits());
    ctor.set_num_8(1, v.locality.to_bits());
    ctor
  }
}

impl<R: LeanRef> LeanIxonValueContract<R> {
  pub fn decode(&self) -> ValueContract {
    ValueContract {
      owned: Owned::from_bits(self.get_num_8(0))
        .expect("invalid Ixon.Owned tag"),
      locality: Locality::from_bits(self.get_num_8(1))
        .expect("invalid Ixon.Locality tag"),
    }
  }
}

impl LeanIxonBinderContract<LeanOwned> {
  pub fn build(b: &BinderContract) -> Self {
    let ctor = Self::alloc(0);
    ctor.set_obj(0, LeanIxonValueContract::build(&b.value));
    ctor.set_num_8(0, b.uses.to_bits());
    ctor
  }
}

impl<R: LeanRef> LeanIxonBinderContract<R> {
  pub fn decode(&self) -> BinderContract {
    BinderContract {
      uses: Uses::from_bits(self.get_num_8(0)).expect("invalid Ixon.Uses tag"),
      value: LeanIxonValueContract(self.get_obj(0)).decode(),
    }
  }
}

impl LeanIxonLetContract<LeanOwned> {
  pub fn build(c: &LetContract) -> Self {
    let ctor = Self::alloc(0);
    ctor.set_obj(0, LeanIxonBinderContract::build(&c.binder));
    ctor.set_num_8(0, u8::from(c.non_dep));
    ctor.set_num_8(1, c.kind as u8);
    ctor
  }
}

impl<R: LeanRef> LeanIxonLetContract<R> {
  pub fn decode(&self) -> LetContract {
    LetContract {
      non_dep: self.get_num_8(0) != 0,
      kind: match self.get_num_8(1) {
        0 => LetKind::Value,
        1 => LetKind::BorrowShared,
        _ => panic!("invalid Ixon.LetKind tag"),
      },
      binder: LeanIxonBinderContract(self.get_obj(0)).decode(),
    }
  }
}
