//! Independent usage, ownership, and relative-locality contracts.

use crate::expr::{Owned, Uses};
use crate::serialize::get_u8;

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum Locality {
  #[default]
  Unrestricted = 0,
  Local = 1,
}

impl Locality {
  pub const fn to_bits(self) -> u8 {
    self as u8
  }
  pub const fn from_bits(bits: u8) -> Option<Self> {
    match bits {
      0 => Some(Self::Unrestricted),
      1 => Some(Self::Local),
      _ => None,
    }
  }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ValueContract {
  pub owned: Owned,
  pub locality: Locality,
}

impl Default for ValueContract {
  fn default() -> Self {
    Self::shared()
  }
}

impl ValueContract {
  pub const fn shared() -> Self {
    Self { owned: Owned::Shared, locality: Locality::Unrestricted }
  }
  pub const fn unique() -> Self {
    Self { owned: Owned::Unique, locality: Locality::Unrestricted }
  }
  pub const fn local_shared() -> Self {
    Self { owned: Owned::Shared, locality: Locality::Local }
  }
  pub const fn local_unique() -> Self {
    Self { owned: Owned::Unique, locality: Locality::Local }
  }
  pub const fn to_bits(self) -> u8 {
    self.owned.to_bits() | (self.locality.to_bits() << 1)
  }
  pub fn from_bits(bits: u8) -> Option<Self> {
    if bits > 3 {
      return None;
    }
    Some(Self {
      owned: Owned::from_bits(bits & 1)?,
      locality: Locality::from_bits(bits >> 1)?,
    })
  }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct BinderContract {
  pub uses: Uses,
  pub value: ValueContract,
}

impl Default for BinderContract {
  fn default() -> Self {
    Self::plain(Uses::Many)
  }
}

impl BinderContract {
  pub const fn plain(uses: Uses) -> Self {
    Self { uses, value: ValueContract::shared() }
  }
  pub const fn to_bits(self) -> u8 {
    self.uses.to_bits() | (self.value.to_bits() << 2)
  }
  pub fn from_bits(bits: u8) -> Option<Self> {
    if bits > 15 {
      return None;
    }
    Some(Self {
      uses: Uses::from_bits(bits & 3)?,
      value: ValueContract::from_bits(bits >> 2)?,
    })
  }
}

pub const fn pack_all_contract(
  input: BinderContract,
  result: ValueContract,
) -> u8 {
  input.to_bits() | (result.to_bits() << 4)
}

pub fn unpack_all_contract(
  bits: u8,
) -> Option<(BinderContract, ValueContract)> {
  if bits > 63 {
    return None;
  }
  Some((
    BinderContract::from_bits(bits & 15)?,
    ValueContract::from_bits(bits >> 4)?,
  ))
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum LetKind {
  #[default]
  Value = 0,
  BorrowShared = 1,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct LetContract {
  pub non_dep: bool,
  pub kind: LetKind,
  pub binder: BinderContract,
}

impl LetContract {
  pub const fn plain(non_dep: bool) -> Self {
    Self {
      non_dep,
      kind: LetKind::Value,
      binder: BinderContract::plain(Uses::Many),
    }
  }
  pub const fn borrow(non_dep: bool, uses: Uses) -> Self {
    Self {
      non_dep,
      kind: LetKind::BorrowShared,
      binder: BinderContract { uses, value: ValueContract::local_shared() },
    }
  }
  pub const fn flags(self) -> u64 {
    (self.non_dep as u64) | ((self.kind as u64) << 1)
  }
  pub fn from_flags(flags: u64, binder: BinderContract) -> Option<Self> {
    if flags > 3 {
      return None;
    }
    Some(Self {
      non_dep: flags & 1 == 1,
      kind: if flags & 2 == 2 { LetKind::BorrowShared } else { LetKind::Value },
      binder,
    })
  }
}

pub fn put_value_contract(value: &ValueContract, buf: &mut Vec<u8>) {
  buf.push(value.to_bits());
}

pub fn get_value_contract(buf: &mut &[u8]) -> Result<ValueContract, String> {
  let bits = get_u8(buf)?;
  ValueContract::from_bits(bits)
    .ok_or_else(|| format!("invalid value contract {bits}"))
}

pub fn put_binder_contract(binder: &BinderContract, buf: &mut Vec<u8>) {
  buf.push(binder.to_bits());
}

pub fn get_binder_contract(buf: &mut &[u8]) -> Result<BinderContract, String> {
  let bits = get_u8(buf)?;
  BinderContract::from_bits(bits)
    .ok_or_else(|| format!("invalid binder contract {bits}"))
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn independent_modes_have_canonical_codes() {
    let values = [
      ValueContract::unique(),
      ValueContract::shared(),
      ValueContract::local_unique(),
      ValueContract::local_shared(),
    ];
    let uses = [Uses::Erased, Uses::Linear, Uses::Affine, Uses::Many];
    for (value_code, value) in values.into_iter().enumerate() {
      assert_eq!(value.to_bits(), u8::try_from(value_code).unwrap());
      assert_eq!(
        ValueContract::from_bits(u8::try_from(value_code).unwrap()),
        Some(value)
      );
      for (use_code, uses) in uses.into_iter().enumerate() {
        let binder = BinderContract { uses, value };
        let code = u8::try_from(use_code).unwrap()
          + 4 * u8::try_from(value_code).unwrap();
        assert_eq!(binder.to_bits(), code);
        assert_eq!(BinderContract::from_bits(code), Some(binder));
        for (result_code, result) in values.into_iter().enumerate() {
          let all_code = code + 16 * u8::try_from(result_code).unwrap();
          assert_eq!(pack_all_contract(binder, result), all_code);
          assert_eq!(unpack_all_contract(all_code), Some((binder, result)));
        }
        for flags in 0..4 {
          let let_contract = LetContract::from_flags(flags, binder).unwrap();
          assert_eq!(let_contract.flags(), flags);
          assert_eq!(let_contract.binder, binder);
        }
      }
    }
    for code in 4..=u8::MAX {
      assert!(ValueContract::from_bits(code).is_none());
    }
    for code in 16..=u8::MAX {
      assert!(BinderContract::from_bits(code).is_none());
    }
    for code in 64..=u8::MAX {
      assert!(unpack_all_contract(code).is_none());
    }
    assert!(LetContract::from_flags(4, BinderContract::default()).is_none());
    assert!(
      LetContract::from_flags(u64::MAX, BinderContract::default()).is_none()
    );
  }
}
