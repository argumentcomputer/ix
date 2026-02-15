pub mod bytecode;
pub mod constraints;
pub mod execute;
pub mod gadgets;
pub mod memory;
pub mod synthesis;
pub mod trace;

use multi_stark::p3_field::PrimeCharacteristicRing;

pub type G = multi_stark::p3_goldilocks::Goldilocks;

#[inline]
pub const fn function_channel() -> G {
  G::ZERO
}

#[inline]
pub const fn memory_channel() -> G {
  G::ONE
}

#[inline]
pub const fn u8_bit_decomposition_channel() -> G {
  G::TWO
}

#[inline]
pub fn u8_shift_left_channel() -> G {
  G::from_u8(3)
}

#[inline]
pub fn u8_shift_right_channel() -> G {
  G::from_u8(4)
}

#[inline]
pub fn u8_xor_channel() -> G {
  G::from_u8(5)
}

#[inline]
pub fn u8_add_channel() -> G {
  G::from_u8(6)
}

#[inline]
pub fn u8_sub_channel() -> G {
  G::from_u8(7)
}

#[inline]
pub fn u8_and_channel() -> G {
  G::from_u8(8)
}

#[inline]
pub fn u8_or_channel() -> G {
  G::from_u8(9)
}

#[inline]
pub fn u8_less_than_channel() -> G {
  G::from_u8(10)
}
