pub mod bytecode;
mod call_order;
pub mod constraints;
mod emission_checks;
pub mod execute;
pub mod gadgets;
mod graph_shape;
mod lookup_budget;
mod lookup_shapes;
pub mod memory;
pub mod querymap;
mod row_counts;
pub mod synthesis;
pub mod trace;
mod trace_heights;
pub mod vk_codec;

use indexmap::IndexMap;
use multi_stark::p3_field::PrimeCharacteristicRing;
use rustc_hash::FxBuildHasher;

pub type G = multi_stark::p3_goldilocks::Goldilocks;
pub type FxIndexMap<K, V> = IndexMap<K, V, FxBuildHasher>;

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

#[inline]
pub fn u8_range_check_channel() -> G {
  G::from_u8(11)
}

#[inline]
pub fn u8_mul_channel() -> G {
  G::from_u8(12)
}

#[inline]
pub fn u8_xor_split7_channel() -> G {
  G::from_u8(13)
}

#[inline]
pub fn u8_xor_split4_channel() -> G {
  G::from_u8(14)
}
