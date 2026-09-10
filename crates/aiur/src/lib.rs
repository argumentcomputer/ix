pub mod bytecode;
pub mod constraints;
pub mod execute;
pub mod gadgets;
pub mod memory;
pub mod querymap;
pub mod range;
pub mod shard;
pub mod synthesis;
pub mod trace;
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

/// Memory segment boundaries. Every real memory row pushes its own pointer
/// and pulls its successor on this channel, so a contiguous pointer run
/// `[a, b)` contributes exactly one push of `a` and one pull of `b`; the
/// batch verifier closes the channel with one pull of `0` and one push of the
/// table's total length per memory width (see `shard.rs`).
#[inline]
pub fn memseg_channel() -> G {
  G::from_u8(15)
}
