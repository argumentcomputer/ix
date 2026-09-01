pub mod bytecode;
pub mod constraints;
pub mod execute;
pub mod gadgets;
pub mod memory;
pub mod querymap;
pub mod synthesis;
pub mod trace;
pub mod vk_codec;

use indexmap::IndexMap;
use multi_stark::p3_field::{Field, PrimeField64, TwoAdicField};
use rustc_hash::FxBuildHasher;

/// The default (and currently only proving-ready) Aiur field.
pub type G = multi_stark::p3_goldilocks::Goldilocks;
pub type FxIndexMap<K, V> = IndexMap<K, V, FxBuildHasher>;

/// The field surface Aiur needs beyond multi-stark's crate traits:
/// canonical integer extraction. The executor and witness builders only
/// ever call it on values that are small by construction (bytes,
/// pointers, counters, u32 words) or on the deliberate 8-byte hint
/// decomposition (`UnconstrainedGToBytes`), so implementations for
/// fields larger than 64 bits may take the canonical value's low 64
/// bits — with the caveat that such a field's toplevels must not use
/// the 8-byte hint (the foreign Goldilocks interface doesn't).
pub trait AiurField: Field + TwoAdicField + Ord + std::fmt::Display {
  /// The canonical value as a `u64`; exact for values < 2^64.
  fn as_canonical_u64(&self) -> u64;
}

impl AiurField for G {
  #[inline]
  fn as_canonical_u64(&self) -> u64 {
    <Self as PrimeField64>::as_canonical_u64(self)
  }
}

#[inline]
pub fn function_channel<F: AiurField>() -> F {
  F::ZERO
}

#[inline]
pub fn memory_channel<F: AiurField>() -> F {
  F::ONE
}

#[inline]
pub fn u8_bit_decomposition_channel<F: AiurField>() -> F {
  F::from_u8(2)
}

#[inline]
pub fn u8_shift_left_channel<F: AiurField>() -> F {
  F::from_u8(3)
}

#[inline]
pub fn u8_shift_right_channel<F: AiurField>() -> F {
  F::from_u8(4)
}

#[inline]
pub fn u8_xor_channel<F: AiurField>() -> F {
  F::from_u8(5)
}

#[inline]
pub fn u8_add_channel<F: AiurField>() -> F {
  F::from_u8(6)
}

#[inline]
pub fn u8_sub_channel<F: AiurField>() -> F {
  F::from_u8(7)
}

#[inline]
pub fn u8_and_channel<F: AiurField>() -> F {
  F::from_u8(8)
}

#[inline]
pub fn u8_or_channel<F: AiurField>() -> F {
  F::from_u8(9)
}

#[inline]
pub fn u8_less_than_channel<F: AiurField>() -> F {
  F::from_u8(10)
}

#[inline]
pub fn u8_range_check_channel<F: AiurField>() -> F {
  F::from_u8(11)
}

#[inline]
pub fn u8_mul_channel<F: AiurField>() -> F {
  F::from_u8(12)
}

#[inline]
pub fn u8_xor_split7_channel<F: AiurField>() -> F {
  F::from_u8(13)
}

#[inline]
pub fn u8_xor_split4_channel<F: AiurField>() -> F {
  F::from_u8(14)
}
