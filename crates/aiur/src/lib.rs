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

/// The field surface Aiur needs: the p3 field traits plus canonical
/// integer extraction. The executor and witness builders only ever call
/// `as_canonical_u64` on values that are small by construction (bytes,
/// pointers, counters, u32 words) or on the deliberate 8-byte hint
/// decomposition (`UnconstrainedGToBytes`). Every 64-bit-or-smaller prime
/// field qualifies, so Aiur circuits synthesize and execute over
/// Goldilocks (the default, `G`) or e.g. KoalaBear alike.
pub trait AiurField: Field + TwoAdicField + Ord + std::fmt::Display {
  /// The canonical value as a `u64`.
  fn as_canonical_u64(&self) -> u64;
}

impl<F> AiurField for F
where
  F: Field + TwoAdicField + Ord + std::fmt::Display + PrimeField64,
{
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

/// Channel of the memory allocation counter: backends without row
/// transitions (Hypercube) thread the pointers of each memory table through
/// a lookup chain on this channel instead of a `ptr + 1 = ptr_next`
/// constraint.
#[inline]
pub fn memory_counter_channel<F: AiurField>() -> F {
  F::from_u8(15)
}
