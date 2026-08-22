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
use multi_stark::p3_field::PrimeCharacteristicRing;
use rustc_hash::FxBuildHasher;

pub type G = multi_stark::p3_goldilocks::Goldilocks;
pub type FxIndexMap<K, V> = IndexMap<K, V, FxBuildHasher>;

/// Per-row multiplicity budget declared for committed count columns —
/// function-call return counts, memory load counts, and gadget table
/// counts: each entry supports up to 2^32 queries. The columns are not
/// range-constrained; the weight-1 pushes at the query sites are what keep
/// actual counts within the budget. Feeds the logUp height bound
/// `Σ wᵢ·hᵢ + |claims| < p` (see `multi_stark::lookup::Lookup`'s
/// `max_multiplicity`).
pub const COUNT_COLUMN_BUDGET: u64 = 1 << 32;

/// # Channel discipline (width binding by construction)
///
/// Aiur declares `WidthBinding::ByConstruction` to multi-stark: message
/// fingerprints are the plain Horner fold, so a message equals its own
/// zero-padding. That is what licenses branch-shared lookup slots — with
/// mutually exclusive selectors, sibling branches superpose messages of
/// different natural widths into one slot at the maximum width, and the
/// padded send still matches its natural-width provider.
///
/// The contract this declaration takes on is prefix-freeness: every
/// message's natural width must be a function of its constant-constrained
/// leading prefix, so zero-extension can only ever equate a padded message
/// with its own natural form. The channels below uphold it —
///
/// - function channel: `[tag, fun_idx, inputs.., outputs..]`, width
///   `2 + in + out` fixed by `fun_idx`;
/// - memory channel: `[tag, size, ptr, values..]`, width `3 + size` fixed
///   by the size coordinate;
/// - gadget channels: one fixed width per tag (each byte-table op has its
///   own channel).
///
/// Every op that emits a lookup gates these leading coordinates as
/// constants, so a new channel (or a new width for an existing one) must
/// keep the width derivable from the prefix.
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
