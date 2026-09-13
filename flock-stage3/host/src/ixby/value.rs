//! Experimental physical scalar cells: one canonical tag word and one full
//! F128 payload. This is NOT the variable-length IxBy byte codec. Zero/zero is
//! unused padding, distinct from the live Bool(false) and erased values.
//! The control component treats cells opaquely except at a Bool branch;
//! separate value/primitive/codec constraints must establish live canonicality.

use flock_prover::field::F128;

pub type ValueWords = [F128; 2];

pub const BOOL_TAG: u64 = 1;
pub const WORD32_TAG: u64 = 2;
pub const FIELD_TAG: u64 = 3;
pub const EXT_TAG: u64 = 4;
pub const ERASED_TAG: u64 = 5;

pub fn bool_words(value: bool) -> ValueWords {
  [F128::new(BOOL_TAG, 0), F128::new(u64::from(value), 0)]
}

pub fn word32_words(value: u32) -> ValueWords {
  [F128::new(WORD32_TAG, 0), F128::new(u64::from(value), 0)]
}
