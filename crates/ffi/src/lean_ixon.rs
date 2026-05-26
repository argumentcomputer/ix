//! FFI for Ixon types (canonical serialization format).
//!
//! This module provides build/decode/roundtrip functions for Ixon types used in
//! cross-implementation compatibility testing and serialization.

#[cfg(feature = "test-ffi")]
pub mod compare;
pub mod constant;
pub mod enums;
pub mod env;
pub mod expr;
pub mod meta;
#[cfg(feature = "test-ffi")]
pub mod serialize;
#[cfg(feature = "test-ffi")]
pub mod sharing;
pub mod univ;
