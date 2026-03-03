//! FFI for Ixon types (canonical serialization format).
//!
//! This module provides build/decode/roundtrip functions for Ixon types used in
//! cross-implementation compatibility testing and serialization.

pub mod compare;
pub mod constant;
pub mod enums;
pub mod env;
pub mod expr;
pub mod meta;
pub mod serialize;
pub mod sharing;
pub mod univ;

pub use compare::*;
pub use constant::*;
pub use enums::*;
pub use env::*;
pub use expr::*;
pub use meta::*;
pub use serialize::*;
pub use sharing::*;
pub use univ::*;
