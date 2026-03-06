//! FFI for Ix types (canonical types with embedded hashes).
//!
//! This module provides build/decode/roundtrip functions for Ix types:
//! - Ix.Address - Blake3 hash wrapper
//! - Ix.Name - anonymous, str, num
//! - Ix.Level - zero, succ, max, imax, param, mvar
//! - Ix.Expr - 12 constructors
//! - Ix.ConstantInfo - 8 variants
//! - Ix.DataValue, Ix.Syntax, Ix.SourceInfo
//! - Ix.Environment

pub mod address;
pub mod constant;
pub mod data;
pub mod env;
pub mod expr;
pub mod level;
pub mod name;

pub use address::*;
pub use constant::*;
pub use data::*;
pub use env::*;
pub use expr::*;
pub use level::*;
pub use name::*;
