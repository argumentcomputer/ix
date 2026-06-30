//! Foundational types shared across the Ix project.
//!
//! Contains:
//! - `address`: 32-byte content-address newtype.
//! - `env`: the Lean kernel type representation (`Name`, `Level`, `Expr`,
//!   `ConstantInfo`, `Env`, …) and the tag-byte constants used throughout.
//! - `mutual`: mutual-block helpers used by both compile and kernel.
//! - `strong_ordering`: small comparison helper.
//!
//! Plus the `FxIndexMap` / `FxIndexSet` aliases that the rest of the project
//! uses.

use indexmap::{IndexMap, IndexSet};
use rustc_hash::FxBuildHasher;

pub mod address;
pub mod env;
pub mod strong_ordering;

pub type FxIndexMap<K, V> = IndexMap<K, V, FxBuildHasher>;
pub type FxIndexSet<K> = IndexSet<K, FxBuildHasher>;
