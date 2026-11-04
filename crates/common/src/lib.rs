//! Foundational types shared across the Ix project.
//!
//! Contains:
//! - `address`: 32-byte content-address newtype.
//! - `env`: the Lean kernel type representation (`Name`, `Level`, `Expr`,
//!   `ConstantInfo`, `Env`, …) and the tag-byte constants used throughout.
//! - `name_table`: generated-name tables with confirmed structural lookup.
//! - `prim_addrs`: hard-coded primitive content addresses.
//!
//! Plus the `FxIndexMap` / `FxIndexSet` aliases that the rest of the project
//! uses.

use indexmap::{IndexMap, IndexSet};
use rustc_hash::FxBuildHasher;

pub mod address;
pub mod env;
pub mod name_table;
pub mod prim_addrs;

pub type FxIndexMap<K, V> = IndexMap<K, V, FxBuildHasher>;
pub type FxIndexSet<K> = IndexSet<K, FxBuildHasher>;
