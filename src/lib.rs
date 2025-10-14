use indexmap::{IndexMap, IndexSet};
use rustc_hash::FxBuildHasher;

pub mod aiur;
pub mod lean;
pub mod lean_env;

pub type FxIndexMap<K, V> = IndexMap<K, V, FxBuildHasher>;
pub type FxIndexSet<K> = IndexSet<K, FxBuildHasher>;
