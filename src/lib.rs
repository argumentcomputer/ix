#[allow(unused_extern_crates)]
#[cfg(test)]
extern crate quickcheck;
#[allow(unused_extern_crates)]
#[cfg(test)]
#[macro_use(quickcheck)]
extern crate quickcheck_macros;
#[allow(unused_extern_crates)]
#[cfg(test)]
extern crate rand;

use indexmap::{IndexMap, IndexSet};
use rustc_hash::FxBuildHasher;

pub mod aiur;
pub mod cons_list;
pub mod iroh;
pub mod ixon;
pub mod lean;
pub mod lean_env;

pub type FxIndexMap<K, V> = IndexMap<K, V, FxBuildHasher>;
pub type FxIndexSet<K> = IndexSet<K, FxBuildHasher>;
