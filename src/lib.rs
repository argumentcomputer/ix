#![allow(clippy::type_complexity)]
#![allow(clippy::too_many_arguments)]
#![allow(clippy::unnecessary_wraps)]

// Use mimalloc as the global allocator for Rust-side allocations.
//
// Dropping the post-ingress IxonEnv is dominated by freeing millions of nested
// `Arc<Expr>` / `Arc<Univ>` trees concurrently across rayon workers. glibc
// malloc serializes freelist updates per-arena and scales poorly past ~16
// threads on free-heavy workloads; mimalloc has fully thread-local free lists
// and consistently outperforms glibc by 1.5–2× on this kind of teardown.
//
// `ix_rs` is `crate-type = ["staticlib"]` linked into Lean. This declaration
// only governs Rust-side allocations (DashMap, Arc, Vec, etc.); Lean's runtime
// continues to manage its own heap, and the FFI boundary routes Lean-owned
// objects through `lean-ffi`, so there is no allocator-mismatch risk on
// cross-boundary frees.
#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;

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
pub mod ffi;
// Iroh functionality is enabled by the `net` feature. However, Iroh doesn't work on `aarch64-darwin`, so it is always disabled for that target.
#[cfg(all(
  feature = "net",
  not(all(target_os = "macos", target_arch = "aarch64"))
))]
pub mod iroh;
pub mod ix;
pub mod lean;
mod sha256;

pub type FxIndexMap<K, V> = IndexMap<K, V, FxBuildHasher>;
pub type FxIndexSet<K> = IndexSet<K, FxBuildHasher>;
