// Diagnostic env-var helpers. zkVM std targets (`target_os = "zkvm"` — Zisk,
// SP1, risc0, …) return `Ok` from `std::env::var` for any key (no real env
// in the guest), so every `IX_*` flag fires "on" by default and runs
// expensive diagnostic code paths whose output the guest can't even surface.
// These wrappers short-circuit to "not present" on any zkVM target and
// delegate to the real call elsewhere.
//
// Use these in place of `std::env::var` / `std::env::var_os` everywhere in
// the kernel. The Result / Option chains downstream (`.is_ok()`, `.ok()`,
// `.is_some()`, `.is_err()`, `match`, ...) all work identically.
#[inline]
pub(crate) fn env_var(name: &str) -> Result<String, std::env::VarError> {
  #[cfg(target_os = "zkvm")]
  {
    let _ = name;
    Err(std::env::VarError::NotPresent)
  }
  #[cfg(not(target_os = "zkvm"))]
  {
    std::env::var(name)
  }
}

#[inline]
pub(crate) fn env_var_os(name: &str) -> Option<std::ffi::OsString> {
  #[cfg(target_os = "zkvm")]
  {
    let _ = name;
    None
  }
  #[cfg(not(target_os = "zkvm"))]
  {
    std::env::var_os(name)
  }
}

// =============================================================================
// LazyLock replacements for diagnostic env-var statics.
//
// On non-zkVM targets we want the existing thread-safe lazy-init behaviour
// (`std::sync::LazyLock`). On zkVM targets the initialiser would always
// produce a "not set" value (because `env_var` is hard-wired to `Err`), so
// `LazyLock`'s per-access atomic state load is pure overhead. These types
// collapse to a plain `bool` / `Option<T>` field on zkVM and a real
// `LazyLock` everywhere else. Same `*FLAG` / `FLAG.as_ref()` call sites
// either way.
// =============================================================================

/// Boolean env-var flag (e.g. `IX_HOT_MISSES`). Compiles to `false` on zkVM.
pub(crate) struct EnvFlag {
  #[cfg(not(target_os = "zkvm"))]
  inner: std::sync::LazyLock<bool, fn() -> bool>,
  #[cfg(target_os = "zkvm")]
  inner: bool,
}

impl EnvFlag {
  pub(crate) const fn new(_init: fn() -> bool) -> Self {
    Self {
      #[cfg(not(target_os = "zkvm"))]
      inner: std::sync::LazyLock::new(_init),
      #[cfg(target_os = "zkvm")]
      inner: false,
    }
  }
}

impl std::ops::Deref for EnvFlag {
  type Target = bool;
  #[inline]
  fn deref(&self) -> &bool {
    &self.inner
  }
}

/// `Option<String>` env-var flag (e.g. `IX_DELTA_TRACE`). Compiles to
/// `None` on zkVM (so `IX_X.as_ref()` always returns `None` cheaply).
pub(crate) struct EnvString {
  #[cfg(not(target_os = "zkvm"))]
  inner: std::sync::LazyLock<Option<String>, fn() -> Option<String>>,
  #[cfg(target_os = "zkvm")]
  inner: Option<String>,
}

impl EnvString {
  pub(crate) const fn new(_init: fn() -> Option<String>) -> Self {
    Self {
      #[cfg(not(target_os = "zkvm"))]
      inner: std::sync::LazyLock::new(_init),
      #[cfg(target_os = "zkvm")]
      inner: None,
    }
  }
}

impl std::ops::Deref for EnvString {
  type Target = Option<String>;
  #[inline]
  fn deref(&self) -> &Option<String> {
    &self.inner
  }
}

/// `Option<u64>` env-var flag (e.g. `IX_MAX_REC_FUEL`). Compiles to `None`
/// on zkVM.
pub(crate) struct EnvOptU64 {
  #[cfg(not(target_os = "zkvm"))]
  inner: std::sync::LazyLock<Option<u64>, fn() -> Option<u64>>,
  #[cfg(target_os = "zkvm")]
  inner: Option<u64>,
}

impl EnvOptU64 {
  pub(crate) const fn new(_init: fn() -> Option<u64>) -> Self {
    Self {
      #[cfg(not(target_os = "zkvm"))]
      inner: std::sync::LazyLock::new(_init),
      #[cfg(target_os = "zkvm")]
      inner: None,
    }
  }
}

impl std::ops::Deref for EnvOptU64 {
  type Target = Option<u64>;
  #[inline]
  fn deref(&self) -> &Option<u64> {
    &self.inner
  }
}

pub mod anon_env;
pub mod anon_work;
pub mod canonical_check;
pub mod check;
pub mod claim;
pub mod congruence;
pub mod constant;
pub mod def_eq;
pub mod env;
pub mod equiv;
pub mod error;
pub mod expr;
pub mod id;
pub mod inductive;
pub mod infer;
pub mod ingress;
pub mod lctx;
pub mod level;
pub mod mode;
pub mod perf;
pub mod primitive;
// Sharding cost model + partitioner (out-of-circuit). `profile` records
// per-block heartbeats + the delta-unfold graph (the cost graph); `shard`
// partitions that graph into balanced, low-cross-ingress shards. Ported here
// from jcb/kernel-sharding (was the monolithic `crate::ix::{profile,shard}`):
// `profile` must live in the kernel crate because `KEnv` holds a `ProfileSink`.
//
// `profile` is dependency-light (hash maps only) so it compiles for the zkVM
// guest, where the `ProfileSink` field is simply always `None`. `shard` is the
// host-only partitioner — it uses rayon + `std::time` (gated to the same
// non-riscv targets that supply those deps), and the guest never partitions.
pub mod profile;
#[cfg(not(target_arch = "riscv64"))]
pub mod shard;
pub mod subst;
pub mod tc;
pub mod whnf;

#[cfg(test)]
pub mod testing;
#[cfg(test)]
mod tutorial;
