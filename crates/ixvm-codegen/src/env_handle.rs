//! `EnvHandle`: a Rust-owned `ixon::Env` exposed to Lean as an opaque
//! external handle.
//!
//! Built once per CLI invocation from either a memory-mappable `.ixe`
//! path or a `Ixon.serEnv`-shaped byte blob. All downstream per-claim /
//! per-shard FFI calls take a `&EnvHandle` (shared across the batch) so
//! the env is parsed exactly once instead of every call.
//!
//! `anon_hints` (`Defn` reducibility hints) are populated at handle
//! construction time. `Env::get_anon_mmap` already harvests them;
//! `Env::get` (full-form decode used by the bytes-blob path) does
//! not, so `from_bytes` runs the harvest post-decode.

use ixon::{Env, metadata::ConstantMetaInfo};

pub struct EnvHandle {
  pub env: Env,
}

impl EnvHandle {
  /// Load via `Env::get_anon_mmap` (zero-copy mmap of the `.ixe` file).
  /// Anon-mode parser already harvests `anon_hints` — no post-pass.
  pub fn from_ixe_path(path: &std::path::Path) -> Result<Self, String> {
    let env = Env::get_anon_mmap(path)?;
    Ok(Self { env })
  }

  /// Decode a serialized env blob (`Ixon.serEnv` output) via
  /// `Env::get`, then harvest `anon_hints` from each `Def` named
  /// entry. Used by the compiled-Lean-env path where the env is built
  /// in Lean memory and serialized for the cross-FFI handoff.
  pub fn from_bytes(bytes: &[u8]) -> Result<Self, String> {
    let mut cursor: &[u8] = bytes;
    let mut env = Env::get(&mut cursor)?;
    // `Env::get` reads named entries but doesn't populate
    // `env.anon_hints`. Walk `env.named` and insert each `Def`
    // variant's `hints`. Mirrors the in-line harvest inside
    // `Env::get_anon`.
    let hints: Vec<_> = env
      .named
      .iter()
      .filter_map(|entry| {
        let named = entry.value();
        if let ConstantMetaInfo::Def { hints, .. } = &named.meta().info {
          Some((named.addr.clone(), *hints))
        } else {
          None
        }
      })
      .collect();
    for (addr, h) in hints {
      env.anon_hints.insert(addr, h);
    }
    Ok(Self { env })
  }
}
