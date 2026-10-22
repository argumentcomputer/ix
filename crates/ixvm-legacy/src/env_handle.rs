//! `EnvHandle`: a Rust-owned `ixon::Env` exposed to Lean as an opaque
//! external handle.
//!
//! Built once per CLI invocation from either a memory-mappable `.ixe`
//! path or a `Ixon.serEnv`-shaped byte blob. All downstream per-claim /
//! per-shard FFI calls take a `&EnvHandle` (shared across the batch) so
//! the env is parsed exactly once instead of every call.
//!
//! `anon_hints` (`Defn` reducibility hints) come from the `.ixe` §3
//! hints section, which every writer emits straight from the
//! `Env::anon_hints` map — both readers used here populate the map
//! directly, so no post-decode harvest is needed.

use ixon::Env;

pub struct EnvHandle {
  pub env: Env,
}

impl EnvHandle {
  /// Load via `Env::get_anon_mmap` (zero-copy mmap of the `.ixe` file).
  pub fn from_ixe_path(path: &std::path::Path) -> Result<Self, String> {
    let env = Env::get_anon_mmap(path)?;
    Ok(Self { env })
  }

  /// Decode a serialized env blob (`Ixon.serEnv` output) via
  /// `Env::get`. Used by the compiled-Lean-env path where the env is
  /// built in Lean memory and serialized for the cross-FFI handoff.
  pub fn from_bytes(bytes: &[u8]) -> Result<Self, String> {
    let mut cursor: &[u8] = bytes;
    let env = Env::get(&mut cursor)?;
    Ok(Self { env })
  }
}
