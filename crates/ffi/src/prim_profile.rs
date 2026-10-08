//! `ix prims` FFI: export the primitive profile of an `.ixe` and describe
//! a profile file. Presentation lives in `Ix/Cli/PrimsCmd.lean`; the object
//! itself is `ixon::prim_profile::PrimProfile`.

use std::sync::Arc;

use ixon::env::Env as IxonEnv;
use ixon::prim_profile::PrimProfile;
use lean_ffi::object::{LeanBorrowed, LeanIOResult, LeanOwned, LeanString};

fn load_env(path: &str) -> Result<IxonEnv, String> {
  let file = std::fs::File::open(path).map_err(|e| format!("{path}: {e}"))?;
  let mmap = unsafe { memmap2::Mmap::map(&file) }
    .map_err(|e| format!("{path}: mmap failed: {e}"))?;
  let mmap = Arc::new(mmap);
  let index =
    IxonEnv::parse_lazy_index(&mmap[..]).map_err(|e| format!("{path}: {e}"))?;
  IxonEnv::from_lazy_index_mmap(&index, &mmap)
    .map_err(|e| format!("{path}: {e}"))
}

fn export(ixe_path: &str, out_path: &str) -> Result<String, String> {
  let env = load_env(ixe_path)?;
  let profile = PrimProfile::from_env(&env)?;
  let (addr, bytes) = profile.commit();
  std::fs::write(out_path, bytes).map_err(|e| format!("{out_path}: {e}"))?;
  Ok(addr.hex())
}

fn info(path: &str) -> Result<String, String> {
  let bytes = std::fs::read(path).map_err(|e| format!("{path}: {e}"))?;
  let profile = PrimProfile::get(&mut &bytes[..])?;
  let builtin =
    PrimProfile::from_addrs(&ix_common::prim_addrs::PrimAddrs::new());
  let roles: Vec<serde_json::Value> = PrimProfile::role_names()
    .zip(profile.addrs.iter())
    .map(|(name, addr)| serde_json::json!({"name": name, "addr": addr.hex()}))
    .collect();
  let summary = serde_json::json!({
    "address": profile.address().hex(),
    "objectFormat": IxonEnv::OBJECT_FORMAT,
    "roles": roles,
    "matchesBuiltin": profile == builtin,
  });
  Ok(summary.to_string())
}

/// Lean signature:
/// ```lean
/// @[extern "rs_prim_profile_export"]
/// opaque rsPrimProfileExportFFI : @& String → @& String → IO String
/// ```
/// Writes the profile object of `ixe_path`'s toolchain to `out_path` and
/// returns its address hex.
#[unsafe(no_mangle)]
pub extern "C" fn rs_prim_profile_export(
  ixe_path: LeanString<LeanBorrowed<'_>>,
  out_path: LeanString<LeanBorrowed<'_>>,
) -> LeanIOResult<LeanOwned> {
  match export(ixe_path.as_str(), out_path.as_str()) {
    Ok(hex) => LeanIOResult::ok(LeanString::new(&hex)),
    Err(e) => {
      LeanIOResult::error_string(&format!("rs_prim_profile_export: {e}"))
    },
  }
}

/// Lean signature:
/// ```lean
/// @[extern "rs_prim_profile_info"]
/// opaque rsPrimProfileInfoFFI : @& String → IO String
/// ```
/// JSON `{address, objectFormat, roles: [{name, addr}], matchesBuiltin}`.
#[unsafe(no_mangle)]
pub extern "C" fn rs_prim_profile_info(
  path: LeanString<LeanBorrowed<'_>>,
) -> LeanIOResult<LeanOwned> {
  match info(path.as_str()) {
    Ok(json) => LeanIOResult::ok(LeanString::new(&json)),
    Err(e) => LeanIOResult::error_string(&format!("rs_prim_profile_info: {e}")),
  }
}
