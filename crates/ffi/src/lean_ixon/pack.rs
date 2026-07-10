//! `rs_pack_env`: read a serialized env, prune it to the self-contained
//! closure of one named constant ([`ixon::env::Env::prune_to_closure`] —
//! sets `main` and collects reached cut-points into `assumptions`),
//! validate the result ([`ixon::env::Env::validate_closed`]), and write
//! the bundle `.ixe`.
//!
//! Uses the full reader (`Env::get`): the prune's named fixpoint carries
//! display metadata (names, `DataValue` blobs, aux `original`s), which
//! the anon/lazy views drop. At mathlib scale that means tens of GB
//! resident for the source env — functional, but heavy; a leaner
//! selective-metadata pack (stream §5, carry only survivors) is future
//! work on the diff meta-sweep streaming machinery.

use ix_common::address::Address;
use ixon::env::Env as IxonEnv;
use lean_ffi::object::{
  LeanArray, LeanBool, LeanBorrowed, LeanIOResult, LeanOwned, LeanString,
};
use rustc_hash::{FxHashMap, FxHashSet};

/// FFI: pack a value bundle.
/// `(envPath mainName : String) → (assume : Array String) →
/// (outPath : String) → (verbose : Bool) → IO Unit`.
///
/// `assume` entries resolve as displayed constant names first, else as
/// 64-hex constant addresses (cut points need not be named).
#[unsafe(no_mangle)]
pub extern "C" fn rs_pack_env(
  env_path: LeanString<LeanBorrowed<'_>>,
  main_name: LeanString<LeanBorrowed<'_>>,
  assume: LeanArray<LeanBorrowed<'_>>,
  out_path: LeanString<LeanBorrowed<'_>>,
  verbose: LeanBool<LeanBorrowed<'_>>,
) -> LeanIOResult<LeanOwned> {
  let verbose = verbose.to_bool();
  let path = env_path.to_string();
  let main_str = main_name.to_string();
  let out = out_path.to_string();
  let assume_vec: Vec<String> = assume.map(|obj| obj.as_string().to_string());

  let bytes = match std::fs::read(&path) {
    Ok(bytes) => bytes,
    Err(e) => {
      return LeanIOResult::error_string(&format!(
        "rs_pack_env: failed to read {path}: {e}"
      ));
    },
  };
  if verbose {
    eprintln!(
      "[rs_pack_env] parsing {path} ({} MB, full reader)...",
      bytes.len() / 1_000_000
    );
  }
  let mut slice: &[u8] = &bytes;
  let full = match IxonEnv::get(&mut slice) {
    Ok(env) => env,
    Err(e) => {
      return LeanIOResult::error_string(&format!(
        "rs_pack_env: failed to deserialize {path}: {e}"
      ));
    },
  };
  if verbose {
    eprintln!(
      "[rs_pack_env] source env: {} consts, {} named, {} blobs",
      full.consts.len(),
      full.named.len(),
      full.blobs.len()
    );
  }

  // Resolve displayed names → addresses through the full env's `named`
  // metadata (the `rs_env_extract` idiom).
  let by_name: FxHashMap<String, Address> = full
    .named
    .iter()
    .map(|e| (e.key().to_string(), e.value().addr.clone()))
    .collect();
  let main = match by_name.get(&main_str) {
    Some(a) => a.clone(),
    None => {
      return LeanIOResult::error_string(&format!(
        "rs_pack_env: no constant named {main_str} in {path}"
      ));
    },
  };
  let mut assumed: FxHashSet<Address> = FxHashSet::default();
  let mut unresolved: Vec<&str> = Vec::new();
  for s in &assume_vec {
    if let Some(a) = by_name.get(s.as_str()) {
      assumed.insert(a.clone());
    } else if let Some(a) = Address::from_hex(s) {
      assumed.insert(a);
    } else {
      unresolved.push(s);
    }
  }
  if !unresolved.is_empty() {
    return LeanIOResult::error_string(&format!(
      "rs_pack_env: --assume entries neither named in {path} nor 64-hex \
       addresses: [{}]",
      unresolved.join(", ")
    ));
  }

  let bundle = match full.prune_to_closure(&main, &assumed) {
    Ok(b) => b,
    Err(e) => return LeanIOResult::error_string(&format!("rs_pack_env: {e}")),
  };
  if let Err(e) = bundle.validate_closed() {
    return LeanIOResult::error_string(&format!("rs_pack_env: {e}"));
  }
  let mut buf = Vec::new();
  if let Err(e) = bundle.put(&mut buf) {
    return LeanIOResult::error_string(&format!(
      "rs_pack_env: bundle serialization failed: {e}"
    ));
  }
  if let Err(e) = std::fs::write(&out, &buf) {
    return LeanIOResult::error_string(&format!(
      "rs_pack_env: failed to write {out}: {e}"
    ));
  }
  if verbose {
    eprintln!("[rs_pack_env] main {} ({main_str})", main.hex());
    eprintln!(
      "[rs_pack_env] kept {}/{} consts, {}/{} named, {}/{} blobs, \
       {} assumption(s)",
      bundle.consts.len(),
      full.consts.len(),
      bundle.named.len(),
      full.named.len(),
      bundle.blobs.len(),
      full.blobs.len(),
      bundle.assumptions.len()
    );
    eprintln!("[rs_pack_env] wrote {out} ({} bytes)", buf.len());
  }
  LeanIOResult::ok(LeanOwned::box_usize(0))
}
