//! `rs_pack_env`: read a serialized env, prune it to the self-contained
//! closure of one named constant ([`ixon::env::Env::prune_to_closure`]
//! semantics — sets `main` and collects reached cut-points into
//! `assumptions`), validate the result
//! ([`ixon::env::Env::validate_closed`]), and write the bundle `.ixe`.
//!
//! The source env is memory-mapped and lazily loaded (constant windows
//! stay zero-copy mmap slices); metadata is never bulk-materialized.
//! The default mode carries display metadata by re-streaming §5 per
//! prune fixpoint round (`Env::prune_to_closure_streaming` —
//! O(survivors) resident metadata); `anon` mode skips metadata
//! entirely (`Env::prune_to_closure_anon` — value closure + §3 hints
//! only, the minimal typecheck/eval artifact).

use ix_common::address::Address;
use ixon::env::Env as IxonEnv;
use lean_ffi::object::{
  LeanArray, LeanBool, LeanBorrowed, LeanIOResult, LeanOwned, LeanString,
};
use rustc_hash::{FxHashMap, FxHashSet};

use super::diff::mmap_file;

/// FFI: pack a value bundle.
/// `(envPath mainName : String) → (assume : Array String) →
/// (outPath : String) → (anon verbose : Bool) → IO Unit`.
///
/// `assume` entries resolve as displayed constant names first, else as
/// 64-hex constant addresses (cut points need not be named).
#[unsafe(no_mangle)]
pub extern "C" fn rs_pack_env(
  env_path: LeanString<LeanBorrowed<'_>>,
  main_name: LeanString<LeanBorrowed<'_>>,
  assume: LeanArray<LeanBorrowed<'_>>,
  out_path: LeanString<LeanBorrowed<'_>>,
  anon: LeanBool<LeanBorrowed<'_>>,
  verbose: LeanBool<LeanBorrowed<'_>>,
) -> LeanIOResult<LeanOwned> {
  let anon = anon.to_bool();
  let verbose = verbose.to_bool();
  let path = env_path.to_string();
  let main_str = main_name.to_string();
  let out = out_path.to_string();
  let assume_vec: Vec<String> = assume.map(|obj| obj.as_string().to_string());

  let mmap = match mmap_file(&path, "source") {
    Ok(m) => m,
    Err(e) => return LeanIOResult::error_string(&format!("rs_pack_env: {e}")),
  };
  if verbose {
    eprintln!(
      "[rs_pack_env] parsing {path} ({} MB, lazy reader)...",
      mmap.len() / 1_000_000
    );
  }
  let (index, names) = match IxonEnv::parse_lazy_index_with_names(&mmap[..]) {
    Ok(v) => v,
    Err(e) => {
      return LeanIOResult::error_string(&format!(
        "rs_pack_env: failed to index {path}: {e}"
      ));
    },
  };
  let src = match IxonEnv::from_lazy_index_mmap(&index, &mmap) {
    Ok(env) => env,
    Err(e) => {
      return LeanIOResult::error_string(&format!(
        "rs_pack_env: failed to load {path}: {e}"
      ));
    },
  };
  if verbose {
    eprintln!(
      "[rs_pack_env] source env: {} consts, {} named, {} blobs",
      src.consts.len(),
      src.named.len(),
      src.blobs.len()
    );
  }

  // Resolve displayed names → addresses through the lazy index's
  // name→addr entries (the `rs_env_extract` idiom).
  let by_name: FxHashMap<String, Address> =
    index.named.iter().map(|n| (n.name.to_string(), n.addr.clone())).collect();
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

  let bundle = if anon {
    src.prune_to_closure_anon(&main, &assumed)
  } else {
    src.prune_to_closure_streaming(&index, &mmap[..], &names, &main, &assumed)
  };
  let bundle = match bundle {
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
       {} assumption(s){}",
      bundle.consts.len(),
      src.consts.len(),
      bundle.named.len(),
      src.named.len(),
      bundle.blobs.len(),
      src.blobs.len(),
      bundle.assumptions.len(),
      if anon { " [anon: no display metadata]" } else { "" }
    );
    eprintln!("[rs_pack_env] wrote {out} ({} bytes)", buf.len());
  }
  LeanIOResult::ok(LeanOwned::box_usize(0))
}
