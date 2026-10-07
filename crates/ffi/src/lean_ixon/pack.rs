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
//!
//! The bundle is the root's transitive reference closure, never its
//! compilation unit (owner, 2026-10-07): until M6R slice 6 an
//! `rs_pack_env_units` variant completed the logical units (slice 5,
//! M1-h's `packWholeUnits`); it was removed with the unit view it read.
//! Lean's implementation of the same closure is the test oracle
//! (`Tests.Ix.Compile.PackParity.packOracle`, byte for byte).

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
  match pack_env(
    &env_path.to_string(),
    &main_name.to_string(),
    &assume.map(|obj| obj.as_string().to_string()),
    &out_path.to_string(),
    anon.to_bool(),
    verbose.to_bool(),
  ) {
    Ok(()) => LeanIOResult::ok(LeanOwned::box_usize(0)),
    Err(e) => LeanIOResult::error_string(&e),
  }
}

/// The body of [`rs_pack_env`].
fn pack_env(
  path: &str,
  main_str: &str,
  assume_vec: &[String],
  out: &str,
  anon: bool,
  verbose: bool,
) -> Result<(), String> {
  let mmap =
    mmap_file(path, "source").map_err(|e| format!("rs_pack_env: {e}"))?;
  if verbose {
    eprintln!(
      "[rs_pack_env] parsing {path} ({} MB, lazy reader)...",
      mmap.len() / 1_000_000
    );
  }
  let (index, names) = IxonEnv::parse_lazy_index_with_names(&mmap[..])
    .map_err(|e| format!("rs_pack_env: failed to index {path}: {e}"))?;
  let src = IxonEnv::from_lazy_index_mmap(&index, &mmap)
    .map_err(|e| format!("rs_pack_env: failed to load {path}: {e}"))?;
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
  let main = match by_name.get(main_str) {
    Some(a) => a.clone(),
    None => {
      return Err(format!(
        "rs_pack_env: no constant named {main_str} in {path}"
      ));
    },
  };
  let mut assumed: FxHashSet<Address> = FxHashSet::default();
  let mut unresolved: Vec<&str> = Vec::new();
  for s in assume_vec {
    if let Some(a) = by_name.get(s.as_str()) {
      assumed.insert(a.clone());
    } else if let Some(a) = Address::from_hex(s) {
      assumed.insert(a);
    } else {
      unresolved.push(s);
    }
  }
  if !unresolved.is_empty() {
    return Err(format!(
      "rs_pack_env: --assume entries neither named in {path} nor 64-hex \
       addresses: [{}]",
      unresolved.join(", ")
    ));
  }

  let bundle = if anon {
    src.prune_to_closure_anon(&main, &assumed)
  } else {
    src.prune_to_closure_streaming(&index, &mmap[..], &names, &main, &assumed)
  }
  .map_err(|e| format!("rs_pack_env: {e}"))?;
  bundle.validate_closed().map_err(|e| format!("rs_pack_env: {e}"))?;
  let mut buf = Vec::new();
  bundle
    .put(&mut buf)
    .map_err(|e| format!("rs_pack_env: bundle serialization failed: {e}"))?;
  std::fs::write(out, &buf)
    .map_err(|e| format!("rs_pack_env: failed to write {out}: {e}"))?;
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
  Ok(())
}
