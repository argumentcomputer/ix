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
//! `rs_pack_env_units` (M6R slice 5): the same bundle carrying whole
//! logical units, the Rust form of `Ix.Cli.PackCmd.packWholeUnits` (design
//! document §6.3): every member of the unit of every name whose constant the
//! bundle carries, read from the source's names and metadata
//! ([`ixon::unit::IxonUnitView`], one streamed pass over §5, also in `anon`
//! mode), joins the walk to a fixpoint
//! (`Env::prune_to_closure_streaming_units`,
//! `Env::prune_to_closure_anon_units`). Returns the rounds in which members
//! were missing and the members added.

use ix_common::address::Address;
use ix_common::env::Name;
use ixon::env::Env as IxonEnv;
use ixon::unit::{IxonUnitView, UnitStats};
use lean_ffi::object::{
  LeanArray, LeanBool, LeanBorrowed, LeanIOResult, LeanOwned, LeanProd,
  LeanString,
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
    false,
  ) {
    Ok(_) => LeanIOResult::ok(LeanOwned::box_usize(0)),
    Err(e) => LeanIOResult::error_string(&e),
  }
}

/// FFI: pack a value bundle carrying whole logical units (M6R slice 5).
/// `(envPath mainName : String) → (assume : Array String) →
/// (outPath : String) → (anon verbose : Bool) → IO (Nat × Nat)`: the
/// rounds in which unit members were missing and the members added.
#[unsafe(no_mangle)]
pub extern "C" fn rs_pack_env_units(
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
    true,
  ) {
    Ok(stats) => LeanIOResult::ok(LeanProd::new(
      LeanOwned::from_nat_u64(stats.rounds as u64),
      LeanOwned::from_nat_u64(stats.members as u64),
    )),
    Err(e) => LeanIOResult::error_string(&e),
  }
}

/// The body of both FFIs: `units` completes the logical units.
fn pack_env(
  path: &str,
  main_str: &str,
  assume_vec: &[String],
  out: &str,
  anon: bool,
  verbose: bool,
  units: bool,
) -> Result<UnitStats, String> {
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

  let (bundle, stats) = if units {
    let view = IxonUnitView::of_lazy(&index, &mmap[..], &names)
      .map_err(|e| format!("rs_pack_env: {e}"))?;
    if anon {
      src.prune_to_closure_anon_units(&main, &assumed, &view)
    } else {
      src.prune_to_closure_streaming_units(
        &index,
        &mmap[..],
        &names,
        &main,
        &assumed,
        &view,
      )
    }
  } else {
    let bundle = if anon {
      src.prune_to_closure_anon(&main, &assumed)
    } else {
      src.prune_to_closure_streaming(&index, &mmap[..], &names, &main, &assumed)
    };
    bundle.map(|b| (b, UnitStats::default()))
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
    if units {
      eprintln!(
        "[rs_pack_env] whole units: {} member(s) added in {} round(s)",
        stats.members, stats.rounds
      );
    }
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
  Ok(stats)
}

/// FFI: the Rust unit view of a serialized env (`ixon::unit::IxonUnitView`),
/// for comparison with `Ix.Cli.PackCmd.ixonUnitView` (the `pack-units` and
/// `pass3-rust-parity` suites). `(path : String) → IO (owners × roots ×
/// index)`: every name with an auxiliary owner and its owner; every owner (a
/// name's owner, or the name itself) and the roots of its unit, in order;
/// every unit key and its auxiliaries (in no particular order). Together
/// they determine `members` of every name.
#[unsafe(no_mangle)]
pub extern "C" fn rs_ixon_unit_view(
  env_path: LeanString<LeanBorrowed<'_>>,
) -> LeanIOResult<LeanOwned> {
  use crate::builder::LeanBuildCache;
  use crate::lean::LeanIxName;

  let path = env_path.to_string();
  let tables = unit_view_tables(&path);
  let (owners, roots, index) = match tables {
    Ok(t) => t,
    Err(e) => {
      return LeanIOResult::error_string(&format!("rs_ixon_unit_view: {e}"));
    },
  };
  let mut cache = LeanBuildCache::new();
  let names_arr = |cache: &mut LeanBuildCache, ns: &[Name]| {
    let arr = LeanArray::alloc(ns.len());
    for (i, m) in ns.iter().enumerate() {
      arr.set(i, LeanIxName::build(cache, m));
    }
    arr
  };
  let owners_arr = LeanArray::alloc(owners.len());
  for (i, (n, o)) in owners.iter().enumerate() {
    let pair = LeanProd::new(
      LeanIxName::build(&mut cache, n),
      LeanIxName::build(&mut cache, o),
    );
    owners_arr.set(i, pair);
  }
  let roots_arr = LeanArray::alloc(roots.len());
  for (i, (o, r)) in roots.iter().enumerate() {
    let pair =
      LeanProd::new(LeanIxName::build(&mut cache, o), names_arr(&mut cache, r));
    roots_arr.set(i, pair);
  }
  let index_arr = LeanArray::alloc(index.len());
  for (i, (k, ms)) in index.iter().enumerate() {
    let pair = LeanProd::new(
      LeanIxName::build(&mut cache, k),
      names_arr(&mut cache, ms),
    );
    index_arr.set(i, pair);
  }
  LeanIOResult::ok(LeanProd::new(
    owners_arr,
    LeanProd::new(roots_arr, index_arr),
  ))
}

/// The tables of [`rs_ixon_unit_view`]: owners, roots by owner, index by key.
type UnitTables =
  (Vec<(Name, Name)>, Vec<(Name, Vec<Name>)>, Vec<(Name, Vec<Name>)>);

fn unit_view_tables(path: &str) -> Result<UnitTables, String> {
  use ixon::unit::UnitView;
  let mmap = mmap_file(path, "source")?;
  let (index, names) = IxonEnv::parse_lazy_index_with_names(&mmap[..])
    .map_err(|e| format!("failed to index {path}: {e}"))?;
  let view = IxonUnitView::of_lazy(&index, &mmap[..], &names)?;
  let idx = view.index();
  let mut all: Vec<Name> = view.names();
  all.sort();
  let mut owners: Vec<(Name, Name)> = Vec::new();
  let mut roots: Vec<(Name, Vec<Name>)> = Vec::new();
  let mut seen: FxHashSet<Name> = FxHashSet::default();
  for n in &all {
    let o = match view.aux_owner(n) {
      Some(o) => {
        owners.push((n.clone(), o.clone()));
        o
      },
      None => n.clone(),
    };
    if seen.insert(o.clone()) {
      let r = view.roots(&o);
      roots.push((o, r));
    }
  }
  let mut index: Vec<(Name, Vec<Name>)> = idx.into_iter().collect();
  index.sort_by(|a, b| a.0.cmp(&b.0));
  Ok((owners, roots, index))
}
