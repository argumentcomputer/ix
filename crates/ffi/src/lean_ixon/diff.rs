//! Env diff FFI: `rs_diff_envs` (two serialized byte arrays),
//! `rs_diff_env_files` (two file paths, memory-mapped), and
//! `rs_ixe_files_equal` (byte-equality fast path) — all marshaling the
//! [`EnvDiff`] report to Lean (`Ixon.EnvDiff`).
//!
//! Both modes load via the memory-lean lazy-index path
//! (`parse_lazy_index` + `from_lazy_index`/`from_lazy_index_mmap` —
//! `ConstantMeta` is never bulk-materialized); meta mode additionally
//! streams both files' §5 named sections in a lockstep merge-join
//! (`ixon::diff::diff_envs_lazy`). The file-path entry keeps constant
//! windows as zero-copy mmap slices, so neither the 2× file bytes nor
//! the const-window copies of the ByteArray path are resident. Large
//! inputs get incremental progress on stderr.
//!
//! Names cross the boundary pre-rendered (`Name::pretty()`) and
//! pre-sorted; addresses cross raw so Lean owns display formatting.

use std::sync::Arc;
use std::time::Instant;

use ix_common::address::Address;
use ixon::diff::{
  DiffPhase, EnvDiff, EnvStats, JoinProgress, LazySide, NamedChange,
  diff_envs_lazy,
};
use ixon::env::{Env as IxonEnv, LazyIndex};
use lean_ffi::object::{
  LeanArray, LeanBool, LeanBorrowed, LeanByteArray, LeanExcept, LeanIOResult,
  LeanOption, LeanOwned, LeanProd, LeanString,
};

use crate::lean::{
  LeanIxAddress, LeanIxonEnvDiff, LeanIxonEnvStats, LeanIxonNamedDiff,
};

fn addr_array(v: &[Address]) -> LeanArray<LeanOwned> {
  let arr = LeanArray::alloc(v.len());
  for (i, a) in v.iter().enumerate() {
    arr.set(i, LeanIxAddress::build(a));
  }
  arr
}

fn string_array(v: &[String]) -> LeanArray<LeanOwned> {
  let arr = LeanArray::alloc(v.len());
  for (i, s) in v.iter().enumerate() {
    arr.set(i, LeanString::new(s));
  }
  arr
}

/// `Array (String × Address)`
fn name_addr_array(v: &[(String, Address)]) -> LeanArray<LeanOwned> {
  let arr = LeanArray::alloc(v.len());
  for (i, (s, a)) in v.iter().enumerate() {
    arr.set(i, LeanProd::new(LeanString::new(s), LeanIxAddress::build(a)));
  }
  arr
}

/// `Array (String × Array String)`
fn name_labels_array(v: &[(String, Vec<String>)]) -> LeanArray<LeanOwned> {
  let arr = LeanArray::alloc(v.len());
  for (i, (s, labels)) in v.iter().enumerate() {
    arr.set(i, LeanProd::new(LeanString::new(s), string_array(labels)));
  }
  arr
}

/// `Array (Address × String × String)` (right-nested prod)
fn hint_array(v: &[(Address, String, String)]) -> LeanArray<LeanOwned> {
  let arr = LeanArray::alloc(v.len());
  for (i, (a, old, new)) in v.iter().enumerate() {
    arr.set(
      i,
      LeanProd::new(
        LeanIxAddress::build(a),
        LeanProd::new(LeanString::new(old), LeanString::new(new)),
      ),
    );
  }
  arr
}

fn opt_addr(o: &Option<Address>) -> LeanOwned {
  match o {
    None => LeanOption::none().into(),
    Some(a) => LeanOption::some(LeanIxAddress::build(a)).into(),
  }
}

impl LeanIxonEnvStats<LeanOwned> {
  /// Build `Ixon.EnvStats { consts, named, blobs, comms }`.
  fn build(s: &EnvStats) -> Self {
    let ctor = LeanIxonEnvStats::alloc(0);
    ctor.set_num_64(0, s.consts as u64);
    ctor.set_num_64(1, s.named as u64);
    ctor.set_num_64(2, s.blobs as u64);
    ctor.set_num_64(3, s.comms as u64);
    ctor
  }
}

impl LeanIxonNamedDiff<LeanOwned> {
  /// Build `Ixon.NamedDiff { name, oldAddr, newAddr, oldKind, newKind,
  /// fields, metaFields, rippled }`.
  fn build(c: &NamedChange) -> Self {
    let ctor = LeanIxonNamedDiff::alloc(0);
    ctor.set_obj(0, LeanString::new(&c.name));
    ctor.set_obj(1, LeanIxAddress::build(&c.old_addr));
    ctor.set_obj(2, LeanIxAddress::build(&c.new_addr));
    ctor.set_obj(3, LeanString::new(c.old_kind));
    ctor.set_obj(4, LeanString::new(c.new_kind));
    ctor.set_obj(5, string_array(&c.fields));
    ctor.set_obj(6, string_array(&c.meta_fields));
    ctor.set_num_8(0, u8::from(c.rippled));
    ctor
  }
}

impl LeanIxonEnvDiff<LeanOwned> {
  /// Build `Ixon.EnvDiff` — field order MUST match the Lean structure.
  fn build(d: &EnvDiff) -> Self {
    let main_changed: LeanOwned = match &d.main_changed {
      None => LeanOption::none().into(),
      Some((a, b)) => {
        LeanOption::some(LeanProd::new(opt_addr(a), opt_addr(b))).into()
      },
    };
    let named_changed = LeanArray::alloc(d.named_changed.len());
    for (i, c) in d.named_changed.iter().enumerate() {
      named_changed.set(i, LeanIxonNamedDiff::build(c));
    }
    let ctor = LeanIxonEnvDiff::alloc(0);
    ctor.set_obj(0, main_changed);
    ctor.set_obj(1, addr_array(&d.assumptions_added));
    ctor.set_obj(2, addr_array(&d.assumptions_removed));
    ctor.set_obj(3, name_addr_array(&d.named_added));
    ctor.set_obj(4, name_addr_array(&d.named_removed));
    ctor.set_obj(5, named_changed);
    ctor.set_obj(6, name_labels_array(&d.named_meta_only));
    ctor.set_obj(7, addr_array(&d.comms_added));
    ctor.set_obj(8, addr_array(&d.comms_removed));
    ctor.set_obj(9, addr_array(&d.comms_changed));
    ctor.set_obj(10, addr_array(&d.consts_only_a));
    ctor.set_obj(11, addr_array(&d.consts_only_b));
    ctor.set_obj(12, addr_array(&d.blobs_only_a));
    ctor.set_obj(13, addr_array(&d.blobs_only_b));
    ctor.set_obj(14, hint_array(&d.hints_changed));
    ctor.set_obj(15, LeanIxonEnvStats::build(&d.stats_a));
    ctor.set_obj(16, LeanIxonEnvStats::build(&d.stats_b));
    ctor
  }
}

/// Inputs at least this large get incremental progress on stderr
/// (`[rs_diff_envs] …` lines, matching the `[rs_compile_env]` idiom).
/// Small inputs — unit tests, property tests, tiny bundles — stay
/// silent.
const PROGRESS_MIN_BYTES: usize = 100 * 1024 * 1024;

/// Stderr line per progress event, tagged by phase.
fn print_progress(p: &JoinProgress) {
  match p.phase {
    DiffPhase::MetaSweep => eprintln!(
      "[rs_diff_envs] meta sweep: {}/{} ({} differing so far)",
      p.done, p.total, p.changed
    ),
    DiffPhase::NamedJoin => eprintln!(
      "[rs_diff_envs] named join: {}/{} ({} changed so far)",
      p.done, p.total, p.changed
    ),
    DiffPhase::RippleClassify => eprintln!(
      "[rs_diff_envs] ripple pass: {}/{} ({} roots so far)",
      p.done, p.total, p.changed
    ),
  }
}

fn print_parse_start(which: &str, len: usize, progress: bool) {
  if progress {
    eprintln!(
      "[rs_diff_envs] parsing {which} env ({} MB, lazy reader)...",
      len / 1_000_000
    );
  }
}

fn print_parse_done(which: &str, t: Instant, env: &IxonEnv, progress: bool) {
  if progress {
    eprintln!(
      "[rs_diff_envs] {which} env parsed in {:.1}s ({} consts, {} named, {} blobs)",
      t.elapsed().as_secs_f64(),
      env.consts.len(),
      env.named.len(),
      env.blobs.len()
    );
  }
}

/// Lazy-parse one heap-backed side: index + env.
fn parse_side_bytes(
  bytes: &[u8],
  which: &str,
  progress: bool,
) -> Result<(LazyIndex, IxonEnv), String> {
  print_parse_start(which, bytes.len(), progress);
  let t = Instant::now();
  let index = IxonEnv::parse_lazy_index(bytes)
    .map_err(|e| format!("{which} input: {e}"))?;
  let env = IxonEnv::from_lazy_index(&index, bytes)
    .map_err(|e| format!("{which} input: {e}"))?;
  print_parse_done(which, t, &env, progress);
  Ok((index, env))
}

/// Run the shared lazy diff over two prepared sides and marshal.
fn run_diff(
  a: LazySide<'_>,
  b: LazySide<'_>,
  want_meta: bool,
  progress: bool,
  who: &str,
) -> Result<EnvDiff, String> {
  let t = Instant::now();
  let mut on_progress = |p: JoinProgress| {
    if progress {
      print_progress(&p);
    }
  };
  let d = diff_envs_lazy(a, b, want_meta, &mut on_progress)?;
  if progress {
    eprintln!("[{who}] diff computed in {:.1}s", t.elapsed().as_secs_f64());
  }
  Ok(d)
}

/// FFI: diff two serialized envs.
/// `(a b : ByteArray) → (meta : Bool) → Except String Ixon.EnvDiff`.
/// Pure result; both modes use the lazy reader (meta mode adds the
/// streaming §5 sweep). For large inputs, progress goes to stderr.
#[unsafe(no_mangle)]
pub extern "C" fn rs_diff_envs(
  a: LeanByteArray<LeanBorrowed<'_>>,
  b: LeanByteArray<LeanBorrowed<'_>>,
  meta: LeanBool<LeanBorrowed<'_>>,
) -> LeanExcept<LeanOwned> {
  let (a_bytes, b_bytes) = (a.as_bytes(), b.as_bytes());
  let progress =
    a_bytes.len() >= PROGRESS_MIN_BYTES || b_bytes.len() >= PROGRESS_MIN_BYTES;
  let want_meta = meta.to_bool();
  let sides = parse_side_bytes(a_bytes, "first", progress)
    .and_then(|a| Ok((a, parse_side_bytes(b_bytes, "second", progress)?)));
  let ((ia, ea), (ib, eb)) = match sides {
    Ok(s) => s,
    Err(e) => return LeanExcept::error_string(&format!("rs_diff_envs: {e}")),
  };
  match run_diff(
    LazySide { env: &ea, index: &ia, data: a_bytes },
    LazySide { env: &eb, index: &ib, data: b_bytes },
    want_meta,
    progress,
    "rs_diff_envs",
  ) {
    Ok(d) => LeanExcept::ok(LeanIxonEnvDiff::build(&d)),
    Err(e) => LeanExcept::error_string(&format!("rs_diff_envs: {e}")),
  }
}

/// Memory-map a file, guarding against a concurrent length change.
/// Shared with `rs_pack_env` (`super::pack`).
pub(crate) fn mmap_file(
  path: &str,
  which: &str,
) -> Result<Arc<memmap2::Mmap>, String> {
  let file = std::fs::File::open(path)
    .map_err(|e| format!("{which} input {path}: {e}"))?;
  let expected =
    file.metadata().map_err(|e| format!("{which} input {path}: {e}"))?.len();
  let mmap = unsafe { memmap2::Mmap::map(&file) }
    .map_err(|e| format!("{which} input {path}: mmap failed: {e}"))?;
  if mmap.len() as u64 != expected {
    return Err(format!(
      "{which} input {path}: mapped length {} != metadata length {expected}",
      mmap.len()
    ));
  }
  Ok(Arc::new(mmap))
}

/// Lazy-parse one mmap-backed side: constant windows stay zero-copy.
fn parse_side_mmap(
  mmap: &Arc<memmap2::Mmap>,
  which: &str,
  progress: bool,
) -> Result<(LazyIndex, IxonEnv), String> {
  print_parse_start(which, mmap.len(), progress);
  let t = Instant::now();
  let index = IxonEnv::parse_lazy_index(&mmap[..])
    .map_err(|e| format!("{which} input: {e}"))?;
  let env = IxonEnv::from_lazy_index_mmap(&index, mmap)
    .map_err(|e| format!("{which} input: {e}"))?;
  print_parse_done(which, t, &env, progress);
  Ok((index, env))
}

/// FFI: diff two `.ixe` files by path, memory-mapped.
/// `(a b : String) → (meta : Bool) → IO Ixon.EnvDiff`.
/// Constant windows are zero-copy mmap slices, so neither the file
/// bytes nor const-window copies are heap-resident — the leanest diff
/// path for multi-GB envs. Errors surface as `IO` errors.
#[unsafe(no_mangle)]
pub extern "C" fn rs_diff_env_files(
  a_path: LeanString<LeanBorrowed<'_>>,
  b_path: LeanString<LeanBorrowed<'_>>,
  meta: LeanBool<LeanBorrowed<'_>>,
) -> LeanIOResult<LeanOwned> {
  let want_meta = meta.to_bool();
  let a_path = a_path.to_string();
  let b_path = b_path.to_string();
  let sides = mmap_file(&a_path, "first")
    .and_then(|ma| Ok((ma, mmap_file(&b_path, "second")?)));
  let (ma, mb) = match sides {
    Ok(s) => s,
    Err(e) => {
      return LeanIOResult::error_string(&format!("rs_diff_env_files: {e}"));
    },
  };
  let progress =
    ma.len() >= PROGRESS_MIN_BYTES || mb.len() >= PROGRESS_MIN_BYTES;
  let parsed = parse_side_mmap(&ma, "first", progress)
    .and_then(|a| Ok((a, parse_side_mmap(&mb, "second", progress)?)));
  let ((ia, ea), (ib, eb)) = match parsed {
    Ok(s) => s,
    Err(e) => {
      return LeanIOResult::error_string(&format!("rs_diff_env_files: {e}"));
    },
  };
  match run_diff(
    LazySide { env: &ea, index: &ia, data: &ma[..] },
    LazySide { env: &eb, index: &ib, data: &mb[..] },
    want_meta,
    progress,
    "rs_diff_env_files",
  ) {
    Ok(d) => LeanIOResult::ok(LeanIxonEnvDiff::build(&d)),
    Err(e) => LeanIOResult::error_string(&format!("rs_diff_env_files: {e}")),
  }
}

/// FFI: byte-equality of two files. `(a b : String) → IO Bool`.
/// Length fast path via metadata, then an mmap memcmp — no heap reads.
#[unsafe(no_mangle)]
pub extern "C" fn rs_ixe_files_equal(
  a_path: LeanString<LeanBorrowed<'_>>,
  b_path: LeanString<LeanBorrowed<'_>>,
) -> LeanIOResult<LeanOwned> {
  let a_path = a_path.to_string();
  let b_path = b_path.to_string();
  let len = |path: &str, which: &str| -> Result<u64, String> {
    std::fs::metadata(path)
      .map(|m| m.len())
      .map_err(|e| format!("{which} input {path}: {e}"))
  };
  let lens =
    len(&a_path, "first").and_then(|la| Ok((la, len(&b_path, "second")?)));
  let (la, lb) = match lens {
    Ok(s) => s,
    Err(e) => {
      return LeanIOResult::error_string(&format!("rs_ixe_files_equal: {e}"));
    },
  };
  let eq = if la != lb {
    false
  } else if la == 0 {
    true // two empty files; mmap of a zero-length file errors
  } else {
    let maps = mmap_file(&a_path, "first")
      .and_then(|ma| Ok((ma, mmap_file(&b_path, "second")?)));
    match maps {
      Ok((ma, mb)) => ma[..] == mb[..],
      Err(e) => {
        return LeanIOResult::error_string(&format!("rs_ixe_files_equal: {e}"));
      },
    }
  };
  LeanIOResult::ok(LeanOwned::box_usize(usize::from(eq)))
}
