//! `rs_diff_envs`: parse two serialized envs, diff them in Rust
//! (`ixon::diff`), and marshal the [`EnvDiff`] report to Lean
//! (`Ixon.EnvDiff`).
//!
//! Anon mode (the default) loads via the memory-lean lazy-index path
//! (`parse_lazy_index` + `Env::from_lazy_index` — ConstantMeta is never
//! materialized); meta mode uses the full reader (`Env::get`,
//! preserving `Named.meta`/`original`). Large inputs get incremental
//! progress on stderr.
//!
//! Names cross the boundary pre-rendered (`Name::pretty()`) and
//! pre-sorted; addresses cross raw so Lean owns display formatting.

use std::time::Instant;

use ix_common::address::Address;
use ixon::diff::{EnvDiff, EnvStats, NamedChange, diff_envs_with};
use ixon::env::Env as IxonEnv;
use lean_ffi::object::{
  LeanArray, LeanBool, LeanBorrowed, LeanByteArray, LeanExcept, LeanOption,
  LeanOwned, LeanProd, LeanString,
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
  /// fields, metaFields }`.
  fn build(c: &NamedChange) -> Self {
    let ctor = LeanIxonNamedDiff::alloc(0);
    ctor.set_obj(0, LeanString::new(&c.name));
    ctor.set_obj(1, LeanIxAddress::build(&c.old_addr));
    ctor.set_obj(2, LeanIxAddress::build(&c.new_addr));
    ctor.set_obj(3, LeanString::new(c.old_kind));
    ctor.set_obj(4, LeanString::new(c.new_kind));
    ctor.set_obj(5, string_array(&c.fields));
    ctor.set_obj(6, string_array(&c.meta_fields));
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

/// FFI: diff two serialized envs.
/// `(a b : ByteArray) → (meta : Bool) → Except String Ixon.EnvDiff`.
/// Pure result; reader choice (lazy-index vs full) follows `meta` —
/// see the module docs. For large inputs, progress goes to stderr.
#[unsafe(no_mangle)]
pub extern "C" fn rs_diff_envs(
  a: LeanByteArray<LeanBorrowed<'_>>,
  b: LeanByteArray<LeanBorrowed<'_>>,
  meta: LeanBool<LeanBorrowed<'_>>,
) -> LeanExcept<LeanOwned> {
  let progress = a.as_bytes().len() >= PROGRESS_MIN_BYTES
    || b.as_bytes().len() >= PROGRESS_MIN_BYTES;
  let want_meta = meta.to_bool();
  // Anon mode loads via the lazy index: constant byte-windows +
  // name→addr + §3 hints + §6 comms, never materializing ConstantMeta
  // — at mathlib scale the full reader's metadata costs tens of GB and
  // OOMs a 128 GB machine when two envs are held at once. Meta mode
  // needs `Named.meta`/`original`, so it pays for the full reader.
  let parse = |bytes: &[u8], which: &str| -> Result<IxonEnv, String> {
    let reader = if want_meta { "full" } else { "anon" };
    if progress {
      eprintln!(
        "[rs_diff_envs] parsing {which} env ({} MB, {reader} reader)...",
        bytes.len() / 1_000_000
      );
    }
    let t = Instant::now();
    let env = if want_meta {
      let mut cursor: &[u8] = bytes;
      IxonEnv::get(&mut cursor).map_err(|e| format!("{which} input: {e}"))?
    } else {
      let index = IxonEnv::parse_lazy_index(bytes)
        .map_err(|e| format!("{which} input: {e}"))?;
      IxonEnv::from_lazy_index(&index, bytes)
        .map_err(|e| format!("{which} input: {e}"))?
    };
    if progress {
      eprintln!(
        "[rs_diff_envs] {which} env parsed in {:.1}s ({} consts, {} named, {} blobs)",
        t.elapsed().as_secs_f64(),
        env.consts.len(),
        env.named.len(),
        env.blobs.len()
      );
    }
    Ok(env)
  };
  let env_a = match parse(a.as_bytes(), "first") {
    Ok(env) => env,
    Err(e) => return LeanExcept::error_string(&format!("rs_diff_envs: {e}")),
  };
  let env_b = match parse(b.as_bytes(), "second") {
    Ok(env) => env,
    Err(e) => return LeanExcept::error_string(&format!("rs_diff_envs: {e}")),
  };
  let t = Instant::now();
  let mut on_progress = |p: ixon::diff::JoinProgress| {
    if progress {
      eprintln!(
        "[rs_diff_envs] named join: {}/{} ({} changed so far)",
        p.done, p.total, p.changed
      );
    }
  };
  match diff_envs_with(&env_a, &env_b, want_meta, &mut on_progress) {
    Ok(d) => {
      if progress {
        eprintln!(
          "[rs_diff_envs] diff computed in {:.1}s",
          t.elapsed().as_secs_f64()
        );
      }
      LeanExcept::ok(LeanIxonEnvDiff::build(&d))
    },
    Err(e) => LeanExcept::error_string(&format!("rs_diff_envs: {e}")),
  }
}
