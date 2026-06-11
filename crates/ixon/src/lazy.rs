//! Lazy materialization of `Constant` from on-disk bytes.
//!
//! Stored inside `Env::consts`: `DashMap<Address, LazyConstant>`. The
//! `.ixe` loader reads each constant's bytes (preceded by a Tag0
//! length sidecar at the env-section level — see `Env::get`) into a
//! `LazyConstant::from_bytes`, deferring `Constant::get` until first
//! access via [`LazyConstant::get`].
//!
//! Cache policy:
//! - The compile-side constructor [`LazyConstant::from_constant`]
//!   pre-populates `cache: Some(Arc::new(c))` so subsequent `get()`s
//!   are free; re-serializing the structured value would be wasteful.
//! - The lazy load constructors [`LazyConstant::from_bytes`] and
//!   [`LazyConstant::from_mmap_slice`] leave `cache: None`. Every
//!   `get()` parses fresh from `bytes` and returns the parsed value
//!   *without* storing it. Callers (typically kernel ingress) consume
//!   the returned `Arc<Constant>` immediately to build a `KConst` in
//!   the worker's `KEnv`, then drop it. The `KEnv` is the only
//!   long-lived materialization layer; it is reset periodically by
//!   `clear_releasing_memory()` — every `clear_every` work items
//!   (see `kernel_check_clear_every`, default 1 but tunable via
//!   `IX_KERNEL_CHECK_CLEAR_EVERY`). The result is that env-level
//!   memory stays bounded to "bytes + mmap header" regardless of
//!   how much of the env the workers eventually visit; the only
//!   meaningful working set is the union of currently-checking
//!   work items' ingress closures.
//!
//! Invariants:
//! - `raw_bytes()` returns exactly what `Constant::put` produces and
//!   `Address::hash` consumes — the Tag0 length prefix is *not*
//!   included.
//! - `Address::hash(self.raw_bytes()) == addr` for the address this
//!   lazy entry was stored under (`verify_address` checks this).
//!
//! Storage backend:
//! - [`BytesSource::Heap`] owns an `Arc<[u8]>`; used by the
//!   compile-side path and tests.
//! - [`BytesSource::Mmap`] is a `(Arc<Mmap>, offset, len)` window
//!   into a memory-mapped `.ixe` file. The mmap stays alive as long
//!   as any [`LazyConstant`] (or `Env`) holds a clone of the
//!   `Arc<Mmap>`; on Linux the OS handles paging — no heap copy of
//!   the on-disk bytes.

use std::sync::Arc;

use memmap2::Mmap;

use ix_common::address::Address;

use super::constant::{Constant, ConstantInfo};

/// Backing storage for a `LazyConstant`'s serialized bytes.
#[derive(Debug, Clone)]
pub enum BytesSource {
  /// Heap-allocated bytes. Produced by `store_const`,
  /// `LazyConstant::from_constant`, and the eager
  /// `Env::get`/`Env::get_anon` paths that `std::fs::read` the file
  /// into a `Vec<u8>` first.
  Heap(Arc<[u8]>),
  /// Slice into a memory-mapped `.ixe` file. Produced by
  /// `Env::get_anon_mmap`. The `Arc<Mmap>` is shared across every
  /// `LazyConstant` from the same load, so the mapping is kept
  /// alive as long as any constant entry references it.
  Mmap { mmap: Arc<Mmap>, offset: usize, len: usize },
}

impl BytesSource {
  /// View the bytes as a `&[u8]`. Zero-copy for both variants:
  /// `Heap` derefs the `Arc<[u8]>`; `Mmap` slices the mapping.
  pub fn as_slice(&self) -> &[u8] {
    match self {
      BytesSource::Heap(arc) => arc,
      BytesSource::Mmap { mmap, offset, len } => &mmap[*offset..*offset + *len],
    }
  }
}

/// Tag identifying which `ConstantInfo` variant a `LazyConstant`
/// holds, derivable from one byte of the serialized prefix. Used by
/// `LazyConstant::peek_variant` so callers can dispatch without
/// parsing the body.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum ConstVariantTag {
  Defn,
  Recr,
  Axio,
  Quot,
  Muts,
  IPrj,
  CPrj,
  RPrj,
  DPrj,
}

/// Lazy-materialized `Constant` backed by serialized bytes.
#[derive(Debug, Clone)]
pub struct LazyConstant {
  /// Tag4-encoded constant bytes (exactly the slice consumed by
  /// `Constant::get` and hashed by `Address::hash`).
  bytes: BytesSource,
  /// Pre-materialized `Constant`. Populated *only* by
  /// `from_constant` (the compile-side path, where we already own
  /// the parsed value). `from_bytes` and `from_mmap_slice` leave
  /// this `None`; their `get()` parses fresh and does not store —
  /// see the module-level "Cache policy" docs.
  cache: Option<Arc<Constant>>,
  /// Deferred address verification: when set (the `.ixe` load paths),
  /// `get()` checks `Address::hash(bytes) == pending_addr` before
  /// parsing. This moves the per-constant content-hash from env parse
  /// time to first materialization, so constants that are shipped in a
  /// closure but never forced by the typechecker are never hashed —
  /// while everything the kernel CERTIFIES is still verified (checking
  /// a constant forces its materialization). `None` for the
  /// compile-side path, which owns the parsed value already.
  pending_addr: Option<Address>,
}

impl LazyConstant {
  /// Construct from already-serialized heap-resident bytes (the
  /// `std::fs::read` lazy load path and the test-FFI path).
  ///
  /// The caller is responsible for ensuring `bytes` is exactly what
  /// `Constant::put` produced for the address this entry is stored
  /// under. Use [`Self::verify_address`] for an explicit check.
  pub fn from_bytes(bytes: Arc<[u8]>) -> Self {
    LazyConstant { bytes: BytesSource::Heap(bytes), cache: None, pending_addr: None }
  }

  /// Like [`Self::from_bytes`], but with the address-binding check
  /// deferred to first [`Self::get`]. Used by `Env::get_anon` so env
  /// parse time does not pay one content hash per constant.
  pub fn from_bytes_deferred(bytes: Arc<[u8]>, addr: Address) -> Self {
    LazyConstant {
      bytes: BytesSource::Heap(bytes),
      cache: None,
      pending_addr: Some(addr),
    }
  }

  /// Construct from a memory-mapped window. The `Arc<Mmap>` keeps
  /// the underlying mapping alive; cloning the `LazyConstant` only
  /// bumps the refcount.
  ///
  /// Used by `Env::get_anon_mmap` to avoid heap-copying the on-disk
  /// byte stream — the OS page cache is the source of truth.
  pub fn from_mmap_slice(mmap: Arc<Mmap>, offset: usize, len: usize) -> Self {
    LazyConstant {
      bytes: BytesSource::Mmap { mmap, offset, len },
      cache: None,
      pending_addr: None,
    }
  }

  /// Construct from a structured `Constant` (the in-memory build path,
  /// e.g. from the compiler). Serializes once and pre-populates the
  /// cache so `get()` is free and `raw_bytes()` is ready for
  /// `Env::put`.
  pub fn from_constant(c: Constant) -> Self {
    let mut buf = Vec::new();
    c.put(&mut buf);
    LazyConstant {
      bytes: BytesSource::Heap(buf.into()),
      cache: Some(Arc::new(c)),
      pending_addr: None,
    }
  }

  /// Materialize the `Constant`.
  ///
  /// If this entry was built via [`Self::from_constant`], returns the
  /// pre-populated cached `Arc` (zero-cost clone). Otherwise parses
  /// fresh from `bytes` on every call and returns a new `Arc`
  /// without storing it — see the module-level "Cache policy" docs
  /// for why.
  pub fn get(&self) -> Result<Arc<Constant>, String> {
    if let Some(c) = &self.cache {
      return Ok(c.clone());
    }
    if let Some(expected) = &self.pending_addr {
      let computed = Address::hash(self.bytes.as_slice());
      if computed != *expected {
        return Err(format!(
          "LazyConstant::get: bytes hash to {} but stored under {}",
          computed.hex(),
          expected.hex()
        ));
      }
    }
    let mut slice: &[u8] = self.bytes.as_slice();
    let parsed = Constant::get(&mut slice)
      .map_err(|e| format!("LazyConstant::get: {e}"))?;
    if !slice.is_empty() {
      return Err(format!(
        "LazyConstant::get: trailing {} bytes after Constant",
        slice.len()
      ));
    }
    Ok(Arc::new(parsed))
  }

  /// Identify the `ConstantInfo` variant by reading just the outer
  /// `Tag4` head byte — no allocation, no body parse.
  ///
  /// `Tag4` encoding (see `src/ix/ixon/tag.rs:64-70`): head is
  /// `[flag:4][large:1][size:3]`. For `Constant`:
  /// - `flag = 0xC` (`Constant::FLAG_MUTS`) → Muts block (size field
  ///   encodes the entry count, possibly in large form; we ignore it
  ///   here — knowing it's Muts is enough).
  /// - `flag = 0xD` (`Constant::FLAG`) → non-Muts variant; index
  ///   0..=7 in the `size` field. All non-Muts variants fit in 3
  ///   bits, so `large=0` always; the index is read directly.
  ///
  /// Used by `build_anon_work` to dispatch on variant without
  /// materializing the entire `Arc<Expr>` body. For the ~95% of
  /// constants that are standalone or projections, this is the only
  /// byte we ever read at enumeration time.
  pub fn peek_variant(&self) -> Result<ConstVariantTag, String> {
    let bytes = self.bytes.as_slice();
    let head = *bytes
      .first()
      .ok_or_else(|| "LazyConstant::peek_variant: empty bytes".to_string())?;
    let flag = head >> 4;
    let large = head & 0b1000 != 0;
    let small = head & 0b0111;
    match flag {
      Constant::FLAG_MUTS => Ok(ConstVariantTag::Muts),
      Constant::FLAG => {
        if large {
          return Err(format!(
            "LazyConstant::peek_variant: unexpected large-form Tag4 for non-Muts constant (head=0x{head:02X})"
          ));
        }
        match u64::from(small) {
          ConstantInfo::CONST_DEFN => Ok(ConstVariantTag::Defn),
          ConstantInfo::CONST_RECR => Ok(ConstVariantTag::Recr),
          ConstantInfo::CONST_AXIO => Ok(ConstVariantTag::Axio),
          ConstantInfo::CONST_QUOT => Ok(ConstVariantTag::Quot),
          ConstantInfo::CONST_CPRJ => Ok(ConstVariantTag::CPrj),
          ConstantInfo::CONST_RPRJ => Ok(ConstVariantTag::RPrj),
          ConstantInfo::CONST_IPRJ => Ok(ConstVariantTag::IPrj),
          ConstantInfo::CONST_DPRJ => Ok(ConstVariantTag::DPrj),
          n => Err(format!(
            "LazyConstant::peek_variant: unknown variant index {n}"
          )),
        }
      },
      _ => Err(format!(
        "LazyConstant::peek_variant: unexpected Tag4 flag 0x{flag:X} (expected 0xC or 0xD)"
      )),
    }
  }

  /// Raw serialized bytes (the Tag4 constant body, no length prefix).
  pub fn raw_bytes(&self) -> &[u8] {
    self.bytes.as_slice()
  }

  /// Whether a pre-materialized `Constant` is cached. True only for
  /// entries built via [`Self::from_constant`]; the lazy-load paths
  /// (`from_bytes`, `from_mmap_slice`) always return `false` — see
  /// the module-level "Cache policy" docs.
  pub fn is_materialized(&self) -> bool {
    self.cache.is_some()
  }

  /// Verify that `Address::hash(self.raw_bytes()) == *expected`.
  pub fn verify_address(&self, expected: &Address) -> bool {
    Address::hash(self.bytes.as_slice()) == *expected
  }
}

/// Bytes are deterministic for a given `Constant`, so byte-equality
/// implies `Constant`-equality.
impl PartialEq for LazyConstant {
  fn eq(&self, other: &Self) -> bool {
    self.bytes.as_slice() == other.bytes.as_slice()
  }
}
impl Eq for LazyConstant {}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::constant::{Axiom, ConstantInfo, DefKind, Definition};
  use crate::expr::Expr;
  use ix_common::env::DefinitionSafety;

  fn axiom_constant() -> Constant {
    Constant::new(ConstantInfo::Axio(Axiom {
      is_unsafe: false,
      lvls: 0,
      typ: Expr::sort(0),
    }))
  }

  fn defn_constant() -> Constant {
    Constant::new(ConstantInfo::Defn(Definition {
      kind: DefKind::Definition,
      safety: DefinitionSafety::Safe,
      lvls: 1,
      typ: Expr::sort(0),
      value: Expr::var(0),
    }))
  }

  #[test]
  fn from_constant_materializes_immediately() {
    let c = axiom_constant();
    let lazy = LazyConstant::from_constant(c.clone());
    assert!(lazy.is_materialized());
    assert_eq!(*lazy.get().unwrap(), c);
  }

  #[test]
  fn from_bytes_does_not_cache() {
    let c = defn_constant();
    let (addr, bytes) = c.commit();
    let lazy = LazyConstant::from_bytes(bytes.into());
    assert!(!lazy.is_materialized());
    assert!(lazy.verify_address(&addr));
    let a1 = lazy.get().unwrap();
    let a2 = lazy.get().unwrap();
    // Both decoded to equal Constants...
    assert_eq!(*a1, c);
    assert_eq!(*a2, c);
    // ...but no caching, so distinct Arc allocations each call.
    assert!(!Arc::ptr_eq(&a1, &a2));
    // Never materialized — there's nothing to materialize into.
    assert!(!lazy.is_materialized());
  }

  #[test]
  fn from_constant_clones_share_cache() {
    let c = axiom_constant();
    let lazy = LazyConstant::from_constant(c);
    let cloned = lazy.clone();
    let a1 = lazy.get().unwrap();
    let a2 = cloned.get().unwrap();
    // Both came from the pre-populated cache; same Arc.
    assert!(Arc::ptr_eq(&a1, &a2));
    assert!(lazy.is_materialized());
    assert!(cloned.is_materialized());
  }

  #[test]
  fn raw_bytes_equals_constant_put() {
    let c = defn_constant();
    let mut expected = Vec::new();
    c.put(&mut expected);
    let lazy = LazyConstant::from_constant(c);
    assert_eq!(lazy.raw_bytes(), &expected[..]);
  }

  #[test]
  fn from_bytes_then_get_roundtrips() {
    let c = defn_constant();
    let (_addr, bytes) = c.commit();
    let lazy = LazyConstant::from_bytes(bytes.into());
    let got = lazy.get().unwrap();
    assert_eq!(*got, c);
  }

  #[test]
  fn verify_address_detects_corruption() {
    let c = axiom_constant();
    let (_addr, mut bytes) = c.commit();
    // Flip the last byte
    let last = bytes.len() - 1;
    bytes[last] ^= 0xFF;
    let lazy = LazyConstant::from_bytes(bytes.into());
    // Address of mutated bytes shouldn't match the original
    let original_addr = c.commit().0;
    assert!(!lazy.verify_address(&original_addr));
  }

  #[test]
  fn equality_by_bytes() {
    let a = LazyConstant::from_constant(axiom_constant());
    let b = LazyConstant::from_constant(axiom_constant());
    assert_eq!(a, b);
    let d = LazyConstant::from_constant(defn_constant());
    assert_ne!(a, d);
  }

  #[test]
  fn trailing_bytes_rejected() {
    let mut bytes = axiom_constant().commit().1;
    bytes.push(0xAB);
    let lazy = LazyConstant::from_bytes(bytes.into());
    let err = lazy.get().unwrap_err();
    assert!(err.contains("trailing"), "got: {err}");
  }

  #[test]
  fn mmap_slice_roundtrips() {
    use std::fs::File;
    use std::io::Write;
    let tmp = std::env::temp_dir().join("ix_lazy_mmap_test.bin");
    let c = defn_constant();
    let mut payload = Vec::new();
    // Some leading bytes so offset != 0 exercises the windowing.
    payload.extend_from_slice(&[0xDE, 0xAD, 0xBE, 0xEF]);
    c.put(&mut payload);
    {
      let mut f = File::create(&tmp).unwrap();
      f.write_all(&payload).unwrap();
    }
    let file = File::open(&tmp).unwrap();
    let mmap = unsafe { Mmap::map(&file).unwrap() };
    let mmap = Arc::new(mmap);
    let len = payload.len() - 4;
    let lazy = LazyConstant::from_mmap_slice(Arc::clone(&mmap), 4, len);
    // Mmap-backed entries are never marked materialized — they parse
    // fresh on every `get()` and don't cache.
    assert!(!lazy.is_materialized());
    assert_eq!(lazy.raw_bytes().len(), len);
    let got = lazy.get().unwrap();
    assert_eq!(*got, c);
    assert!(!lazy.is_materialized());
    std::fs::remove_file(&tmp).ok();
  }

  // -------------------- peek_variant --------------------

  /// Build a Muts constant with two trivial Defn members so we can
  /// roundtrip it through `Constant::put`/`Constant::get` for the
  /// `peek_variant` Muts test.
  fn muts_constant() -> Constant {
    use crate::constant::{ConstantInfo, MutConst};
    let m1 = MutConst::Defn(Definition {
      kind: DefKind::Definition,
      safety: DefinitionSafety::Safe,
      lvls: 0,
      typ: Expr::sort(0),
      value: Expr::var(0),
    });
    let m2 = MutConst::Defn(Definition {
      kind: DefKind::Definition,
      safety: DefinitionSafety::Safe,
      lvls: 0,
      typ: Expr::sort(0),
      value: Expr::var(0),
    });
    Constant::new(ConstantInfo::Muts(vec![m1, m2]))
  }

  fn peek_for(c: &Constant) -> Result<ConstVariantTag, String> {
    let (_addr, bytes) = c.commit();
    LazyConstant::from_bytes(bytes.into()).peek_variant()
  }

  #[test]
  fn peek_variant_defn() {
    assert_eq!(peek_for(&defn_constant()).unwrap(), ConstVariantTag::Defn);
  }

  #[test]
  fn peek_variant_axio() {
    assert_eq!(peek_for(&axiom_constant()).unwrap(), ConstVariantTag::Axio);
  }

  #[test]
  fn peek_variant_muts() {
    assert_eq!(peek_for(&muts_constant()).unwrap(), ConstVariantTag::Muts);
  }

  #[test]
  fn peek_variant_quot() {
    use crate::constant::{ConstantInfo, Quotient};
    use ix_common::env::QuotKind;
    let q = Constant::new(ConstantInfo::Quot(Quotient {
      kind: QuotKind::Type,
      lvls: 1,
      typ: Expr::sort(0),
    }));
    assert_eq!(peek_for(&q).unwrap(), ConstVariantTag::Quot);
  }

  #[test]
  fn peek_variant_dprj() {
    use crate::constant::{ConstantInfo, DefinitionProj};
    let p = Constant::new(ConstantInfo::DPrj(DefinitionProj {
      idx: 0,
      block: Address::hash(b"some-block"),
    }));
    assert_eq!(peek_for(&p).unwrap(), ConstVariantTag::DPrj);
  }

  #[test]
  fn peek_variant_iprj() {
    use crate::constant::{ConstantInfo, InductiveProj};
    let p = Constant::new(ConstantInfo::IPrj(InductiveProj {
      idx: 0,
      block: Address::hash(b"some-block"),
    }));
    assert_eq!(peek_for(&p).unwrap(), ConstVariantTag::IPrj);
  }

  #[test]
  fn peek_variant_rprj() {
    use crate::constant::{ConstantInfo, RecursorProj};
    let p = Constant::new(ConstantInfo::RPrj(RecursorProj {
      idx: 0,
      block: Address::hash(b"some-block"),
    }));
    assert_eq!(peek_for(&p).unwrap(), ConstVariantTag::RPrj);
  }

  #[test]
  fn peek_variant_cprj() {
    use crate::constant::{ConstantInfo, ConstructorProj};
    let p = Constant::new(ConstantInfo::CPrj(ConstructorProj {
      idx: 0,
      cidx: 0,
      block: Address::hash(b"some-block"),
    }));
    assert_eq!(peek_for(&p).unwrap(), ConstVariantTag::CPrj);
  }

  #[test]
  fn peek_variant_empty_bytes_error() {
    let lazy = LazyConstant::from_bytes(Arc::from(&[][..]));
    let err = lazy.peek_variant().unwrap_err();
    assert!(err.contains("empty"), "got: {err}");
  }

  #[test]
  fn peek_variant_unknown_flag_error() {
    // 0x10 = flag 0x1 (not 0xC or 0xD)
    let lazy = LazyConstant::from_bytes(Arc::from(&[0x10][..]));
    let err = lazy.peek_variant().unwrap_err();
    assert!(err.contains("flag"), "got: {err}");
  }
}
