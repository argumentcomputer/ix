//! `.ixc` catalog: a merkle commitment over a set of anonymous `.ixe`
//! environments ("pieces"), plus the anonymous k-way merge that
//! materializes a catalog subset as one ordinary `.ixe`.
//!
//! Semantically a catalog IS one big anonymous env — the union of all
//! member const sets — and the `.ixc` is its merklized form. Two roots:
//!
//! - `members_root`: `merkle_root_canonical` over member ENV ROOTS —
//!   the membership commitment.
//! - `content_root`: `merkle_root_canonical` over the UNION of the
//!   members' §2 constant addresses — the env root of the virtual
//!   union env (the "merklized linear `.ixe` §2"). The union is never
//!   materialized: it is swept k-way over the members' already-sorted
//!   §2 address lists, O(k) resident.
//!
//! Anonymous Ixon is conflict-free: §2 is content-addressed
//! (`blake3(bytes) == addr`), so a key collision between two pieces
//! implies byte-equal values. §5 `named` — the only non-content-
//! addressed map in the format — plays no part in catalog identity,
//! which is what removes the entire import/qualification problem.
//!
//! Storage profiles (header flag bit0):
//! - **fat** (0, v1): one self-contained piece file per member;
//!   closures may overlap freely — identity dedup only.
//! - **chunked** (1, end-state): disjoint chunk `.ixe`s partitioning
//!   the union under the first-owner rule. An address in two chunks is
//!   a HARD format error (`shardsCover`'s exactly-one-owner rule
//!   promoted to the artifact layer).
//!
//! Because both roots are set functions of content, re-chunking never
//! moves a commitment. The manifest carries no piece bytes — it is a
//! commitment; the piece files live NEXT TO it inside the `.ixc`
//! directory, so a catalog is one self-contained tree.
//!
//! Wire format: Convention B (own magic + explicit version, the
//! `.ixes`/`.ixprof` precedent). Fixed-width little-endian integers —
//! deliberately unlike `.ixe`'s Tag0 varints. Trailing bytes after the
//! storage section are preserved opaquely (future sections: 0x01 agg
//! tree, 0x02 per-unit assumption roots); readers of this version stop
//! after storage, the `.ixes` trick.
//!
//! On disk, a `.ixc` is a DIRECTORY — self-contained, no separate
//! pieces dir:
//!
//! ```text
//! <name>.ixc/
//!   manifest            the binary manifest above
//!   <label>.ixe         one piece per member (fat profile)
//!   <label>.chunk<i>.ixe chunk files (chunked profile)
//!   .cache/             build-cache metadata (drivers'; not catalog
//!                       content, ignored by verify)
//! ```
//!
//! `assemble_into` ingests external piece files by hard link (falling
//! back to copy), so building a catalog from pieces already on the
//! same filesystem moves no bytes.

use crate::merkle::{merkle_root_canonical, zero_address};
use ix_common::address::Address;

/// Magic bytes at the head of every `.ixc` manifest.
pub const CATALOG_MAGIC: &[u8; 8] = b"IXC\0\0\0\0\0";

/// The manifest's filename inside a `.ixc` directory.
pub const MANIFEST_FILE: &str = "manifest";

/// `.ixc` format version.
pub const CATALOG_VERSION: u32 = 1;

/// Storage-profile flag: bit0 of the header `flags` word.
pub const FLAG_CHUNKED: u32 = 1;

/// One catalog member: the semantic identity (anon env root) plus
/// catalog-level metadata — which is where "consistent naming" now
/// lives (labels + pins), not in per-constant names.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CatalogMember {
  /// Anon env root: `merkle_root_canonical` over the piece's §2
  /// addresses. Name-independent semantic identity.
  pub env_root: Address,
  /// §2 entry count of the piece.
  pub const_count: u64,
  /// Qualifier, e.g. `"Mathlib"`. Doubles as the piece filename stem
  /// (`<label>.ixe`) under a pieces dir, so it must be a bare name.
  pub label: String,
  /// Toolchain the piece was compiled on (e.g. the Lean version
  /// string). Members of one catalog may span toolchains.
  pub toolchain: String,
  /// Source pin, e.g. `git:<url>@<rev>`; empty for local builds.
  pub source_pin: String,
  /// Member dependencies as indices into the member list; must all be
  /// `<` this member's own index (topo order, deps first).
  pub deps: Vec<u32>,
  /// Store key of the member's const-addr set as an `AssumptionTree`
  /// keyed by env root (the `ix tree env` object), when persisted.
  pub preimage: Option<Address>,
}

/// Fat-profile storage row (one per member, same order).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FatPiece {
  /// blake3 of the whole piece file — the transport identity.
  pub file_hash: Address,
  /// Piece file size in bytes.
  pub file_bytes: u64,
}

/// Chunked-profile storage row: a disjoint slice of the union.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Chunk {
  /// Env root of the chunk `.ixe` (canonical over its §2 addresses).
  pub chunk_root: Address,
  /// blake3 of the chunk file.
  pub file_hash: Address,
  /// Chunk file size in bytes.
  pub file_bytes: u64,
  /// First-owner member index this chunk belongs to.
  pub owner: u32,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CatalogStorage {
  /// v1: self-contained piece files, one per member (same order);
  /// closures may overlap.
  Fat(Vec<FatPiece>),
  /// End-state: disjoint chunk files covering the union exactly once.
  Chunked(Vec<Chunk>),
}

/// The parsed `.ixc` manifest.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Catalog {
  /// `merkle_root_canonical` over member env roots.
  pub members_root: Address,
  /// `merkle_root_canonical` over the union's constant addresses.
  pub content_root: Address,
  pub members: Vec<CatalogMember>,
  pub storage: CatalogStorage,
  /// Bytes after the storage section, preserved verbatim (future
  /// trailing sections; opaque to this version).
  pub trailing: Vec<u8>,
}

/// Reject a label that cannot double as a filename stem: empty, path
/// separators, traversal, or NULs would let a hostile manifest escape
/// the pieces dir on verify.
fn validate_label(label: &str) -> Result<(), String> {
  if label.is_empty() {
    return Err("catalog: empty member label".into());
  }
  if label.contains(['/', '\\', '\0']) || label == "." || label == ".." {
    return Err(format!("catalog: label {label:?} is not a bare filename"));
  }
  Ok(())
}

/// `merkle_root_canonical` over the entries' env roots (the members
/// commitment). Canonical-set semantics: duplicates collapse.
pub fn members_root_of(members: &[CatalogMember]) -> Address {
  let roots: Vec<Address> =
    members.iter().map(|m| m.env_root.clone()).collect();
  merkle_root_canonical(&roots).unwrap_or_else(zero_address)
}

// ============================================================================
// Wire format
// ============================================================================

struct Cur<'a> {
  buf: &'a [u8],
  pos: usize,
}

impl<'a> Cur<'a> {
  fn take(&mut self, n: usize) -> Result<&'a [u8], String> {
    let end = self
      .pos
      .checked_add(n)
      .filter(|&e| e <= self.buf.len())
      .ok_or_else(|| "truncated .ixc".to_string())?;
    let s = &self.buf[self.pos..end];
    self.pos = end;
    Ok(s)
  }

  fn u8(&mut self) -> Result<u8, String> {
    Ok(self.take(1)?[0])
  }

  fn u32(&mut self) -> Result<u32, String> {
    Ok(u32::from_le_bytes(self.take(4)?.try_into().unwrap()))
  }

  fn u64(&mut self) -> Result<u64, String> {
    Ok(u64::from_le_bytes(self.take(8)?.try_into().unwrap()))
  }

  fn addr(&mut self) -> Result<Address, String> {
    Address::from_slice(self.take(32)?)
      .map_err(|_e| "bad address in .ixc".to_string())
  }

  fn string(&mut self) -> Result<String, String> {
    let len = u16::from_le_bytes(self.take(2)?.try_into().unwrap()) as usize;
    String::from_utf8(self.take(len)?.to_vec())
      .map_err(|_e| "invalid utf8 string in .ixc".to_string())
  }
}

fn put_string(s: &str, out: &mut Vec<u8>) -> Result<(), String> {
  let bytes = s.as_bytes();
  let len = u16::try_from(bytes.len())
    .map_err(|_e| format!("catalog: string over 64 KiB: {:.40}…", s))?;
  out.extend_from_slice(&len.to_le_bytes());
  out.extend_from_slice(bytes);
  Ok(())
}

impl Catalog {
  pub fn is_chunked(&self) -> bool {
    matches!(self.storage, CatalogStorage::Chunked(_))
  }

  /// Serialize to the `.ixc` binary format.
  pub fn to_bytes(&self) -> Result<Vec<u8>, String> {
    let mut out = Vec::new();
    out.extend_from_slice(CATALOG_MAGIC);
    out.extend_from_slice(&CATALOG_VERSION.to_le_bytes());
    let flags: u32 = if self.is_chunked() { FLAG_CHUNKED } else { 0 };
    out.extend_from_slice(&flags.to_le_bytes());
    out.extend_from_slice(self.members_root.as_bytes());
    out.extend_from_slice(self.content_root.as_bytes());
    let count = u32::try_from(self.members.len())
      .map_err(|_e| "catalog: over u32::MAX members".to_string())?;
    out.extend_from_slice(&count.to_le_bytes());
    for m in &self.members {
      out.extend_from_slice(m.env_root.as_bytes());
      out.extend_from_slice(&m.const_count.to_le_bytes());
      put_string(&m.label, &mut out)?;
      put_string(&m.toolchain, &mut out)?;
      put_string(&m.source_pin, &mut out)?;
      let dep_count = u32::try_from(m.deps.len())
        .map_err(|_e| "catalog: over u32::MAX deps".to_string())?;
      out.extend_from_slice(&dep_count.to_le_bytes());
      for d in &m.deps {
        out.extend_from_slice(&d.to_le_bytes());
      }
      match &m.preimage {
        Some(a) => {
          out.push(1);
          out.extend_from_slice(a.as_bytes());
        },
        None => out.push(0),
      }
    }
    match &self.storage {
      CatalogStorage::Fat(pieces) => {
        if pieces.len() != self.members.len() {
          return Err(format!(
            "catalog: fat profile carries {} storage rows for {} members",
            pieces.len(),
            self.members.len()
          ));
        }
        for p in pieces {
          out.extend_from_slice(p.file_hash.as_bytes());
          out.extend_from_slice(&p.file_bytes.to_le_bytes());
        }
      },
      CatalogStorage::Chunked(chunks) => {
        let n = u32::try_from(chunks.len())
          .map_err(|_e| "catalog: over u32::MAX chunks".to_string())?;
        out.extend_from_slice(&n.to_le_bytes());
        for c in chunks {
          out.extend_from_slice(c.chunk_root.as_bytes());
          out.extend_from_slice(c.file_hash.as_bytes());
          out.extend_from_slice(&c.file_bytes.to_le_bytes());
          out.extend_from_slice(&c.owner.to_le_bytes());
        }
      },
    }
    out.extend_from_slice(&self.trailing);
    Ok(out)
  }

  /// Deserialize and structurally validate: magic, version, no
  /// unknown flags, deps strictly before their member (topo), labels
  /// filename-safe, chunk owners in range — and `members_root`
  /// recomputed from the entries (a mismatch is rejected on load, the
  /// `.ixe` root discipline one level up). `content_root` needs the
  /// storage bytes and is verified by [`verify`].
  pub fn from_bytes(bytes: &[u8]) -> Result<Self, String> {
    let mut c = Cur { buf: bytes, pos: 0 };
    if c.take(8)? != CATALOG_MAGIC {
      return Err("not an .ixc file (bad magic)".into());
    }
    let version = c.u32()?;
    if version != CATALOG_VERSION {
      return Err(format!(
        "unsupported .ixc version {version} (expected {CATALOG_VERSION})"
      ));
    }
    let flags = c.u32()?;
    if flags & !FLAG_CHUNKED != 0 {
      // Fail closed on flag bits this version does not understand:
      // they may change the meaning of everything that follows.
      return Err(format!("unknown .ixc flags 0x{flags:X}"));
    }
    let members_root = c.addr()?;
    let content_root = c.addr()?;
    let member_count = c.u32()? as usize;
    let mut members = Vec::with_capacity(member_count.min(4096));
    for idx in 0..member_count {
      let env_root = c.addr()?;
      let const_count = c.u64()?;
      let label = c.string()?;
      validate_label(&label)?;
      let toolchain = c.string()?;
      let source_pin = c.string()?;
      let dep_count = c.u32()? as usize;
      let mut deps = Vec::with_capacity(dep_count.min(4096));
      for _ in 0..dep_count {
        let d = c.u32()?;
        if d as usize >= idx {
          return Err(format!(
            "catalog: member {idx} ({label}) depends on member {d}, which \
             is not strictly before it — members are topo-ordered, deps \
             first"
          ));
        }
        deps.push(d);
      }
      let preimage = if c.u8()? == 1 { Some(c.addr()?) } else { None };
      members.push(CatalogMember {
        env_root,
        const_count,
        label,
        toolchain,
        source_pin,
        deps,
        preimage,
      });
    }
    let storage = if flags & FLAG_CHUNKED == 0 {
      let mut pieces = Vec::with_capacity(member_count.min(4096));
      for _ in 0..member_count {
        let file_hash = c.addr()?;
        let file_bytes = c.u64()?;
        pieces.push(FatPiece { file_hash, file_bytes });
      }
      CatalogStorage::Fat(pieces)
    } else {
      let chunk_count = c.u32()? as usize;
      let mut chunks = Vec::with_capacity(chunk_count.min(4096));
      for _ in 0..chunk_count {
        let chunk_root = c.addr()?;
        let file_hash = c.addr()?;
        let file_bytes = c.u64()?;
        let owner = c.u32()?;
        if owner as usize >= member_count {
          return Err(format!(
            "catalog: chunk owner {owner} out of range ({member_count} \
             members)"
          ));
        }
        chunks.push(Chunk { chunk_root, file_hash, file_bytes, owner });
      }
      CatalogStorage::Chunked(chunks)
    };
    let trailing = bytes[c.pos..].to_vec();
    let catalog =
      Catalog { members_root, content_root, members, storage, trailing };
    let recomputed = members_root_of(&catalog.members);
    if recomputed != catalog.members_root {
      return Err(format!(
        "catalog: members_root mismatch — stored {}, recomputed {} from \
         the member entries",
        catalog.members_root.hex(),
        recomputed.hex()
      ));
    }
    Ok(catalog)
  }
}

// ============================================================================
// Host-side operations: open, assemble, verify, merge
// ============================================================================

#[cfg(not(target_arch = "riscv64"))]
pub use host::*;

#[cfg(not(target_arch = "riscv64"))]
mod host {
  use std::path::{Path, PathBuf};
  use std::sync::Arc;

  use memmap2::Mmap;
  use rustc_hash::FxHashSet;

  use super::*;
  use crate::env::{Env, LazyIndex};
  use crate::merkle::merkle_root_canonical_sorted;

  /// One opened piece: mmap + lazy index + identities. The index's
  /// `consts` vector IS the sorted §2 (addr, span) list; nothing is
  /// materialized.
  pub struct OpenPiece {
    pub path: PathBuf,
    pub mmap: Arc<Mmap>,
    pub index: LazyIndex,
    pub env_root: Address,
    pub file_hash: Address,
    pub file_bytes: u64,
  }

  fn mmap_file(path: &Path) -> Result<Arc<Mmap>, String> {
    let file = std::fs::File::open(path)
      .map_err(|e| format!("catalog: open {}: {e}", path.display()))?;
    let meta = file
      .metadata()
      .map_err(|e| format!("catalog: stat {}: {e}", path.display()))?;
    let mmap = unsafe { Mmap::map(&file) }
      .map_err(|e| format!("catalog: mmap {}: {e}", path.display()))?;
    if mmap.len() as u64 != meta.len() {
      return Err(format!(
        "catalog: {}: mmap length {} != file length {}",
        path.display(),
        mmap.len(),
        meta.len()
      ));
    }
    Ok(Arc::new(mmap))
  }

  /// Open a piece: mmap, parse the lazy index (which enforces §2
  /// strict ascent and re-verifies the stored env root), blake3 the
  /// file. Constant BODIES are not hashed here — that is `--deep`'s
  /// job (`get_anon_mmap`) or the merge's (per unique constant).
  pub fn open_piece(path: &Path) -> Result<OpenPiece, String> {
    let mmap = mmap_file(path)?;
    let index = Env::parse_lazy_index(&mmap)
      .map_err(|e| format!("catalog: {}: {e}", path.display()))?;
    let addrs: Vec<Address> =
      index.consts.iter().map(|c| c.addr.clone()).collect();
    let env_root =
      merkle_root_canonical_sorted(&addrs).unwrap_or_else(zero_address);
    let file_hash = {
      let mut hasher = blake3::Hasher::new();
      hasher.update(&mmap);
      Address::from_blake3_hash(hasher.finalize())
    };
    let file_bytes = mmap.len() as u64;
    Ok(OpenPiece {
      path: path.to_path_buf(),
      mmap,
      index,
      env_root,
      file_hash,
      file_bytes,
    })
  }

  /// K-way sweep over the pieces' sorted §2 address lists. Returns the
  /// sorted union; `on_dup` observes every address carried by more
  /// than one piece (with the piece indices), for the chunked
  /// profile's no-redeclaration gate and for diagnostics.
  fn sweep_union(
    pieces: &[&OpenPiece],
    mut on_dup: impl FnMut(&Address, &[usize]) -> Result<(), String>,
  ) -> Result<Vec<Address>, String> {
    use std::cmp::Reverse;
    use std::collections::BinaryHeap;

    let mut heap: BinaryHeap<Reverse<(Address, usize)>> = BinaryHeap::new();
    let mut cursors = vec![0usize; pieces.len()];
    for (i, p) in pieces.iter().enumerate() {
      if let Some(c) = p.index.consts.first() {
        heap.push(Reverse((c.addr.clone(), i)));
      }
    }
    let mut union: Vec<Address> = Vec::new();
    let mut carriers: Vec<usize> = Vec::new();
    while let Some(Reverse((addr, piece))) = heap.pop() {
      cursors[piece] += 1;
      if let Some(c) = pieces[piece].index.consts.get(cursors[piece]) {
        heap.push(Reverse((c.addr.clone(), piece)));
      }
      if union.last() == Some(&addr) {
        carriers.push(piece);
        continue;
      }
      if carriers.len() > 1 {
        // Safe: union is non-empty whenever carriers is.
        on_dup(union.last().unwrap(), &carriers)?;
      }
      carriers.clear();
      carriers.push(piece);
      union.push(addr);
    }
    if carriers.len() > 1 {
      on_dup(union.last().unwrap(), &carriers)?;
    }
    Ok(union)
  }

  /// Assembly input: one member piece plus its catalog metadata.
  pub struct MemberSpec {
    pub path: PathBuf,
    pub label: String,
    pub toolchain: String,
    pub source_pin: String,
    /// Indices into the spec list, `<` this member's own index.
    pub deps: Vec<u32>,
  }

  /// Bring one piece file inside the catalog dir as `<label>.ixe`:
  /// no-op when the spec path already IS the destination, hard link
  /// when the filesystem allows (zero bytes moved), copy otherwise. A
  /// pre-existing destination with DIFFERENT content is an error —
  /// never silently replace a piece another member of the dir's
  /// history put there.
  fn ingest_piece(
    dir: &Path,
    spec_path: &Path,
    label: &str,
    file_hash: &Address,
  ) -> Result<PathBuf, String> {
    let dst = piece_path(dir, label, None);
    if let (Ok(a), Ok(b)) =
      (std::fs::canonicalize(spec_path), std::fs::canonicalize(&dst))
      && a == b
    {
      return Ok(dst);
    }
    if dst.exists() {
      let existing = open_piece(&dst)?;
      if existing.file_hash == *file_hash {
        return Ok(dst);
      }
      return Err(format!(
        "catalog: {} already exists with different content ({} vs the \
         ingested piece's {}) — remove it or pick another label",
        dst.display(),
        existing.file_hash.hex(),
        file_hash.hex()
      ));
    }
    if std::fs::hard_link(spec_path, &dst).is_err() {
      std::fs::copy(spec_path, &dst).map_err(|e| {
        format!(
          "catalog: ingest {} -> {}: {e}",
          spec_path.display(),
          dst.display()
        )
      })?;
    }
    Ok(dst)
  }

  /// Assemble a fat-profile `.ixc` DIRECTORY from piece files: create
  /// `dir`, ingest every piece as `<label>.ixe` (hard link or copy;
  /// already-inside paths untouched), and write `dir/manifest`
  /// (`.tmp` + atomic rename). Reads only piece headers/indexes
  /// (O(k) resident, never a materialized union): recomputes each
  /// piece's env root, hashes each file, sweeps the union for
  /// `content_root`. Fat members must be self-contained (empty
  /// `assumptions`) — a thin piece cannot be independently checked,
  /// which is the fat profile's whole point.
  pub fn assemble_into(
    dir: &Path,
    specs: &[MemberSpec],
  ) -> Result<Catalog, String> {
    if specs.is_empty() {
      return Err("catalog: no members".into());
    }
    std::fs::create_dir_all(dir)
      .map_err(|e| format!("catalog: create {}: {e}", dir.display()))?;
    let mut members = Vec::with_capacity(specs.len());
    let mut pieces = Vec::with_capacity(specs.len());
    let mut opened = Vec::with_capacity(specs.len());
    for (idx, spec) in specs.iter().enumerate() {
      validate_label(&spec.label)?;
      for d in &spec.deps {
        if *d as usize >= idx {
          return Err(format!(
            "catalog: member {idx} ({}) depends on member {d}, which is \
             not strictly before it",
            spec.label
          ));
        }
      }
      let source = open_piece(&spec.path)?;
      if !source.index.assumptions.is_empty() {
        return Err(format!(
          "catalog: {} is a thin bundle ({} assumptions); fat members \
           must be self-contained",
          spec.path.display(),
          source.index.assumptions.len()
        ));
      }
      let ingested =
        ingest_piece(dir, &spec.path, &spec.label, &source.file_hash)?;
      // Re-open at the ingested path so the mmaps backing the sweep
      // (and any later use) reference the catalog's own copy.
      let piece = if ingested == spec.path {
        source
      } else {
        open_piece(&ingested)?
      };
      members.push(CatalogMember {
        env_root: piece.env_root.clone(),
        const_count: piece.index.consts.len() as u64,
        label: spec.label.clone(),
        toolchain: spec.toolchain.clone(),
        source_pin: spec.source_pin.clone(),
        deps: spec.deps.clone(),
        preimage: None,
      });
      pieces.push(FatPiece {
        file_hash: piece.file_hash.clone(),
        file_bytes: piece.file_bytes,
      });
      opened.push(piece);
    }
    let refs: Vec<&OpenPiece> = opened.iter().collect();
    // Fat profile: overlaps are expected; the union collapses them.
    let union = sweep_union(&refs, |_a, _c| Ok(()))?;
    let content_root =
      merkle_root_canonical_sorted(&union).unwrap_or_else(zero_address);
    let members_root = members_root_of(&members);
    let catalog = Catalog {
      members_root,
      content_root,
      members,
      storage: CatalogStorage::Fat(pieces),
      trailing: Vec::new(),
    };
    write_manifest(dir, &catalog)?;
    Ok(catalog)
  }

  /// Write `dir/manifest` fail-closed (`.tmp` + atomic rename).
  pub fn write_manifest(dir: &Path, catalog: &Catalog) -> Result<u64, String> {
    let bytes = catalog.to_bytes()?;
    let path = dir.join(MANIFEST_FILE);
    let tmp = {
      let mut s = path.clone().into_os_string();
      s.push(".tmp");
      PathBuf::from(s)
    };
    if let Err(e) = std::fs::write(&tmp, &bytes) {
      std::fs::remove_file(&tmp).ok();
      return Err(format!("catalog: write {}: {e}", tmp.display()));
    }
    if let Err(e) = std::fs::rename(&tmp, &path) {
      std::fs::remove_file(&tmp).ok();
      return Err(format!("catalog: rename to {}: {e}", path.display()));
    }
    Ok(bytes.len() as u64)
  }

  /// Read and parse `dir/manifest` (all of `from_bytes`' load-time
  /// validation applies, `members_root` recompute included).
  pub fn load_dir(dir: &Path) -> Result<Catalog, String> {
    let path = dir.join(MANIFEST_FILE);
    let bytes = std::fs::read(&path)
      .map_err(|e| format!("catalog: read {}: {e}", path.display()))?;
    Catalog::from_bytes(&bytes)
      .map_err(|e| format!("catalog: {}: {e}", path.display()))
  }

  /// Verification report (counts for the human/JSON dump).
  #[derive(Debug)]
  pub struct VerifyOutcome {
    pub members: usize,
    pub union_consts: u64,
    pub deep: bool,
  }

  /// Resolve a member/chunk file under the pieces dir.
  fn piece_path(dir: &Path, label: &str, suffix: Option<usize>) -> PathBuf {
    match suffix {
      None => dir.join(format!("{label}.ixe")),
      Some(i) => dir.join(format!("{label}.chunk{i}.ixe")),
    }
  }

  /// Verify a catalog directory against its own piece files: both
  /// roots recomputed (`members` from the entries — already enforced
  /// by `from_bytes` — and `content` by the k-way sweep), every
  /// storage unit's env root, const count, and file size checked, and
  /// the profile's dedup rule enforced (chunked: an address in two
  /// chunks is a hard error naming both). `deep` additionally
  /// re-hashes every file against its manifest `file_hash` and fully
  /// loads each unit through `get_anon_mmap` (per-constant blake3
  /// verification).
  ///
  /// The `.ixc` is self-contained: pieces resolve INSIDE it as
  /// `<dir>/<label>.ixe` (fat) or `<dir>/<label>.chunk<i>.ixe`
  /// (chunked, per owner) — the label IS the filename stem, validated
  /// filename-safe on load. Anything else in the directory (e.g. a
  /// driver's `.cache/`) is ignored.
  pub fn verify(
    cat: &Catalog,
    dir: &Path,
    deep: bool,
  ) -> Result<VerifyOutcome, String> {
    let mut opened: Vec<OpenPiece> = Vec::new();
    match &cat.storage {
      CatalogStorage::Fat(pieces) => {
        if pieces.len() != cat.members.len() {
          return Err(format!(
            "catalog: fat profile carries {} storage rows for {} members",
            pieces.len(),
            cat.members.len()
          ));
        }
        for (m, p) in cat.members.iter().zip(pieces) {
          let path = piece_path(dir, &m.label, None);
          let piece = open_piece(&path)?;
          if piece.env_root != m.env_root {
            return Err(format!(
              "catalog: {}: env root {} does not match the manifest's {}",
              path.display(),
              piece.env_root.hex(),
              m.env_root.hex()
            ));
          }
          if piece.index.consts.len() as u64 != m.const_count {
            return Err(format!(
              "catalog: {}: {} constants, manifest says {}",
              path.display(),
              piece.index.consts.len(),
              m.const_count
            ));
          }
          if piece.file_bytes != p.file_bytes {
            return Err(format!(
              "catalog: {}: {} bytes on disk, manifest says {}",
              path.display(),
              piece.file_bytes,
              p.file_bytes
            ));
          }
          if deep && piece.file_hash != p.file_hash {
            return Err(format!(
              "catalog: {}: file hash {} does not match the manifest's {}",
              path.display(),
              piece.file_hash.hex(),
              p.file_hash.hex()
            ));
          }
          opened.push(piece);
        }
      },
      CatalogStorage::Chunked(chunks) => {
        for (i, ch) in chunks.iter().enumerate() {
          let owner = &cat.members[ch.owner as usize];
          let path = piece_path(dir, &owner.label, Some(i));
          let piece = open_piece(&path)?;
          if piece.env_root != ch.chunk_root {
            return Err(format!(
              "catalog: {}: chunk root {} does not match the manifest's {}",
              path.display(),
              piece.env_root.hex(),
              ch.chunk_root.hex()
            ));
          }
          if piece.file_bytes != ch.file_bytes {
            return Err(format!(
              "catalog: {}: {} bytes on disk, manifest says {}",
              path.display(),
              piece.file_bytes,
              ch.file_bytes
            ));
          }
          if deep && piece.file_hash != ch.file_hash {
            return Err(format!(
              "catalog: {}: file hash {} does not match the manifest's {}",
              path.display(),
              piece.file_hash.hex(),
              ch.file_hash.hex()
            ));
          }
          opened.push(piece);
        }
      },
    }
    // The sweep: content_root equality, plus the profile's dedup rule.
    let refs: Vec<&OpenPiece> = opened.iter().collect();
    let chunked = cat.is_chunked();
    let union = sweep_union(&refs, |addr, carriers| {
      if chunked {
        let names: Vec<String> = carriers
          .iter()
          .map(|&i| {
            let owner = match &cat.storage {
              CatalogStorage::Chunked(chs) => chs[i].owner as usize,
              CatalogStorage::Fat(_) => unreachable!(),
            };
            format!("chunk {i} (owner {})", cat.members[owner].label)
          })
          .collect();
        Err(format!(
          "catalog: constant {} redeclared across chunks: {} — chunks \
           must be disjoint (no-redeclaration invariant)",
          addr.hex(),
          names.join(", ")
        ))
      } else {
        Ok(())
      }
    })?;
    let content_root =
      merkle_root_canonical_sorted(&union).unwrap_or_else(zero_address);
    if content_root != cat.content_root {
      return Err(format!(
        "catalog: content_root mismatch — stored {}, swept {} from the \
         storage units",
        cat.content_root.hex(),
        content_root.hex()
      ));
    }
    // Chunked coverage half: every member's preimage must be a subset
    // of the union — with disjointness above and count equality this
    // pins exact coverage. Fat pieces ARE the members, so the sweep
    // already equals the member union by construction.
    if deep {
      for piece in &opened {
        // Full anon load: per-constant blake3 on every slice.
        Env::get_anon_mmap(&piece.path)
          .map_err(|e| format!("catalog: {}: {e}", piece.path.display()))?;
      }
    }
    Ok(VerifyOutcome {
      members: cat.members.len(),
      union_consts: union.len() as u64,
      deep,
    })
  }

  /// Merge statistics for reporting.
  pub struct MergeStats {
    pub root: Address,
    pub consts: u64,
    pub blobs: u64,
    pub bytes_written: u64,
  }

  /// Anonymous k-way merge: materialize the union of the given piece
  /// files as ONE ordinary v1 `.ixe` env — the derived single-file
  /// view of a catalog subset. Never the source of truth (the `.ixc`
  /// is); this exists for consumers that want one file.
  ///
  /// - §2: k-way union over the sorted lists; every UNIQUE constant's
  ///   bytes are blake3-verified against its address before re-emission
  ///   (fail closed on a corrupt input; identity dedup means each
  ///   address is verified and written once).
  /// - §1 blobs: union (content-addressed; readers verified each
  ///   entry's hash on parse).
  /// - §3 hints: `register_hint` min-merge, order-independent.
  /// - `assumptions`: union of the inputs' sets minus everything the
  ///   union itself carries (constants and blobs).
  /// - `main`: kept only if exactly one distinct main exists among the
  ///   inputs; otherwise absent (whole-env output).
  /// - §4/§5/§6: empty — the output is anonymous (the writer emits the
  ///   anon name as §4 entry 0 by itself).
  ///
  /// Output is written `<out>.tmp` + atomic rename, root computed
  /// before the writer runs (the compile FFI's fail-closed pattern).
  pub fn merge_anon(
    piece_paths: &[PathBuf],
    out: &Path,
  ) -> Result<MergeStats, String> {
    if piece_paths.is_empty() {
      return Err("merge: no input pieces".into());
    }
    let mut opened = Vec::with_capacity(piece_paths.len());
    for p in piece_paths {
      opened.push(open_piece(p)?);
    }
    let refs: Vec<&OpenPiece> = opened.iter().collect();
    let union = sweep_union(&refs, |_a, _c| Ok(()))?;

    let mut env = Env::new();
    // Re-emit each unique constant zero-copy from its first carrier's
    // mmap, after verifying the bytes against the address.
    {
      let mut cursors = vec![0usize; opened.len()];
      for addr in &union {
        let mut stored = false;
        for (i, piece) in opened.iter().enumerate() {
          while cursors[i] < piece.index.consts.len()
            && piece.index.consts[cursors[i]].addr < *addr
          {
            cursors[i] += 1;
          }
          if cursors[i] < piece.index.consts.len()
            && piece.index.consts[cursors[i]].addr == *addr
          {
            let slice = &piece.index.consts[cursors[i]];
            let bytes = &piece.mmap[slice.offset..slice.offset + slice.len];
            if Address::hash(bytes) != *addr {
              return Err(format!(
                "merge: {}: constant {} bytes do not hash to their \
                 address — corrupt piece",
                piece.path.display(),
                addr.hex()
              ));
            }
            env.store_const_lazy_mmap(
              addr.clone(),
              piece.mmap.clone(),
              slice.offset,
              slice.len,
            );
            stored = true;
            break;
          }
        }
        if !stored {
          return Err(format!(
            "merge: union address {} lost between sweeps (bug)",
            addr.hex()
          ));
        }
      }
    }
    // Blobs union + hints min-merge.
    for piece in &opened {
      for (addr, bytes) in &piece.index.blobs {
        if env.blobs.get(addr).is_none() {
          env.blobs.insert(addr.clone(), bytes.clone());
        }
      }
      for (addr, hints) in &piece.index.hints {
        env.register_hint(addr.clone(), *hints);
      }
    }
    // Assumptions: union of inputs' sets minus what the union carries.
    let mut assumptions: FxHashSet<Address> = FxHashSet::default();
    for piece in &opened {
      assumptions.extend(piece.index.assumptions.iter().cloned());
    }
    assumptions
      .retain(|a| env.consts.get(a).is_none() && env.blobs.get(a).is_none());
    for a in assumptions {
      env.assumptions.insert(a);
    }
    // Main: unique-or-absent.
    let mains: FxHashSet<Address> =
      opened.iter().filter_map(|p| p.index.main.clone()).collect();
    if mains.len() == 1 {
      env.main = mains.into_iter().next();
    }

    let root =
      merkle_root_canonical_sorted(&union).unwrap_or_else(zero_address);
    let tmp = {
      let mut s = out.to_path_buf().into_os_string();
      s.push(".tmp");
      PathBuf::from(s)
    };
    let bytes_written = match env.put_file_with_header(&tmp, &union, &root) {
      Ok(n) => n,
      Err(e) => {
        std::fs::remove_file(&tmp).ok();
        return Err(format!("merge: write {}: {e}", tmp.display()));
      },
    };
    if let Err(e) = std::fs::rename(&tmp, out) {
      std::fs::remove_file(&tmp).ok();
      return Err(format!("merge: rename to {}: {e}", out.display()));
    }
    Ok(MergeStats {
      root,
      consts: union.len() as u64,
      blobs: env.blobs.len() as u64,
      bytes_written,
    })
  }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(all(test, not(target_arch = "riscv64")))]
mod tests {
  use std::path::PathBuf;
  use std::sync::Arc;

  use super::*;
  use crate::env::Env;

  /// A fabricated constant: opaque bytes under their own blake3
  /// address. Piece-level machinery (index, sweep, merge) never parses
  /// constant BODIES, so structural validity is not required here.
  fn fab(seed: &[u8]) -> (Address, Arc<[u8]>) {
    let mut v = b"fab-const-".to_vec();
    v.extend_from_slice(seed);
    let bytes: Arc<[u8]> = Arc::from(v.into_boxed_slice());
    (Address::hash(&bytes), bytes)
  }

  fn tmp_dir(tag: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!(
      "ixc-test-{tag}-{}",
      std::process::id()
    ));
    std::fs::create_dir_all(&dir).unwrap();
    dir
  }

  fn write_piece(dir: &std::path::Path, name: &str, seeds: &[&[u8]]) -> PathBuf {
    let env = Env::new();
    for s in seeds {
      let (addr, bytes) = fab(s);
      env.store_const_lazy(addr, bytes);
    }
    let path = dir.join(format!("{name}.ixe"));
    env.put_file(&path).unwrap();
    path
  }

  fn spec(path: &std::path::Path, label: &str, deps: Vec<u32>) -> MemberSpec {
    MemberSpec {
      path: path.to_path_buf(),
      label: label.to_string(),
      toolchain: "test".to_string(),
      source_pin: String::new(),
      deps,
    }
  }

  #[test]
  fn assemble_verify_roundtrip_fat() {
    let dir = tmp_dir("fat");
    // B's closure overlaps A's (shared dep "x") — fat allows it.
    // Sources live OUTSIDE the catalog dir: ingest must link them in.
    let a = write_piece(&dir, "srcA", &[b"x", b"a1"]);
    let b = write_piece(&dir, "srcB", &[b"x", b"b1", b"b2"]);
    let cat_dir = dir.join("cat.ixc");
    let cat = assemble_into(&cat_dir,
      &[spec(&a, "A", vec![]), spec(&b, "B", vec![0])]).unwrap();
    assert_eq!(cat.members.len(), 2);
    assert_eq!(cat.members[0].const_count, 2);
    assert_eq!(cat.members[1].const_count, 3);
    assert!(cat_dir.join("A.ixe").exists(), "piece ingested as label");
    // The written manifest parses back identical (load-time
    // members_root recompute included).
    let back = load_dir(&cat_dir).unwrap();
    assert_eq!(back, cat);
    // Union: x, a1, b1, b2 = 4 unique. Self-contained verify.
    let outcome = verify(&back, &cat_dir, true).unwrap();
    assert_eq!(outcome.members, 2);
    assert_eq!(outcome.union_consts, 4);
    // Re-assembling in place (paths now INSIDE the dir) is a no-op
    // ingest and commits identically.
    let again = assemble_into(&cat_dir,
      &[spec(&cat_dir.join("A.ixe"), "A", vec![]),
        spec(&cat_dir.join("B.ixe"), "B", vec![0])]).unwrap();
    assert_eq!(again, cat);
    std::fs::remove_dir_all(&dir).ok();
  }

  #[test]
  fn ingest_refuses_conflicting_label() {
    let dir = tmp_dir("ingest-conflict");
    let a = write_piece(&dir, "srcA", &[b"a"]);
    let other = write_piece(&dir, "srcOther", &[b"different"]);
    let cat_dir = dir.join("cat.ixc");
    assemble_into(&cat_dir, &[spec(&a, "A", vec![])]).unwrap();
    // Same label, different content: never silently replaced.
    let err = assemble_into(&cat_dir, &[spec(&other, "A", vec![])])
      .unwrap_err();
    assert!(err.contains("different content"), "{err}");
    std::fs::remove_dir_all(&dir).ok();
  }

  #[test]
  fn content_root_is_chunking_invariant() {
    // The same union split two different ways commits identically:
    // re-partitioning storage can never move the roots (plan D4).
    let dir = tmp_dir("invariant");
    let a1 = write_piece(&dir, "A1", &[b"x", b"y"]);
    let b1 = write_piece(&dir, "B1", &[b"z"]);
    let a2 = write_piece(&dir, "A2", &[b"x"]);
    let b2 = write_piece(&dir, "B2", &[b"y", b"z"]);
    let cat1 = assemble_into(&dir.join("one.ixc"),
      &[spec(&a1, "A1", vec![]), spec(&b1, "B1", vec![])]).unwrap();
    let cat2 = assemble_into(&dir.join("two.ixc"),
      &[spec(&a2, "A2", vec![]), spec(&b2, "B2", vec![])]).unwrap();
    assert_eq!(cat1.content_root, cat2.content_root);
    assert_ne!(cat1.members_root, cat2.members_root);
    std::fs::remove_dir_all(&dir).ok();
  }

  #[test]
  fn from_bytes_rejects_tampering() {
    let dir = tmp_dir("tamper");
    let a = write_piece(&dir, "A", &[b"a"]);
    let cat = assemble_into(&dir.join("cat.ixc"),
      &[spec(&a, "A", vec![])]).unwrap();
    let good = cat.to_bytes().unwrap();

    // Bad magic.
    let mut bad = good.clone();
    bad[0] ^= 0xFF;
    assert!(Catalog::from_bytes(&bad).unwrap_err().contains("magic"));

    // Unknown flag bit.
    let mut bad = good.clone();
    bad[12] |= 0x02;
    assert!(Catalog::from_bytes(&bad).unwrap_err().contains("flags"));

    // Flipped member env root breaks the recomputed members_root.
    let mut bad = good.clone();
    let member_root_off = 8 + 4 + 4 + 32 + 32 + 4;
    bad[member_root_off] ^= 0xFF;
    assert!(
      Catalog::from_bytes(&bad).unwrap_err().contains("members_root")
    );

    // Truncation.
    assert!(Catalog::from_bytes(&good[..good.len() - 1]).is_err());
    std::fs::remove_dir_all(&dir).ok();
  }

  #[test]
  fn verify_rejects_wrong_content_root() {
    let dir = tmp_dir("wrongroot");
    let a = write_piece(&dir, "A", &[b"a"]);
    let cat_dir = dir.join("cat.ixc");
    let mut cat =
      assemble_into(&cat_dir, &[spec(&a, "A", vec![])]).unwrap();
    cat.content_root = Address::hash(b"not the root");
    let err = verify(&cat, &cat_dir, false).unwrap_err();
    assert!(err.contains("content_root"), "{err}");
    std::fs::remove_dir_all(&dir).ok();
  }

  #[test]
  fn verify_rejects_swapped_piece() {
    // The piece file inside the catalog drifts from the manifest: env
    // root check fires before any hash work.
    let dir = tmp_dir("swap");
    let a = write_piece(&dir, "A", &[b"a"]);
    let cat_dir = dir.join("cat.ixc");
    let cat = assemble_into(&cat_dir, &[spec(&a, "A", vec![])]).unwrap();
    // Overwrite the INGESTED A.ixe with different content.
    let env = Env::new();
    let (addr, bytes) = fab(b"other");
    env.store_const_lazy(addr, bytes);
    std::fs::remove_file(cat_dir.join("A.ixe")).unwrap();
    env.put_file(&cat_dir.join("A.ixe")).unwrap();
    let err = verify(&cat, &cat_dir, false).unwrap_err();
    assert!(err.contains("env root"), "{err}");
    std::fs::remove_dir_all(&dir).ok();
  }

  #[test]
  fn chunked_redeclaration_is_a_hard_error() {
    // Two chunks force-built with one shared address must fail with
    // the no-redeclaration error naming both chunks (plan A4.2).
    let dir = tmp_dir("chunkdup");
    let c0 = write_piece(&dir, "M.chunk0", &[b"x", b"a"]);
    let c1 = write_piece(&dir, "M.chunk1", &[b"x", b"b"]);
    let p0 = open_piece(&c0).unwrap();
    let p1 = open_piece(&c1).unwrap();
    // Hand-build a chunked catalog over the overlapping chunks; the
    // member is the virtual union (3 unique addrs).
    let union_root = {
      let mut all: Vec<Address> = p0
        .index
        .consts
        .iter()
        .chain(p1.index.consts.iter())
        .map(|c| c.addr.clone())
        .collect();
      all.sort_unstable();
      all.dedup();
      merkle_root_canonical(&all).unwrap()
    };
    let member = CatalogMember {
      env_root: union_root.clone(),
      const_count: 3,
      label: "M".to_string(),
      toolchain: "test".to_string(),
      source_pin: String::new(),
      deps: vec![],
      preimage: None,
    };
    let members_root = members_root_of(std::slice::from_ref(&member));
    let cat = Catalog {
      members_root,
      content_root: union_root,
      members: vec![member],
      storage: CatalogStorage::Chunked(vec![
        Chunk {
          chunk_root: p0.env_root.clone(),
          file_hash: p0.file_hash.clone(),
          file_bytes: p0.file_bytes,
          owner: 0,
        },
        Chunk {
          chunk_root: p1.env_root.clone(),
          file_hash: p1.file_hash.clone(),
          file_bytes: p1.file_bytes,
          owner: 0,
        },
      ]),
      trailing: Vec::new(),
    };
    let err = verify(&cat, &dir, false).unwrap_err();
    assert!(err.contains("redeclared across chunks"), "{err}");
    std::fs::remove_dir_all(&dir).ok();
  }

  #[test]
  fn merge_dedups_and_roundtrips() {
    let dir = tmp_dir("merge");
    let a = write_piece(&dir, "A", &[b"x", b"a1"]);
    let b = write_piece(&dir, "B", &[b"x", b"b1"]);
    let out = dir.join("union.ixe");
    let stats =
      merge_anon(&[a.clone(), b.clone()], &out).unwrap();
    assert_eq!(stats.consts, 3, "shared dep dedups");
    // The output is an ordinary v1 anon env: readable, root-stable,
    // and re-assembling it as a single-member catalog reproduces the
    // two-member catalog's content_root (union semantics).
    let opened = open_piece(&out).unwrap();
    assert_eq!(opened.env_root, stats.root);
    let cat2 = assemble_into(&dir.join("m.ixc"),
      &[spec(&a, "A", vec![]), spec(&b, "B", vec![])]).unwrap();
    assert_eq!(cat2.content_root, stats.root);
    // Idempotent: merging the merge with an input changes nothing.
    let out2 = dir.join("union2.ixe");
    let stats2 = merge_anon(&[out.clone(), a], &out2).unwrap();
    assert_eq!(stats2.root, stats.root);
    std::fs::remove_dir_all(&dir).ok();
  }

  #[test]
  fn merge_rejects_corrupt_piece() {
    let dir = tmp_dir("corrupt");
    let a = write_piece(&dir, "A", &[b"aaaa", b"bbbb"]);
    // Flip one byte inside a constant BODY (§2 payload, located via
    // the lazy index). The index still parses — the env root covers
    // keys, not bodies — so the merge's per-constant re-hash is the
    // only thing standing between a corrupt piece and a corrupt
    // merged artifact.
    let mut bytes = std::fs::read(&a).unwrap();
    let index = Env::parse_lazy_index(&bytes).unwrap();
    let body = &index.consts[0];
    bytes[body.offset] ^= 0xFF;
    std::fs::write(&a, &bytes).unwrap();
    let out = dir.join("union.ixe");
    match merge_anon(&[a], &out) {
      Err(e) => {
        assert!(e.contains("do not hash"), "unexpected error: {e}")
      },
      Ok(_) => panic!("corrupt piece must not merge"),
    }
    std::fs::remove_dir_all(&dir).ok();
  }

  #[test]
  fn label_path_traversal_rejected() {
    let dir = tmp_dir("label");
    let a = write_piece(&dir, "A", &[b"a"]);
    let err = assemble_into(&dir.join("cat.ixc"),
      &[spec(&a, "../evil", vec![])]).unwrap_err();
    assert!(err.contains("bare filename"), "{err}");
    std::fs::remove_dir_all(&dir).ok();
  }
}
