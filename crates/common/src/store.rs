//! High-performance content-addressed store for Ix (`~/.ix/store`).
//!
//! Combines four storage tiers:
//! 1. **Tier 0 — Hot RAM Cache (`DashMap<Address, Arc<[u8]>>`)** for zero-syscall
//!    intra-process reads and existence short-circuiting.
//! 2. **Tier 1 — Warm `.ixs` + `.ixsp` (`StoreTier::Warm`)**: Memory-mapped
//!    immutable store slabs (`packs/store-<hash>.ixs`, `TagN(4, 0xE, 13)` = `E8 05`)
//!    with 8-byte-aligned raw payloads and a memory-mapped pointer index
//!    (`packs/store-<hash>.ixsp`, `TagN(4, 0xE, 14)` = `E8 06`) containing a
//!    256-entry first-byte fan-out table and sorted 32-byte keys for zero-syscall
//!    `O(log(N/256))` binary search and zero-copy `mmap` slice reads.
//! 3. **Tier 2 — Cold `.ixs` + `.ixsp` (`StoreTier::Cold`)**: `zstd`-compressed
//!    `.ixs` slabs indexed by the exact same `.ixsp` pointer format (`flags & 0xFF == 1`),
//!    preserving `O(log(N/256))` random access while shrinking constant/blob
//!    storage by 3x–5x and promoting decompressed objects into Tier 0 on read.
//! 4. **Tier 3 — Loose Landing Zone (`objects/<aa>/<62-hex>`)**: 1-level sharded
//!    loose object files (`256` shard directories instead of `256^3 = 16.7M`)
//!    with a per-process atomic shard-creation bitmap and atomic temp-rename writes.

use crate::address::Address;
use dashmap::DashMap;
use memmap2::Mmap;
use rustc_hash::FxBuildHasher;
use std::borrow::Cow;
use std::env;
use std::fs::{self, File};
use std::io::{self, Write};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, OnceLock, RwLock};

/// `TagN(4, 0xE, 13)` (`[0xE8, 0x05]`) 8-byte header for a Warm `.ixs` ("Ix Store") slab.
/// Layout: `[0xE8, 0x05, version=1, tier=0 (Warm), 0, 0, 0, 0]`.
pub const IXS_HEADER_WARM: [u8; 8] = [0xE8, 0x05, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00];

/// `TagN(4, 0xE, 13)` (`[0xE8, 0x05]`) 8-byte header for a Cold (`zstd`) `.ixs` slab.
/// Layout: `[0xE8, 0x05, version=1, tier=1 (Cold/zstd), 0, 0, 0, 0]`.
pub const IXS_HEADER_COLD: [u8; 8] = [0xE8, 0x05, 0x01, 0x01, 0x00, 0x00, 0x00, 0x00];

/// `TagN(4, 0xE, 14)` (`[0xE8, 0x06]`) 8-byte header for an `.ixsp` ("Ix Store Pointer") index.
/// Layout: `[0xE8, 0x06, version=1, target=0 (.ixs), 0, 0, 0, 0]`.
pub const IXSP_HEADER: [u8; 8] = [0xE8, 0x06, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00];

/// Header size of `.ixsp`: 8-byte `TagN` header + 8-byte LE object count.
const IXSP_HEADER_SIZE: usize = 16;

/// Size of the 256-entry `u64` fan-out table in `.ixsp` (`256 * 8 = 2048`).
const IXSP_FANOUT_SIZE: usize = 256 * 8;

/// Offset where the sorted 32-byte `Address` array begins in `.ixsp`.
const IXSP_KEYS_OFFSET: usize = IXSP_HEADER_SIZE + IXSP_FANOUT_SIZE;

/// Size of each entry descriptor in `.ixsp` (`u64 offset + u32 stored_len + u32 flags = 16`).
const IXSP_ENTRY_SIZE: usize = 16;

/// Entry compression codec stored in `flags & 0xFF` of each `.ixsp` entry.
const COMPRESSION_NONE: u32 = 0;
const COMPRESSION_ZSTD: u32 = 1;

/// Default `zstd` compression level for Cold `.ixs` segments.
const ZSTD_DEFAULT_LEVEL: i32 = 3;

/// Temperature tier for `.ixs` store segments.
#[repr(u8)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum StoreTier {
  /// Uncompressed, 8-byte-aligned payloads for zero-copy `mmap` slicing.
  #[default]
  Warm = 0,
  /// `zstd`-compressed payloads with random-access pointer lookup via `.ixsp`.
  Cold = 1,
}

/// Tag identifying the kind of stored object in `.ixsp` entry flags (`(flags >> 8) & 0xFF`).
#[repr(u8)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ObjectKind {
  Raw = 0,
  Constant = 1,
  Blob = 2,
  Claim = 3,
  AssumptionTree = 4,
  Proof = 5,
  Env = 6,
}

impl ObjectKind {
  #[must_use]
  pub const fn from_u8(v: u8) -> Self {
    match v {
      1 => Self::Constant,
      2 => Self::Blob,
      3 => Self::Claim,
      4 => Self::AssumptionTree,
      5 => Self::Proof,
      6 => Self::Env,
      _ => Self::Raw,
    }
  }
}

/// Errors that can occur during store operations.
#[derive(Debug)]
pub enum StoreError {
  /// The requested address does not exist in the store.
  UnknownAddress(Address),
  /// An underlying filesystem I/O error.
  IoError(io::Error),
  /// An error during ixon serialization, deserialization, or digest verification.
  IxonError(String),
  /// Neither `IX_STORE_DIR` nor `HOME` is set.
  NoHome(env::VarError),
}

impl std::fmt::Display for StoreError {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      Self::UnknownAddress(a) => write!(f, "unknown address {}", a.hex()),
      Self::IoError(e) => write!(f, "IO error: {e}"),
      Self::IxonError(e) => write!(f, "ixon error: {e}"),
      Self::NoHome(e) => write!(f, "no HOME environment variable: {e}"),
    }
  }
}

impl std::error::Error for StoreError {}

impl From<io::Error> for StoreError {
  fn from(error: io::Error) -> Self {
    Self::IoError(error)
  }
}

/// Alias for `Result<T, StoreError>`.
pub type StoreResult<T> = Result<T, StoreError>;

/// Summary statistics for an [`IxStore`] instance.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct StoreStats {
  pub hot_cache_objects: usize,
  pub pack_count: usize,
  pub packed_objects: usize,
  pub loose_objects: usize,
  pub total_pack_bytes: u64,
  pub total_loose_bytes: u64,
}

#[inline]
fn is_valid_ixs_header(hdr: &[u8]) -> bool {
  hdr.len() >= 8
    && hdr[0] == 0xE8
    && hdr[1] == 0x05
    && hdr[2] == 0x01
    && (hdr[3] == 0x00 || hdr[3] == 0x01)
}

#[inline]
fn is_valid_ixsp_header(hdr: &[u8]) -> bool {
  hdr.len() >= 8 && hdr[0] == 0xE8 && hdr[1] == 0x06 && hdr[2] == 0x01
}

/// A memory-mapped `.ixs` ("Ix Store") + `.ixsp` ("Ix Store Pointer") pair.
struct MappedSegment {
  segment_id: String,
  ixsp_mmap: Mmap,
  ixs_mmap: Mmap,
  count: usize,
}

impl MappedSegment {
  fn open(ixsp_path: &Path, ixs_path: &Path) -> io::Result<Self> {
    let ixsp_file = File::open(ixsp_path)?;
    let ixs_file = File::open(ixs_path)?;
    // SAFETY: `.ixsp` and `.ixs` files are written atomically via temp-file
    // rename and are immutable once published.
    let ixsp_mmap = unsafe { Mmap::map(&ixsp_file)? };
    let ixs_mmap = unsafe { Mmap::map(&ixs_file)? };

    if ixsp_mmap.len() < IXSP_KEYS_OFFSET || !is_valid_ixsp_header(&ixsp_mmap[0..8]) {
      return Err(io::Error::new(
        io::ErrorKind::InvalidData,
        "invalid .ixsp header (expected TagN E8 06)",
      ));
    }
    if !is_valid_ixs_header(&ixs_mmap) {
      return Err(io::Error::new(
        io::ErrorKind::InvalidData,
        "invalid .ixs header (expected TagN E8 05)",
      ));
    }
    let count_u64 = u64::from_le_bytes(
      ixsp_mmap[8..16].try_into().expect("8-byte slice"),
    );
    let count = usize::try_from(count_u64).map_err(|_| {
      io::Error::new(io::ErrorKind::InvalidData, ".ixsp count overflow")
    })?;
    let expected_ixsp_len =
      IXSP_KEYS_OFFSET + count * 32 + count * IXSP_ENTRY_SIZE;
    if ixsp_mmap.len() < expected_ixsp_len {
      return Err(io::Error::new(
        io::ErrorKind::InvalidData,
        "truncated .ixsp file",
      ));
    }
    let segment_id = ixsp_path
      .file_stem()
      .and_then(|s| s.to_str())
      .unwrap_or("store")
      .to_owned();
    Ok(Self { segment_id, ixsp_mmap, ixs_mmap, count })
  }

  #[inline]
  fn fanout(&self, byte: u8) -> usize {
    let off = IXSP_HEADER_SIZE + usize::from(byte) * 8;
    let val = u64::from_le_bytes(
      self.ixsp_mmap[off..off + 8].try_into().expect("8-byte fanout"),
    );
    usize::try_from(val).unwrap_or(0)
  }

  #[inline]
  fn key_at(&self, index: usize) -> &[u8; 32] {
    let off = IXSP_KEYS_OFFSET + index * 32;
    self.ixsp_mmap[off..off + 32].try_into().expect("32-byte key")
  }

  #[inline]
  fn entry_at(&self, index: usize) -> (usize, usize, u32) {
    let entries_base = IXSP_KEYS_OFFSET + self.count * 32;
    let off = entries_base + index * IXSP_ENTRY_SIZE;
    let data_off_u64 = u64::from_le_bytes(
      self.ixsp_mmap[off..off + 8].try_into().expect("8-byte offset"),
    );
    let data_len_u32 = u32::from_le_bytes(
      self.ixsp_mmap[off + 8..off + 12].try_into().expect("4-byte len"),
    );
    let flags = u32::from_le_bytes(
      self.ixsp_mmap[off + 12..off + 16].try_into().expect("4-byte flags"),
    );
    let data_off = usize::try_from(data_off_u64).unwrap_or(0);
    let data_len = usize::try_from(data_len_u32).unwrap_or(0);
    (data_off, data_len, flags)
  }

  /// Look up `addr` in `O(log(N/256))` using the 256-entry fan-out table in `.ixsp`.
  fn find_index(&self, addr: &Address) -> Option<usize> {
    let target = addr.as_bytes();
    let first = target[0];
    let lo = if first == 0 { 0 } else { self.fanout(first - 1) };
    let hi = self.fanout(first);
    if lo >= hi || hi > self.count {
      return None;
    }
    let mut left = lo;
    let mut right = hi;
    while left < right {
      let mid = left + (right - left) / 2;
      let key = self.key_at(mid);
      match key.cmp(target) {
        std::cmp::Ordering::Less => left = mid + 1,
        std::cmp::Ordering::Greater => right = mid,
        std::cmp::Ordering::Equal => return Some(mid),
      }
    }
    None
  }

  fn contains(&self, addr: &Address) -> bool {
    self.find_index(addr).is_some()
  }

  /// Read an object from `.ixs` via its `.ixsp` pointer.
  /// Returns `Cow::Borrowed` for Warm (uncompressed) entries and `Cow::Owned`
  /// for Cold (`zstd`-compressed) entries.
  fn get_bytes(&self, addr: &Address) -> Option<Cow<'_, [u8]>> {
    let idx = self.find_index(addr)?;
    let (data_off, data_len, flags) = self.entry_at(idx);
    let end = data_off.checked_add(data_len)?;
    if end > self.ixs_mmap.len() {
      return None;
    }
    let raw_slice = &self.ixs_mmap[data_off..end];
    match flags & 0xFF {
      COMPRESSION_NONE => Some(Cow::Borrowed(raw_slice)),
      COMPRESSION_ZSTD => {
        let decompressed = zstd::stream::decode_all(raw_slice).ok()?;
        Some(Cow::Owned(decompressed))
      },
      _ => None,
    }
  }
}

/// Thread-safe, memory-mapped (`.ixs` + `.ixsp`) + shard-backed content-addressed store.
pub struct IxStore {
  root: PathBuf,
  objects_dir: PathBuf,
  packs_dir: PathBuf,
  /// Tier 0: Hot in-memory object cache.
  hot: DashMap<Address, Arc<[u8]>, FxBuildHasher>,
  /// Tier 1 (Warm) & Tier 2 (Cold): Memory-mapped `.ixs` + `.ixsp` pairs.
  segments: RwLock<Vec<MappedSegment>>,
  /// 256-bit bitmap tracking which `objects/<aa>` directories have been created.
  shard_ready: [AtomicU64; 4],
}

static GLOBAL_STORES: OnceLock<DashMap<PathBuf, Arc<IxStore>, FxBuildHasher>> =
  OnceLock::new();

static WRITE_SEQ: AtomicU64 = AtomicU64::new(0);

fn store_registry() -> &'static DashMap<PathBuf, Arc<IxStore>, FxBuildHasher> {
  GLOBAL_STORES.get_or_init(|| DashMap::with_hasher(FxBuildHasher))
}

impl IxStore {
  /// Resolve the default store root directory: `$IX_STORE_DIR` if set and
  /// non-empty, otherwise `$HOME/.ix/store`.
  pub fn default_root() -> StoreResult<PathBuf> {
    if let Ok(custom) = env::var("IX_STORE_DIR") {
      if !custom.is_empty() {
        return Ok(PathBuf::from(custom));
      }
    }
    let home = env::var("HOME").map_err(StoreError::NoHome)?;
    Ok(Path::new(&home).join(".ix").join("store"))
  }

  /// Resolve the `~/.ix/cache/<namespace>` directory (or `$IX_CACHE_DIR/<namespace>`).
  pub fn cache_dir(namespace: &str) -> StoreResult<PathBuf> {
    let base = if let Ok(custom) = env::var("IX_CACHE_DIR") {
      if !custom.is_empty() {
        PathBuf::from(custom)
      } else {
        let home = env::var("HOME").map_err(StoreError::NoHome)?;
        Path::new(&home).join(".ix").join("cache")
      }
    } else {
      let home = env::var("HOME").map_err(StoreError::NoHome)?;
      Path::new(&home).join(".ix").join("cache")
    };
    let path = base.join(namespace);
    if !path.exists() {
      fs::create_dir_all(&path)?;
    }
    Ok(path)
  }

  /// Open (or reuse the process-wide handle for) the store rooted at `root`.
  pub fn open(root: &Path) -> StoreResult<Arc<Self>> {
    let registry = store_registry();
    if let Some(existing) = registry.get(root) {
      return Ok(Arc::clone(existing.value()));
    }
    let objects_dir = root.join("objects");
    let packs_dir = root.join("packs");
    fs::create_dir_all(&objects_dir)?;
    fs::create_dir_all(&packs_dir)?;

    let store = Arc::new(Self {
      root: root.to_path_buf(),
      objects_dir,
      packs_dir,
      hot: DashMap::with_hasher(FxBuildHasher),
      segments: RwLock::new(Vec::new()),
      shard_ready: [
        AtomicU64::new(0),
        AtomicU64::new(0),
        AtomicU64::new(0),
        AtomicU64::new(0),
      ],
    });
    store.reload_segments()?;
    registry.insert(root.to_path_buf(), Arc::clone(&store));
    Ok(store)
  }

  /// Open or retrieve the default [`IxStore`] (`$IX_STORE_DIR` or `~/.ix/store`).
  pub fn global() -> StoreResult<Arc<Self>> {
    let root = Self::default_root()?;
    Self::open(&root)
  }

  /// Root path of this store (`~/.ix/store`).
  #[must_use]
  pub fn root(&self) -> &Path {
    &self.root
  }

  /// Scan `packs/*.ixsp` and memory-map any newly discovered `.ixs` + `.ixsp` pairs.
  pub fn reload_segments(&self) -> StoreResult<()> {
    let Ok(entries) = fs::read_dir(&self.packs_dir) else {
      return Ok(());
    };
    let mut guard = self.segments.write().expect("segments lock poisoned");
    for entry in entries.flatten() {
      let path = entry.path();
      if path.extension().and_then(|s| s.to_str()) != Some("ixsp") {
        continue;
      }
      let stem = path
        .file_stem()
        .and_then(|s| s.to_str())
        .unwrap_or("")
        .to_owned();
      if stem.is_empty() || guard.iter().any(|s| s.segment_id == stem) {
        continue;
      }
      let ixs_path = self.packs_dir.join(format!("{stem}.ixs"));
      if let Ok(mapped) = MappedSegment::open(&path, &ixs_path) {
        guard.push(mapped);
      }
    }
    Ok(())
  }

  /// Ensure the 1-level shard directory `objects/<aa>` exists, executing
  /// `create_dir_all` at most once per shard per process.
  #[inline]
  fn ensure_shard_dir(&self, first_byte: u8, hex_prefix: &str) -> io::Result<PathBuf> {
    let dir = self.objects_dir.join(hex_prefix);
    let word = usize::from(first_byte >> 6);
    let bit = 1u64 << (first_byte & 63);
    if (self.shard_ready[word].load(Ordering::Acquire) & bit) == 0 {
      fs::create_dir_all(&dir)?;
      self.shard_ready[word].fetch_or(bit, Ordering::Release);
    }
    Ok(dir)
  }

  /// Return the loose file path `objects/<aa>/<62-hex>` for `addr`.
  #[must_use]
  pub fn loose_path(&self, addr: &Address) -> PathBuf {
    let hex = addr.hex();
    self.objects_dir.join(&hex[0..2]).join(&hex[2..])
  }

  /// Legacy 3-level path `<root>/<aa>/<bb>/<cc>/<58-hex>` used only as a
  /// read-fallback for pre-migration stores.
  fn legacy_path(&self, addr: &Address) -> PathBuf {
    let hex = addr.hex();
    self
      .root
      .join(&hex[0..2])
      .join(&hex[2..4])
      .join(&hex[4..6])
      .join(&hex[6..])
  }

  /// Check whether `addr` is present in the hot cache, any mapped `.ixs`+`.ixsp`,
  /// or the loose shard directory.
  #[must_use]
  pub fn contains(&self, addr: &Address) -> bool {
    if self.hot.contains_key(addr) {
      return true;
    }
    {
      let segments = self.segments.read().expect("segments lock poisoned");
      if segments.iter().any(|s| s.contains(addr)) {
        return true;
      }
    }
    if self.loose_path(addr).exists() {
      return true;
    }
    if self.reload_segments().is_ok() {
      let segments = self.segments.read().expect("segments lock poisoned");
      if segments.iter().any(|s| s.contains(addr)) {
        return true;
      }
    }
    self.legacy_path(addr).exists()
  }

  /// Persist `bytes` at `addr` (either content-hashed or caller-supplied via `write_at`).
  /// Short-circuits immediately if `addr` already exists in memory or on disk.
  pub fn write_at(&self, addr: &Address, bytes: &[u8]) -> StoreResult<()> {
    if self.hot.contains_key(addr) {
      return Ok(());
    }
    {
      let segments = self.segments.read().expect("segments lock poisoned");
      if segments.iter().any(|s| s.contains(addr)) {
        self.hot.insert(addr.clone(), Arc::from(bytes));
        return Ok(());
      }
    }
    let hex = addr.hex();
    let shard_dir = self.ensure_shard_dir(addr.as_bytes()[0], &hex[0..2])?;
    let target_path = shard_dir.join(&hex[2..]);
    if !target_path.exists() {
      let seq = WRITE_SEQ.fetch_add(1, Ordering::Relaxed);
      let tmp_path =
        shard_dir.join(format!("{}.tmp.{}.{}", &hex[2..], std::process::id(), seq));
      fs::write(&tmp_path, bytes)?;
      if let Err(err) = fs::rename(&tmp_path, &target_path) {
        let _ = fs::remove_file(&tmp_path);
        if !target_path.exists() {
          return Err(StoreError::IoError(err));
        }
      }
    }
    self.hot.insert(addr.clone(), Arc::from(bytes));
    Ok(())
  }

  /// Compute `addr = blake3(bytes)`, persist `bytes` if not already present,
  /// and return `addr`.
  pub fn write(&self, bytes: &[u8]) -> StoreResult<Address> {
    let addr = Address::hash(bytes);
    self.write_at(&addr, bytes)?;
    Ok(addr)
  }

  /// Read the bytes stored at `addr` (checking Tier 0 hot cache -> Tier 1/2 `.ixs`+`.ixsp` -> Tier 3 loose shard).
  pub fn read(&self, addr: &Address) -> StoreResult<Vec<u8>> {
    if let Some(cached) = self.hot.get(addr) {
      return Ok(cached.value().as_ref().to_vec());
    }
    {
      let segments = self.segments.read().expect("segments lock poisoned");
      for seg in segments.iter() {
        if let Some(cow) = seg.get_bytes(addr) {
          let vec = cow.into_owned();
          self.hot.insert(addr.clone(), Arc::from(vec.as_slice()));
          return Ok(vec);
        }
      }
    }
    let loose = self.loose_path(addr);
    if let Ok(bytes) = fs::read(&loose) {
      self.hot.insert(addr.clone(), Arc::from(bytes.as_slice()));
      return Ok(bytes);
    }
    // Refresh segments in case another process wrote a new `.ixs`+`.ixsp` since we opened.
    self.reload_segments()?;
    {
      let segments = self.segments.read().expect("segments lock poisoned");
      for seg in segments.iter() {
        if let Some(cow) = seg.get_bytes(addr) {
          let vec = cow.into_owned();
          self.hot.insert(addr.clone(), Arc::from(vec.as_slice()));
          return Ok(vec);
        }
      }
    }
    let legacy = self.legacy_path(addr);
    if let Ok(bytes) = fs::read(&legacy) {
      self.hot.insert(addr.clone(), Arc::from(bytes.as_slice()));
      return Ok(bytes);
    }
    Err(StoreError::UnknownAddress(addr.clone()))
  }

  /// Read the bytes at `addr` and verify that `blake3(bytes) == addr`.
  pub fn read_verified(&self, addr: &Address) -> StoreResult<Vec<u8>> {
    let bytes = self.read(addr)?;
    let actual = Address::hash(&bytes);
    if &actual != addr {
      return Err(StoreError::IxonError(format!(
        "BLAKE3 digest mismatch for {}: got {}",
        addr.hex(),
        actual.hex()
      )));
    }
    Ok(bytes)
  }

  /// Write a batch of `(Address, &[u8], ObjectKind)` entries into a single
  /// immutable, sorted Warm `.ixs` + `.ixsp` pair and memory-map it immediately.
  pub fn write_pack<'a, I>(&self, entries: I) -> StoreResult<(Address, usize)>
  where
    I: IntoIterator<Item = (Address, &'a [u8], ObjectKind)>,
  {
    self.write_pack_tiered(entries, StoreTier::Warm)
  }

  /// Write a batch of `(Address, &[u8], ObjectKind)` entries into a single
  /// immutable, sorted `.ixs` ("Ix Store") + `.ixsp` ("Ix Store Pointer") pair
  /// at the requested [`StoreTier`] (`Warm` = uncompressed `mmap`, `Cold` = `zstd`).
  pub fn write_pack_tiered<'a, I>(
    &self,
    entries: I,
    tier: StoreTier,
  ) -> StoreResult<(Address, usize)>
  where
    I: IntoIterator<Item = (Address, &'a [u8], ObjectKind)>,
  {
    let mut sorted: Vec<(Address, &[u8], ObjectKind)> =
      entries.into_iter().collect();
    if sorted.is_empty() {
      return Ok((Address::hash(&[]), 0));
    }
    sorted.sort_unstable_by(|a, b| a.0.as_bytes().cmp(b.0.as_bytes()));
    sorted.dedup_by(|a, b| a.0 == b.0);

    let ixs_header = match tier {
      StoreTier::Warm => IXS_HEADER_WARM,
      StoreTier::Cold => IXS_HEADER_COLD,
    };

    // Populate hot cache and compute segment digest over header + sorted `(addr, len, bytes)`.
    let mut seg_hasher = blake3::Hasher::new();
    seg_hasher.update(&ixs_header);
    for (addr, bytes, kind) in &sorted {
      seg_hasher.update(addr.as_bytes());
      seg_hasher.update(&[*kind as u8]);
      seg_hasher.update(&(bytes.len() as u64).to_le_bytes());
      seg_hasher.update(bytes);
      self.hot.insert(addr.clone(), Arc::from(*bytes));
    }
    let seg_addr = Address::from_blake3_hash(seg_hasher.finalize());
    let seg_stem = format!("store-{}", seg_addr.hex());
    let ixsp_path = self.packs_dir.join(format!("{seg_stem}.ixsp"));
    let ixs_path = self.packs_dir.join(format!("{seg_stem}.ixs"));

    if ixsp_path.exists() && ixs_path.exists() {
      self.reload_segments()?;
      return Ok((seg_addr, sorted.len()));
    }

    let seq = WRITE_SEQ.fetch_add(1, Ordering::Relaxed);
    let pid = std::process::id();
    let tmp_ixs = self.packs_dir.join(format!("{seg_stem}.ixs.tmp.{pid}.{seq}"));
    let tmp_ixsp = self.packs_dir.join(format!("{seg_stem}.ixsp.tmp.{pid}.{seq}"));

    // 1. Write `.ixs` (8-byte `TagN` E8 05 header + 8-byte-aligned object payloads).
    let mut descriptors: Vec<(u64, u32, u32)> = Vec::with_capacity(sorted.len());
    {
      let mut ixs_out = io::BufWriter::new(File::create(&tmp_ixs)?);
      ixs_out.write_all(&ixs_header)?;
      let mut offset: u64 = 8;
      for (_addr, bytes, kind) in &sorted {
        let (encoded, comp_flag): (Cow<'_, [u8]>, u32) = match tier {
          StoreTier::Warm => (Cow::Borrowed(*bytes), COMPRESSION_NONE),
          StoreTier::Cold => {
            if let Ok(compressed) = zstd::bulk::compress(bytes, ZSTD_DEFAULT_LEVEL)
              && compressed.len() < bytes.len()
            {
              (Cow::Owned(compressed), COMPRESSION_ZSTD)
            } else {
              (Cow::Borrowed(*bytes), COMPRESSION_NONE)
            }
          },
        };
        let len_u32 = u32::try_from(encoded.len()).map_err(|_| {
          io::Error::new(io::ErrorKind::InvalidInput, "object exceeds 4 GiB")
        })?;
        let flags = (u32::from(*kind as u8) << 8) | comp_flag;
        descriptors.push((offset, len_u32, flags));
        ixs_out.write_all(&encoded)?;
        offset += u64::from(len_u32);
        let pad = (8 - (offset % 8)) % 8;
        if pad > 0 {
          const ZEROS: [u8; 8] = [0u8; 8];
          let pad_usize = usize::try_from(pad).unwrap_or(0);
          ixs_out.write_all(&ZEROS[..pad_usize])?;
          offset += pad;
        }
      }
      ixs_out.flush()?;
    }

    // 2. Build 256-entry fan-out table + sorted keys + entry descriptors for `.ixsp`.
    let count = sorted.len();
    let mut fanout = [0u64; 256];
    for (addr, _, _) in &sorted {
      let b = usize::from(addr.as_bytes()[0]);
      fanout[b] += 1;
    }
    let mut running = 0u64;
    for slot in &mut fanout {
      running += *slot;
      *slot = running;
    }

    {
      let mut ixsp_out = io::BufWriter::new(File::create(&tmp_ixsp)?);
      ixsp_out.write_all(&IXSP_HEADER)?;
      ixsp_out.write_all(&(count as u64).to_le_bytes())?;
      for f in &fanout {
        ixsp_out.write_all(&f.to_le_bytes())?;
      }
      for (addr, _, _) in &sorted {
        ixsp_out.write_all(addr.as_bytes())?;
      }
      for (off, len, flags) in &descriptors {
        ixsp_out.write_all(&off.to_le_bytes())?;
        ixsp_out.write_all(&len.to_le_bytes())?;
        ixsp_out.write_all(&flags.to_le_bytes())?;
      }
      ixsp_out.flush()?;
    }

    // Publish `.ixs` first, then `.ixsp` so readers scanning `.ixsp`
    // always see a complete `.ixs`.
    fs::rename(&tmp_ixs, &ixs_path)?;
    fs::rename(&tmp_ixsp, &ixsp_path)?;

    self.reload_segments()?;
    Ok((seg_addr, count))
  }

  /// Compact all loose objects in `objects/<aa>/*` into a Warm `.ixs` + `.ixsp` pair.
  pub fn compact(&self) -> StoreResult<(usize, u64)> {
    self.compact_tiered(StoreTier::Warm)
  }

  /// Compact all loose objects in `objects/<aa>/*` into a single `.ixs` + `.ixsp`
  /// at the requested [`StoreTier`] (`Warm` = uncompressed `mmap`, `Cold` = `zstd`)
  /// and unlink the loose files once the segment is mapped.
  /// Returns `(num_compacted_objects, raw_bytes_compacted)`.
  pub fn compact_tiered(&self, tier: StoreTier) -> StoreResult<(usize, u64)> {
    let mut loose_paths: Vec<(Address, PathBuf)> = Vec::new();
    if let Ok(shards) = fs::read_dir(&self.objects_dir) {
      for shard_entry in shards.flatten() {
        let shard_path = shard_entry.path();
        let Some(prefix) = shard_path.file_name().and_then(|s| s.to_str()) else {
          continue;
        };
        if prefix.len() != 2 || !prefix.bytes().all(|b| b.is_ascii_hexdigit()) {
          continue;
        }
        if let Ok(files) = fs::read_dir(&shard_path) {
          for file_entry in files.flatten() {
            let fpath = file_entry.path();
            let Some(rest) = fpath.file_name().and_then(|s| s.to_str()) else {
              continue;
            };
            if rest.len() != 62 || !rest.bytes().all(|b| b.is_ascii_hexdigit()) {
              continue;
            }
            let full_hex = format!("{prefix}{rest}");
            if let Some(addr) = Address::from_hex(&full_hex) {
              loose_paths.push((addr, fpath));
            }
          }
        }
      }
    }
    if loose_paths.is_empty() {
      return Ok((0, 0));
    }

    let mut payloads: Vec<(Address, Vec<u8>)> =
      Vec::with_capacity(loose_paths.len());
    let mut total_bytes: u64 = 0;
    for (addr, path) in &loose_paths {
      if let Ok(bytes) = fs::read(path) {
        total_bytes += bytes.len() as u64;
        payloads.push((addr.clone(), bytes));
      }
    }
    let refs: Vec<(Address, &[u8], ObjectKind)> = payloads
      .iter()
      .map(|(a, b)| (a.clone(), b.as_slice(), ObjectKind::Raw))
      .collect();
    let (_seg_addr, count) = self.write_pack_tiered(refs, tier)?;

    // Now that the `.ixs` + `.ixsp` segment is durably published and mapped, unlink loose files.
    for (_addr, path) in &loose_paths {
      let _ = fs::remove_file(path);
    }
    Ok((count, total_bytes))
  }

  /// Compute current store statistics across hot cache, mapped `.ixs`+`.ixsp` segments, and loose shards.
  pub fn stats(&self) -> StoreResult<StoreStats> {
    self.reload_segments()?;
    let (pack_count, packed_objects, total_pack_bytes) = {
      let segments = self.segments.read().expect("segments lock poisoned");
      let p_count = segments.len();
      let p_objs: usize = segments.iter().map(|s| s.count).sum();
      let p_bytes: u64 = segments.iter().map(|s| s.ixs_mmap.len() as u64).sum();
      (p_count, p_objs, p_bytes)
    };
    let mut loose_objects = 0usize;
    let mut total_loose_bytes = 0u64;
    if let Ok(shards) = fs::read_dir(&self.objects_dir) {
      for shard in shards.flatten() {
        if let Ok(files) = fs::read_dir(shard.path()) {
          for f in files.flatten() {
            if let Some(name) = f.file_name().to_str() {
              if name.len() == 62 && name.bytes().all(|b| b.is_ascii_hexdigit())
              {
                loose_objects += 1;
                if let Ok(meta) = f.metadata() {
                  total_loose_bytes += meta.len();
                }
              }
            }
          }
        }
      }
    }
    Ok(StoreStats {
      hot_cache_objects: self.hot.len(),
      pack_count,
      packed_objects,
      loose_objects,
      total_pack_bytes,
      total_loose_bytes,
    })
  }

  /// Ingest an `.ixe` file (or all `.ixe` member/chunk files inside a `.ixc`
  /// catalog directory) into a Warm `.ixs` + `.ixsp` segment.
  pub fn ingest_ixe(&self, path: &Path) -> StoreResult<(Address, usize)> {
    self.ingest_ixe_tiered(path, StoreTier::Warm)
  }

  /// Ingest an `.ixe` file (or all `.ixe` member/chunk files inside a `.ixc`
  /// catalog directory) into a single deduplicated, 8-byte-aligned `.ixs` + `.ixsp`
  /// segment at the requested [`StoreTier`] (`Warm` = uncompressed `mmap`,
  /// `Cold` = `zstd`-compressed), stripping inline keys/lengths and `§4/§5` metadata.
  pub fn ingest_ixe_tiered(
    &self,
    path: &Path,
    tier: StoreTier,
  ) -> StoreResult<(Address, usize)> {
    let mut ixe_files: Vec<PathBuf> = Vec::new();
    if path.is_dir() {
      for e in fs::read_dir(path)?.flatten() {
        let p = e.path();
        if p.extension().and_then(|s| s.to_str()) == Some("ixe") {
          ixe_files.push(p);
        }
      }
      ixe_files.sort();
    } else {
      ixe_files.push(path.to_path_buf());
    }

    let mut mmaps: Vec<Mmap> = Vec::with_capacity(ixe_files.len());
    for ixe in &ixe_files {
      let file = File::open(ixe)?;
      // SAFETY: read-only memory map of `.ixe` file during ingestion.
      let mmap = unsafe { Mmap::map(&file)? };
      mmaps.push(mmap);
    }

    let mut entries: Vec<(Address, &[u8], ObjectKind)> = Vec::new();
    for mmap in &mmaps {
      let (_stored_root, windows) =
        scan_ixe_windows(mmap).map_err(StoreError::IxonError)?;
      for (addr, off, len, kind) in windows {
        let start = usize::try_from(off).unwrap_or(0);
        let end = start + usize::try_from(len).unwrap_or(0);
        if end <= mmap.len() {
          entries.push((addr, &mmap[start..end], kind));
        }
      }
    }

    self.write_pack_tiered(entries, tier)
  }
}

/// Read a `TagN(0)` unsigned integer from `buf` (`Ixon.getTagN 0`).
fn read_tagn0(buf: &mut &[u8]) -> Result<u64, String> {
  let Some((&head, rest)) = buf.split_first() else {
    return Err("TagN(0): EOF".to_string());
  };
  *buf = rest;
  let p = u64::from(head);
  if p < 128 {
    return Ok(p);
  }
  if p < 192 {
    let Some((&lo, rest2)) = buf.split_first() else {
      return Err("TagN(0): EOF in rung 2".to_string());
    };
    *buf = rest2;
    return Ok(128 + (p - 128) * 256 + u64::from(lo));
  }
  let (len, base): (usize, u64) = match p - 192 {
    0 => (2, 16512),
    1 => (3, 82048),
    2 => (4, 16_859_264),
    3 => (8, 4_311_826_560),
    c => return Err(format!("TagN(0): invalid rung code {c}")),
  };
  let Some((head_bytes, rest2)) = buf.split_at_checked(len) else {
    return Err(format!("TagN(0): EOF, need {len} bytes"));
  };
  *buf = rest2;
  let mut raw = [0u8; 8];
  raw[..len].copy_from_slice(head_bytes);
  base
    .checked_add(u64::from_le_bytes(raw))
    .ok_or_else(|| "TagN(0): u64 overflow".to_string())
}

fn read_addr(buf: &mut &[u8]) -> Result<Address, String> {
  let Some((bytes, rest)) = buf.split_at_checked(32) else {
    return Err("scan_ixe_windows: EOF reading 32-byte Address".to_string());
  };
  *buf = rest;
  Address::from_slice(bytes).map_err(|e| e.to_string())
}

/// Scan an `.ixe` buffer's header, §1 (`Blobs`), and §2 (`Constants`) in one
/// pass without parsing constant bodies, returning `(stored_root, windows)`
/// where each window is `(Address, byte_offset, byte_len, ObjectKind)`.
pub fn scan_ixe_windows(
  data: &[u8],
) -> Result<(Address, Vec<(Address, u64, u32, ObjectKind)>), String> {
  let mut buf = data;
  let Some((&head, rest)) = buf.split_first() else {
    return Err("scan_ixe_windows: empty .ixe file".to_string());
  };
  if head != 0xE4 && head != 0xE5 {
    return Err(format!(
      "scan_ixe_windows: expected .ixe v4 (0xE4) or v5 (0xE5) header, got 0x{head:02X}"
    ));
  }
  buf = rest;
  let stored_root = read_addr(&mut buf)?;

  // `main : Option<Address>`
  let Some((&opt_tag, rest2)) = buf.split_first() else {
    return Err("scan_ixe_windows: EOF at main option tag".to_string());
  };
  buf = rest2;
  match opt_tag {
    0 => {},
    1 => {
      let _main = read_addr(&mut buf)?;
    },
    t => {
      return Err(format!("scan_ixe_windows: invalid main option tag {t}"));
    },
  }

  // `assumptions : Vec<Address>`
  let num_assumptions = usize::try_from(read_tagn0(&mut buf)?)
    .map_err(|_| "scan_ixe_windows: assumption count overflow".to_string())?;
  let asm_bytes = num_assumptions
    .checked_mul(32)
    .ok_or_else(|| "scan_ixe_windows: assumption bytes overflow".to_string())?;
  let Some((_, rest3)) = buf.split_at_checked(asm_bytes) else {
    return Err("scan_ixe_windows: truncated assumptions".to_string());
  };
  buf = rest3;

  // v5 (`0xE5`) role binding section: `addr: 32` + `len: TagN(0)` + `len` bytes
  if head == 0xE5 {
    let _rb_addr = read_addr(&mut buf)?;
    let rb_len = usize::try_from(read_tagn0(&mut buf)?)
      .map_err(|_| "scan_ixe_windows: role binding length overflow".to_string())?;
    let Some((_, rest4)) = buf.split_at_checked(rb_len) else {
      return Err("scan_ixe_windows: truncated role binding section".to_string());
    };
    buf = rest4;
  }

  // §1: Blobs
  let num_blobs = usize::try_from(read_tagn0(&mut buf)?)
    .map_err(|_| "scan_ixe_windows: blob count overflow".to_string())?;
  let mut windows: Vec<(Address, u64, u32, ObjectKind)> = Vec::new();
  for _ in 0..num_blobs {
    let addr = read_addr(&mut buf)?;
    let len_u64 = read_tagn0(&mut buf)?;
    let len = usize::try_from(len_u64)
      .map_err(|_| "scan_ixe_windows: blob length overflow".to_string())?;
    let len_u32 = u32::try_from(len_u64)
      .map_err(|_| "scan_ixe_windows: blob exceeds 4 GiB".to_string())?;
    let offset = (data.len() - buf.len()) as u64;
    let Some((_, rest_b)) = buf.split_at_checked(len) else {
      return Err("scan_ixe_windows: truncated blob payload".to_string());
    };
    buf = rest_b;
    windows.push((addr, offset, len_u32, ObjectKind::Blob));
  }

  // §2: Constants
  let num_consts = usize::try_from(read_tagn0(&mut buf)?)
    .map_err(|_| "scan_ixe_windows: const count overflow".to_string())?;
  windows.reserve(num_consts);
  for _ in 0..num_consts {
    let addr = read_addr(&mut buf)?;
    let len_u64 = read_tagn0(&mut buf)?;
    let len = usize::try_from(len_u64)
      .map_err(|_| "scan_ixe_windows: const length overflow".to_string())?;
    let len_u32 = u32::try_from(len_u64)
      .map_err(|_| "scan_ixe_windows: const exceeds 4 GiB".to_string())?;
    let offset = (data.len() - buf.len()) as u64;
    let Some((_, rest_c)) = buf.split_at_checked(len) else {
      return Err("scan_ixe_windows: truncated constant payload".to_string());
    };
    buf = rest_c;
    windows.push((addr, offset, len_u32, ObjectKind::Constant));
  }

  Ok((stored_root, windows))
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn test_loose_and_warm_cold_ixs_roundtrip() {
    let tmp = env::temp_dir().join(format!(
      "ix-store-test-{}-{}",
      std::process::id(),
      WRITE_SEQ.fetch_add(1, Ordering::Relaxed)
    ));
    let store = IxStore::open(&tmp).expect("open store");

    let a1 = store.write(b"alpha").expect("write alpha");
    let a2 = store.write(b"beta").expect("write beta");
    assert!(store.contains(&a1));
    assert!(store.contains(&a2));
    assert_eq!(store.read_verified(&a1).expect("read a1"), b"alpha");
    assert_eq!(store.read_verified(&a2).expect("read a2"), b"beta");

    // Compact loose files into a Warm `.ixs` + `.ixsp` pair
    let (compacted, _) = store.compact().expect("compact warm");
    assert_eq!(compacted, 2);
    assert!(!store.loose_path(&a1).exists());
    assert!(!store.loose_path(&a2).exists());

    // Clear hot cache to force reading from the memory-mapped `.ixs` via `.ixsp`
    store.hot.clear();
    assert!(store.contains(&a1));
    assert_eq!(store.read_verified(&a1).expect("read a1 from warm .ixs"), b"alpha");
    assert_eq!(store.read_verified(&a2).expect("read a2 from warm .ixs"), b"beta");

    // Write a larger repetitive payload and compact into a Cold (`zstd`) `.ixs` + `.ixsp`
    let big_payload: Vec<u8> = b"ix-constant-sharing-table-pattern-".repeat(64);
    let a3 = store.write(&big_payload).expect("write big_payload");
    let (cold_compacted, raw_bytes) = store
      .compact_tiered(StoreTier::Cold)
      .expect("compact cold");
    assert_eq!(cold_compacted, 1);
    assert_eq!(raw_bytes, big_payload.len() as u64);

    // Clear hot cache to force zstd decompression from the Cold `.ixs`
    store.hot.clear();
    assert_eq!(
      store.read_verified(&a3).expect("read a3 from cold .ixs"),
      big_payload
    );

    let st = store.stats().expect("stats");
    assert_eq!(st.pack_count, 2);
    assert_eq!(st.packed_objects, 3);
    assert_eq!(st.loose_objects, 0);

    let _ = fs::remove_dir_all(&tmp);
  }

  #[test]
  fn test_ixe_to_ixs_ingest() {
    let tmp = env::temp_dir().join(format!(
      "ix-store-ixe-test-{}-{}",
      std::process::id(),
      WRITE_SEQ.fetch_add(1, Ordering::Relaxed)
    ));
    let store = IxStore::open(&tmp).expect("open store");

    let blob_payload = b"hello-ixe-blob";
    let blob_addr = Address::hash(blob_payload);
    let const_payload: Vec<u8> = b"\xD0minimal-const-payload-".repeat(20);
    let const_addr = Address::hash(&const_payload);
    let env_root = Address::hash(b"test-env-root");

    let mut ixe_bytes: Vec<u8> = Vec::new();
    ixe_bytes.push(0xE4); // v4 .ixe header
    ixe_bytes.extend_from_slice(env_root.as_bytes());
    ixe_bytes.push(0x00); // main = None
    ixe_bytes.push(0x00); // assumptions count = 0
    // §1 Blobs: count = 1
    ixe_bytes.push(0x01);
    ixe_bytes.extend_from_slice(blob_addr.as_bytes());
    ixe_bytes.push(blob_payload.len() as u8);
    ixe_bytes.extend_from_slice(blob_payload);
    // §2 Constants: count = 1 (TagN(0) rung 2 length since const_payload.len() = 460 >= 128)
    ixe_bytes.push(0x01);
    ixe_bytes.extend_from_slice(const_addr.as_bytes());
    let clen = const_payload.len() - 128;
    ixe_bytes.push((128 + clen / 256) as u8);
    ixe_bytes.push((clen % 256) as u8);
    ixe_bytes.extend_from_slice(&const_payload);
    // §3 Hints: count = 0
    ixe_bytes.push(0x00);

    let src_ixe = tmp.join("sample.ixe");
    fs::write(&src_ixe, &ixe_bytes).expect("write sample.ixe");

    let (_seg_id, count) = store
      .ingest_ixe_tiered(&src_ixe, StoreTier::Cold)
      .expect("ingest_ixe_tiered cold");
    assert_eq!(count, 2);

    store.hot.clear();
    assert!(store.contains(&blob_addr));
    assert!(store.contains(&const_addr));
    assert_eq!(store.read_verified(&blob_addr).expect("read blob"), blob_payload);
    assert_eq!(
      store.read_verified(&const_addr).expect("read const"),
      const_payload
    );

    let _ = fs::remove_dir_all(&tmp);
  }
}
