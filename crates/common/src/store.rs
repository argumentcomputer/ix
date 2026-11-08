//! High-performance content-addressed store for Ix (`~/.ix/store`).
//!
//! Combines:
//! 1. **In-memory hot cache (`DashMap<Address, Arc<[u8]>>`)** for zero-syscall
//!    intra-process reads and existence short-circuiting.
//! 2. **Memory-mapped immutable packfiles (`packs/pack-<hash>.ixpack` + `.ixidx`)**
//!    with a 256-entry first-byte fan-out table and sorted 32-byte keys for
//!    zero-syscall `O(log(N/256))` binary search and zero-copy slice reads.
//! 3. **1-level loose object shards (`objects/<aa>/<62-hex>`)** (`256` shard
//!    directories instead of `256^3 = 16.7M`), with per-process atomic shard
//!    initialization bitmaps and atomic temp-file-plus-rename publishing.

use crate::address::Address;
use dashmap::DashMap;
use memmap2::Mmap;
use rustc_hash::FxBuildHasher;
use std::env;
use std::fs::{self, File};
use std::io::{self, Write};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, OnceLock, RwLock};

/// Magic bytes for an `.ixpack` data file (`"IXPK\x00\x00\x00\x01"`).
pub const PACK_MAGIC: [u8; 8] = *b"IXPK\x00\x00\x00\x01";

/// Magic bytes for an `.ixidx` index file (`"IXID\x00\x00\x00\x01"`).
pub const IDX_MAGIC: [u8; 8] = *b"IXID\x00\x00\x00\x01";

/// Header size of `.ixidx`: 8-byte magic + 8-byte LE object count.
const IDX_HEADER_SIZE: usize = 16;

/// Size of the 256-entry `u64` fan-out table in `.ixidx` (`256 * 8 = 2048`).
const IDX_FANOUT_SIZE: usize = 256 * 8;

/// Offset where the sorted 32-byte `Address` array begins in `.ixidx`.
const IDX_KEYS_OFFSET: usize = IDX_HEADER_SIZE + IDX_FANOUT_SIZE;

/// Size of each entry descriptor in `.ixidx` (`u64 offset + u32 len + u32 flags = 16`).
const IDX_ENTRY_SIZE: usize = 16;

/// Tag identifying the kind of stored object in `.ixidx` flags.
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

/// A memory-mapped `.ixpack` + `.ixidx` pair.
struct MappedPack {
  pack_id: String,
  idx_mmap: Mmap,
  pack_mmap: Mmap,
  count: usize,
}

impl MappedPack {
  fn open(idx_path: &Path, pack_path: &Path) -> io::Result<Self> {
    let idx_file = File::open(idx_path)?;
    let pack_file = File::open(pack_path)?;
    // SAFETY: `.ixidx` and `.ixpack` files are written atomically via temp-file
    // rename and are immutable once published.
    let idx_mmap = unsafe { Mmap::map(&idx_file)? };
    let pack_mmap = unsafe { Mmap::map(&pack_file)? };

    if idx_mmap.len() < IDX_KEYS_OFFSET || idx_mmap[0..8] != IDX_MAGIC {
      return Err(io::Error::new(
        io::ErrorKind::InvalidData,
        "invalid .ixidx header",
      ));
    }
    if pack_mmap.len() < 8 || pack_mmap[0..8] != PACK_MAGIC {
      return Err(io::Error::new(
        io::ErrorKind::InvalidData,
        "invalid .ixpack header",
      ));
    }
    let count_u64 = u64::from_le_bytes(
      idx_mmap[8..16].try_into().expect("8-byte slice"),
    );
    let count = usize::try_from(count_u64).map_err(|_| {
      io::Error::new(io::ErrorKind::InvalidData, "pack count overflow")
    })?;
    let expected_idx_len =
      IDX_KEYS_OFFSET + count * 32 + count * IDX_ENTRY_SIZE;
    if idx_mmap.len() < expected_idx_len {
      return Err(io::Error::new(
        io::ErrorKind::InvalidData,
        "truncated .ixidx file",
      ));
    }
    let pack_id = idx_path
      .file_stem()
      .and_then(|s| s.to_str())
      .unwrap_or("pack")
      .to_owned();
    Ok(Self { pack_id, idx_mmap, pack_mmap, count })
  }

  #[inline]
  fn fanout(&self, byte: u8) -> usize {
    let off = IDX_HEADER_SIZE + usize::from(byte) * 8;
    let val = u64::from_le_bytes(
      self.idx_mmap[off..off + 8].try_into().expect("8-byte fanout"),
    );
    usize::try_from(val).unwrap_or(0)
  }

  #[inline]
  fn key_at(&self, index: usize) -> &[u8; 32] {
    let off = IDX_KEYS_OFFSET + index * 32;
    self.idx_mmap[off..off + 32].try_into().expect("32-byte key")
  }

  #[inline]
  fn entry_at(&self, index: usize) -> (usize, usize, u32) {
    let entries_base = IDX_KEYS_OFFSET + self.count * 32;
    let off = entries_base + index * IDX_ENTRY_SIZE;
    let data_off_u64 = u64::from_le_bytes(
      self.idx_mmap[off..off + 8].try_into().expect("8-byte offset"),
    );
    let data_len_u32 = u32::from_le_bytes(
      self.idx_mmap[off + 8..off + 12].try_into().expect("4-byte len"),
    );
    let flags = u32::from_le_bytes(
      self.idx_mmap[off + 12..off + 16].try_into().expect("4-byte flags"),
    );
    let data_off = usize::try_from(data_off_u64).unwrap_or(0);
    let data_len = usize::try_from(data_len_u32).unwrap_or(0);
    (data_off, data_len, flags)
  }

  /// Look up `addr` in `O(log(N/256))` using the 256-entry fan-out table.
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

  fn get_slice(&self, addr: &Address) -> Option<&[u8]> {
    let idx = self.find_index(addr)?;
    let (data_off, data_len, _flags) = self.entry_at(idx);
    let end = data_off.checked_add(data_len)?;
    if end <= self.pack_mmap.len() {
      Some(&self.pack_mmap[data_off..end])
    } else {
      None
    }
  }
}

/// Thread-safe, memory-mapped + shard-backed content-addressed store rooted at `root`.
pub struct IxStore {
  root: PathBuf,
  objects_dir: PathBuf,
  packs_dir: PathBuf,
  /// Hot in-memory object cache.
  hot: DashMap<Address, Arc<[u8]>, FxBuildHasher>,
  /// Memory-mapped `.ixpack` + `.ixidx` pairs.
  packs: RwLock<Vec<MappedPack>>,
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
  /// Resolve the default store root directory:
  /// 1. `$IX_STORE_DIR` if set and non-empty,
  /// 2. `$HOME/.ix/store` otherwise.
  pub fn default_root() -> StoreResult<PathBuf> {
    if let Ok(custom) = env::var("IX_STORE_DIR") {
      if !custom.is_empty() {
        return Ok(PathBuf::from(custom));
      }
    }
    let home = env::var("HOME").map(PathBuf::from).map_err(StoreError::NoHome)?;
    Ok(home.join(".ix").join("store"))
  }

  /// Resolve the default cache directory `~/.ix/cache/<namespace>`.
  pub fn default_cache_dir(namespace: &str) -> StoreResult<PathBuf> {
    let home = env::var("HOME").map(PathBuf::from).map_err(StoreError::NoHome)?;
    let dir = home.join(".ix").join("cache").join(namespace);
    if !dir.exists() {
      fs::create_dir_all(&dir)?;
    }
    Ok(dir)
  }

  /// Open or retrieve the cached process-wide [`IxStore`] for `root`.
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
      packs: RwLock::new(Vec::new()),
      shard_ready: [
        AtomicU64::new(0),
        AtomicU64::new(0),
        AtomicU64::new(0),
        AtomicU64::new(0),
      ],
    });
    store.reload_packs()?;
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

  /// Scan `packs/*.ixidx` and memory-map any newly discovered packfiles.
  pub fn reload_packs(&self) -> StoreResult<()> {
    let Ok(entries) = fs::read_dir(&self.packs_dir) else {
      return Ok(());
    };
    let mut guard = self.packs.write().expect("packs lock poisoned");
    for entry in entries.flatten() {
      let path = entry.path();
      if path.extension().and_then(|s| s.to_str()) != Some("ixidx") {
        continue;
      }
      let stem = path
        .file_stem()
        .and_then(|s| s.to_str())
        .unwrap_or("")
        .to_owned();
      if stem.is_empty() || guard.iter().any(|p| p.pack_id == stem) {
        continue;
      }
      let pack_path = self.packs_dir.join(format!("{stem}.ixpack"));
      if let Ok(mapped) = MappedPack::open(&path, &pack_path) {
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

  /// Check whether `addr` is present in the hot cache, any mapped `.ixpack`,
  /// or the loose shard directory.
  #[must_use]
  pub fn contains(&self, addr: &Address) -> bool {
    if self.hot.contains_key(addr) {
      return true;
    }
    {
      let packs = self.packs.read().expect("packs lock poisoned");
      if packs.iter().any(|p| p.contains(addr)) {
        return true;
      }
    }
    if self.loose_path(addr).exists() {
      return true;
    }
    if self.reload_packs().is_ok() {
      let packs = self.packs.read().expect("packs lock poisoned");
      if packs.iter().any(|p| p.contains(addr)) {
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
      let packs = self.packs.read().expect("packs lock poisoned");
      if packs.iter().any(|p| p.contains(addr)) {
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

  /// Read the bytes stored at `addr` (checking hot cache -> mapped `.ixpack`s -> loose shard).
  pub fn read(&self, addr: &Address) -> StoreResult<Vec<u8>> {
    if let Some(cached) = self.hot.get(addr) {
      return Ok(cached.value().as_ref().to_vec());
    }
    {
      let packs = self.packs.read().expect("packs lock poisoned");
      for pack in packs.iter() {
        if let Some(slice) = pack.get_slice(addr) {
          let arc: Arc<[u8]> = Arc::from(slice);
          self.hot.insert(addr.clone(), Arc::clone(&arc));
          return Ok(arc.as_ref().to_vec());
        }
      }
    }
    let loose = self.loose_path(addr);
    if let Ok(bytes) = fs::read(&loose) {
      self.hot.insert(addr.clone(), Arc::from(bytes.as_slice()));
      return Ok(bytes);
    }
    // Refresh packs in case another process wrote a new `.ixpack` since we opened.
    self.reload_packs()?;
    {
      let packs = self.packs.read().expect("packs lock poisoned");
      for pack in packs.iter() {
        if let Some(slice) = pack.get_slice(addr) {
          let arc: Arc<[u8]> = Arc::from(slice);
          self.hot.insert(addr.clone(), Arc::clone(&arc));
          return Ok(arc.as_ref().to_vec());
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
  /// immutable, sorted `.ixpack` + `.ixidx` pair and memory-map it immediately.
  /// Returns the pack's content-addressed ID (`Address`) and number of objects written.
  pub fn write_pack<'a, I>(&self, entries: I) -> StoreResult<(Address, usize)>
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

    // Populate hot cache and compute pack digest over sorted `(addr, len, bytes)`.
    let mut pack_hasher = blake3::Hasher::new();
    pack_hasher.update(&PACK_MAGIC);
    for (addr, bytes, kind) in &sorted {
      pack_hasher.update(addr.as_bytes());
      pack_hasher.update(&[*kind as u8]);
      pack_hasher.update(&(bytes.len() as u64).to_le_bytes());
      pack_hasher.update(bytes);
      self.hot.insert(addr.clone(), Arc::from(*bytes));
    }
    let pack_addr = Address::from_blake3_hash(pack_hasher.finalize());
    let pack_stem = format!("pack-{}", pack_addr.hex());
    let idx_path = self.packs_dir.join(format!("{pack_stem}.ixidx"));
    let pack_path = self.packs_dir.join(format!("{pack_stem}.ixpack"));

    if idx_path.exists() && pack_path.exists() {
      self.reload_packs()?;
      return Ok((pack_addr, sorted.len()));
    }

    let seq = WRITE_SEQ.fetch_add(1, Ordering::Relaxed);
    let pid = std::process::id();
    let tmp_pack = self.packs_dir.join(format!("{pack_stem}.ixpack.tmp.{pid}.{seq}"));
    let tmp_idx = self.packs_dir.join(format!("{pack_stem}.ixidx.tmp.{pid}.{seq}"));

    // 1. Write `.ixpack` (8-byte header + 8-byte-aligned object payloads).
    let mut descriptors: Vec<(u64, u32, u32)> = Vec::with_capacity(sorted.len());
    {
      let mut pack_out = io::BufWriter::new(File::create(&tmp_pack)?);
      pack_out.write_all(&PACK_MAGIC)?;
      let mut offset: u64 = 8;
      for (_addr, bytes, kind) in &sorted {
        let len_u32 = u32::try_from(bytes.len()).map_err(|_| {
          io::Error::new(io::ErrorKind::InvalidInput, "object exceeds 4 GiB")
        })?;
        let flags = u32::from(*kind as u8) << 8;
        descriptors.push((offset, len_u32, flags));
        pack_out.write_all(bytes)?;
        offset += u64::from(len_u32);
        let pad = (8 - (offset % 8)) % 8;
        if pad > 0 {
          const ZEROS: [u8; 8] = [0u8; 8];
          let pad_usize = usize::try_from(pad).unwrap_or(0);
          pack_out.write_all(&ZEROS[..pad_usize])?;
          offset += pad;
        }
      }
      pack_out.flush()?;
    }

    // 2. Build 256-entry fan-out table + sorted keys + entry descriptors for `.ixidx`.
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
      let mut idx_out = io::BufWriter::new(File::create(&tmp_idx)?);
      idx_out.write_all(&IDX_MAGIC)?;
      idx_out.write_all(&(count as u64).to_le_bytes())?;
      for f in &fanout {
        idx_out.write_all(&f.to_le_bytes())?;
      }
      for (addr, _, _) in &sorted {
        idx_out.write_all(addr.as_bytes())?;
      }
      for (off, len, flags) in &descriptors {
        idx_out.write_all(&off.to_le_bytes())?;
        idx_out.write_all(&len.to_le_bytes())?;
        idx_out.write_all(&flags.to_le_bytes())?;
      }
      idx_out.flush()?;
    }

    // Publish `.ixpack` first, then `.ixidx` so readers scanning `.ixidx`
    // always see a complete `.ixpack`.
    fs::rename(&tmp_pack, &pack_path)?;
    fs::rename(&tmp_idx, &idx_path)?;

    self.reload_packs()?;
    Ok((pack_addr, count))
  }

  /// Compact all loose objects in `objects/<aa>/*` into a single `.ixpack` + `.ixidx`
  /// and unlink the loose files once the pack is mapped.
  /// Returns `(num_compacted_objects, pack_bytes)`.
  pub fn compact(&self) -> StoreResult<(usize, u64)> {
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
    let (_pack_addr, count) = self.write_pack(refs)?;

    // Now that the pack is durably published and mapped, unlink the loose files.
    for (_addr, path) in &loose_paths {
      let _ = fs::remove_file(path);
    }
    Ok((count, total_bytes))
  }

  /// Compute current store statistics across hot cache, mapped packs, and loose shards.
  pub fn stats(&self) -> StoreResult<StoreStats> {
    self.reload_packs()?;
    let (pack_count, packed_objects, total_pack_bytes) = {
      let packs = self.packs.read().expect("packs lock poisoned");
      let p_count = packs.len();
      let p_objs: usize = packs.iter().map(|p| p.count).sum();
      let p_bytes: u64 = packs.iter().map(|p| p.pack_mmap.len() as u64).sum();
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
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn test_loose_and_pack_roundtrip() {
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

    // Compact loose files into an mmap packfile
    let (compacted, _) = store.compact().expect("compact");
    assert_eq!(compacted, 2);
    assert!(!store.loose_path(&a1).exists());
    assert!(!store.loose_path(&a2).exists());

    // Clear hot cache to force reading from the memory-mapped `.ixpack`
    store.hot.clear();
    assert!(store.contains(&a1));
    assert_eq!(store.read_verified(&a1).expect("read a1 from pack"), b"alpha");
    assert_eq!(store.read_verified(&a2).expect("read a2 from pack"), b"beta");

    let st = store.stats().expect("stats");
    assert_eq!(st.pack_count, 1);
    assert_eq!(st.packed_objects, 2);
    assert_eq!(st.loose_objects, 0);

    let _ = fs::remove_dir_all(&tmp);
  }
}
