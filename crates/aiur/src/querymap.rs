use std::sync::atomic::{AtomicU64, AtomicUsize, Ordering};
use std::sync::{Mutex, OnceLock};

use multi_stark::p3_field::{PrimeCharacteristicRing, PrimeField64};

use crate::G;

/// Immutable view of one query entry.
#[derive(Clone, Copy)]
pub struct QueryRef<'a> {
  pub output: &'a [G],
  pub multiplicity: G,
}

/// Mutable view of one query entry: the output is fixed at insertion,
/// only the multiplicity is bumped on memo hits.
pub struct QueryRefMut<'a> {
  pub output: &'a [G],
  pub multiplicity: &'a AtomicU64,
}

/// Key hash, with the LOW BIT FORCED to 1: the stored hash word doubles
/// as the entry's COMPLETION MARKER (zero = mmap-fresh, unwritten), so
/// no legitimate hash may be 0. Costs one bit of hash quality; every
/// consumer (stripes, tables, probe-cache tags) sees the same marked
/// value, so bucket selection stays consistent across table growth.
fn hash_g_slice(key: &[G]) -> u64 {
  use std::hash::Hasher;
  let mut h = rustc_hash::FxHasher::default();
  for g in key {
    h.write_u64(g.as_canonical_u64());
  }
  h.finish() | 1
}

/// Entries per storage segment (2^20). Segments are fixed-size, so growth
/// never reallocates or copies: appending past a segment boundary just
/// allocates the next segment. This removes the O(len) memmove of a growing
/// `Vec` AND its transient 2x memory spike — on kernel-heavy executions the
/// arenas reach tens of GB, where a doubling copy is both seconds of pure
/// memmove and the difference between fitting in RAM and OOM. Capacity is
/// only reserved virtual address space; physical pages are committed on
/// first touch, so idle circuits stay tiny.
const SEG_BITS: usize = 20;
const SEG_ENTRIES: usize = 1 << SEG_BITS;
const SEG_MASK: usize = SEG_ENTRIES - 1;

/// Segment-slot count per arena: bounds entries at 2^32, matching the
/// `u32` entry indices the hash tables store. Slots are `AtomicPtr`s so
/// readers walk arenas lock-free while a writer publishes a new segment.
const MAX_SEGS: usize = 1 << (32 - SEG_BITS);

/// Hash-table stripes per map: probes and inserts lock only their
/// stripe, so concurrent executors sharing one record contend only on
/// same-stripe keys. The stripe id comes from a multiplicative scramble
/// of the hash — hashbrown consumes the LOW bits for bucket selection
/// and the TOP 7 for its control bytes, so a stripe keyed on any fixed
/// bit range would leave those bits constant within its table and
/// collapse probe filtering.
const STRIPES: usize = 512;

/// Pads a field to TWO cachelines (128 B): the map's `len` is
/// fetch_add'd by EVERY insert; unpadded it shares cachelines with the read-hottest fields
/// there are — the arena pointers and strides every probe on every
/// thread dereferences — so each insert invalidated the map's own read
/// path box-wide (and the neighboring map's in the record's Vec). 128
/// rather than 64 because x86_64's adjacent-line prefetcher pulls line
/// PAIRS, so 64 B padding still lets a store drag the neighboring line
/// out of other cores' caches (crossbeam-utils does the same).
#[repr(align(128))]
struct CachePadded<T>(T);

/// Per-thread positive probe cache: direct-mapped `tag -> entry index`,
/// where the tag mixes the key hash with the map's address so one cache
/// serves every map. The shared hash tables' bucket arrays are
/// perpetually write-shared (uniform-hash inserts dirty the lines every
/// reader traverses), so repeat hits pay coherence misses on the walk;
/// a cache hit skips the bucket walk AND the stripe lock entirely,
/// touching only the immutable entry arena. Correctness needs no
/// pending check and survives map drops: the cache holds no pointers,
/// only completed entries are inserted, completion is permanent, and
/// every use re-validates `idx < len` plus a full key compare against
/// the live map — within a map, dedup makes key -> index unique, so a
/// validated index IS the entry.
const PROBE_CACHE_BITS: u32 = 21;
const PROBE_CACHE_SLOTS: usize = 1 << PROBE_CACHE_BITS;

#[derive(Clone, Copy)]
struct ProbeCacheSlot {
  tag: u64,
  idx: u32,
}

thread_local! {
  static PROBE_CACHE: std::cell::RefCell<Option<Box<[ProbeCacheSlot]>>> =
    const { std::cell::RefCell::new(None) };
}

#[inline]
fn probe_cache_slot_of(tag: u64) -> usize {
  usize::try_from(tag >> (64 - PROBE_CACHE_BITS)).expect("cache bits")
}

#[inline]
fn probe_cache_get(tag: u64) -> Option<usize> {
  PROBE_CACHE.with(|c| {
    let c = c.borrow();
    let cache = c.as_ref()?;
    let slot = cache[probe_cache_slot_of(tag)];
    (slot.tag == tag && slot.idx != u32::MAX).then_some(slot.idx as usize)
  })
}

#[inline]
fn probe_cache_put(tag: u64, idx: usize) {
  let Ok(idx) = u32::try_from(idx) else {
    return;
  };
  PROBE_CACHE.with(|c| {
    let mut c = c.borrow_mut();
    let cache = c.get_or_insert_with(|| {
      vec![ProbeCacheSlot { tag: 0, idx: u32::MAX }; PROBE_CACHE_SLOTS]
        .into_boxed_slice()
    });
    cache[probe_cache_slot_of(tag)] = ProbeCacheSlot { tag, idx };
  });
}

#[inline]
fn stripe_of(hash: u64) -> usize {
  usize::try_from(
    hash.wrapping_mul(0x9E37_79B9_7F4A_7C15) >> (64 - STRIPES.trailing_zeros()),
  )
  .expect("stripe bits")
}

/// Bit-preserving G <-> u64 views. `G` is `repr(transparent)` over
/// `u64` (compile-checked below), and the arenas store G's EXACT bits:
/// round-tripping through these helpers is the identity, so lazily
/// reduced field representations survive storage unchanged.
const _: () = assert!(
  size_of::<G>() == 8 && align_of::<G>() == 8,
  "arena cells assume 8-byte G"
);

#[inline]
pub(crate) fn g_bits(g: G) -> u64 {
  // SAFETY: repr(transparent) over u64, asserted above.
  unsafe { std::mem::transmute::<G, u64>(g) }
}

#[inline]
pub(crate) fn g_from_bits(b: u64) -> G {
  // SAFETY: repr(transparent) over u64; every bit pattern the arenas
  // hold was produced by `g_bits` of a live G.
  unsafe { std::mem::transmute::<u64, G>(b) }
}

/// One anonymous mapping of u64 cells — the only mmap in the record,
/// and deliberately PLAIN: default 4 KiB paging, no hugepage advice,
/// no populate, no collapse. Measured (2026-08-16, same-hour A/B on
/// init/initstd/lean): 2 MiB backing saved only ~8-9% user time at
/// every scale — the per-thread probe cache absorbs most of the TLB
/// pressure — while every scheme
/// for OBTAINING 2 MiB pages costs more than that: fault-time THP
/// degrades ~1.5x as the box fragments (drift), populate+collapse at
/// segment creation serialized workers behind the OnceLock for ~2x
/// wall, and a reserved hugetlb pool taxes prover RAM and needs boot
/// configuration. Plain 4 KiB paging is within ~10% of the best huge
/// number ever recorded here, identical on every box, and immune to
/// machine aging by having nothing to age.
///
/// All access goes through two views: [`Self::cells`] (atomic, for
/// anything ever mutated or not yet published) and [`Self::frozen`]
/// (plain `&[G]`, ONLY for publish-frozen cells — the write-before-
/// publish discipline means a published key/output cell is never
/// stored again, so the plain view cannot race).
pub(crate) struct Segment {
  map: memmap2::MmapMut,
  cells: usize,
}

impl Segment {
  pub(crate) fn new(cells: usize) -> Self {
    assert!(cells > 0, "segment must be non-empty");
    let map = memmap2::MmapOptions::new()
      .len(cells * 8)
      .map_anon()
      .expect("arena mmap failed");
    Self { map, cells }
  }

  /// The cells as atomics — the sole mutable view. SAFETY: the mapping
  /// is owned by `self` and lives for the borrow, is page-aligned, and
  /// `AtomicU64` has `u64`'s size/alignment; every mutation of these
  /// bytes goes through this view.
  #[inline]
  pub(crate) fn cells(&self) -> &[AtomicU64] {
    unsafe {
      std::slice::from_raw_parts(self.map.as_ptr().cast(), self.cells)
    }
  }

  /// Plain `&[G]` view of PUBLISH-FROZEN cells. SAFETY: sound only for
  /// ranges the caller obtained through publication (a table hit, a
  /// completion marker, or seal-time quiescence) — frozen cells are
  /// never stored again, so no write can race this view, and disjoint
  /// cells of the same mapping may be atomically written concurrently.
  #[inline]
  pub(crate) fn frozen(&self, start: usize, len: usize) -> &[G] {
    debug_assert!(start + len <= self.cells);
    unsafe {
      std::slice::from_raw_parts(self.map.as_ptr().cast::<G>().add(start), len)
    }
  }

  /// Store `vals`' bits at `start` (Relaxed: publication ordering is
  /// the caller's marker/lock, not these stores).
  pub(crate) fn write_g(&self, start: usize, vals: &[G]) {
    let cells = &self.cells()[start..start + vals.len()];
    for (c, v) in cells.iter().zip(vals) {
      c.store(g_bits(*v), Ordering::Relaxed);
    }
  }
}

/// Append-only segmented arena of fixed-stride entries. Entry `i` lives
/// at segment `i >> SEG_BITS`, offset `(i & SEG_MASK) * stride` — no
/// entry ever straddles a segment. Slots are `OnceLock`s: readers reach
/// published segments lock-free, and racing first-touch writers are
/// serialized by `get_or_init`, so exactly one mapping is ever created
/// per slot.
///
/// Slot 0 is INLINE and the remaining directory is lazy: almost every
/// map never outgrows one segment (2^20 entries), and a record holds
/// three arenas for each of ~800 maps, so an eager 4096-slot directory
/// per arena cost ~300 MiB of metadata on every fresh record — paid
/// again per fine-segment cut and per shard. The 4095 tail slots
/// materialize on the first touch of segment 1; the directory's
/// `OnceLock` publication (Acquire on read) keeps every access
/// lock-free after that.
struct SegArena {
  seg0: OnceLock<Segment>,
  rest: OnceLock<Box<[OnceLock<Segment>]>>,
}

impl SegArena {
  fn new() -> Self {
    Self { seg0: OnceLock::new(), rest: OnceLock::new() }
  }

  /// Slot `s`'s lock, if its directory exists yet.
  #[inline]
  fn slot(&self, s: usize) -> Option<&OnceLock<Segment>> {
    if s == 0 {
      Some(&self.seg0)
    } else {
      self.rest.get().map(|r| &r[s - 1])
    }
  }

  #[inline]
  fn seg(&self, s: usize) -> &Segment {
    self
      .slot(s)
      .and_then(OnceLock::get)
      .expect("read of unpublished segment")
  }

  fn ensure_seg(&self, s: usize, stride: usize) -> &Segment {
    let lock = if s == 0 {
      &self.seg0
    } else {
      &self.rest.get_or_init(|| {
        let mut v = Vec::with_capacity(MAX_SEGS - 1);
        v.resize_with(MAX_SEGS - 1, OnceLock::new);
        v.into_boxed_slice()
      })[s - 1]
    };
    lock.get_or_init(|| Segment::new(SEG_ENTRIES * stride))
  }

  /// Entry `i`'s publish-frozen G view (see [`Segment::frozen`]).
  #[inline]
  fn at(&self, i: usize, stride: usize) -> &[G] {
    if stride == 0 {
      return &[];
    }
    self.seg(i >> SEG_BITS).frozen((i & SEG_MASK) * stride, stride)
  }

  /// Write entry `i`. Caller owns the reserved slot (index reserved,
  /// not yet published).
  fn write(&self, i: usize, stride: usize, vals: &[G]) {
    debug_assert_eq!(vals.len(), stride);
    if stride == 0 {
      return;
    }
    self
      .ensure_seg(i >> SEG_BITS, stride)
      .write_g((i & SEG_MASK) * stride, vals);
  }

  /// Write a sub-range of entry `i` at `off`. Sound for the slot's
  /// owner (reservation-then-publish, as before). The segment is
  /// ensured even for an EMPTY write: publishing an index promises
  /// readers a dereferenceable entry slice.
  fn write_at(&self, i: usize, stride: usize, off: usize, vals: &[G]) {
    debug_assert!(off + vals.len() <= stride);
    if stride == 0 {
      return;
    }
    self
      .ensure_seg(i >> SEG_BITS, stride)
      .write_g((i & SEG_MASK) * stride + off, vals);
  }

  /// Atomic cell `off` of entry `i` — for the mutated words
  /// (multiplicities) and the completion marker.
  #[inline]
  fn cell(&self, i: usize, stride: usize, off: usize) -> &AtomicU64 {
    &self.seg(i >> SEG_BITS).cells()[(i & SEG_MASK) * stride + off]
  }

  /// [`Self::cell`] that creates the segment first (marker stores land
  /// before publication, possibly on a fresh segment).
  #[inline]
  fn cell_ensured(&self, i: usize, stride: usize) -> &AtomicU64 {
    &self.ensure_seg(i >> SEG_BITS, stride).cells()[(i & SEG_MASK) * stride]
  }

  /// Stride-1 cell `i` if its segment exists yet; `None` means no
  /// entry at `i` can be complete. `i` may be arbitrary attacker-ish
  /// input (an unbound memory pointer is any field element) — bounds
  /// are checked before indexing.
  #[inline]
  fn try_cell(&self, i: usize) -> Option<&AtomicU64> {
    if i >> SEG_BITS >= MAX_SEGS {
      return None;
    }
    self
      .slot(i >> SEG_BITS)?
      .get()
      .map(|s| &s.cells()[i & SEG_MASK])
  }
}

/// Append-only query store with a striped hash index, shareable across
/// executor threads.
///
/// Functionally the insertion-ordered map `args -> (output, multiplicity)`
/// it replaces (`FxIndexMap<Vec<G>, QueryResult>`) — but every circuit has
/// a FIXED key arity and output width, so keys and outputs live in flat
/// segmented `G` arenas addressed by entry index, and the hash tables hold
/// only `u32` indices. This cuts per-entry overhead from ~130 B (two heap
/// `Vec`s + IndexMap bucket + allocator metadata) to the raw field
/// elements plus ~21 B of index + stored hash. The record IS the proof
/// witness, so entries cannot be dropped — only stored compactly; on
/// kernel-heavy executions it is the dominant RAM consumer (billions of
/// entries). Segmented storage keeps growth copy-free (no doubling
/// memmove, no transient 2x RSS), stored hashes make table growth a cheap
/// sequential pass, and segments are plain 4 KiB anonymous mappings
/// (see [`Segment`]).
///
/// Entry index == insertion order; memory circuits use it as the pointer
/// value, so a stored tuple's pointer IS its entry index.
///
/// # Concurrency
///
/// The map is safely shareable (`&self` ops) between executor threads
/// filling one record:
///
/// - Probes lock only their key's stripe; the whole miss path (probe +
///   arena append + table publish) holds the stripe lock, so two threads
///   racing the same key resolve into one insert and one hit.
/// - Entry indices are reserved by a lock-free `fetch_add` on `len`;
///   slot data is written in parallel (one owner per slot) and the
///   entry's stored hash word — forced nonzero — is its COMPLETION
///   MARKER, Release-stored last. `i < len` alone therefore proves
///   only reservation; completeness is the marker, and raw-index
///   readers (memory loads) check it. Table- and cache-mediated
///   readers only ever see marked entries.
/// - Multiplicity bumps are relaxed atomic adds on the `G` slots (a
///   canonical multiplicity stays far below the field modulus, so `u64`
///   addition IS field addition here).
/// - Readers reach entries only through published state (a table hit
///   under the stripe lock, or an index below the `Acquire`-loaded
///   `len`), which orders them after the entry's arena writes.
///
/// The unique-entry SET a concurrent execution produces is
/// interleaving-independent (memoization is confluent); multiplicities
/// are exact only under exclusive (`&mut`) use — the parallel scan does
/// not read them.
pub struct QueryMap {
  key_stride: usize,
  out_stride: usize,
  /// Per-entry `[key | outs]`, contiguous. The two reads a hit needs
  /// (key compare, output copy) land on adjacent lines instead of two
  /// scattered arenas — at billions of random probes the extra
  /// dependent DRAM fetch per hit was measurable. Multiplicities stay
  /// in their own arena ON PURPOSE: they are the only mutated word, and
  /// isolating them keeps bump RMWs from dirtying the immutable entry
  /// lines other threads have cached.
  entries: SegArena,
  mults: SegArena,
  /// Per-entry key hashes, kept so hash-table growth re-inserts from
  /// stored hashes instead of re-hashing keys from the arena — without
  /// them, each doubling of a multi-GB map is a full sequential
  /// re-hash pass, log-many times.
  hashes: SegArena,
  /// Unique-entry count BY RESERVATION: fetch_add'd at insert, before
  /// the slot's data lands. Entries below `len` are complete except
  /// the few whose owners are mid-write; completeness of entry `i` is
  /// its nonzero hash marker, never `i < len`. At quiescence (seal —
  /// workers drained) reservation and completion coincide.
  len: CachePadded<AtomicUsize>,
  stripes: Box<[Mutex<hashbrown::HashTable<u32>>]>,
  /// Never-reused construction salt for probe-cache tags (see
  /// [`Self::cache_tag`]).
  salt: u64,
}

/// Monotone source for per-map construction salts. Map ADDRESSES recur
/// across record replacements (drop/new cycles land in the same
/// allocator size classes), while the thread-local probe cache outlives
/// records on long-lived threads — an address-keyed tag could validate a
/// stale index against a NEW map's PENDING entry (its key is written at
/// reserve, its output is not) and read an unwritten output. A salt that
/// is never reused makes cross-record tag aliasing structurally
/// impossible.
static MAP_SALT: AtomicU64 = AtomicU64::new(1);

impl QueryMap {
  pub fn new(key_stride: usize, out_stride: usize) -> Self {
    let mut stripes = Vec::with_capacity(STRIPES);
    stripes.resize_with(STRIPES, || Mutex::new(hashbrown::HashTable::new()));
    Self {
      key_stride,
      out_stride,
      entries: SegArena::new(),
      mults: SegArena::new(),
      hashes: SegArena::new(),
      len: CachePadded(AtomicUsize::new(0)),
      stripes: stripes.into_boxed_slice(),
      salt: MAP_SALT.fetch_add(1, Ordering::Relaxed),
    }
  }

  /// Overwrite entry `i`'s multiplicity — the seal-time application of
  /// DERIVED counts (`trace::derive_multiplicities`). The concurrent
  /// set path never writes multiplicities during execution.
  /// Bump entry `i`'s multiplicity by one, returning the PREVIOUS
  /// count — the seal-time derivation walk counting directly into the
  /// record (counts stay far below the modulus, so `u64` addition on
  /// the cell is field addition).
  pub(crate) fn mult_add(&self, i: usize) -> u64 {
    self.mult_atomic(i).fetch_add(1, Ordering::Relaxed)
  }

  /// Whether entry `i`'s multiplicity is zero — the witness builder's
  /// live-row scan, without materializing the entry.
  pub(crate) fn mult_is_zero(&self, i: usize) -> bool {
    self.mult_atomic(i).load(Ordering::Relaxed) == 0
  }

  #[inline]
  pub fn len(&self) -> usize {
    self.len.0.load(Ordering::Acquire)
  }

  #[inline]
  pub fn is_empty(&self) -> bool {
    self.len() == 0
  }

  #[inline]
  fn out_stride(&self) -> usize {
    self.out_stride
  }

  #[inline]
  fn entry_stride(&self) -> usize {
    self.key_stride + self.out_stride
  }

  #[inline]
  fn key_at(&self, i: usize) -> &[G] {
    &self.entries.at(i, self.entry_stride())[..self.key_stride]
  }

  #[inline]
  fn outs_at(&self, i: usize) -> &[G] {
    &self.entries.at(i, self.entry_stride())[self.key_stride..]
  }

  /// Mix the key hash with this map's never-reused construction salt:
  /// one thread-local cache serves every map, the mix keeps different
  /// maps' identical hashes from aliasing, and the salt (unlike the map
  /// ADDRESS it replaced) cannot recur across record replacements — see
  /// [`MAP_SALT`] for why address-keyed tags were a live corruption
  /// window.
  #[inline]
  fn cache_tag(&self, hash: u64) -> u64 {
    self.salt.wrapping_mul(0x9E37_79B9_7F4A_7C15).rotate_left(32) ^ hash
  }

  /// Atomic view of entry `i`'s multiplicity slot. `G` is
  /// `repr(transparent)` over `u64` and multiplicities are canonical,
  /// so relaxed `u64` adds implement field addition exactly. The
  /// pointer is derived through the arena's raw allocation pointer
  /// (`at_ptr`), NOT through a shared reference — writes through a
  /// `&`-derived pointer would carry read-only provenance.
  #[inline]
  fn mult_atomic(&self, i: usize) -> &AtomicU64 {
    self.mults.cell(i, 1, 0)
  }

  /// Total retained field elements (keys + outputs); used by the
  /// `IX_AIUR_QUERY_STATS` RAM-attribution dump.
  pub fn retained_elems(&self) -> usize {
    self.len() * (self.key_stride + self.out_stride())
  }

  /// Visit the stored 64-bit hash of every unique entry, in insertion
  /// order. The hashes are already computed and resident (they back
  /// table growth), so this is a pure sequential read — the scanner's
  /// union-pricing sketches are built from these without rehashing.
  pub fn for_each_hash(&self, mut f: impl FnMut(u64)) {
    for i in 0..self.len() {
      f(self.hash_at(i));
    }
  }

  /// Entry `i`'s stored hash word. Relaxed: callers reach `i` through
  /// publication (table membership or seal-time quiescence), which
  /// already ordered the marker store.
  #[inline]
  fn hash_at(&self, i: usize) -> u64 {
    self.hashes.cell(i, 1, 0).load(Ordering::Relaxed)
  }

  /// Probe under the key's stripe lock; `Some(index)` on hit.
  fn probe_index(&self, key: &[G]) -> Option<usize> {
    debug_assert_eq!(key.len(), self.key_stride);
    let hash = hash_g_slice(key);
    let table = self.stripes[stripe_of(hash)].lock().unwrap();
    table.find(hash, |&i| self.key_at(i as usize) == key).map(|&i| i as usize)
  }

  pub fn get_index_of(&self, key: &[G]) -> Option<usize> {
    self.probe_index(key)
  }

  pub fn get(&self, key: &[G]) -> Option<QueryRef<'_>> {
    let i = self.probe_index(key)?;
    Some(QueryRef {
      output: self.outs_at(i),
      multiplicity: g_from_bits(self.mult_atomic(i).load(Ordering::Relaxed)),
    })
  }

  /// A hit's entry index alongside its output. The row walk needs both
  /// — the output to continue the row, the index to charge the push —
  /// and resolving them separately probes the same multi-GB map twice
  /// per call.
  pub fn get_indexed(&self, key: &[G]) -> Option<(usize, &[G])> {
    let i = self.probe_index(key)?;
    Some((i, self.outs_at(i)))
  }

  /// A hit's output plus its multiplicity CELL. Takes `&self`: the only
  /// mutable thing it hands back is the atomic counter, and the record
  /// is shared, so exclusive access was never what made this sound.
  pub fn get_mut(&self, key: &[G]) -> Option<QueryRefMut<'_>> {
    let i = self.probe_index(key)?;
    Some(QueryRefMut {
      output: self.outs_at(i),
      multiplicity: self.mult_atomic(i),
    })
  }

  /// Concurrent memo probe: a hit returns the cached output (bumping
  /// the runtime multiplicity only when `bump` — the single-threaded
  /// reference interpreter's accounting; the concurrent set path always
  /// passes `false`); a miss returns `None` and the caller executes the
  /// body and inserts the result. There is NO reservation and NO
  /// waiting: concurrent same-key racers both execute and dedup at
  /// insert (first publish wins), which is sound because the witness's
  /// multiplicities are DERIVED from the unique-query set at seal
  /// (`trace::derive_multiplicities`), never accumulated from
  /// execution — duplicate speculative execution costs wall clock only
  /// and cannot unbalance anything.
  pub fn probe_bump(&self, key: &[G], bump: bool) -> Option<&[G]> {
    debug_assert_eq!(key.len(), self.key_stride);
    let hash = hash_g_slice(key);
    let tag = self.cache_tag(hash);
    if let Some(i) = probe_cache_get(tag)
      && i < self.len()
      && self.key_at(i) == key
    {
      if bump {
        self.mult_atomic(i).fetch_add(1, Ordering::Relaxed);
      }
      return Some(self.outs_at(i));
    }
    let i = {
      let table = self.stripes[stripe_of(hash)].lock().unwrap();
      match table.find(hash, |&i| self.key_at(i as usize) == key) {
        Some(&i) => i as usize,
        None => return None,
      }
    };
    probe_cache_put(tag, i);
    if bump {
      self.mult_atomic(i).fetch_add(1, Ordering::Relaxed);
    }
    Some(self.outs_at(i))
  }

  /// Lock-free entry-index reservation: bumps `len` and returns the
  /// slot, which the caller owns exclusively until its marker store.
  #[inline]
  fn reserve_index(&self) -> usize {
    let i = self.len.0.fetch_add(1, Ordering::Relaxed);
    assert!(
      i < MAX_SEGS * SEG_ENTRIES,
      "QueryMap full (2^32 entries; key_stride {}, out_stride {})",
      self.key_stride,
      self.out_stride,
    );
    i
  }

  /// Publish entry `i` complete: Release-store its (nonzero) hash word,
  /// ordering every slot write before any reader that Acquires it.
  #[inline]
  fn mark_complete(&self, i: usize, hash: u64) {
    debug_assert_ne!(hash, 0);
    self.hashes.cell_ensured(i, 1).store(hash, Ordering::Release);
  }

  /// Entry `i`'s completion marker: its stored hash word, 0 while the
  /// owner is still writing (or its segment does not exist yet).
  #[inline]
  fn complete_hash(&self, i: usize) -> u64 {
    self.hashes.try_cell(i).map_or(0, |c| c.load(Ordering::Acquire))
  }

  /// Insert holding the stripe lock for the WHOLE path, so a same-key
  /// race resolves into ONE published entry (first insert wins; the
  /// loser's insert is the memo hit it raced — identical key and, by
  /// determinism, identical output). Entries publish COMPLETE in a
  /// single step: key, output, multiplicity, and hash are all written
  /// before the index enters the table, so any found entry is readable.
  /// `mult`/`on_existing_bump` carry the single-threaded reference
  /// interpreter's runtime accounting; the concurrent set path passes
  /// zero/false and multiplicities are derived at seal instead.
  /// Returns the entry index.
  fn insert_inner(
    &self,
    key: &[G],
    output: &[G],
    mult: G,
    on_existing_bump: bool,
  ) -> usize {
    debug_assert_eq!(key.len(), self.key_stride);
    let hash = hash_g_slice(key);
    let mut table = self.stripes[stripe_of(hash)].lock().unwrap();
    if let Some(&i) = table.find(hash, |&i| self.key_at(i as usize) == key) {
      let i = i as usize;
      drop(table);
      if on_existing_bump && mult != G::ZERO {
        self.mult_atomic(i).fetch_add(1, Ordering::Relaxed);
      }
      probe_cache_put(self.cache_tag(hash), i);
      return i;
    }
    assert_eq!(
      output.len(),
      self.out_stride,
      "insert output arity != map out stride"
    );
    let i = self.reserve_index();
    self.entries.write_at(i, self.entry_stride(), 0, key);
    self.entries.write_at(i, self.entry_stride(), self.key_stride, output);
    self.mults.write(i, 1, &[mult]);
    self.mark_complete(i, hash);
    let i32 = u32::try_from(i).expect("entry index fits u32");
    table.insert_unique(hash, i32, |&j| self.hash_at(j as usize));
    probe_cache_put(self.cache_tag(hash), i);
    i
  }


  pub fn insert(&mut self, key: &[G], output: &[G], multiplicity: G) {
    self.insert_inner(key, output, multiplicity, true);
  }

  /// Concurrent function-return insert: new entries start at
  /// multiplicity 1 (0 when unconstrained); a concurrent duplicate
  /// becomes a bump, exactly the hit it raced with.
  pub fn insert_cc(&self, key: &[G], output: &[G], constrained: bool) {
    self.insert_inner(key, output, G::from_bool(constrained), true);
  }

  /// Concurrent content-addressed store (memory circuits): the pointer
  /// is the entry index of the value's FIRST insertion — hits bump the
  /// multiplicity and return the existing pointer.
  pub fn store_cc(&self, values: &[G], constrained: bool) -> G {
    debug_assert_eq!(values.len(), self.key_stride);
    let hash = hash_g_slice(values);
    let tag = self.cache_tag(hash);
    if let Some(i) = probe_cache_get(tag)
      && i < self.len()
      && self.key_at(i) == values
    {
      // Memory entries complete inside their inserting store, so a
      // validated cached index is always readable.
      if constrained {
        self.mult_atomic(i).fetch_add(1, Ordering::Relaxed);
      }
      return self.outs_at(i)[0];
    }
    let mut table = self.stripes[stripe_of(hash)].lock().unwrap();
    if let Some(&i) = table.find(hash, |&i| self.key_at(i as usize) == values) {
      probe_cache_put(tag, i as usize);
      if constrained {
        self.mult_atomic(i as usize).fetch_add(1, Ordering::Relaxed);
      }
      return self.outs_at(i as usize)[0];
    }
    assert_eq!(self.out_stride, 1, "memory map out stride must be 1");
    let i = self.reserve_index();
    let ptr = G::from_usize(i);
    self.entries.write_at(i, self.entry_stride(), 0, values);
    self.entries.write_at(i, self.entry_stride(), self.key_stride, &[ptr]);
    self.mults.write(i, 1, &[G::from_bool(constrained)]);
    self.mark_complete(i, hash);
    let i32 = u32::try_from(i).expect("entry index fits u32");
    table.insert_unique(hash, i32, |&j| self.hash_at(j as usize));
    probe_cache_put(tag, i);
    ptr
  }

  /// Concurrent memory load: entry `i`'s stored value, atomically
  /// bumping its multiplicity when `bump`. `None` for an unpublished
  /// index (an unbound pointer).
  pub fn load_bump(&self, i: usize, bump: bool) -> Option<&[G]> {
    // `i < len` proves only reservation; an unbound pointer must fail
    // and a mid-write slot must not be read. The marker proves both
    // absence and completeness, and Acquire-orders the slot's data.
    if self.complete_hash(i) == 0 {
      return None;
    }
    if bump {
      self.mult_atomic(i).fetch_add(1, Ordering::Relaxed);
    }
    Some(self.key_at(i))
  }

  /// Entry at insertion index `i`: the key slice plus a mutable handle on
  /// the multiplicity (memory `Load` bumps the pointed-to row's count).
  pub fn get_index_mut(&mut self, i: usize) -> Option<(&[G], &AtomicU64)> {
    if i >= self.len() {
      return None;
    }
    Some((self.key_at(i), self.mult_atomic(i)))
  }

  /// QUIESCENT-ONLY raw read (seal-time trace building, single-thread
  /// tools): `len` counts RESERVED indices, so while workers are
  /// inserting, an `i < len` entry may not be published yet — reading
  /// it races the writer. Concurrent readers must use
  /// [`Self::get_index_complete`].
  pub fn get_index(&self, i: usize) -> Option<(&[G], QueryRef<'_>)> {
    if i >= self.len() {
      return None;
    }
    Some((
      self.key_at(i),
      QueryRef {
        output: self.outs_at(i),
        multiplicity: g_from_bits(self.mult_atomic(i).load(Ordering::Relaxed)),
      },
    ))
  }

  /// Completion-gated entry read, safe WHILE WORKERS ARE WRITING:
  /// `None` until the entry's stored hash — its completion marker,
  /// Release-stored last — is visible (Acquire), so the key/output
  /// cells it covers are publish-frozen. The mid-run diagnostic dumps
  /// go through this; anything quiescent can use [`Self::get_index`].
  pub fn get_index_complete(&self, i: usize) -> Option<(&[G], QueryRef<'_>)> {
    if i >= self.len()
      || self.hashes.try_cell(i)?.load(Ordering::Acquire) == 0
    {
      return None;
    }
    self.get_index(i)
  }

  pub fn iter(&self) -> impl Iterator<Item = (&[G], QueryRef<'_>)> {
    (0..self.len()).map(|i| {
      (
        self.key_at(i),
        QueryRef {
          output: self.outs_at(i),
          multiplicity: g_from_bits(self.mult_atomic(i).load(Ordering::Relaxed)),
        },
      )
    })
  }
}
