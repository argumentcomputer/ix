use multi_stark::p3_field::{PrimeCharacteristicRing, PrimeField64};
use std::sync::{
  Arc,
  atomic::{AtomicU64, Ordering},
};

use crate::{G, call_order::RANK_BOUND};

mod storage;
use storage::PackedStore;
pub use storage::{PackedRow, QuerySlice};

/// Immutable view of one query entry.
#[derive(Clone, Copy)]
pub struct QueryRef<'a> {
  pub(crate) output: QuerySlice<'a>,
  pub multiplicity: G,
  pub(crate) rank: u64,
}

/// Mutable view of one query entry: the output is fixed at insertion,
/// only the multiplicity is bumped on memo hits.
pub struct QueryRefMut<'a> {
  pub output: QuerySlice<'a>,
  pub multiplicity: &'a mut G,
}

fn hash_g_slice(key: &[G]) -> u64 {
  use std::hash::Hasher;
  let mut h = rustc_hash::FxHasher::default();
  for g in key {
    h.write_u64(g.as_canonical_u64());
  }
  h.finish()
}

/// Entries per storage segment (2^20). Crossing a segment boundary allocates
/// a new segment without copying older rows. Packed columns may widen by
/// copying the active segment; closed segments retain their original layout.
/// Capacity reserves virtual address space, with physical pages committed
/// on first touch.
const SEG_BITS: usize = 20;
const SEG_ENTRIES: usize = 1 << SEG_BITS;
const SEG_MASK: usize = SEG_ENTRIES - 1;

/// A fixed-capacity append-only buffer mmap'd straight from the kernel,
/// with `MADV_HUGEPAGE` applied BEFORE any page is touched. At billions of
/// entries the query maps are walked by random probes; with 4K pages nearly
/// every probe pays a 4-level page walk on top of the DRAM miss, and 2M
/// pages cut TLB reach pressure by 512x. Going through the global allocator
/// doesn't work here: mimalloc (the process allocator) commits its segments
/// itself, so pages are already faulted at 4K before any post-hoc madvise.
/// Capacity is virtual reservation only — physical pages are committed on
/// first touch, so idle circuits stay tiny. Off Linux this degrades to a
/// plain `Vec`.
struct HugeVec<T: Copy> {
  #[cfg(target_os = "linux")]
  ptr: *mut T,
  #[cfg(target_os = "linux")]
  cap: usize,
  #[cfg(target_os = "linux")]
  len: usize,
  #[cfg(not(target_os = "linux"))]
  inner: Vec<T>,
}

#[cfg(target_os = "linux")]
unsafe impl<T: Copy + Send> Send for HugeVec<T> {}
#[cfg(target_os = "linux")]
unsafe impl<T: Copy + Sync> Sync for HugeVec<T> {}

impl<T: Copy> HugeVec<T> {
  #[cfg(target_os = "linux")]
  fn with_capacity(cap: usize) -> Self {
    assert!(cap > 0, "HugeVec capacity must be positive");
    let bytes = cap.checked_mul(size_of::<T>()).expect("query arena overflow");
    let ptr = unsafe {
      let p = libc::mmap(
        std::ptr::null_mut(),
        bytes,
        libc::PROT_READ | libc::PROT_WRITE,
        libc::MAP_PRIVATE | libc::MAP_ANONYMOUS,
        -1,
        0,
      );
      assert!(p != libc::MAP_FAILED, "HugeVec mmap failed");
      // Advisory only: failure (old kernel, THP disabled) is harmless.
      libc::madvise(p, bytes, libc::MADV_HUGEPAGE);
      p.cast::<T>()
    };
    Self { ptr, cap, len: 0 }
  }

  #[cfg(not(target_os = "linux"))]
  fn with_capacity(cap: usize) -> Self {
    Self { inner: Vec::with_capacity(cap) }
  }

  #[cfg(target_os = "linux")]
  #[inline]
  fn extend_from_slice(&mut self, vals: &[T]) {
    debug_assert!(self.len + vals.len() <= self.cap);
    unsafe {
      std::ptr::copy_nonoverlapping(
        vals.as_ptr(),
        self.ptr.add(self.len),
        vals.len(),
      );
    }
    self.len += vals.len();
  }

  #[cfg(not(target_os = "linux"))]
  #[inline]
  fn extend_from_slice(&mut self, vals: &[T]) {
    self.inner.extend_from_slice(vals);
  }

  #[cfg(target_os = "linux")]
  #[inline]
  fn slice(&self, start: usize, len: usize) -> &[T] {
    debug_assert!(start + len <= self.len);
    unsafe { std::slice::from_raw_parts(self.ptr.add(start), len) }
  }

  #[cfg(not(target_os = "linux"))]
  #[inline]
  fn slice(&self, start: usize, len: usize) -> &[T] {
    &self.inner[start..start + len]
  }

  #[cfg(target_os = "linux")]
  #[inline]
  fn slice_mut(&mut self, start: usize, len: usize) -> &mut [T] {
    debug_assert!(start + len <= self.len);
    unsafe { std::slice::from_raw_parts_mut(self.ptr.add(start), len) }
  }

  #[cfg(not(target_os = "linux"))]
  #[inline]
  fn slice_mut(&mut self, start: usize, len: usize) -> &mut [T] {
    &mut self.inner[start..start + len]
  }
}

#[cfg(target_os = "linux")]
impl<T: Copy> Drop for HugeVec<T> {
  fn drop(&mut self) {
    unsafe {
      libc::munmap(self.ptr.cast(), self.cap * size_of::<T>());
    }
  }
}

/// Append-only segmented arena of fixed-stride `G` entries. Entry `i` lives
/// at segment `i >> SEG_BITS`, offset `(i & SEG_MASK) * stride` — no entry
/// ever straddles a segment.
struct SegStore {
  stride: usize,
  segs: Vec<HugeVec<G>>,
  entries: usize,
}

impl SegStore {
  fn new(stride: usize) -> Self {
    Self { stride, segs: Vec::new(), entries: 0 }
  }

  #[inline]
  fn at(&self, i: usize) -> &[G] {
    if self.stride == 0 {
      return &[];
    }
    let base = (i & SEG_MASK) * self.stride;
    self.segs[i >> SEG_BITS].slice(base, self.stride)
  }

  #[inline]
  fn at_mut(&mut self, i: usize) -> &mut [G] {
    if self.stride == 0 {
      return &mut [];
    }
    let base = (i & SEG_MASK) * self.stride;
    self.segs[i >> SEG_BITS].slice_mut(base, self.stride)
  }

  #[inline]
  fn push(&mut self, vals: &[G]) {
    debug_assert_eq!(vals.len(), self.stride);
    if self.stride != 0 {
      let seg = self.entries >> SEG_BITS;
      if seg == self.segs.len() {
        self.segs.push(HugeVec::with_capacity(SEG_ENTRIES * self.stride));
      }
      self.segs[seg].extend_from_slice(vals);
    }
    self.entries += 1;
  }
}

/// Segmented store of per-entry `u64` key hashes. Keeping the hashes lets
/// hash-table growth re-insert entries without re-hashing every key from the
/// keys arena; table doubling on a multi-GB map used to be a full sequential
/// re-hash pass over the arena, log-many times.
struct SegU64s {
  segs: Vec<HugeVec<u64>>,
  entries: usize,
}

impl SegU64s {
  fn new() -> Self {
    Self { segs: Vec::new(), entries: 0 }
  }

  #[inline]
  fn at(&self, i: usize) -> u64 {
    self.segs[i >> SEG_BITS].slice(i & SEG_MASK, 1)[0]
  }

  fn set(&mut self, i: usize, value: u64) {
    self.segs[i >> SEG_BITS].slice_mut(i & SEG_MASK, 1)[0] = value;
  }

  #[inline]
  fn push(&mut self, h: u64) {
    let seg = self.entries >> SEG_BITS;
    if seg == self.segs.len() {
      self.segs.push(HugeVec::with_capacity(SEG_ENTRIES));
    }
    self.segs[seg].extend_from_slice(&[h]);
    self.entries += 1;
  }
}

/// Shared completion order across function maps. Memory maps omit it.
/// Reverse completion order gives the root rank zero and every constrained
/// callee a strictly greater rank than its caller.
struct CompletionOrder {
  clock: Arc<AtomicU64>,
  times: SegU64s,
}

impl CompletionOrder {
  fn next(&self) -> u64 {
    let time = self.clock.fetch_add(1, Ordering::Relaxed);
    assert!(
      time < RANK_BOUND,
      "function completion count exceeds 48-bit rank bound"
    );
    time
  }

  fn rank(&self, i: usize) -> u64 {
    let last = self.clock.load(Ordering::Relaxed) - 1;
    last - self.times.at(i)
  }
}

/// Append-only query store with a hash index.
///
/// Every circuit has a fixed key arity and output width. Keys and outputs
/// use segmented byte/u32/full-field columns selected from canonical values.
/// Encoding preserves exact field equality; stored hashes accelerate table
/// growth but never replace key comparison. Multiplicities retain full-field
/// storage, and ranked function maps retain their completion timestamps.
///
/// The hash table stores stable u32 row indices. Compressed rows decode into
/// the existing field traces, without retaining another full-width copy.
///
/// Entry index == insertion order; memory circuits use it as the pointer
/// value, mirroring the old `IndexMap::get_index_of` semantics.
pub struct QueryMap {
  /// Output width; inferred on first insert (not statically available in
  /// `FunctionLayout`).
  out_stride_set: bool,
  keys: PackedStore,
  outs: PackedStore,
  mults: SegStore,
  hashes: SegU64s,
  table: hashbrown::HashTable<u32>,
  completion: Option<CompletionOrder>,
}

impl QueryMap {
  pub fn new(key_stride: usize) -> Self {
    Self::with_storage(key_stride, true)
  }

  fn with_storage(key_stride: usize, compact: bool) -> Self {
    Self {
      out_stride_set: false,
      keys: PackedStore::new(key_stride, compact),
      outs: PackedStore::new(0, compact),
      mults: SegStore::new(1),
      hashes: SegU64s::new(),
      table: hashbrown::HashTable::new(),
      completion: None,
    }
  }

  pub(crate) fn new_function(key_stride: usize, clock: Arc<AtomicU64>) -> Self {
    let mut map = Self::new(key_stride);
    map.completion = Some(CompletionOrder { clock, times: SegU64s::new() });
    map
  }

  fn rank_at(&self, i: usize) -> u64 {
    self.completion.as_ref().map_or(0, |order| order.rank(i))
  }

  #[inline]
  pub fn len(&self) -> usize {
    self.mults.entries
  }

  #[inline]
  pub fn is_empty(&self) -> bool {
    self.mults.entries == 0
  }

  /// Logical field elements (keys + outputs), before encoding; used by the
  /// `IX_AIUR_QUERY_STATS` RAM-attribution dump.
  pub fn retained_elems(&self) -> usize {
    self.keys.retained_elems() + self.outs.retained_elems()
  }

  /// Encoded key/output payload, excluding hashes, multiplicities and index.
  pub fn retained_bytes(&self) -> usize {
    self.keys.retained_bytes() + self.outs.retained_bytes()
  }

  /// Number of stored completion timestamps. Certified acyclic functions
  /// and memory maps do not need completion order; generic functions do.
  pub(crate) fn completion_entries(&self) -> usize {
    self.completion.as_ref().map_or(0, |order| order.times.entries)
  }

  pub fn get_index_of(&self, key: &[G]) -> Option<usize> {
    debug_assert_eq!(key.len(), self.keys.stride);
    self.find_hashed(key, hash_g_slice(key))
  }

  fn find_hashed(&self, key: &[G], hash: u64) -> Option<usize> {
    self
      .table
      .find(hash, |&i| self.keys.at(i as usize).matches(key))
      .map(|&i| i as usize)
  }

  pub fn get(&self, key: &[G]) -> Option<QueryRef<'_>> {
    let i = self.get_index_of(key)?;
    Some(QueryRef {
      output: self.outs.at(i),
      multiplicity: self.mults.at(i)[0],
      rank: self.rank_at(i),
    })
  }

  pub fn get_mut(&mut self, key: &[G]) -> Option<QueryRefMut<'_>> {
    let i = self.get_index_of(key)?;
    Some(QueryRefMut {
      output: self.outs.at(i),
      multiplicity: &mut self.mults.at_mut(i)[0],
    })
  }

  /// Multiplicity of entry `i`.
  #[inline]
  pub fn mult_at(&self, i: usize) -> G {
    self.mults.at(i)[0]
  }

  /// Lossless output view of entry `i`.
  #[inline]
  pub fn output_at(&self, i: usize) -> QuerySlice<'_> {
    self.outs.at(i)
  }

  /// Record a constrained memo hit on entry `i`.
  #[inline]
  pub fn bump_multiplicity(&mut self, i: usize) {
    self.mults.at_mut(i)[0] += G::ONE;
  }

  /// Register a function query at `Ctrl::Return`: insert on first
  /// registration and bump on constrained promotion of a cached hint row.
  pub fn finish(&mut self, key: &[G], output: &[G], constrained: bool) {
    if let Some(i) = self.get_index_of(key) {
      // The only ordinary way to execute an already cached function is
      // constrained promotion of an unconstrained hint entry.
      debug_assert!(self.outs.at(i).matches(output));
      if constrained {
        self.bump_multiplicity(i);
        // Promotion executes/promotes children first, so its new completion
        // time must follow them even when the hint entry was inserted early.
        if let Some(order) = &mut self.completion {
          let time = order.next();
          order.times.set(i, time);
        }
      }
    } else {
      self.insert(key, output, G::from_bool(constrained));
    }
  }

  /// Append a new entry. The key must not already be present: call sites
  /// only insert on a confirmed miss, and a same-key re-entrant call
  /// would loop forever before reaching its own insert.
  pub fn insert(&mut self, key: &[G], output: &[G], multiplicity: G) {
    assert_eq!(key.len(), self.keys.stride);
    debug_assert!(self.get_index_of(key).is_none());
    if self.out_stride_set {
      assert_eq!(output.len(), self.outs.stride);
    }
    let hash = hash_g_slice(key);
    let i = u32::try_from(self.mults.entries).expect("query map overflow");
    self.keys.push(key);
    self.outs.push(output);
    self.out_stride_set = true;
    self.mults.push(&[multiplicity]);
    self.hashes.push(hash);
    if let Some(order) = &mut self.completion {
      let time = order.next();
      order.times.push(time);
    }
    let hashes = &self.hashes;
    self.table.insert_unique(hash, i, |&j| hashes.at(j as usize));
  }

  /// Entry at insertion index `i`: the key slice plus a mutable handle on
  /// the multiplicity (memory `Load` bumps the pointed-to row's count).
  pub fn get_index_mut(
    &mut self,
    i: usize,
  ) -> Option<(QuerySlice<'_>, &mut G)> {
    if i >= self.mults.entries {
      return None;
    }
    Some((self.keys.at(i), &mut self.mults.at_mut(i)[0]))
  }

  pub fn get_index(&self, i: usize) -> Option<(QuerySlice<'_>, QueryRef<'_>)> {
    if i >= self.len() {
      return None;
    }
    Some((
      self.keys.at(i),
      QueryRef {
        output: self.outs.at(i),
        multiplicity: self.mults.at(i)[0],
        rank: self.rank_at(i),
      },
    ))
  }

  pub fn iter(&self) -> impl Iterator<Item = (QuerySlice<'_>, QueryRef<'_>)> {
    (0..self.len()).map(|i| {
      (
        self.keys.at(i),
        QueryRef {
          output: self.outs.at(i),
          multiplicity: self.mults.at(i)[0],
          rank: self.rank_at(i),
        },
      )
    })
  }
}

#[cfg(test)]
mod tests;
