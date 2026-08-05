use multi_stark::p3_field::PrimeField64;

use crate::G;

/// Immutable view of one query entry.
#[derive(Clone, Copy)]
pub struct QueryRef<'a> {
  pub(crate) output: &'a [G],
  pub multiplicity: G,
}

/// Mutable view of one query entry: the output is fixed at insertion,
/// only the multiplicity is bumped on memo hits.
pub struct QueryRefMut<'a> {
  pub output: &'a [G],
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
    let bytes = cap * size_of::<T>();
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

  fn retained_elems(&self) -> usize {
    self.entries * self.stride
  }
}

/// Segmented store of per-entry key hashes. Kept so hash-table growth can
/// re-insert from stored hashes instead of re-hashing every key from the
/// keys arena — table doubling on a multi-GB map used to be a full
/// sequential re-hash pass over the arena, log-many times.
struct SegHashes {
  segs: Vec<HugeVec<u64>>,
  entries: usize,
}

impl SegHashes {
  fn new() -> Self {
    Self { segs: Vec::new(), entries: 0 }
  }

  #[inline]
  fn at(&self, i: usize) -> u64 {
    self.segs[i >> SEG_BITS].slice(i & SEG_MASK, 1)[0]
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

/// Append-only query store with a hash index.
///
/// Functionally the insertion-ordered map `args -> (output, multiplicity)`
/// it replaces (`FxIndexMap<Vec<G>, QueryResult>`) — but every circuit has
/// a FIXED key arity and output width, so keys and outputs live in flat
/// segmented `G` arenas addressed by entry index, and the hash table holds
/// only `u32` indices. This cuts per-entry overhead from ~130 B (two heap
/// `Vec`s + IndexMap bucket + allocator metadata) to the raw field
/// elements plus ~21 B of index + stored hash. The record IS the proof
/// witness, so entries cannot be dropped — only stored compactly; on
/// kernel-heavy executions it is the dominant RAM consumer (billions of
/// entries). Segmented storage keeps growth copy-free (no doubling
/// memmove, no transient 2x RSS), stored hashes make table growth a cheap
/// sequential pass, and segments are hugepage-advised (see `advise_huge`).
///
/// Entry index == insertion order; memory circuits use it as the pointer
/// value, mirroring the old `IndexMap::get_index_of` semantics.
pub struct QueryMap {
  /// Output width; inferred on first insert (not statically available in
  /// `FunctionLayout`).
  out_stride_set: bool,
  keys: SegStore,
  outs: SegStore,
  mults: SegStore,
  hashes: SegHashes,
  table: hashbrown::HashTable<u32>,
}

impl QueryMap {
  pub fn new(key_stride: usize) -> Self {
    Self {
      out_stride_set: false,
      keys: SegStore::new(key_stride),
      outs: SegStore::new(0),
      mults: SegStore::new(1),
      hashes: SegHashes::new(),
      table: hashbrown::HashTable::new(),
    }
  }

  #[inline]
  pub fn len(&self) -> usize {
    self.mults.entries
  }

  #[inline]
  pub fn is_empty(&self) -> bool {
    self.mults.entries == 0
  }

  /// Total retained field elements (keys + outputs); used by the
  /// `IX_AIUR_QUERY_STATS` RAM-attribution dump.
  pub fn retained_elems(&self) -> usize {
    self.keys.retained_elems() + self.outs.retained_elems()
  }

  pub fn get_index_of(&self, key: &[G]) -> Option<usize> {
    debug_assert_eq!(key.len(), self.keys.stride);
    let hash = hash_g_slice(key);
    self
      .table
      .find(hash, |&i| self.keys.at(i as usize) == key)
      .map(|&i| i as usize)
  }

  pub fn get(&self, key: &[G]) -> Option<QueryRef<'_>> {
    let i = self.get_index_of(key)?;
    Some(QueryRef {
      output: self.outs.at(i),
      multiplicity: self.mults.at(i)[0],
    })
  }

  pub fn get_mut(&mut self, key: &[G]) -> Option<QueryRefMut<'_>> {
    let i = self.get_index_of(key)?;
    Some(QueryRefMut {
      output: self.outs.at(i),
      multiplicity: &mut self.mults.at_mut(i)[0],
    })
  }

  /// Append a new entry. The key must not already be present: call sites
  /// only insert on a confirmed miss, and a same-key re-entrant call
  /// would loop forever before reaching its own insert.
  pub fn insert(&mut self, key: &[G], output: &[G], multiplicity: G) {
    debug_assert_eq!(key.len(), self.keys.stride);
    debug_assert!(self.get_index_of(key).is_none());
    if !self.out_stride_set {
      self.outs.stride = output.len();
      self.out_stride_set = true;
    } else {
      debug_assert_eq!(output.len(), self.outs.stride);
    }
    let hash = hash_g_slice(key);
    let i = u32::try_from(self.mults.entries).expect("query map overflow");
    self.keys.push(key);
    self.outs.push(output);
    self.mults.push(&[multiplicity]);
    self.hashes.push(hash);
    let hashes = &self.hashes;
    self.table.insert_unique(hash, i, |&j| hashes.at(j as usize));
  }

  /// Entry at insertion index `i`: the key slice plus a mutable handle on
  /// the multiplicity (memory `Load` bumps the pointed-to row's count).
  pub fn get_index_mut(&mut self, i: usize) -> Option<(&[G], &mut G)> {
    if i >= self.mults.entries {
      return None;
    }
    Some((self.keys.at(i), &mut self.mults.at_mut(i)[0]))
  }

  pub fn get_index(&self, i: usize) -> Option<(&[G], QueryRef<'_>)> {
    if i >= self.len() {
      return None;
    }
    Some((
      self.keys.at(i),
      QueryRef { output: self.outs.at(i), multiplicity: self.mults.at(i)[0] },
    ))
  }

  pub fn iter(&self) -> impl Iterator<Item = (&[G], QueryRef<'_>)> {
    (0..self.len()).map(|i| {
      (
        self.keys.at(i),
        QueryRef { output: self.outs.at(i), multiplicity: self.mults.at(i)[0] },
      )
    })
  }
}
