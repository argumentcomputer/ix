//! A hash index of row numbers in cache-line buckets, for query tables and the
//! ROM. Keys live in their row arenas; the index keeps only a 32-bit tag
//! folded from each key's hash and the key's row number, side by side, so a
//! probe loads one cache line before the row it confirms.
//!
//! A bucket is 16 `u32` words on one 64-byte line:
//!
//! ```text
//! [ tag0 … tag7 | row0 + 1 … row7 + 1 ]
//! ```
//!
//! A zero row word marks an empty slot, so a zeroed allocation is an empty
//! index, and slots fill in order.
//!
//! A key's home bucket is a function of its tag alone, so growth rehashes
//! from the tags without loading rows. Full buckets overflow into the next
//! one (linear probing). Entries are never removed, so a bucket that is not
//! full ends every probe that reaches it.
//!
//! Sizes follow hashbrown's: an index of size class `k` holds `7/8 · 2^k`
//! entries in `9 · 2^k` bytes (`9/8 · 2^(k-3)` buckets of 8 slots, a load
//! factor of 7/9), so it grows at the same points and to the same size as the
//! `HashTable` of 8-byte entries it replaces.

/// Entries per bucket.
const SLOTS: usize = 8;
/// `u32` words per bucket.
const WORDS: usize = 16;
/// The first row word.
const ROWS: usize = SLOTS;
/// The occupancy of a full bucket.
const FULL: u32 = (1 << SLOTS) - 1;
/// Bucket size and alignment in bytes.
const LINE: usize = 64;
/// The smallest size class: 9 buckets, holding 56 entries.
const MIN_CLASS: u32 = 6;

/// The tag of a key with `hash`: its 32-bit fold.
#[inline(always)]
#[allow(clippy::cast_possible_truncation)] // The tag keeps the low 32 bits of the folded hash.
pub(crate) fn tag(hash: u64) -> u32 {
  (hash ^ (hash >> 32)) as u32
}

/// Buckets of size class `class`.
#[inline]
const fn buckets(class: u32) -> usize {
  9 << (class - MIN_CLASS)
}

/// Entries an index of size class `class` holds before it grows.
#[inline]
const fn limit(class: u32) -> usize {
  7 << (class - 3)
}

/// Bytes allocated for `buckets` buckets, including a spare bucket that lets
/// the first one start on a line boundary.
#[inline]
const fn bytes(buckets: usize) -> usize {
  if buckets == 0 { 0 } else { (buckets + 1) * LINE }
}

/// One bit per lane of `lanes` equal to `value`: one vector compare and a
/// move-mask. A scalar loop over the lanes does not vectorize this way. The
/// lanes are gathered by value, which the compiler folds into one 32-byte
/// load, so no pointer is dereferenced.
#[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
#[inline(always)]
#[allow(clippy::cast_possible_wrap, clippy::cast_sign_loss)] // bit patterns only
fn lanes_equal(lanes: &[u32; SLOTS], value: u32) -> u32 {
  use std::arch::x86_64::{
    _mm256_castsi256_ps, _mm256_cmpeq_epi32, _mm256_movemask_ps,
    _mm256_set1_epi32, _mm256_setr_epi32,
  };
  let [a, b, c, d, e, f, g, h] = lanes.map(|lane| lane as i32);
  // SAFETY: these intrinsics only require AVX and AVX2, which this build
  // targets (the `cfg` above), so every CPU that runs it supports them. They
  // take and return values and touch no memory.
  unsafe {
    let lanes = _mm256_setr_epi32(a, b, c, d, e, f, g, h);
    let equal = _mm256_cmpeq_epi32(lanes, _mm256_set1_epi32(value as i32));
    _mm256_movemask_ps(_mm256_castsi256_ps(equal)) as u32
  }
}

#[cfg(not(all(target_arch = "x86_64", target_feature = "avx2")))]
#[inline(always)]
fn lanes_equal(lanes: &[u32; SLOTS], value: u32) -> u32 {
  let mut mask = 0u32;
  for (i, &lane) in lanes.iter().enumerate() {
    mask |= u32::from(lane == value) << i;
  }
  mask
}

/// Hint that the line at `address` will be read soon.
#[cfg(feature = "native")]
#[inline(always)]
pub(crate) fn prefetch<T>(address: *const T) {
  #[cfg(target_arch = "x86_64")]
  // SAFETY: a prefetch is a hint that never dereferences `address` and so
  // never faults, whatever it points to.
  unsafe {
    use std::arch::x86_64::{_MM_HINT_T0, _mm_prefetch};
    _mm_prefetch::<_MM_HINT_T0>(address.cast());
  }
  #[cfg(not(target_arch = "x86_64"))]
  let _ = address;
}

#[derive(Default)]
pub(crate) struct RowIndex {
  // Zero-initialized words; bucket `b` starts at word `base + WORDS * b`.
  words: Vec<u32>,
  base: usize,
  buckets: usize,
  class: u32,
  len: usize,
  grow_at: usize,
}

impl std::fmt::Debug for RowIndex {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    f.debug_struct("RowIndex")
      .field("len", &self.len)
      .field("buckets", &self.buckets)
      .finish()
  }
}

impl Clone for RowIndex {
  // A derived clone would copy the words into an allocation with another
  // alignment, so the bucket offset is recomputed.
  fn clone(&self) -> Self {
    let mut index = Self::with_class(self.class);
    let n = self.buckets * WORDS;
    index.words[index.base..index.base + n]
      .copy_from_slice(&self.words[self.base..self.base + n]);
    index.len = self.len;
    index
  }
}

impl RowIndex {
  fn with_class(class: u32) -> Self {
    if class == 0 {
      return Self::default();
    }
    let buckets = buckets(class);
    // `vec![0; n]` takes zeroed memory from the allocator, so large tables
    // are faulted in only as buckets are first written.
    let words = vec![0u32; (buckets + 1) * WORDS];
    let base = match words.as_ptr().align_offset(LINE) {
      offset if offset < WORDS => offset,
      _ => 0,
    };
    Self { words, base, buckets, class, len: 0, grow_at: limit(class) }
  }

  #[cfg(test)]
  fn len(&self) -> usize {
    self.len
  }

  /// Bytes of the index's allocation.
  pub(crate) fn allocated_bytes(&self) -> usize {
    self.words.capacity() * size_of::<u32>()
  }

  /// The size class that holds `entries` without growing.
  fn class_for(entries: usize) -> u32 {
    let mut class = MIN_CLASS;
    while limit(class) < entries {
      class += 1;
    }
    class
  }

  /// The allocation the next insertion makes, in bytes, if it must grow.
  #[inline(always)]
  pub(crate) fn growth(&self) -> Option<usize> {
    (self.len >= self.grow_at)
      .then(|| bytes(buckets(Self::class_for(self.len + 1))))
  }

  /// The allocation [`Self::reserve`] would make for `entries`, if any.
  pub(crate) fn reservation(&self, entries: usize) -> Option<usize> {
    (entries > self.grow_at).then(|| bytes(buckets(Self::class_for(entries))))
  }

  /// Grow now so that `entries` fit without a later rehash.
  pub(crate) fn reserve(&mut self, entries: usize) {
    if entries > self.grow_at {
      self.rehash(Self::class_for(entries));
    }
  }

  /// The home bucket of `tag`: the top 32 bits of its multiplicative hash,
  /// which mix every tag bit, scaled to the bucket count.
  #[inline(always)]
  fn home(&self, tag: u32) -> usize {
    let mixed = u64::from(tag).wrapping_mul(0x9e37_79b9_7f4a_7c15) >> 32;
    #[allow(clippy::cast_possible_truncation)] // less than `self.buckets`
    let home = ((mixed * self.buckets as u64) >> 32) as usize;
    home
  }

  #[inline(always)]
  fn next(&self, bucket: usize) -> usize {
    if bucket + 1 == self.buckets { 0 } else { bucket + 1 }
  }

  #[inline(always)]
  fn bucket(&self, bucket: usize) -> &[u32; WORDS] {
    let start = self.base + bucket * WORDS;
    self.words[start..start + WORDS].try_into().unwrap()
  }

  #[inline(always)]
  fn bucket_mut(&mut self, bucket: usize) -> &mut [u32; WORDS] {
    let start = self.base + bucket * WORDS;
    (&mut self.words[start..start + WORDS]).try_into().unwrap()
  }

  /// One bit per occupied slot of `bucket`.
  #[inline(always)]
  fn occupied(bucket: &[u32; WORDS]) -> u32 {
    !lanes_equal(bucket[ROWS..].try_into().unwrap(), 0) & FULL
  }

  /// One bit per slot of `bucket` whose tag is `tag`.
  #[inline(always)]
  fn matches(bucket: &[u32; WORDS], tag: u32) -> u32 {
    lanes_equal(bucket[..ROWS].try_into().unwrap(), tag)
  }

  /// The row of a key with `tag` for which `eq` holds.
  #[inline(always)]
  pub(crate) fn find(
    &self,
    tag: u32,
    mut eq: impl FnMut(u32) -> bool,
  ) -> Option<u32> {
    if self.len == 0 {
      return None;
    }
    let mut b = self.home(tag);
    loop {
      let bucket = self.bucket(b);
      let occupied = Self::occupied(bucket);
      let mut mask = Self::matches(bucket, tag) & occupied;
      while mask != 0 {
        let row = bucket[ROWS + mask.trailing_zeros() as usize] - 1;
        if eq(row) {
          return Some(row);
        }
        mask &= mask - 1;
      }
      if occupied != FULL {
        return None;
      }
      b = self.next(b);
    }
  }

  /// Start loading the home bucket of `tag` into the cache, so a probe that
  /// follows other work finds it there. A hint only: it reads nothing and
  /// cannot fault.
  #[cfg(feature = "native")]
  #[inline(always)]
  pub(crate) fn prefetch(&self, tag: u32) {
    if self.buckets != 0 {
      prefetch(
        self.words[self.base..].as_ptr().wrapping_add(WORDS * self.home(tag)),
      );
    }
  }

  /// Add a key known to be absent. Rows are below `u32::MAX`
  /// ([`crate::budget::MAX_ROWS`]).
  #[inline(always)]
  pub(crate) fn insert(&mut self, tag: u32, row: u32) {
    if self.len >= self.grow_at {
      self.grow();
    }
    self.place(tag, row);
    self.len += 1;
  }

  #[inline(always)]
  fn place(&mut self, tag: u32, row: u32) {
    let mut b = self.home(tag);
    loop {
      let next = self.next(b);
      let bucket = self.bucket_mut(b);
      let occupied = Self::occupied(bucket);
      if occupied != FULL {
        let slot = occupied.trailing_ones() as usize;
        bucket[slot] = tag;
        bucket[ROWS + slot] = row + 1;
        return;
      }
      b = next;
    }
  }

  #[cold]
  #[inline(never)]
  fn grow(&mut self) {
    self.rehash(Self::class_for(self.len + 1));
  }

  fn rehash(&mut self, class: u32) {
    let old = std::mem::replace(self, Self::with_class(class));
    self.len = old.len;
    for b in 0..old.buckets {
      let bucket = old.bucket(b);
      for slot in 0..Self::occupied(bucket).trailing_ones() as usize {
        self.place(bucket[slot], bucket[ROWS + slot] - 1);
      }
    }
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn finds_every_row_across_growth_overflow_and_clones() {
    let mut index = RowIndex::default();
    assert_eq!(index.find(0, |_| true), None);
    // Every fourth key shares a tag, so buckets overflow into their
    // neighbours and tag matches must defer to the key comparison.
    let tag_of = |key: u32| key / 4;
    for key in 0..20_000u32 {
      assert_eq!(index.find(tag_of(key), |row| row == key), None);
      index.insert(tag_of(key), key);
    }
    let copy = index.clone();
    for index in [&index, &copy] {
      assert_eq!(index.len(), 20_000);
      for key in 0..20_000u32 {
        assert_eq!(index.find(tag_of(key), |row| row == key), Some(key));
      }
      assert_eq!(index.find(tag_of(20_001), |row| row == 20_001), None);
    }
    assert_eq!((index.words.as_ptr() as usize + index.base * 4) % LINE, 0);
  }

  #[test]
  fn reserve_presizes_and_growth_reports_its_allocation() {
    let mut index = RowIndex::default();
    assert_eq!(index.growth(), Some(bytes(buckets(MIN_CLASS))));
    index.reserve(1000);
    let allocated = index.allocated_bytes();
    assert_eq!(index.reservation(1000), None);
    for key in 0..1000 {
      assert_eq!(index.growth(), None);
      index.insert(key, key);
    }
    assert_eq!(index.allocated_bytes(), allocated);
    // hashbrown's size for 1000 entries: 2048 slots of 9 bytes.
    assert_eq!(allocated, 9 * 2048 + LINE);
    for key in 1000..u32::try_from(limit(11)).unwrap() {
      index.insert(key, key);
    }
    assert!(index.growth().is_some());
  }
}
