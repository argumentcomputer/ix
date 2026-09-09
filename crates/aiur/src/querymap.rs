use multi_stark::p3_field::{PrimeCharacteristicRing, PrimeField64};

use crate::{
  G,
  execute::budget::{BudgetExceeded, ExecutionBudget},
};
use std::sync::Arc;

mod storage;
use storage::PackedStore;
pub use storage::{PackedRow, QuerySlice};
mod stats;
pub use stats::MultiplicityStats;
mod multiplicity;
use multiplicity::Multiplicities;

/// Immutable view of one query entry.
#[derive(Clone, Copy)]
pub struct QueryRef<'a> {
  pub(crate) output: QuerySlice<'a>,
  pub multiplicity: G,
}

pub(crate) fn hash_g_slice(key: &[G]) -> u64 {
  use std::hash::Hasher;
  let mut h = rustc_hash::FxHasher::default();
  for g in key {
    h.write_u64(g.as_canonical_u64());
  }
  h.finish()
}

/// Immutable arguments and their canonical hash for generated execution.
/// Owning the fixed-size array keeps the hash tied to its values across
/// recursive calls. This is not a cached bucket or permission to skip exact
/// equality checks: tables may rehash while the callee executes.
#[derive(Clone, Copy)]
pub struct QueryKey<const N: usize> {
  values: [G; N],
  hash: u64,
}

impl<const N: usize> QueryKey<N> {
  #[inline]
  pub fn new(values: [G; N]) -> Self {
    Self { hash: hash_g_slice(&values), values }
  }

  #[inline]
  pub fn values(&self) -> &[G; N] {
    &self.values
  }
}

/// Entries per storage segment (2^20). Segments are fixed-size, so growth
/// does not copy older segments: appending past a segment boundary just
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
/// segmented arenas addressed by entry index, and the hash table holds
/// only `u32` indices. This cuts per-entry overhead from ~130 B (two heap
/// `Vec`s + IndexMap bucket + allocator metadata) to the raw field
/// elements plus ~21 B of index + stored hash. Columns retain one, four or
/// eight bytes per field and decode losslessly on access; larger values widen
/// only the active segment. Memory outputs are reconstructed indices. The record IS the proof
/// witness, so entries cannot be dropped — only stored compactly; on
/// kernel-heavy executions it is the dominant RAM consumer (billions of
/// entries). Segmented growth avoids whole-arena doubling; active-segment
/// widening is budgeted before copying. Stored hashes make table growth a
/// sequential pass, and segments are hugepage-advised.
/// Multiplicities optionally use u32 segments with budgeted full-field
/// promotion on insertion or a later hit, preserving field arithmetic.
///
/// Entry index == insertion order; memory circuits use it as the pointer
/// value, mirroring the old `IndexMap::get_index_of` semantics.
pub struct QueryMap {
  /// Output width; inferred on first insert (not statically available in
  /// `FunctionLayout`).
  out_stride_set: bool,
  /// Only memory maps may reconstruct outputs from their insertion index.
  implicit_output: bool,
  keys: PackedStore,
  outs: PackedStore,
  mults: Multiplicities,
  hashes: SegU64s,
  table: hashbrown::HashTable<u32>,
  budget: Option<Arc<ExecutionBudget>>,
  charged: u64,
}

impl QueryMap {
  pub fn new(key_stride: usize) -> Self {
    Self::with_budget(key_stride, None)
  }

  pub(crate) fn with_budget(
    key_stride: usize,
    budget: Option<Arc<ExecutionBudget>>,
  ) -> Self {
    Self::with_storage(key_stride, budget, true)
  }

  pub(crate) fn with_storage(
    key_stride: usize,
    budget: Option<Arc<ExecutionBudget>>,
    compact: bool,
  ) -> Self {
    Self::with_encodings(
      key_stride,
      budget,
      compact,
      compact && *multiplicity::COMPACT,
    )
  }

  pub(crate) fn with_encodings(
    key_stride: usize,
    budget: Option<Arc<ExecutionBudget>>,
    compact: bool,
    compact_mults: bool,
  ) -> Self {
    Self {
      out_stride_set: false,
      implicit_output: false,
      keys: PackedStore::new(key_stride, compact),
      outs: PackedStore::new(0, compact),
      mults: Multiplicities::new(compact_mults),
      hashes: SegU64s::new(),
      table: hashbrown::HashTable::new(),
      budget,
      charged: 0,
    }
  }

  pub(crate) fn with_memory_budget(
    key_stride: usize,
    budget: Option<Arc<ExecutionBudget>>,
  ) -> Self {
    let mut map = Self::with_budget(key_stride, budget);
    map.implicit_output = true;
    map
  }

  #[inline]
  pub fn len(&self) -> usize {
    self.mults.entries
  }

  #[inline]
  pub fn is_empty(&self) -> bool {
    self.mults.entries == 0
  }

  /// Logical field elements (including reconstructed memory outputs); used by the
  /// `IX_AIUR_QUERY_STATS` RAM-attribution dump.
  pub fn retained_elems(&self) -> usize {
    self.keys.retained_elems()
      + if self.implicit_output {
        self.len()
      } else {
        self.outs.retained_elems()
      }
  }

  /// Encoded key/output payload, excluding hashes, multiplicities and index.
  pub fn retained_bytes(&self) -> usize {
    self.keys.retained_bytes() + self.outs.retained_bytes()
  }

  pub fn get_index_of(&self, key: &[G]) -> Option<usize> {
    self.get_index_of_hashed(key, hash_g_slice(key))
  }

  #[inline]
  pub fn get_prehashed<const N: usize>(
    &self,
    key: &QueryKey<N>,
  ) -> Option<usize> {
    self.get_index_of_hashed(&key.values, key.hash)
  }

  // The interpreter's mutable value stack retains its original input prefix;
  // it carries this hash in the call frame without cloning those inputs.
  pub(crate) fn get_index_of_hashed(
    &self,
    key: &[G],
    hash: u64,
  ) -> Option<usize> {
    debug_assert_eq!(key.len(), self.keys.stride);
    self
      .table
      .find(hash, |&i| self.keys.at(i as usize).matches(key))
      .map(|&i| i as usize)
  }

  pub fn get(&self, key: &[G]) -> Option<QueryRef<'_>> {
    let i = self.get_index_of(key)?;
    Some(QueryRef { output: self.output_at(i), multiplicity: self.mults.at(i) })
  }

  /// Multiplicity of entry `i`.
  #[inline]
  pub fn mult_at(&self, i: usize) -> G {
    self.mults.at(i)
  }

  /// Lossless output view of entry `i`.
  #[inline]
  pub fn output_at(&self, i: usize) -> QuerySlice<'_> {
    assert!(i < self.len(), "query output index out of bounds");
    if self.implicit_output {
      QuerySlice::Value(G::from_usize(i))
    } else {
      self.outs.at(i)
    }
  }

  /// Record a constrained memo hit on entry `i`. Widening a counter segment
  /// is fallible; rejection leaves every counter and its encoding unchanged.
  #[inline]
  pub fn bump_multiplicity(&mut self, i: usize) -> Result<(), BudgetExceeded> {
    if self.mults.try_bump(i) {
      return Ok(());
    }
    self.bump_widened(i)
  }

  #[cold]
  fn bump_widened(&mut self, i: usize) -> Result<(), BudgetExceeded> {
    let plan = self.mults.plan_bump(i);
    let reservation = if let Some(budget) = &self.budget {
      let next = self
        .accounted_bytes()
        .saturating_sub(self.mults.accounted_bytes())
        .saturating_add(plan.storage_after)
        .saturating_add(plan.transient);
      Some(budget.charge(next - self.charged)?)
    } else {
      None
    };
    self.mults.bump_widened(i, plan);
    if let Some(reservation) = reservation {
      let after = self.accounted_bytes();
      reservation.retain_bytes(after - self.charged);
      self.charged = after;
    }
    Ok(())
  }

  /// Register a function query at `Ctrl::Return`: insert on first
  /// registration and bump on constrained promotion of a cached hint row.
  pub fn finish(
    &mut self,
    key: &[G],
    output: &[G],
    constrained: bool,
  ) -> Result<(), BudgetExceeded> {
    self.finish_hashed(key, hash_g_slice(key), output, constrained)
  }

  #[inline]
  pub fn finish_prehashed<const N: usize>(
    &mut self,
    key: &QueryKey<N>,
    output: &[G],
    constrained: bool,
  ) -> Result<(), BudgetExceeded> {
    self.finish_hashed(&key.values, key.hash, output, constrained)
  }

  pub(crate) fn finish_hashed(
    &mut self,
    key: &[G],
    hash: u64,
    output: &[G],
    constrained: bool,
  ) -> Result<(), BudgetExceeded> {
    if let Some(i) = self.get_index_of_hashed(key, hash) {
      // The only ordinary way to execute an already cached function is
      // constrained promotion of an unconstrained hint entry.
      debug_assert!(self.output_at(i).matches(output));
      if constrained {
        self.bump_multiplicity(i)?;
      }
    } else {
      self.insert_hashed(key, hash, output, G::from_bool(constrained))?;
    }
    Ok(())
  }

  /// Append a new entry. The key must not already be present: call sites
  /// only insert on a confirmed miss, and a same-key re-entrant call
  /// would loop forever before reaching its own insert.
  pub fn insert(
    &mut self,
    key: &[G],
    output: &[G],
    multiplicity: G,
  ) -> Result<(), BudgetExceeded> {
    self.insert_hashed(key, hash_g_slice(key), output, multiplicity)
  }

  /// Insert on a confirmed miss, preserving the existing `insert` contract.
  pub fn insert_prehashed<const N: usize>(
    &mut self,
    key: &QueryKey<N>,
    output: &[G],
    multiplicity: G,
  ) -> Result<(), BudgetExceeded> {
    self.insert_hashed(&key.values, key.hash, output, multiplicity)
  }

  pub(crate) fn insert_hashed(
    &mut self,
    key: &[G],
    hash: u64,
    output: &[G],
    multiplicity: G,
  ) -> Result<(), BudgetExceeded> {
    assert_eq!(key.len(), self.keys.stride);
    debug_assert!(self.get_index_of_hashed(key, hash).is_none());
    if self.implicit_output {
      assert_eq!(
        output,
        &[G::from_usize(self.len())],
        "memory output must equal insertion index"
      );
    } else if self.out_stride_set {
      assert_eq!(output.len(), self.outs.stride);
    }
    let key_plan = self.keys.plan(key);
    let stored_output = if self.implicit_output { &[][..] } else { output };
    let out_plan = self.outs.plan(stored_output);
    let mult_plan = self.mults.plan_append(multiplicity);
    // Cover both tables during rehash, and hugepage-rounded arena growth,
    // BEFORE touching new pages. A failed charge leaves all query data intact.
    let reservation = if let Some(budget) = &self.budget {
      let mut next = key_plan
        .storage_after
        .saturating_add(out_plan.storage_after)
        .saturating_add(key_plan.transient)
        .saturating_add(out_plan.transient)
        .saturating_add(mult_plan.storage_after)
        .saturating_add(mult_plan.transient)
        .saturating_add(arena_bytes(self.len().saturating_add(1), 1));
      if self.len() == self.table.capacity() {
        next = next
          .saturating_add(table_bytes(self.table.capacity()))
          .saturating_add(table_bytes(
            self.table.capacity().saturating_mul(2).saturating_add(1).max(4),
          ));
      } else {
        next = next.saturating_add(table_bytes(self.table.capacity()));
      }
      if next > self.charged {
        Some(budget.charge(next - self.charged)?)
      } else {
        None
      }
    } else {
      None
    };
    if !self.out_stride_set {
      self.outs.stride = stored_output.len();
      self.out_stride_set = true;
    } else {
      debug_assert_eq!(stored_output.len(), self.outs.stride);
    }
    let i = u32::try_from(self.mults.entries).expect("query map overflow");
    self.keys.push(key, key_plan);
    self.outs.push(stored_output, out_plan);
    self.mults.push(multiplicity, mult_plan);
    self.hashes.push(hash);
    let hashes = &self.hashes;
    self.table.insert_unique(hash, i, |&j| hashes.at(j as usize));
    if let Some(reservation) = reservation {
      // Keep only steady-state storage; the temporary old table is now gone.
      let before = self.charged;
      let after = self.accounted_bytes();
      // The reservation includes a conservative upper bound for table growth.
      // Retain exactly the new steady-state charge and return its excess.
      let added = after.saturating_sub(before);
      reservation.retain_bytes(added);
      self.charged = after;
    }
    Ok(())
  }

  fn storage_bytes(&self) -> u64 {
    self
      .keys
      .accounted_bytes()
      .saturating_add(self.outs.accounted_bytes())
      .saturating_add(self.mults.accounted_bytes())
      .saturating_add(arena_bytes(self.len(), 1))
  }

  pub fn accounted_bytes(&self) -> u64 {
    self.storage_bytes().saturating_add(table_bytes(self.table.capacity()))
  }

  /// Explicit linear scan of counter storage, without decoding keys/outputs.
  /// Intended for final opt-in diagnostics, never a progress-tick hot path.
  pub fn multiplicity_stats(&self) -> MultiplicityStats {
    MultiplicityStats::of_store(&self.mults)
  }

  pub fn get_index(&self, i: usize) -> Option<(QuerySlice<'_>, QueryRef<'_>)> {
    if i >= self.len() {
      return None;
    }
    Some((
      self.keys.at(i),
      QueryRef { output: self.output_at(i), multiplicity: self.mults.at(i) },
    ))
  }

  pub fn iter(&self) -> impl Iterator<Item = (QuerySlice<'_>, QueryRef<'_>)> {
    (0..self.len()).map(|i| {
      (
        self.keys.at(i),
        QueryRef { output: self.output_at(i), multiplicity: self.mults.at(i) },
      )
    })
  }
}

impl Drop for QueryMap {
  fn drop(&mut self) {
    if let Some(budget) = &self.budget {
      // Release accounting only AFTER the physical storage has been dropped.
      self.keys.clear_storage();
      self.outs.clear_storage();
      self.mults.segs.clear();
      self.hashes.segs.clear();
      drop(std::mem::replace(&mut self.table, hashbrown::HashTable::new()));
      budget.release(self.charged);
    }
  }
}

fn arena_bytes(entries: usize, stride: usize) -> u64 {
  if entries == 0 || stride == 0 {
    return 0;
  }
  let segment =
    (SEG_ENTRIES as u64).saturating_mul(stride as u64).saturating_mul(8);
  #[cfg(target_os = "linux")]
  {
    let whole = (entries >> SEG_BITS) as u64;
    let tail = ((entries & SEG_MASK) as u64)
      .saturating_mul(stride as u64)
      .saturating_mul(8);
    whole
      .saturating_mul(segment)
      .saturating_add(tail.div_ceil(1 << 21).saturating_mul(1 << 21))
  }
  #[cfg(not(target_os = "linux"))]
  {
    (entries.div_ceil(SEG_ENTRIES) as u64).saturating_mul(segment)
  }
}

// HashTable<u32>: reserve eight bytes per bucket (index + control + margin),
// plus a page for alignment/control-group padding. Include old + new on grow.
fn table_bytes(capacity: usize) -> u64 {
  if capacity == 0 {
    return 0;
  }
  capacity
    .checked_next_power_of_two()
    .map_or(u64::MAX, |b| (b as u64).saturating_mul(8).saturating_add(4096))
}

#[cfg(test)]
mod tests;
