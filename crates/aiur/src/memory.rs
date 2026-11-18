//! Width-local, interned ROM. The record has stable indices for accounting;
//! pointers are indices within a width bucket. A representative store type is
//! retained only for host diagnostics, never for interning or circuit lookups.
use crate::bytecode::Type;
use crate::chunks::Chunks;
use crate::index::{RowIndex, tag};
use serde::{Serialize, Serializer};
use std::hash::{Hash, Hasher};

#[derive(Clone, Copy, Debug, Serialize)]
pub struct CellRef<'a, F = u64> {
  pub r#type: &'a Type,
  pub value: &'a [F],
}

#[derive(Clone, Copy, Debug, Serialize)]
pub struct MemoryEntryRef<'a, F = u64> {
  pub address: usize,
  pub cell: CellRef<'a, F>,
  pub multiplicity: u64,
}

/// A cell's place in its width's bucket and its representative type.
#[derive(Clone, Copy, Debug)]
struct Slot {
  address: u32,
  type_id: u32,
}

/// The cells of one width, in address order: their words, and for each its
/// record index and its load and store count ([`INDEX`], [`COUNT`]). A cell
/// is reached by its address alone, so a load or a repeated store touches
/// its words and its count independently, never through its [`Slot`].
#[derive(Clone, Debug)]
struct Bucket<F> {
  words: Chunks<F>,
  cells: Chunks<u32>,
}

const INDEX: usize = 0;
const COUNT: usize = 1;

/// A cell by its width bucket and its address there.
#[derive(Clone, Copy, Debug)]
pub(crate) struct CellAt {
  bucket: usize,
  pub(crate) address: usize,
}

/// Bytes of one storage chunk.
const CHUNK_BYTES: usize = 1 << 19;

#[derive(Clone, Debug)]
pub struct Memory<F = u64> {
  types: Vec<(Type, usize)>,
  slots: Chunks<Slot>,
  widths: Vec<usize>,
  buckets: Vec<Bucket<F>>,
  type_buckets: Vec<usize>,
  // Every width's cell addresses, tagged with their hashes, with no second
  // payload copy ([`Self::matches`]). Retained after execution so trace population can resolve stores
  // directly.
  index: RowIndex,
  index_bytes: usize,
  // Release the charge after the payload and indexes have been freed.
  pub(crate) budget: crate::budget::Budget,
}

/// The cells of one width, by width-local address.
#[derive(Clone, Copy)]
pub(crate) struct WidthCells<'a, F> {
  memory: &'a Memory<F>,
  bucket: Option<&'a Bucket<F>>,
}

impl<'a, F: Copy + Eq + Hash + Send + Sync> WidthCells<'a, F> {
  pub(crate) fn len(&self) -> usize {
    self.bucket.map_or(0, |bucket| bucket.cells.len())
  }

  #[inline]
  pub(crate) fn get(&self, address: usize) -> Option<MemoryEntryRef<'a, F>> {
    let bucket = self.bucket?;
    if address >= bucket.cells.len() {
      return None;
    }
    self.memory.get(bucket.cells.row(address)[INDEX] as usize)
  }
}

impl<F: Copy + Eq + Hash + Send + Sync> Memory<F> {
  pub(crate) fn new(types: impl Iterator<Item = (Type, usize)>) -> Self {
    let types: Vec<_> = types.collect();
    let mut widths: Vec<_> = types.iter().map(|(_, width)| *width).collect();
    widths.sort_unstable();
    widths.dedup();
    let type_buckets =
      types.iter().map(|(_, w)| widths.binary_search(w).unwrap()).collect();
    let buckets = widths
      .iter()
      .map(|&width| Bucket {
        words: Chunks::new(width, CHUNK_BYTES),
        cells: Chunks::new(2, CHUNK_BYTES),
      })
      .collect();
    Self {
      budget: Default::default(),
      types,
      slots: Chunks::new(1, CHUNK_BYTES),
      widths,
      buckets,
      type_buckets,
      index: RowIndex::default(),
      index_bytes: 0,
    }
  }

  pub fn len(&self) -> usize {
    self.slots.len()
  }
  pub fn is_empty(&self) -> bool {
    self.slots.len() == 0
  }

  /// Free the chunks prefetched for cells that never came.
  pub(crate) fn drop_prefetched(&mut self) {
    self.slots.drop_prefetched(&self.budget);
    for bucket in &mut self.buckets {
      bucket.words.drop_prefetched(&self.budget);
      bucket.cells.drop_prefetched(&self.budget);
    }
  }

  pub(crate) fn storage_usage(&self) -> (usize, usize, usize) {
    let payload =
      self.buckets.iter().map(|b| b.words.payload_bytes()).sum::<usize>();
    let vectors = self.slots.capacity_bytes()
      + self
        .buckets
        .iter()
        .map(|b| b.words.capacity_bytes() + b.cells.capacity_bytes())
        .sum::<usize>()
      + self.buckets.capacity() * size_of::<Bucket<F>>();
    (payload, vectors, self.index.allocated_bytes())
  }

  #[inline]
  pub fn get(&self, index: usize) -> Option<MemoryEntryRef<'_, F>> {
    if index >= self.slots.len() {
      return None;
    }
    let slot = *self.slots.at(index);
    let type_id = slot.type_id as usize;
    let address = slot.address as usize;
    let bucket = &self.buckets[self.type_buckets[type_id]];
    Some(MemoryEntryRef {
      address,
      cell: CellRef {
        r#type: &self.types[type_id].0,
        value: bucket.words.row(address),
      },
      multiplicity: u64::from(bucket.cells.row(address)[COUNT]),
    })
  }

  pub fn iter(&self) -> impl ExactSizeIterator<Item = MemoryEntryRef<'_, F>> {
    (0..self.len()).map(|i| self.get(i).unwrap())
  }

  #[cfg(feature = "parallel")]
  pub(crate) fn par_iter(
    &self,
  ) -> impl rayon::iter::IndexedParallelIterator<Item = MemoryEntryRef<'_, F>>
  {
    use rayon::prelude::*;
    (0..self.len()).into_par_iter().map(|i| self.get(i).unwrap())
  }

  /// The cell at `address` among those of `type_id`'s width.
  #[inline(always)]
  pub(crate) fn cell(&self, type_id: usize, address: usize) -> Option<CellAt> {
    let bucket = self.type_buckets[type_id];
    (address < self.buckets[bucket].cells.len())
      .then_some(CellAt { bucket, address })
  }

  /// A cell's words.
  #[inline(always)]
  pub(crate) fn words(&self, cell: CellAt) -> &[F] {
    self.buckets[cell.bucket].words.row(cell.address)
  }

  /// A cell's count of loads and stores. Callers fail loudly rather than
  /// wrap at `u32::MAX`.
  #[inline(always)]
  pub(crate) fn count_mut(&mut self, cell: CellAt) -> &mut u32 {
    &mut self.buckets[cell.bucket].cells.row_mut(cell.address)[COUNT]
  }

  /// The cells of `width`, consecutive from address zero. The caller may
  /// have an unused circuit width absent from this execution's type layouts.
  pub(crate) fn width_cells(&self, width: usize) -> WidthCells<'_, F> {
    WidthCells {
      memory: self,
      bucket: self.widths.binary_search(&width).ok().map(|i| &self.buckets[i]),
    }
  }

  pub fn get_by_width(
    &self,
    width: usize,
    address: usize,
  ) -> Option<MemoryEntryRef<'_, F>> {
    self.width_cells(width).get(address)
  }

  /// Whether the cell at `address` of `bucket` holds `words`. The index
  /// holds the addresses of every width, so `address` may be past this
  /// width's cells. A match is the answer whichever width's entry led here,
  /// since a width holds each encoding at most once.
  #[inline(always)]
  fn matches(&self, bucket: usize, address: usize, words: &[F]) -> bool {
    let bucket = &self.buckets[bucket];
    address < bucket.cells.len() && bucket.words.row(address) == words
  }

  #[inline(always)]
  fn hash(words: &[F]) -> u64 {
    let mut hasher = rustc_hash::FxHasher::default();
    hasher.write_usize(words.len());
    for word in words {
      word.hash(&mut hasher);
    }
    hasher.finish()
  }

  // Keep this in the store/population hot loops, as QueryTable::lookup does.
  // Otherwise returning the hash plus an optional index spills to the stack.
  #[inline(always)]
  fn lookup(&self, bucket: usize, words: &[F]) -> (u64, Option<usize>) {
    let hash = Self::hash(words);
    let address = self
      .index
      .find(tag(hash), |address| self.matches(bucket, address as usize, words));
    (hash, address.map(|address| address as usize))
  }

  #[inline]
  pub(crate) fn address_of(&self, words: &[F]) -> Option<usize> {
    let bucket = self.widths.binary_search(&words.len()).ok()?;
    self.lookup(bucket, words).1
  }

  /// Start loading the index bucket [`Self::intern`] reads first for
  /// `words`.
  #[inline(always)]
  pub(crate) fn prefetch_intern(&self, words: &[F]) {
    self.index.prefetch(tag(Self::hash(words)));
  }

  /// Start loading the words and the count of `cell`.
  #[inline(always)]
  pub(crate) fn prefetch_cell(&self, cell: CellAt) {
    let bucket = &self.buckets[cell.bucket];
    crate::index::prefetch(bucket.words.row(cell.address).as_ptr());
    crate::index::prefetch(bucket.cells.row(cell.address).as_ptr());
  }

  /// The only insertion path: equal encodings share one cell, regardless of
  /// nominal type, and each width's addresses form a consecutive prefix.
  /// The index holds each cell's address, not its record index, so a
  /// repeated store reads the index and the words only.
  #[inline]
  pub(crate) fn intern(
    &mut self,
    type_id: usize,
    words: &[F],
    modulus: u64,
  ) -> Result<CellAt, crate::budget::StorageError> {
    debug_assert_eq!(words.len(), self.types[type_id].1);
    let bucket_id = self.type_buckets[type_id];
    let (hash, found) = self.lookup(bucket_id, words);
    if let Some(address) = found {
      return Ok(CellAt { bucket: bucket_id, address });
    }
    let index = self.slots.len();
    let entry = self.budget.row(
      index,
      size_of_val(words) + size_of::<Slot>() + 2 * size_of::<u32>(),
    )?;
    let bucket = &mut self.buckets[bucket_id];
    let address = bucket.cells.len();
    // Record indices are below `u32::MAX` ([`crate::budget::MAX_ROWS`]),
    // and a width's addresses are at most its record indices.
    if address as u64 >= modulus {
      return Err("ROM exceeds field capacity".into());
    }
    bucket.words.reserve(&self.budget)?;
    bucket.cells.reserve(&self.budget)?;
    self.slots.reserve(&self.budget)?;
    let replaced =
      self.budget.index(self.index.growth(), &mut self.index_bytes)?;
    self.index.insert(tag(hash), address as u32);
    drop(replaced);
    bucket.words.push(words);
    bucket.cells.push(&[entry, 0]);
    self
      .slots
      .push(&[Slot { address: address as u32, type_id: type_id as u32 }]);
    Ok(CellAt { bucket: bucket_id, address })
  }

  /// Size the index for `cells` cells, so growing to them does not rehash.
  pub(crate) fn reserve_index(
    &mut self,
    cells: usize,
  ) -> Result<(), crate::budget::BudgetError> {
    let replaced = self
      .budget
      .index(self.index.reservation(cells), &mut self.index_bytes)?;
    self.index.reserve(cells);
    drop(replaced);
    Ok(())
  }

  /// The count of the cell with record index `index`.
  #[cfg(test)]
  pub(crate) fn multiplicity_mut(&mut self, index: usize) -> &mut u32 {
    let slot = *self.slots.at(index);
    let cell = CellAt {
      bucket: self.type_buckets[slot.type_id as usize],
      address: slot.address as usize,
    };
    self.count_mut(cell)
  }
}

impl<F: Copy + Eq + Hash + Send + Sync + Serialize> Serialize for Memory<F> {
  fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
    serializer.collect_seq(self.iter())
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::execute::{Cell, MemoryEntry};

  #[test]
  fn retained_index_survives_growth_cloning_and_width_aliases() {
    let mut memory = Memory::new(
      [
        (Type::Field, 1),
        (Type::Tuple { items: vec![Type::Field] }, 1),
        (Type::Tuple { items: vec![Type::Field; 2] }, 2),
        (Type::Tuple { items: vec![] }, 0),
      ]
      .into_iter(),
    );
    for value in 0..1024 {
      memory.intern(2, &[value, 0], 65537).unwrap();
      memory.intern(3, &[], 65537).unwrap();
      let cell = memory.intern(0, &[1023 - value], 65537).unwrap();
      let alias = memory.intern(1, &[1023 - value], 65537).unwrap();
      assert_eq!((alias.bucket, alias.address), (cell.bucket, cell.address));
    }
    assert_eq!(memory.len(), 2049);
    let mut copy = memory.clone();
    for value in 1024..4096 {
      copy.intern(0, &[value], 65537).unwrap();
    }
    // Independently scan the record: indices refer to cells, not allocations
    // or the other width's local address, even after clone/arena/hash growth.
    for record in [&memory, &copy] {
      for entry in record.iter() {
        assert_eq!(record.address_of(entry.cell.value), Some(entry.address));
      }
      assert_eq!(record.address_of(&[7]), Some(1016));
      assert_eq!(record.address_of(&[7, 0]), Some(7));
      assert_eq!(record.address_of(&[]), Some(0));
      assert_eq!(record.address_of(&[7, 0, 0]), None);
    }
    assert_eq!(memory.address_of(&[1024]), None);
    assert_eq!(copy.address_of(&[1024]), Some(1024));
  }

  #[test]
  fn borrowed_cells_preserve_wire_format_and_zero_width_addresses() {
    let unit = Type::Tuple { items: vec![] };
    let mut memory =
      Memory::new([(Type::Field, 1), (unit.clone(), 0)].into_iter());
    memory.intern(0, &[7], 17).unwrap();
    memory.intern(1, &[], 17).unwrap();
    *memory.multiplicity_mut(0) = 3;
    *memory.multiplicity_mut(1) = 1;
    assert!(memory.get(2).is_none());
    assert!(memory.matches(0, 0, &[]));
    assert!(!memory.matches(0, 1, &[]));
    assert_eq!(memory.get_by_width(1, 0).unwrap().cell.value, &[7]);
    assert!(memory.get_by_width(0, 0).unwrap().cell.value.is_empty());
    let expected = vec![
      MemoryEntry {
        address: 0,
        cell: Cell { r#type: Type::Field, value: vec![7] },
        multiplicity: 3,
      },
      MemoryEntry {
        address: 0,
        cell: Cell { r#type: unit, value: vec![] },
        multiplicity: 1,
      },
    ];
    assert_eq!(
      serde_json::to_value(&memory).unwrap(),
      serde_json::to_value(expected).unwrap()
    );
    let mut copy = memory.clone();
    *copy.multiplicity_mut(0) = 8;
    assert_eq!(memory.get(0).unwrap().multiplicity, 3);
  }
}
