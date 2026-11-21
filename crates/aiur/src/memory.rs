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

/// A cell's width-local offset (`address = base + offset`) and representative
/// store type.
#[derive(Clone, Copy, Debug)]
struct Slot {
  offset: u32,
  type_id: u32,
}

/// Cells of one width in consecutive address order: their payload words,
/// stable record indices, and load/store multiplicities in zero-copy chunks.
#[derive(Clone, Debug)]
struct Bucket<F> {
  words: Chunks<F>,
  indices: Chunks<u32>,
  counts: Chunks<u64>,
}

/// Bytes of one storage chunk.
const CHUNK_BYTES: usize = 1 << 19;

#[derive(Clone, Debug)]
pub struct Memory<F = u64> {
  pub(crate) budget: crate::budget::Budget,
  base: usize,
  end: u64,
  types: Vec<(Type, usize)>,
  type_used: Vec<bool>,
  slots: Chunks<Slot>,
  widths: Vec<usize>,
  buckets: Vec<Bucket<F>>,
  type_buckets: Vec<usize>,
  // Every width's cell offsets, tagged with their hashes, with no second
  // payload copy. Retained after execution so trace population can resolve
  // stores directly.
  index: RowIndex,
}

/// Sequential view over all cells of one payload width in address order.
#[cfg(feature = "stark")]
#[derive(Clone, Copy)]
pub(crate) struct WidthCells<'a, F> {
  base: usize,
  bucket: Option<&'a Bucket<F>>,
}

#[cfg(feature = "stark")]
impl<'a, F: Copy + Eq + Hash + Send + Sync> WidthCells<'a, F> {
  #[inline]
  pub(crate) fn len(&self) -> usize {
    self.bucket.map_or(0, |bucket| bucket.indices.len())
  }

  #[inline]
  pub(crate) fn is_empty(&self) -> bool {
    self.len() == 0
  }

  /// First width-local address in this bucket, if nonempty.
  #[inline]
  pub(crate) fn first_address(&self) -> Option<usize> {
    (!self.is_empty()).then_some(self.base)
  }

  /// `(address, multiplicity, payload)` at consecutive offset `i < len()`.
  #[inline]
  pub(crate) fn rom_row(&self, offset: usize) -> (usize, u64, &'a [F]) {
    let bucket = self.bucket.expect("valid width bucket");
    (self.base + offset, *bucket.counts.at(offset), bucket.words.row(offset))
  }

  /// Load/store multiplicity at consecutive offset `i < len()`.
  #[inline]
  pub(crate) fn multiplicity(&self, offset: usize) -> u64 {
    *self.bucket.expect("valid width bucket").counts.at(offset)
  }
}

impl<F: Copy + Eq + Hash + Send + Sync> Memory<F> {
  pub(crate) fn new(types: impl Iterator<Item = (Type, usize)>) -> Self {
    let types: Vec<_> = types.collect();
    let type_used = vec![false; types.len()];
    let mut widths: Vec<_> = types.iter().map(|(_, width)| *width).collect();
    widths.sort_unstable();
    widths.dedup();
    let type_buckets =
      types.iter().map(|(_, w)| widths.binary_search(w).unwrap()).collect();
    let buckets = widths
      .iter()
      .map(|&width| Bucket {
        words: Chunks::new(width, CHUNK_BYTES),
        indices: Chunks::new(1, CHUNK_BYTES),
        counts: Chunks::new(1, CHUNK_BYTES),
      })
      .collect();
    Self {
      budget: Default::default(),
      base: 0,
      end: u64::MAX,
      types,
      type_used,
      slots: Chunks::new(1, CHUNK_BYTES),
      widths,
      buckets,
      type_buckets,
      index: RowIndex::default(),
    }
  }

  pub(crate) fn drop_prefetched(&mut self) {
    self.slots.drop_prefetched();
    for bucket in &mut self.buckets {
      bucket.words.drop_prefetched();
      bucket.indices.drop_prefetched();
      bucket.counts.drop_prefetched();
    }
  }

  pub fn len(&self) -> usize {
    self.slots.len()
  }
  pub fn is_empty(&self) -> bool {
    self.slots.len() == 0
  }

  pub(crate) fn set_range(
    &mut self,
    start: u64,
    end: u64,
  ) -> Result<(), &'static str> {
    if !self.is_empty() || start >= end {
      return Err("invalid empty ROM range");
    }
    self.base = usize::try_from(start).ok().ok_or("ROM base overflow")?;
    self.end = end;
    Ok(())
  }

  /// Distinct registered types along with whether any cell of that type was
  /// interned, plus each cell's raw `(type_id, payload)` lookup for fast
  /// record validation without per-cell `HashMap<Type, Layout>` lookups.
  pub(crate) fn types_used(&self) -> impl Iterator<Item = (usize, &Type)> {
    self
      .types
      .iter()
      .zip(&self.type_used)
      .enumerate()
      .filter_map(|(id, ((ty, _), &used))| used.then_some((id, ty)))
  }

  #[inline]
  pub(crate) fn cell_type_and_words(&self, index: usize) -> (usize, &[F]) {
    let slot = *self.slots.at(index);
    let type_id = slot.type_id as usize;
    let bucket = &self.buckets[self.type_buckets[type_id]];
    (type_id, bucket.words.row(slot.offset as usize))
  }

  /// Largest address assigned in any width bucket, if nonempty.
  pub(crate) fn max_address(&self) -> Option<usize> {
    self
      .buckets
      .iter()
      .filter_map(|bucket| {
        bucket.indices.len().checked_sub(1).map(|last| self.base + last)
      })
      .max()
  }

  #[inline]
  pub fn get(&self, index: usize) -> Option<MemoryEntryRef<'_, F>> {
    if index >= self.slots.len() {
      return None;
    }
    let slot = *self.slots.at(index);
    let type_id = slot.type_id as usize;
    let (ty, _) = &self.types[type_id];
    let bucket = &self.buckets[self.type_buckets[type_id]];
    let offset = slot.offset as usize;
    Some(MemoryEntryRef {
      address: self.base + offset,
      cell: CellRef { r#type: ty, value: bucket.words.row(offset) },
      multiplicity: *bucket.counts.at(offset),
    })
  }

  pub fn iter(&self) -> impl ExactSizeIterator<Item = MemoryEntryRef<'_, F>> {
    (0..self.len()).map(|i| self.get(i).unwrap())
  }

  #[inline]
  pub(crate) fn index_for_type(
    &self,
    type_id: usize,
    address: usize,
  ) -> Option<usize> {
    let offset = address.checked_sub(self.base)?;
    let bucket = &self.buckets[self.type_buckets[type_id]];
    (offset < bucket.indices.len()).then(|| *bucket.indices.at(offset) as usize)
  }

  pub fn get_by_width(
    &self,
    width: usize,
    address: usize,
  ) -> Option<MemoryEntryRef<'_, F>> {
    let bucket_id = self.widths.binary_search(&width).ok()?;
    let offset = address.checked_sub(self.base)?;
    let bucket = &self.buckets[bucket_id];
    if offset >= bucket.indices.len() {
      return None;
    }
    self.get(*bucket.indices.at(offset) as usize)
  }

  /// Cells of `width` in consecutive width-local address order.
  #[cfg(feature = "stark")]
  pub(crate) fn width_cells(&self, width: usize) -> WidthCells<'_, F> {
    let bucket =
      self.widths.binary_search(&width).ok().map(|i| &self.buckets[i]);
    WidthCells { base: self.base, bucket }
  }

  #[inline]
  pub(crate) fn address(&self, index: usize) -> usize {
    self.base + self.slots.at(index).offset as usize
  }

  #[inline]
  fn matches(&self, bucket_id: usize, offset: usize, words: &[F]) -> bool {
    let bucket = &self.buckets[bucket_id];
    offset < bucket.words.len() && bucket.words.row(offset) == words
  }

  // Keep this in the store/population hot loops, as QueryTable::lookup does.
  // Otherwise returning the hash plus an optional offset spills to the stack.
  #[inline(always)]
  fn lookup(&self, bucket_id: usize, words: &[F]) -> (u64, Option<usize>) {
    let mut hasher = rustc_hash::FxHasher::default();
    hasher.write_usize(words.len());
    for word in words {
      word.hash(&mut hasher);
    }
    let hash = hasher.finish();
    let offset = self
      .index
      .find(tag(hash), |offset| self.matches(bucket_id, offset as usize, words))
      .map(|offset| offset as usize);
    (hash, offset)
  }

  #[inline]
  pub(crate) fn address_of(&self, words: &[F]) -> Option<usize> {
    let bucket_id = self.widths.binary_search(&words.len()).ok()?;
    self.lookup(bucket_id, words).1.map(|offset| self.base + offset)
  }

  /// The only insertion path: equal encodings share one cell, regardless of
  /// nominal type, and each width's addresses form a consecutive prefix.
  #[inline]
  pub(crate) fn intern(
    &mut self,
    type_id: usize,
    words: &[F],
    modulus: u64,
  ) -> Result<usize, crate::budget::StorageError> {
    debug_assert_eq!(words.len(), self.types[type_id].1);
    let bucket_id = self.type_buckets[type_id];
    let (hash, found) = self.lookup(bucket_id, words);
    if let Some(offset) = found {
      return Ok(*self.buckets[bucket_id].indices.at(offset) as usize);
    }
    let index = self.slots.len();
    let entry = self.budget.row(
      index,
      size_of_val(words)
        + size_of::<Slot>()
        + size_of::<u32>()
        + size_of::<u64>(),
    )?;
    let bucket = &mut self.buckets[bucket_id];
    let offset = bucket.indices.len();
    let offset_u32 = self
      .budget
      .row(offset, size_of_val(words) + size_of::<u32>() + size_of::<u64>())?;
    let address =
      self.base.checked_add(offset).ok_or("ROM address overflow")?;
    if u64::try_from(address).ok().ok_or("ROM address overflow")?
      >= modulus.min(self.end)
    {
      return Err("ROM exceeds field capacity".into());
    }
    bucket.words.reserve(&self.budget)?;
    bucket.indices.reserve(&self.budget)?;
    bucket.counts.reserve(&self.budget)?;
    self.slots.reserve(&self.budget)?;
    self.budget.index(self.index.growth())?;
    self.index.insert(tag(hash), offset_u32);
    bucket.words.push(words);
    bucket.indices.push(&[entry]);
    bucket.counts.push(&[0]);
    #[allow(clippy::cast_possible_truncation)]
    // type_id comes from the bytecode type table
    self.slots.push(&[Slot { offset: offset_u32, type_id: type_id as u32 }]);
    self.type_used[type_id] = true;
    Ok(index)
  }

  #[inline]
  pub(crate) fn multiplicity_mut(&mut self, index: usize) -> &mut u64 {
    let slot = *self.slots.at(index);
    let bucket = &mut self.buckets[self.type_buckets[slot.type_id as usize]];
    bucket.counts.at_mut(slot.offset as usize)
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
      let index = memory.intern(0, &[1023 - value], 65537).unwrap();
      assert_eq!(memory.intern(1, &[1023 - value], 65537).unwrap(), index);
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
