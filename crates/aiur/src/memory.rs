//! Width-local, interned ROM. The record has stable indices for accounting;
//! pointers are indices within a width bucket. A representative store type is
//! retained only for host diagnostics, never for interning or circuit lookups.
use crate::bytecode::Type;
use hashbrown::HashTable;
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

#[derive(Clone, Debug)]
struct Slot {
  address: usize,
  type_id: usize,
  offset: usize,
  multiplicity: u64,
}

#[derive(Clone, Debug)]
pub struct Memory<F = u64> {
  pub(crate) budget: crate::budget::Budget,
  base: usize,
  end: u64,
  types: Vec<(Type, usize)>,
  words: Vec<F>,
  slots: Vec<Slot>,
  widths: Vec<usize>,
  buckets: Vec<Vec<usize>>,
  type_buckets: Vec<usize>,
  // Stable record indices and cached hashes, with no second payload copy.
  // Retained after execution so trace population can resolve stores directly.
  index: HashTable<(u64, usize)>,
}

impl<F: Copy + Eq + Hash + Send + Sync> Memory<F> {
  pub(crate) fn new(types: impl Iterator<Item = (Type, usize)>) -> Self {
    let types: Vec<_> = types.collect();
    let mut widths: Vec<_> = types.iter().map(|(_, width)| *width).collect();
    widths.sort_unstable();
    widths.dedup();
    let type_buckets =
      types.iter().map(|(_, w)| widths.binary_search(w).unwrap()).collect();
    let buckets = vec![vec![]; widths.len()];
    Self {
      budget: Default::default(),
      base: 0,
      end: u64::MAX,
      types,
      words: vec![],
      slots: vec![],
      widths,
      buckets,
      type_buckets,
      index: HashTable::new(),
    }
  }

  pub fn len(&self) -> usize {
    self.slots.len()
  }
  pub fn is_empty(&self) -> bool {
    self.slots.is_empty()
  }

  pub(crate) fn set_range(
    &mut self,
    start: u64,
    end: u64,
  ) -> Result<(), &'static str> {
    if !self.is_empty() || start >= end {
      return Err("invalid empty ROM range");
    }
    self.base = usize::try_from(start).map_err(|_| "ROM base overflow")?;
    self.end = end;
    Ok(())
  }

  #[inline]
  pub fn get(&self, index: usize) -> Option<MemoryEntryRef<'_, F>> {
    let slot = self.slots.get(index)?;
    let (ty, width) = &self.types[slot.type_id];
    Some(MemoryEntryRef {
      address: slot.address,
      cell: CellRef {
        r#type: ty,
        value: &self.words[slot.offset..slot.offset + width],
      },
      multiplicity: slot.multiplicity,
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

  #[inline]
  pub(crate) fn index_for_type(
    &self,
    type_id: usize,
    address: usize,
  ) -> Option<usize> {
    self.buckets[self.type_buckets[type_id]]
      .get(address.checked_sub(self.base)?)
      .copied()
  }

  pub fn get_by_width(
    &self,
    width: usize,
    address: usize,
  ) -> Option<MemoryEntryRef<'_, F>> {
    let bucket = self.widths.binary_search(&width).ok()?;
    self.get(*self.buckets[bucket].get(address.checked_sub(self.base)?)?)
  }

  /// Record indices in consecutive width-local address order. The caller may
  /// have an unused circuit width absent from this execution's type layouts.
  #[cfg(feature = "stark")]
  pub(crate) fn indices_for_width(&self, width: usize) -> &[usize] {
    self.widths.binary_search(&width).map_or(&[], |i| &self.buckets[i])
  }

  #[inline]
  pub(crate) fn address(&self, index: usize) -> usize {
    self.slots[index].address
  }

  #[inline]
  fn matches(&self, index: usize, words: &[F]) -> bool {
    let slot = &self.slots[index];
    self.words[slot.offset..slot.offset + self.types[slot.type_id].1] == *words
  }

  // Keep this in the store/population hot loops, as QueryTable::lookup does.
  // Otherwise returning the hash plus an optional index spills to the stack.
  #[inline(always)]
  fn lookup(&self, words: &[F]) -> (u64, Option<usize>) {
    let mut hasher = rustc_hash::FxHasher::default();
    hasher.write_usize(words.len());
    for word in words {
      word.hash(&mut hasher);
    }
    let hash = hasher.finish();
    let index = self
      .index
      .find(hash, |&(cached, i)| cached == hash && self.matches(i, words));
    (hash, index.map(|&(_, i)| i))
  }

  #[inline]
  pub(crate) fn address_of(&self, words: &[F]) -> Option<usize> {
    self.lookup(words).1.map(|i| self.address(i))
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
    let (hash, found) = self.lookup(words);
    if let Some(index) = found {
      return Ok(index);
    }
    self.budget.vector(&self.words, words.len())?;
    self.budget.vector(&self.slots, 1)?;
    self
      .budget
      .hash::<(u64, usize)>(self.index.len(), self.index.capacity())?;
    let bucket = &mut self.buckets[self.type_buckets[type_id]];
    self.budget.vector(bucket, 1)?;
    let address =
      self.base.checked_add(bucket.len()).ok_or("ROM address overflow")?;
    if u64::try_from(address).map_err(|_| "ROM address overflow")?
      >= modulus.min(self.end)
    {
      return Err("ROM exceeds field capacity".into());
    }
    let index = self.slots.len();
    self.index.insert_unique(hash, (hash, index), |&(hash, _)| hash);
    let offset = self.words.len();
    self.words.extend_from_slice(words);
    bucket.push(index);
    self.slots.push(Slot { address, type_id, offset, multiplicity: 0 });
    Ok(index)
  }

  #[inline]
  pub(crate) fn multiplicity_mut(&mut self, address: usize) -> &mut u64 {
    &mut self.slots[address].multiplicity
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
    assert!(memory.matches(1, &[]));
    assert!(!memory.matches(1, &[7]));
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
