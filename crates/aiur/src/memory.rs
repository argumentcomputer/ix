//! Width-local, interned ROM. The record has stable indices for accounting;
//! pointers are indices within a width bucket. A representative store type is
//! retained only for host diagnostics, never for interning or circuit lookups.
use crate::bytecode::Type;
use serde::{Serialize, Serializer};

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
  types: Vec<(Type, usize)>,
  words: Vec<F>,
  slots: Vec<Slot>,
  widths: Vec<usize>,
  buckets: Vec<Vec<usize>>,
  type_buckets: Vec<usize>,
}

impl<F: Copy + Eq + Send + Sync> Memory<F> {
  pub(crate) fn new(types: impl Iterator<Item = (Type, usize)>) -> Self {
    let types: Vec<_> = types.collect();
    let mut widths: Vec<_> = types.iter().map(|(_, width)| *width).collect();
    widths.sort_unstable();
    widths.dedup();
    let type_buckets =
      types.iter().map(|(_, w)| widths.binary_search(w).unwrap()).collect();
    let buckets = vec![vec![]; widths.len()];
    Self { types, words: vec![], slots: vec![], widths, buckets, type_buckets }
  }

  pub fn len(&self) -> usize {
    self.slots.len()
  }
  pub fn is_empty(&self) -> bool {
    self.slots.is_empty()
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
    self.buckets[self.type_buckets[type_id]].get(address).copied()
  }

  pub fn get_by_width(
    &self,
    width: usize,
    address: usize,
  ) -> Option<MemoryEntryRef<'_, F>> {
    let bucket = self.widths.binary_search(&width).ok()?;
    self.get(*self.buckets[bucket].get(address)?)
  }

  pub(crate) fn next_address(&self, type_id: usize) -> usize {
    self.buckets[self.type_buckets[type_id]].len()
  }

  #[inline]
  pub(crate) fn address(&self, index: usize) -> usize {
    self.slots[index].address
  }

  #[inline]
  pub(crate) fn matches(&self, index: usize, words: &[F]) -> bool {
    let slot = &self.slots[index];
    self.words[slot.offset..slot.offset + self.types[slot.type_id].1] == *words
  }

  pub(crate) fn push(&mut self, type_id: usize, words: &[F]) {
    debug_assert_eq!(words.len(), self.types[type_id].1);
    let offset = self.words.len();
    self.words.extend_from_slice(words);
    let bucket = &mut self.buckets[self.type_buckets[type_id]];
    let address = bucket.len();
    bucket.push(self.slots.len());
    self.slots.push(Slot { address, type_id, offset, multiplicity: 0 });
  }

  #[inline]
  pub(crate) fn multiplicity_mut(&mut self, address: usize) -> &mut u64 {
    &mut self.slots[address].multiplicity
  }
}

impl<F: Copy + Eq + Send + Sync + Serialize> Serialize for Memory<F> {
  fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
    serializer.collect_seq(self.iter())
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::execute::{Cell, MemoryEntry};

  #[test]
  fn borrowed_cells_preserve_wire_format_and_zero_width_addresses() {
    let unit = Type::Tuple { items: vec![] };
    let mut memory =
      Memory::new([(Type::Field, 1), (unit.clone(), 0)].into_iter());
    memory.push(0, &[7]);
    memory.push(1, &[]);
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
