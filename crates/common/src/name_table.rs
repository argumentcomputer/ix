//! Generated-name tables with confirmed structural lookup.
//! Cached digests select candidates; they never establish name equality.

use crate::env::Name;
use blake3::Hash;
use rustc_hash::FxHashMap;

/// The shared cache-insensitive name relation. Its implementation lives on Name.
pub fn name_eq(a: &Name, b: &Name) -> bool {
  a.same_structure(b)
}

/// Generated-name lookup with exactly the structural name equality used
/// by Lean. Derived `Name::eq` also compares cached fields and is not this
/// relation, even for a constructor-built name above a rehashed prefix.
#[derive(Clone)]
pub struct NameTable<T> {
  entries: Vec<(Name, T)>,
  cache: FxHashMap<Hash, usize>,
}

impl<T> Default for NameTable<T> {
  fn default() -> Self {
    Self { entries: Vec::new(), cache: FxHashMap::default() }
  }
}

impl<T> NameTable<T> {
  pub fn with_capacity(capacity: usize) -> Self {
    Self { entries: Vec::with_capacity(capacity), cache: FxHashMap::default() }
  }

  pub fn get(&self, name: &Name) -> Option<&T> {
    if let Some(&index) = self.cache.get(name.get_hash())
      && let Some((stored, value)) = self.entries.get(index)
      && name_eq(stored, name)
    {
      return Some(value);
    }
    self
      .entries
      .iter()
      .rev()
      .find_map(|(stored, value)| name_eq(stored, name).then_some(value))
  }

  pub fn contains(&self, name: &Name) -> bool {
    self.get(name).is_some()
  }

  pub fn contains_key(&self, name: &Name) -> bool {
    self.contains(name)
  }

  pub fn insert(&mut self, name: Name, value: T) {
    if self.get(&name).is_some() {
      self.entries.retain(|(stored, _)| !name_eq(stored, &name));
      self.cache.clear();
    }
    self.cache.insert(*name.get_hash(), self.entries.len());
    self.entries.push((name, value));
  }

  pub fn is_empty(&self) -> bool {
    self.entries.is_empty()
  }
  pub fn len(&self) -> usize {
    self.entries.len()
  }
  pub fn iter(&self) -> std::iter::Rev<std::slice::Iter<'_, (Name, T)>> {
    self.entries.iter().rev()
  }
}

impl<'a, T> IntoIterator for &'a NameTable<T> {
  type Item = &'a (Name, T);
  type IntoIter = std::iter::Rev<std::slice::Iter<'a, (Name, T)>>;
  fn into_iter(self) -> Self::IntoIter {
    self.iter()
  }
}

impl<T> FromIterator<(Name, T)> for NameTable<T> {
  fn from_iter<I: IntoIterator<Item = (Name, T)>>(iter: I) -> Self {
    let mut table = Self::default();
    for (name, value) in iter {
      table.insert(name, value);
    }
    table
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::env::NameData;
  use std::sync::Arc;

  fn name(text: &str) -> Name {
    Name::str(Name::anon(), text.into())
  }

  #[test]
  fn last_write_and_forged_bucket_keep_structural_keys() {
    let original = name("x");
    let other_cache = Name(Arc::new(NameData::Str(
      Name(Arc::new(NameData::Anonymous(blake3::hash(b"prefix")))),
      "x".into(),
      blake3::hash(b"other leaf cache"),
    )));
    assert!(name_eq(&original, &other_cache));
    assert_ne!(original, other_cache);
    let collision = Name(Arc::new(NameData::Str(
      Name::anon(),
      "y".into(),
      *other_cache.get_hash(),
    )));
    assert!(!name_eq(&original, &collision));
    for capacity in [0, 1, 32] {
      let mut table = NameTable::with_capacity(capacity);
      table.insert(original.clone(), 0);
      table.insert(other_cache.clone(), 1);
      assert_eq!(table.len(), 1);
      assert_eq!(table.get(&original), Some(&1));
      assert_eq!(table.get(&name("x")), Some(&1));
      table.insert(collision.clone(), 2);
      assert_eq!(table.get(&original), Some(&1));
      assert_eq!(table.get(&other_cache), Some(&1));
      assert_eq!(table.get(&collision), Some(&2));
      assert_eq!(table.get(&name("y")), Some(&2));
      assert_eq!(table.len(), 2);
      table.insert(original.clone(), 3);
      assert_eq!(table.get(&other_cache), Some(&3));
      assert_eq!(table.get(&collision), Some(&2));
      let order: Vec<_> = table.iter().map(|(_, value)| *value).collect();
      assert_eq!(order, [3, 2]);
    }
  }

  #[test]
  fn forward_collection_preserves_last_structural_position() {
    let x = name("x");
    let x_other = Name(Arc::new(NameData::Str(
      Name::anon(),
      "x".into(),
      blake3::hash(b"changed cache"),
    )));
    let table: NameTable<_> =
      [(x.clone(), 0), (name("y"), 1), (x_other, 2)].into_iter().collect();
    assert_eq!(table.get(&x), Some(&2));
    assert_eq!(table.get(&name("y")), Some(&1));
    assert_eq!(table.get(&name("absent")), None);
    assert_eq!(table.len(), 2);
  }
}
