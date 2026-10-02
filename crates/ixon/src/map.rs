//! Map type used by `Env`.
//!
//! On host, this is `dashmap::DashMap` — concurrent reads/writes for the
//! parallel ingress path. On `riscv64`, `DashMap` pulls in `parking_lot_core`,
//! whose `HashTable::new` calls `Instant::now()` (unavailable in guest
//! standard libraries). Instead, alias to a thin single-threaded wrapper around
//! `rustc_hash::FxHashMap` that mirrors the subset of DashMap's API used here.
//!
//! Both hash with `FxBuildHasher`: every key is an `Address` or a `Name`,
//! whose `Hash` feeds 32 blake3 bytes, so the default SipHash buys nothing
//! but cost. Construct with `IxonMap::default()` (`DashMap::new` exists
//! only for the default hasher). Iteration order is unspecified either way
//! and nothing may depend on it (the serializer puts every section in a
//! canonical order of its own).

#[cfg(not(target_arch = "riscv64"))]
pub type IxonMap<K, V> = dashmap::DashMap<K, V, rustc_hash::FxBuildHasher>;

#[cfg(target_arch = "riscv64")]
pub use riscv_impl::IxonMap;

#[cfg(target_arch = "riscv64")]
mod riscv_impl {
  use std::collections::hash_map;
  use std::hash::Hash;
  use std::ops::Deref;

  use rustc_hash::FxHashMap;

  #[derive(Debug, Clone)]
  pub struct IxonMap<K, V>(FxHashMap<K, V>);

  impl<K, V> Default for IxonMap<K, V> {
    fn default() -> Self {
      Self(FxHashMap::default())
    }
  }

  impl<K: Eq + Hash, V> IxonMap<K, V> {
    pub fn new() -> Self {
      Self::default()
    }

    pub fn len(&self) -> usize {
      self.0.len()
    }

    pub fn is_empty(&self) -> bool {
      self.0.is_empty()
    }

    pub fn contains_key(&self, k: &K) -> bool {
      self.0.contains_key(k)
    }

    pub fn insert(&mut self, k: K, v: V) -> Option<V> {
      self.0.insert(k, v)
    }

    pub fn clear(&mut self) {
      self.0.clear();
    }

    pub fn get(&self, k: &K) -> Option<MapRef<'_, K, V>> {
      self.0.get_key_value(k).map(|(k, v)| MapRef { k, v })
    }

    pub fn get_mut(&mut self, k: &K) -> Option<&mut V> {
      self.0.get_mut(k)
    }

    pub fn iter(&self) -> Iter<'_, K, V> {
      Iter(self.0.iter())
    }
  }

  /// Read guard exposing DashMap's `key()` / `value()` shape.
  pub struct MapRef<'a, K, V> {
    k: &'a K,
    v: &'a V,
  }

  impl<'a, K, V> MapRef<'a, K, V> {
    pub fn key(&self) -> &K {
      self.k
    }

    pub fn value(&self) -> &V {
      self.v
    }
  }

  impl<'a, K, V> Deref for MapRef<'a, K, V> {
    type Target = V;
    fn deref(&self) -> &V {
      self.v
    }
  }

  pub struct Iter<'a, K, V>(hash_map::Iter<'a, K, V>);

  impl<'a, K, V> Iterator for Iter<'a, K, V> {
    type Item = MapRef<'a, K, V>;
    fn next(&mut self) -> Option<Self::Item> {
      self.0.next().map(|(k, v)| MapRef { k, v })
    }
  }
}
