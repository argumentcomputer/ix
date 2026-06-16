use multi_stark::p3_field::PrimeField64;

use crate::aiur::G;

/// Immutable view of one query entry.
#[derive(Clone, Copy)]
pub struct QueryRef<'a> {
  pub(crate) output: &'a [G],
  pub(crate) multiplicity: G,
}

/// Mutable view of one query entry: the output is fixed at insertion,
/// only the multiplicity is bumped on memo hits.
pub struct QueryRefMut<'a> {
  pub(crate) output: &'a [G],
  pub(crate) multiplicity: &'a mut G,
}

fn hash_g_slice(key: &[G]) -> u64 {
  use std::hash::Hasher;
  let mut h = rustc_hash::FxHasher::default();
  for g in key {
    h.write_u64(g.as_canonical_u64());
  }
  h.finish()
}

/// Append-only query store with a hash index.
///
/// Functionally the insertion-ordered map `args -> (output, multiplicity)`
/// it replaces (`FxIndexMap<Vec<G>, QueryResult>`) — but every circuit has
/// a FIXED key arity and output width, so keys and outputs live in flat
/// `Vec<G>` arenas addressed by entry index, and the hash table holds only
/// `u32` indices. This cuts per-entry overhead from ~130 B (two heap
/// `Vec`s + IndexMap bucket + allocator metadata) to the raw field
/// elements plus ~13 B of index. The record IS the proof witness, so
/// entries cannot be dropped — only stored compactly; on kernel-heavy
/// executions it is the dominant RAM consumer (billions of entries).
///
/// Entry index == insertion order; memory circuits use it as the pointer
/// value, mirroring the old `IndexMap::get_index_of` semantics.
pub struct QueryMap {
  key_stride: usize,
  /// Output width; inferred on first insert (not statically available in
  /// `FunctionLayout`).
  out_stride: usize,
  keys: Vec<G>,
  outs: Vec<G>,
  mults: Vec<G>,
  table: hashbrown::HashTable<u32>,
}

impl QueryMap {
  pub fn new(key_stride: usize) -> Self {
    Self {
      key_stride,
      out_stride: 0,
      keys: Vec::new(),
      outs: Vec::new(),
      mults: Vec::new(),
      table: hashbrown::HashTable::new(),
    }
  }

  #[inline]
  pub fn len(&self) -> usize {
    self.mults.len()
  }

  #[inline]
  pub fn is_empty(&self) -> bool {
    self.mults.is_empty()
  }

  /// Total retained field elements (keys + outputs); used by the
  /// `IX_AIUR_QUERY_STATS` RAM-attribution dump.
  pub fn retained_elems(&self) -> usize {
    self.keys.len() + self.outs.len()
  }

  #[inline]
  fn key_at(&self, i: usize) -> &[G] {
    &self.keys[i * self.key_stride..(i + 1) * self.key_stride]
  }

  #[inline]
  fn out_at(&self, i: usize) -> &[G] {
    &self.outs[i * self.out_stride..(i + 1) * self.out_stride]
  }

  pub fn get_index_of(&self, key: &[G]) -> Option<usize> {
    debug_assert_eq!(key.len(), self.key_stride);
    let hash = hash_g_slice(key);
    self
      .table
      .find(hash, |&i| self.key_at(i as usize) == key)
      .map(|&i| i as usize)
  }

  pub fn get(&self, key: &[G]) -> Option<QueryRef<'_>> {
    let i = self.get_index_of(key)?;
    Some(QueryRef { output: self.out_at(i), multiplicity: self.mults[i] })
  }

  pub fn get_mut(&mut self, key: &[G]) -> Option<QueryRefMut<'_>> {
    let i = self.get_index_of(key)?;
    let output = &self.outs[i * self.out_stride..(i + 1) * self.out_stride];
    Some(QueryRefMut { output, multiplicity: &mut self.mults[i] })
  }

  /// Append a new entry. The key must not already be present: call sites
  /// only insert on a confirmed miss, and a same-key re-entrant call
  /// would loop forever before reaching its own insert.
  pub fn insert(&mut self, key: &[G], output: &[G], multiplicity: G) {
    debug_assert_eq!(key.len(), self.key_stride);
    debug_assert!(self.get_index_of(key).is_none());
    if self.mults.is_empty() {
      self.out_stride = output.len();
    } else {
      debug_assert_eq!(output.len(), self.out_stride);
    }
    let hash = hash_g_slice(key);
    let i = u32::try_from(self.mults.len()).expect("query map overflow");
    self.keys.extend_from_slice(key);
    self.outs.extend_from_slice(output);
    self.mults.push(multiplicity);
    let keys = &self.keys;
    let stride = self.key_stride;
    self.table.insert_unique(hash, i, |&j| {
      let j = j as usize;
      hash_g_slice(&keys[j * stride..(j + 1) * stride])
    });
  }

  /// Entry at insertion index `i`: the key slice plus a mutable handle on
  /// the multiplicity (memory `Load` bumps the pointed-to row's count).
  pub fn get_index_mut(&mut self, i: usize) -> Option<(&[G], &mut G)> {
    if i >= self.mults.len() {
      return None;
    }
    let key = &self.keys[i * self.key_stride..(i + 1) * self.key_stride];
    Some((key, &mut self.mults[i]))
  }

  pub fn get_index(&self, i: usize) -> Option<(&[G], QueryRef<'_>)> {
    if i >= self.len() {
      return None;
    }
    Some((
      self.key_at(i),
      QueryRef { output: self.out_at(i), multiplicity: self.mults[i] },
    ))
  }

  pub fn iter(&self) -> impl Iterator<Item = (&[G], QueryRef<'_>)> {
    (0..self.len()).map(|i| {
      (
        self.key_at(i),
        QueryRef { output: self.out_at(i), multiplicity: self.mults[i] },
      )
    })
  }
}
