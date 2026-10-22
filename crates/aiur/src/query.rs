//! Fixed-width query storage, indexed independently for each callable. Keys and
//! outputs live in flat arenas; hash buckets contain stable row numbers. No
//! pointer into a hash table is held while recursive calls can grow it.
use crate::execute::QueryInput;
use crate::field::{FieldBackend, PrimeField};
use hashbrown::HashTable;
use serde::Serialize;
use std::hash::{Hash, Hasher};

// Arity belongs to the table. Hash field elements rather than their raw memory
// so equal field values always share a key, even with redundant representations.
#[inline]
pub(crate) fn hash_words<F: Hash>(words: &[F]) -> u64 {
  let mut hash = rustc_hash::FxHasher::default();
  for word in words {
    word.hash(&mut hash);
  }
  hash.finish()
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize)]
pub struct QueryInputRef<'a, F = u64> {
  pub function: usize,
  pub args: &'a [F],
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
pub struct QueryOutputRef<'a, F = u64> {
  pub output: &'a [F],
  pub multiplicity: u64,
}

#[derive(Clone, Debug)]
pub(crate) struct QueryTable<B: FieldBackend = PrimeField> {
  field: B,
  pub(crate) static_map: Option<crate::maps::MapRecord<B>>,
  input_width: usize,
  output_width: usize,
  stride: usize,
  rows: Vec<Vec<B::Element>>,
  counts: Vec<u64>,
  chunk_shift: u32,
  chunk_mask: usize,
  hashes: Vec<u64>,
  index: HashTable<usize>,
  // A bounded front index for dense unary keys (especially ROM addresses).
  // Sparse or large keys still use the exact hash index. Entries are row IDs,
  // including pending rows, so this cannot bypass cycle detection.
  dense_index: Vec<usize>,
}

impl<B: FieldBackend> QueryTable<B> {
  fn new(input_width: usize, output_width: usize, field: B) -> Self {
    let stride = input_width + output_width;
    // At most 4096 rows / 512 KiB per chunk (one full row if wider).
    let chunk_shift =
      (524288 / std::mem::size_of::<B::Element>().max(1) / stride.max(1))
        .max(1)
        .ilog2()
        .min(12);
    Self {
      field,
      counts: vec![],
      static_map: None,
      input_width,
      output_width,
      stride,
      chunk_shift,
      chunk_mask: (1 << chunk_shift) - 1,
      rows: vec![],
      hashes: vec![],
      index: HashTable::new(),
      dense_index: vec![],
    }
  }

  #[inline(always)]
  fn row(&self, row: usize) -> &[B::Element] {
    let start = (row & self.chunk_mask) * self.stride;
    &self.rows[row >> self.chunk_shift][start..start + self.stride]
  }

  #[inline(always)]
  fn row_mut(&mut self, row: usize) -> &mut [B::Element] {
    let start = (row & self.chunk_mask) * self.stride;
    &mut self.rows[row >> self.chunk_shift][start..start + self.stride]
  }

  #[inline(always)]
  pub(crate) fn input(&self, row: usize) -> &[B::Element] {
    if let Some(map) = &self.static_map {
      return map.binding.input(row);
    }
    &self.row(row)[..self.input_width]
  }

  #[inline(always)]
  pub(crate) fn output(&self, row: usize) -> QueryOutputRef<'_, B::Element> {
    if let Some(map) = &self.static_map {
      return QueryOutputRef {
        output: map.binding.output(row),
        multiplicity: map.counts[row],
      };
    }
    let values = self.row(row);
    QueryOutputRef {
      output: &values[self.input_width..self.input_width + self.output_width],
      multiplicity: self.counts[row],
    }
  }

  #[inline(always)]
  pub(crate) fn lookup(&self, args: &[B::Element]) -> (u64, Option<usize>) {
    debug_assert!(
      self.static_map.is_none(),
      "static maps use their prepared row index"
    );
    let hash = hash_words(args);
    if let [key] = args
      && self.input_width == 1
      && let Ok(key) = usize::try_from(self.field.to_u64(*key))
      && let Some(&row) = self.dense_index.get(key)
      && row != usize::MAX
    {
      return (hash, Some(row));
    }
    (hash, self.index.find(hash, |&row| self.input(row) == args).copied())
  }

  /// A zero count marks a pending query, which must never supply an output.
  #[inline(always)]
  pub(crate) fn start(&mut self, args: &[B::Element], hash: u64) -> usize {
    debug_assert!(self.static_map.is_none());
    debug_assert_eq!(args.len(), self.input_width);
    let row = self.len();
    if row & self.chunk_mask == 0 {
      self.rows.push(Vec::with_capacity(self.stride * (self.chunk_mask + 1)));
    }
    let values = self.rows.last_mut().unwrap();
    values.extend_from_slice(args);
    values.resize(values.len() + self.output_width, self.field.zero());
    self.counts.push(0);
    self.hashes.push(hash);
    let hashes = &self.hashes;
    self.index.insert_unique(hash, row, |&row| hashes[row]);
    if let [key] = args
      && let Ok(key) = usize::try_from(self.field.to_u64(*key))
    {
      // Bound space by observed table size, with a small startup allowance
      // and an absolute 8 MiB ceiling on 64-bit hosts. Never allocate in
      // proportion to an arbitrary field element supplied as a key.
      let limit = row.saturating_mul(2).clamp(64, 1 << 20);
      if key < limit {
        if key >= self.dense_index.len() {
          self
            .dense_index
            .resize((key + 1).next_power_of_two().min(limit), usize::MAX);
        }
        self.dense_index[key] = row;
      }
    }
    row
  }

  #[inline(always)]
  pub(crate) fn finish(&mut self, row: usize, output: &[B::Element]) {
    debug_assert_eq!(self.count(row), 0);
    let start = self.input_width;
    let end = start + self.output_width;
    let values = self.row_mut(row);
    values[start..end].copy_from_slice(output);
    self.counts[row] = 1;
  }

  #[inline(always)]
  pub(crate) fn count(&self, row: usize) -> u64 {
    if let Some(map) = &self.static_map {
      return map.counts[row];
    }
    self.counts[row]
  }

  /// Number of stored slots. Fixed tables include rows with zero uses.
  pub(crate) fn len(&self) -> usize {
    if let Some(map) = &self.static_map {
      return map.counts.len();
    }
    self.hashes.len()
  }

  pub(crate) fn widths(&self) -> (usize, usize) {
    (self.input_width, self.output_width)
  }

  #[inline(always)]
  pub(crate) fn bump(&mut self, row: usize) -> Option<()> {
    if let Some(map) = &mut self.static_map {
      let count = &mut map.counts[row];
      *count = count.checked_add(1)?;
      return Some(());
    }
    let count = &mut self.counts[row];
    *count = count.checked_add(1)?;
    Some(())
  }
}

/// Read-only views of completed function queries and fixed-table row counts.
/// Map views borrow canonical inputs/results from the original tables; native
/// candidate results are checked by the caller circuits, not retained here.
/// Iteration allocates nothing and omits unused fixed-table rows. Query order
/// is unspecified for both functions and tables; it has no semantic meaning.
#[derive(Clone, Debug)]
pub struct QueryMap<B: FieldBackend = PrimeField> {
  pub(crate) tables: Vec<QueryTable<B>>,
}

impl<B: FieldBackend> QueryMap<B> {
  pub(crate) fn new(
    widths: impl Iterator<Item = (usize, usize)>,
    field: B,
  ) -> Self {
    Self { tables: widths.map(|(a, b)| QueryTable::new(a, b, field)).collect() }
  }
  pub fn len(&self) -> usize {
    self
      .tables
      .iter()
      .map(|table| match &table.static_map {
        Some(map) => map.counts.iter().filter(|&&count| count != 0).count(),
        None => table.len(),
      })
      .sum()
  }
  pub fn is_empty(&self) -> bool {
    self.tables.iter().all(|table| match &table.static_map {
      Some(map) => map.counts.iter().all(|&count| count == 0),
      None => table.len() == 0,
    })
  }
  pub fn get(
    &self,
    key: &QueryInput<B::Element>,
  ) -> Option<QueryOutputRef<'_, B::Element>> {
    self.get_ref(key.function, &key.args)
  }
  fn get_ref(
    &self,
    function: usize,
    args: &[B::Element],
  ) -> Option<QueryOutputRef<'_, B::Element>> {
    let table = self.tables.get(function)?;
    if let Some(map) = &table.static_map {
      let row = map.binding.row(args).ok()?;
      let multiplicity = *map.counts.get(row)?;
      return (multiplicity != 0).then(|| QueryOutputRef {
        output: map.binding.output(row),
        multiplicity,
      });
    }
    table.lookup(args).1.map(|row| table.output(row))
  }
  pub(crate) fn bind_maps(
    &mut self,
    maps: &[std::sync::Arc<crate::maps::PreparedMap<B>>],
  ) {
    let offset = self.tables.len() - maps.len();
    for (table, binding) in self.tables[offset..].iter_mut().zip(maps) {
      table.static_map = Some(crate::maps::MapRecord::new(binding.clone()));
    }
  }
  pub fn iter(
    &self,
  ) -> impl Iterator<
    Item = (QueryInputRef<'_, B::Element>, QueryOutputRef<'_, B::Element>),
  > {
    self.tables.iter().enumerate().flat_map(|(function, table)| {
      (0..table.len())
        .filter(move |&row| table.static_map.is_none() || table.count(row) != 0)
        .map(move |row| {
          (
            QueryInputRef { function, args: table.input(row) },
            table.output(row),
          )
        })
    })
  }
  pub fn keys(&self) -> impl Iterator<Item = QueryInputRef<'_, B::Element>> {
    self.iter().map(|(key, _)| key)
  }
  pub fn values(&self) -> impl Iterator<Item = QueryOutputRef<'_, B::Element>> {
    self.iter().map(|(_, output)| output)
  }
}

impl<B: FieldBackend> PartialEq for QueryMap<B> {
  fn eq(&self, other: &Self) -> bool {
    self.len() == other.len()
      && self.iter().all(|(key, value)| {
        other.get_ref(key.function, key.args) == Some(value)
      })
  }
}
impl<B: FieldBackend> Eq for QueryMap<B> {}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn fixed_tables_skip_unused_rows_and_compare_without_query_order() {
    let field = PrimeField::new(97).unwrap();
    let program: crate::Program = serde_json::from_value(serde_json::json!({
            "version": 1, "modulus": 97, "enums": [], "functions": [], "entries": [],
            "maps": [{"name": "id", "params": [{"kind": "field"}],
                "result": {"kind": "tuple", "items": [{"kind": "field"}]},
                "input": 0, "output": 0}],
            "tables": [{"name": "values", "type": {"kind": "tuple", "items": [{"kind": "field"}]},
                "rows": [[2], [0], [1]]}]
        }))
        .unwrap();
    let program = program.check().unwrap();
    let bindings = crate::maps::MapOverrides::new().bind(&program).unwrap();
    let mut queries = QueryMap::new([(1, 1)].into_iter(), field);
    queries.bind_maps(&bindings);
    assert!(queries.is_empty());
    assert_eq!(queries.len(), 0);
    assert_eq!(queries.iter().count(), 0);
    let mut reordered = queries.clone();
    for (record, order) in
      [(&mut queries, [1, 2, 1]), (&mut reordered, [2, 1, 1])]
    {
      for input in order {
        record.tables[0]
          .static_map
          .as_mut()
          .unwrap()
          .call(&[input], &mut [0])
          .unwrap();
      }
    }
    assert_eq!(queries, reordered);
    assert!(!queries.is_empty());
    assert_eq!(queries.len(), 2);
    assert_eq!(queries.iter().count(), 2);
    assert!(queries.get_ref(0, &[0]).is_none());
    assert_eq!(queries.get_ref(0, &[1]).unwrap().multiplicity, 2);
    assert_eq!(queries.get_ref(0, &[2]).unwrap().multiplicity, 1);
    assert!(queries.values().all(|value| value.multiplicity != 0));
  }

  #[test]
  fn dense_front_index_keeps_sparse_keys_and_arity_checks() {
    let mut table = QueryTable::new(1, 1, PrimeField::new(97).unwrap());
    let early = table.start(&[80], table.lookup(&[80]).0);
    table.finish(early, &[5]);
    let large = table.start(&[u64::MAX], table.lookup(&[u64::MAX]).0);
    table.finish(large, &[6]);
    for key in 0..200 {
      if key != 80 {
        let row = table.start(&[key], table.lookup(&[key]).0);
        table.finish(row, &[key]);
      }
    }
    assert_eq!(table.lookup(&[80]).1, Some(early));
    assert_eq!(table.lookup(&[u64::MAX]).1, Some(large));
    assert!(table.lookup(&[0, 1]).1.is_none());
    assert!(table.lookup(&[]).1.is_none());
    assert!(table.dense_index.len() <= 2 * table.len());
  }

  #[test]
  fn pending_rows_survive_growth_and_counts_do_not_wrap() {
    let mut table = QueryTable::new(1, 1, PrimeField::new(97).unwrap());
    let first = table.start(&[0], table.lookup(&[0]).0);
    for i in 1..10_000 {
      let (hash, found) = table.lookup(&[i]);
      assert!(found.is_none());
      let row = table.start(&[i], hash);
      table.finish(row, &[i + 1]);
    }
    assert_eq!(table.lookup(&[0]).1, Some(first));
    assert_eq!(table.count(first), 0);
    table.finish(first, &[42]);
    assert_eq!(table.output(first).output, [42]);
    table.counts[first] = u64::MAX;
    assert_eq!(table.bump(first), None);
    assert_eq!(table.count(first), u64::MAX);
  }
}
