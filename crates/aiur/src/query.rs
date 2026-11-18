//! Fixed-width query storage, indexed independently for each callable. Keys and
//! outputs live in flat arenas; hash buckets contain stable row numbers. No
//! pointer into a hash table is held while recursive calls can grow it.
use crate::budget::StorageError;
use crate::chunks::Chunks;
use crate::execute::QueryInput;
use crate::field::{FieldBackend, PrimeField};
use crate::index::{RowIndex, tag};
use serde::Serialize;
use std::borrow::Cow;
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

/// A recorded query's key. `args` is borrowed when the table stores its
/// inputs as field elements and decoded when some are `u32` columns.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize)]
pub struct QueryInputRef<'a, F: Clone = u64> {
  pub function: usize,
  pub args: Cow<'a, [F]>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct QueryOutputRef<'a, F: Clone = u64> {
  pub output: Cow<'a, [F]>,
  pub multiplicity: u64,
}

/// Bytes of one storage chunk.
const CHUNK_BYTES: usize = 1 << 19;

/// Rows a storage chunk is sized for, below [`CHUNK_BYTES`]; the chunk's
/// bytes round up to a power of two, which may fit up to twice as many.
const CHUNK_ROWS: usize = 4096;

/// Why a value cannot be stored in a `u32` column.
pub(crate) const NARROW_OVERFLOW: &str =
  "pointer or enum tag value does not fit 32 bits";

/// A table's row storage, fixed by its function's types
/// ([`crate::bytecode::Layout::narrow_words`]). Pointers, enum tags and enum
/// payload words no constructor fills with a field element are `u32`
/// columns; every other column holds a field element.
///
/// A table with no `u32` column stores its rows as field elements. Any
/// other table packs each row into `u32` words: first the low 32 bits of
/// every column in row order (inputs, then outputs), then the high 32 bits
/// of each field-element column in the same order. A column is then read or
/// compared in one pass in row order, joining its low word with the high
/// word `high` locates (masked to zero for `u32` columns).
#[derive(Clone, Debug)]
struct Columns {
  packed: bool,
  // Each column's high word in a packed row and its mask: `u32::MAX` for a
  // field-element column, and for a `u32` column `0` (its slot is then any
  // valid one).
  high: Box<[(u32, u32)]>,
  // Words per packed row.
  words: usize,
}

impl Columns {
  fn new(narrow: &[bool]) -> Self {
    let stride = narrow.len();
    let mut next = stride;
    let high = narrow
      .iter()
      .map(|&narrow| {
        if narrow {
          (0, 0)
        } else {
          next += 1;
          (u32::try_from(next - 1).expect("row width fits u32"), u32::MAX)
        }
      })
      .collect();
    let packed = narrow.contains(&true);
    Self { packed, high, words: if packed { next } else { 0 } }
  }
}

/// A row's or a table's storage when it holds whole rows of `stride` words:
/// every column is a `u32`, or every column is a field element.
#[cfg(feature = "cuda")]
#[derive(Clone, Copy, Debug)]
pub(crate) enum Stored<'a, N: ?Sized, W: ?Sized> {
  Narrow(&'a N),
  Wide(&'a W),
  Mixed,
}

#[derive(Clone, Debug)]
pub(crate) struct QueryTable<B: FieldBackend = PrimeField> {
  field: B,
  pub(crate) static_map: Option<crate::maps::MapRecord<B>>,
  input_width: usize,
  output_width: usize,
  stride: usize,
  columns: Columns,
  // Packed rows, or rows of field elements when no column is a `u32`
  // ([`Columns`]); the other store has no columns.
  packed: Chunks<u32>,
  wide: Chunks<B::Element>,
  // Each row's multiplicity and, when tracked, its honest height (depth
  // pass), as `u32`s: a count fails loudly rather than wrap, and a height
  // saturates at `u32::MAX`, which record validation rejects.
  track_depth: bool,
  meta: Chunks<u32>,
  index: RowIndex,
  index_bytes: usize,
  // A bounded front index for dense unary keys (especially ROM addresses).
  // Sparse or large keys still use the exact hash index. Entries are row IDs,
  // including pending rows, so this cannot bypass cycle detection.
  dense_index: Vec<u32>,
  // Each row's references, when this function's rows record them.
  pub(crate) refs: Option<crate::refs::TableRefs>,
  // Storage drops before its reservation can admit another allocation.
  pub(crate) budget: crate::budget::Budget,
}

impl<B: FieldBackend> QueryTable<B> {
  /// A table of `input_width` inputs, then outputs, whose columns
  /// `narrow` marks hold values below 2^32.
  fn new(input_width: usize, narrow: &[bool], field: B) -> Self {
    fn store<T: Copy>(values: usize) -> Chunks<T> {
      let bytes = size_of::<T>().max(1);
      let chunk = (CHUNK_ROWS * values * bytes).next_power_of_two();
      Chunks::new(values, chunk.min(CHUNK_BYTES))
    }
    let stride = narrow.len();
    let columns = Columns::new(narrow);
    let wide = if columns.packed { 0 } else { stride };
    Self {
      budget: Default::default(),
      field,
      track_depth: false,
      meta: Chunks::new(1, CHUNK_BYTES),
      static_map: None,
      input_width,
      output_width: stride - input_width,
      stride,
      packed: store(columns.words),
      wide: store(wide),
      columns,
      index: RowIndex::default(),
      index_bytes: 0,
      dense_index: vec![],
      refs: None,
    }
  }

  /// A table whose columns all hold field elements.
  #[cfg(test)]
  fn wide(input_width: usize, output_width: usize, field: B) -> Self {
    Self::new(input_width, &vec![false; input_width + output_width], field)
  }

  #[inline(always)]
  fn rows_len(&self) -> usize {
    self.meta.len()
  }

  /// A stored row (inputs, then outputs), when it is stored whole.
  #[cfg(feature = "cuda")]
  #[inline(always)]
  pub(crate) fn stored(&self, row: usize) -> Stored<'_, [u32], [B::Element]> {
    if !self.columns.packed {
      Stored::Wide(self.wide.row(row))
    } else if self.columns.words == self.stride {
      Stored::Narrow(self.packed.row(row))
    } else {
      Stored::Mixed
    }
  }

  /// Recorded rows in storage order for bulk transfer, when stored whole:
  /// chunks of `rows_per_chunk` rows of `stride` words (inputs, then
  /// outputs). Static maps keep their rows elsewhere and have none here.
  #[cfg(feature = "cuda")]
  pub(crate) fn row_chunks(
    &self,
  ) -> (Stored<'_, [Vec<u32>], [Vec<B::Element>]>, usize, usize) {
    if !self.columns.packed {
      (
        Stored::Wide(self.wide.chunks()),
        self.stride,
        self.wide.rows_per_chunk(),
      )
    } else if self.columns.words == self.stride {
      (
        Stored::Narrow(self.packed.chunks()),
        self.stride,
        self.packed.rows_per_chunk(),
      )
    } else {
      (Stored::Mixed, self.stride, 0)
    }
  }

  /// Track rows' honest heights, from the first row on.
  fn set_track_depth(&mut self, track: bool) {
    debug_assert_eq!(self.rows_len(), 0);
    self.track_depth = track;
    self.meta = Chunks::new(1 + usize::from(track), CHUNK_BYTES);
  }

  /// Number of recorded row heights (`0` when heights are not tracked).
  pub(crate) fn depths_len(&self) -> usize {
    if self.track_depth && self.static_map.is_none() {
      self.meta.len()
    } else {
      0
    }
  }

  /// A row's honest height: the longest call path below it within its SCC
  /// (zero for untracked tables and static maps).
  #[inline(always)]
  pub(crate) fn depth(&self, row: usize) -> u64 {
    if !self.track_depth || row >= self.meta.len() {
      return 0;
    }
    u64::from(self.meta.row(row)[1])
  }

  #[inline(always)]
  pub(crate) fn set_depth(&mut self, row: usize, depth: u64) {
    if self.track_depth && row < self.meta.len() {
      self.meta.row_mut(row)[1] = u32::try_from(depth).unwrap_or(u32::MAX);
    }
  }

  /// The canonical values of packed `row`'s columns `start..start +
  /// out.len()`, mapped by `f` into `out`.
  #[inline(always)]
  fn unpack<T>(
    &self,
    row: usize,
    start: usize,
    out: &mut [T],
    f: impl Fn(u64) -> T,
  ) {
    let words = self.packed.row(row);
    let columns = start..start + out.len();
    let high = &self.columns.high[columns.clone()];
    for ((out, &low), &(slot, mask)) in
      out.iter_mut().zip(&words[columns]).zip(high)
    {
      *out = f(u64::from(low) | u64::from(words[slot as usize] & mask) << 32);
    }
  }

  /// Pack `values` into the pending last row's columns from `start` on.
  /// A value of 2^32 or more in a `u32` column is reported, and its high
  /// bits dropped.
  #[inline(always)]
  #[allow(clippy::cast_possible_truncation)] // Overflow is reported.
  fn pack(
    columns: &Columns,
    field: B,
    words: &mut [u32],
    start: usize,
    values: &[B::Element],
  ) -> Result<(), StorageError> {
    let mut overflow = 0;
    let high = &columns.high[start..start + values.len()];
    for ((&value, low), &(slot, mask)) in
      values.iter().zip(start..start + values.len()).zip(high)
    {
      let value = field
        .try_to_u64(value)
        .map_err(|_| StorageError::Invalid(NARROW_OVERFLOW))?;
      words[low] = value as u32;
      if mask == 0 {
        overflow |= value >> 32;
      } else {
        words[slot as usize] = (value >> 32) as u32;
      }
    }
    if overflow == 0 {
      Ok(())
    } else {
      Err(StorageError::Invalid(NARROW_OVERFLOW))
    }
  }

  /// Write `row`'s inputs, then its outputs, as canonical words into
  /// `out`, which is the table's stride long.
  #[cfg(feature = "cuda")]
  #[inline(always)]
  pub(crate) fn row_words(&self, row: usize, out: &mut [u64])
  where
    B: FieldBackend<Word = u64>,
  {
    debug_assert!(self.static_map.is_none());
    if self.columns.packed {
      self.unpack(row, 0, out, |value| value);
    } else {
      for (out, &value) in out.iter_mut().zip(self.wide.row(row)) {
        *out = self.field.to_u64(value);
      }
    }
  }

  /// Write `row`'s inputs, then its outputs, into `out`, which is the
  /// table's input and output widths long.
  #[inline(always)]
  pub(crate) fn read_row(&self, row: usize, out: &mut [B::Element]) {
    if let Some(map) = &self.static_map {
      let (input, output) = out.split_at_mut(self.input_width);
      input.copy_from_slice(map.binding.input(row));
      output.copy_from_slice(map.binding.output(row));
      return;
    }
    if self.columns.packed {
      let field = self.field;
      self.unpack(row, 0, out, |value| field.from_canonical_u64(value));
    } else {
      out.copy_from_slice(self.wide.row(row));
    }
  }

  /// Write `row`'s outputs into `out`, which is the output width long.
  #[inline(always)]
  pub(crate) fn read_output(&self, row: usize, out: &mut [B::Element]) {
    if let Some(map) = &self.static_map {
      out.copy_from_slice(map.binding.output(row));
      return;
    }
    if self.columns.packed {
      let field = self.field;
      self.unpack(row, self.input_width, out, |value| {
        field.from_canonical_u64(value)
      });
    } else {
      out.copy_from_slice(&self.wide.row(row)[self.input_width..]);
    }
  }

  /// `row`'s inputs, when stored as field elements (or held by a map).
  #[inline(always)]
  fn stored_input(&self, row: usize) -> Option<&[B::Element]> {
    if let Some(map) = &self.static_map {
      return Some(map.binding.input(row));
    }
    (!self.columns.packed).then(|| &self.wide.row(row)[..self.input_width])
  }

  /// `row`'s outputs, when stored as field elements (or held by a map).
  #[inline(always)]
  fn stored_output(&self, row: usize) -> Option<&[B::Element]> {
    if let Some(map) = &self.static_map {
      return Some(map.binding.output(row));
    }
    (!self.columns.packed).then(|| &self.wide.row(row)[self.input_width..])
  }

  /// `row`'s inputs, borrowed when stored as field elements and otherwise
  /// decoded into `buffer`.
  #[inline(always)]
  pub(crate) fn input_in<'a>(
    &'a self,
    row: usize,
    buffer: &'a mut Vec<B::Element>,
  ) -> &'a [B::Element] {
    if let Some(input) = self.stored_input(row) {
      return input;
    }
    let field = self.field;
    buffer.resize(self.input_width, field.zero());
    self.unpack(row, 0, buffer, |value| field.from_canonical_u64(value));
    buffer
  }

  /// `row`'s outputs, borrowed when stored as field elements and otherwise
  /// decoded into `buffer`.
  #[inline(always)]
  pub(crate) fn output_in<'a>(
    &'a self,
    row: usize,
    buffer: &'a mut Vec<B::Element>,
  ) -> &'a [B::Element] {
    if let Some(output) = self.stored_output(row) {
      return output;
    }
    let field = self.field;
    buffer.resize(self.output_width, field.zero());
    self.unpack(row, self.input_width, buffer, |value| {
      field.from_canonical_u64(value)
    });
    buffer
  }

  /// `row`'s inputs, decoded when packed.
  pub(crate) fn input(&self, row: usize) -> Cow<'_, [B::Element]> {
    match self.stored_input(row) {
      Some(input) => Cow::Borrowed(input),
      None => {
        let mut buffer = vec![];
        self.input_in(row, &mut buffer);
        Cow::Owned(buffer)
      },
    }
  }

  /// `row`'s outputs and count, decoded when packed.
  pub(crate) fn output(&self, row: usize) -> QueryOutputRef<'_, B::Element> {
    let multiplicity = self.count(row);
    let output = match self.stored_output(row) {
      Some(output) => Cow::Borrowed(output),
      None => {
        let mut buffer = vec![];
        self.output_in(row, &mut buffer);
        Cow::Owned(buffer)
      },
    };
    QueryOutputRef { output, multiplicity }
  }

  /// Whether stored `row`'s inputs equal `args`, which has the input width.
  /// An argument of 2^32 or more in a `u32` column matches no row, since
  /// its high word is compared with zero.
  #[inline(always)]
  #[allow(clippy::cast_possible_truncation)] // Both halves are compared.
  fn matches(&self, row: usize, args: &[B::Element]) -> bool {
    if !self.columns.packed {
      return self.wide.row(row)[..self.input_width] == *args;
    }
    let words = self.packed.row(row);
    let high = &self.columns.high[..args.len()];
    args.iter().zip(words).zip(high).fold(
      true,
      |equal, ((&arg, &low), &(slot, mask))| {
        // A value beyond 64 bits was never packed, so it matches no row.
        let Ok(value) = self.field.try_to_u64(arg) else {
          return false;
        };
        equal
          & (low == value as u32)
          & (words[slot as usize] & mask == (value >> 32) as u32)
      },
    )
  }

  #[inline(always)]
  pub(crate) fn lookup(&self, args: &[B::Element]) -> (u64, Option<usize>) {
    debug_assert!(
      self.static_map.is_none(),
      "static maps use their prepared row index"
    );
    let hash = hash_words(args);
    if args.len() != self.input_width {
      return (hash, None);
    }
    if let [key] = args
      && let Ok(key) = self.field.try_to_u64(*key)
      && let Ok(key) = usize::try_from(key)
      && let Some(&row) = self.dense_index.get(key)
      && row != u32::MAX
    {
      return (hash, Some(row as usize));
    }
    let found =
      self.index.find(tag(hash), |row| self.matches(row as usize, args));
    (hash, found.map(|row| row as usize))
  }

  /// Start loading the index entry [`Self::lookup`] reads first for
  /// `args`.
  #[inline(always)]
  pub(crate) fn prefetch(&self, args: &[B::Element]) {
    if let [key] = args
      && let Ok(key) = self.field.try_to_u64(*key)
      && let Ok(key) = usize::try_from(key)
      && key < self.dense_index.len()
    {
      crate::index::prefetch(&raw const self.dense_index[key]);
      return;
    }
    self.index.prefetch(tag(hash_words(args)));
  }

  /// A zero count marks a pending query, which must never supply an output.
  /// `outputs` is the table's output width, passed by callers that know it
  /// statically. An input in a `u32` column of 2^32 or more is an invalid
  /// value, not truncated, and leaves the table as it was.
  #[inline(always)]
  pub(crate) fn start(
    &mut self,
    args: &[B::Element],
    outputs: usize,
    hash: u64,
  ) -> Result<usize, StorageError> {
    debug_assert!(self.static_map.is_none());
    // Rows are written in place at the table's stride; a caller with other
    // widths would misalign every later row.
    assert!(
      args.len() == self.input_width && outputs == self.output_width,
      "query of widths ({}, {outputs}) started in a ({}, {}) table",
      args.len(),
      self.input_width,
      self.output_width
    );
    let field = self.field;
    let row = self.len();
    let row_bytes = if self.columns.packed {
      self.columns.words * size_of::<u32>()
    } else {
      self.stride * size_of::<B::Element>()
    };
    let entry = self.budget.row(row, row_bytes)?;
    if self.columns.packed {
      self.packed.reserve(&self.budget)?;
    } else {
      self.wide.reserve(&self.budget)?;
    }
    self.meta.reserve(&self.budget)?;
    let replaced =
      self.budget.index(self.index.growth(), &mut self.index_bytes)?;
    if self.columns.packed {
      let words = self.packed.push_row(0);
      if let Err(e) = Self::pack(&self.columns, field, words, 0, args) {
        self.packed.pop();
        return Err(e);
      }
    } else {
      self.wide.push_padded(args, field.zero());
    }
    self.meta.push_padded(&[], 0);
    self.index.insert(tag(hash), entry);
    drop(replaced);
    if let [key] = args
      && let Ok(key) = field.try_to_u64(*key)
      && let Ok(key) = usize::try_from(key)
    {
      // Bound space by observed table size, with a small startup allowance
      // and an absolute 4 MiB ceiling. Never allocate in
      // proportion to an arbitrary field element supplied as a key.
      let limit = row.saturating_mul(2).clamp(64, 1 << 20);
      if key < limit {
        if key >= self.dense_index.len() {
          let extra =
            (key + 1).next_power_of_two().min(limit) - self.dense_index.len();
          self.budget.vector(&mut self.dense_index, extra)?;
          self
            .dense_index
            .resize((key + 1).next_power_of_two().min(limit), u32::MAX);
        }
        self.dense_index[key] = entry;
      }
    }
    Ok(row)
  }
  /// Size the index for `rows` rows, so growing to them does not rehash.
  pub(crate) fn reserve_index(
    &mut self,
    rows: usize,
  ) -> Result<(), crate::budget::BudgetError> {
    if self.static_map.is_none() {
      let replaced = self
        .budget
        .index(self.index.reservation(rows), &mut self.index_bytes)?;
      self.index.reserve(rows);
      drop(replaced);
    }
    Ok(())
  }

  /// Record the outputs of the pending `row`. An output in a `u32` column
  /// of 2^32 or more is an invalid value, not truncated, and leaves the row
  /// pending.
  #[inline(always)]
  pub(crate) fn finish(
    &mut self,
    row: usize,
    output: &[B::Element],
  ) -> Result<(), StorageError> {
    debug_assert_eq!(self.count(row), 0);
    debug_assert_eq!(output.len(), self.output_width);
    if self.columns.packed {
      let words = self.packed.row_mut(row);
      Self::pack(&self.columns, self.field, words, self.input_width, output)?;
    } else {
      self.wide.row_mut(row)[self.input_width..].copy_from_slice(output);
    }
    self.meta.row_mut(row)[0] = 1;
    Ok(())
  }

  #[inline(always)]
  pub(crate) fn count(&self, row: usize) -> u64 {
    if let Some(map) = &self.static_map {
      return map.counts[row];
    }
    u64::from(self.meta.row(row)[0])
  }

  /// Number of stored slots. Fixed tables include rows with zero uses.
  pub(crate) fn len(&self) -> usize {
    if let Some(map) = &self.static_map {
      return map.counts.len();
    }
    self.rows_len()
  }

  pub(crate) fn widths(&self) -> (usize, usize) {
    (self.input_width, self.output_width)
  }

  fn drop_prefetched(&mut self) {
    self.packed.drop_prefetched(&self.budget);
    self.wide.drop_prefetched(&self.budget);
    self.meta.drop_prefetched(&self.budget);
  }

  pub(crate) fn storage_usage(&self) -> (usize, usize, usize) {
    let payload = self.packed.payload_bytes() + self.wide.payload_bytes();
    let vectors = self.packed.capacity_bytes()
      + self.wide.capacity_bytes()
      + self.meta.capacity_bytes()
      + self.dense_index.capacity() * size_of::<u32>()
      + self.static_map.as_ref().map_or(0, |map| map.counts.len() * 8);
    (payload, vectors, self.index.allocated_bytes())
  }

  #[inline(always)]
  pub(crate) fn bump(&mut self, row: usize) -> Option<()> {
    if let Some(map) = &mut self.static_map {
      let count = &mut map.counts[row];
      *count = count.checked_add(1)?;
      return Some(());
    }
    let count = &mut self.meta.row_mut(row)[0];
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
  pub(crate) budget: crate::budget::Budget,
}

impl<B: FieldBackend> QueryMap<B> {
  /// Tables of the given input widths whose row columns (inputs, then
  /// outputs) are `u32`s where marked, else field elements.
  pub(crate) fn new<'a>(
    tables: impl Iterator<Item = (usize, &'a [bool])>,
    field: B,
  ) -> Self {
    Self {
      tables: tables
        .map(|(inputs, narrow)| QueryTable::new(inputs, narrow, field))
        .collect(),
      budget: Default::default(),
    }
  }
  /// Record the references of the functions `plan` names.
  pub(crate) fn record_refs(&mut self, plan: &crate::refs::RefPlan) {
    for (table, function) in self.tables.iter_mut().zip(&plan.functions) {
      table.refs = function.as_ref().map(|_| Default::default());
    }
  }
  /// Free the chunks prefetched for rows that never came.
  pub(crate) fn drop_prefetched(&mut self) {
    self.tables.iter_mut().for_each(QueryTable::drop_prefetched);
  }
  /// Regroup every table's recorded references by block of rows
  /// ([`crate::refs`]).
  pub(crate) fn compact_refs(
    &mut self,
  ) -> Result<(), crate::budget::BudgetError> {
    let start = std::time::Instant::now();
    let compact = |table: &mut QueryTable<B>| {
      let rows = table.rows_len();
      match &mut table.refs {
        Some(refs) => refs.compact(rows, &table.budget),
        None => Ok(()),
      }
    };
    #[cfg(feature = "parallel")]
    {
      use rayon::prelude::*;
      self.tables.par_iter_mut().try_for_each(compact)?;
    }
    #[cfg(not(feature = "parallel"))]
    self.tables.iter_mut().try_for_each(compact)?;
    if std::env::var_os("AIUR_POPULATION_REPORT").is_some() {
      eprintln!(
        "[aiur] row references compacted in {:.2}s",
        start.elapsed().as_secs_f64()
      );
    }
    Ok(())
  }
  /// Track honest heights for the functions whose SCC `sccs` names.
  pub(crate) fn track_depth(&mut self, sccs: &[u32]) {
    for (table, &scc) in self.tables.iter_mut().zip(sccs) {
      table.set_track_depth(scc != crate::trace::depth::NO_SCC);
    }
  }
  pub(crate) fn reserve_with(
    &mut self,
    reservation: Option<&crate::budget::RecordReservation>,
  ) {
    self.budget = crate::budget::Budget(reservation.cloned());
    for table in &mut self.tables {
      table.budget = self.budget.clone();
    }
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
  /// Multiplicities in the original fixed map's row order, including unused
  /// rows. Function callables and unknown IDs have no fixed counts.
  pub fn fixed_counts(&self, callable: usize) -> Option<&[u64]> {
    self.tables.get(callable)?.static_map.as_ref().map(|map| &*map.counts)
  }
  /// Stored rows for one callable. Fixed maps include unused rows; function
  /// callables count distinct memoized queries, without scanning their payloads.
  pub fn callable_rows(&self, callable: usize) -> Option<usize> {
    self.tables.get(callable).map(QueryTable::len)
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
        output: Cow::Borrowed(map.binding.output(row)),
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
        other.get_ref(key.function, &key.args) == Some(value)
      })
  }
}
impl<B: FieldBackend> Eq for QueryMap<B> {}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  #[should_panic(expected = "started in a (1, 1) table")]
  fn rows_of_other_widths_are_rejected() {
    let mut table = QueryTable::wide(1, 1, PrimeField::new(97).unwrap());
    let _ = table.start(&[1], 2, 0);
  }

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
    let mut queries =
      QueryMap::new([(1, &[false, false][..])].into_iter(), field);
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
    let mut table = QueryTable::wide(1, 1, PrimeField::new(97).unwrap());
    let early =
      table.start(&[80], table.widths().1, table.lookup(&[80]).0).unwrap();
    table.finish(early, &[5]).unwrap();
    let large = table
      .start(&[u64::MAX], table.widths().1, table.lookup(&[u64::MAX]).0)
      .unwrap();
    table.finish(large, &[6]).unwrap();
    for key in 0..200 {
      if key != 80 {
        let row = table
          .start(&[key], table.widths().1, table.lookup(&[key]).0)
          .unwrap();
        table.finish(row, &[key]).unwrap();
      }
    }
    assert_eq!(table.lookup(&[80]).1, Some(early));
    assert_eq!(table.lookup(&[u64::MAX]).1, Some(large));
    assert!(table.lookup(&[0, 1]).1.is_none());
    assert!(table.lookup(&[]).1.is_none());
    assert!(table.dense_index.len() <= 2 * table.len());
  }

  #[test]
  fn mixed_columns_round_trip_and_keep_charges_exact() {
    use crate::budget::{Budget, RecordPool};
    let pool = RecordPool::new(1 << 30, 8);
    let reservation = pool.try_admit().unwrap().unwrap();
    // The Goldilocks modulus.
    let field = PrimeField::new(0xffff_ffff_0000_0001).unwrap();
    let wide = 0xffff_ffff_0000_0000;
    // Inputs (u32, field, u32), outputs (field, u32).
    let mut table =
      QueryTable::new(3, &[true, false, true, false, true], field);
    table.budget = Budget(Some(reservation.clone()));
    let rows = 10_000u64;
    let key = |i: u64| [i, wide - i, u64::from(u32::MAX) - i];
    for i in 0..rows {
      let args = key(i);
      let row = table.start(&args, 2, table.lookup(&args).0).unwrap();
      table.finish(row, &[wide - 2 * i, i * 3]).unwrap();
    }
    let (payload, vectors, index) = table.storage_usage();
    assert_eq!(reservation.bytes(), vectors + index);
    assert_eq!(payload, 10_000 * (3 * 4 + 2 * 8));
    let mut buffer = vec![];
    for i in 0..rows {
      let args = key(i);
      let row = table.lookup(&args).1.unwrap();
      assert_eq!(row, usize::try_from(i).unwrap());
      assert!(
        table.lookup(&[i, wide - i - 1, u64::from(u32::MAX) - i]).1.is_none()
      );
      assert_eq!(*table.input(row), args);
      assert_eq!(*table.output(row).output, [wide - 2 * i, i * 3]);
      assert_eq!(table.input_in(row, &mut buffer), args);
      assert_eq!(table.output_in(row, &mut buffer), [wide - 2 * i, i * 3]);
      let mut out = [0; 5];
      table.read_row(row, &mut out);
      assert_eq!(out, [args[0], args[1], args[2], wide - 2 * i, i * 3]);
      let mut out = [0; 2];
      table.read_output(row, &mut out);
      assert_eq!(out, [wide - 2 * i, i * 3]);
    }
    drop(table);
    reservation.release(reservation.bytes());
  }

  #[test]
  fn values_beyond_u32_columns_fail_loudly() {
    let field = PrimeField::new(0xffff_ffff_0000_0001).unwrap();
    let mut table = QueryTable::new(2, &[true, false, true], field);
    let too_wide = 1 << 32;
    let args = [too_wide, 5];
    let error = table.start(&args, 1, table.lookup(&args).0).unwrap_err();
    assert!(matches!(error, StorageError::Invalid(NARROW_OVERFLOW)));
    assert_eq!(table.len(), 0);
    assert!(table.lookup(&args).1.is_none());
    let args = [u64::from(u32::MAX), too_wide];
    let row = table.start(&args, 1, table.lookup(&args).0).unwrap();
    let error = table.finish(row, &[too_wide]).unwrap_err();
    assert!(matches!(error, StorageError::Invalid(NARROW_OVERFLOW)));
    assert_eq!(table.count(row), 0);
    table.finish(row, &[u64::from(u32::MAX)]).unwrap();
    assert_eq!(*table.output(row).output, [u64::from(u32::MAX)]);
    assert_eq!(*table.input(row), args);
  }

  #[test]
  fn narrow_lookups_compare_canonical_values() {
    let mut table =
      QueryTable::new(1, &[true, true], PrimeField::new(97).unwrap());
    // Keys beyond the dense index go through the hash index.
    for key in [5u64, 96, 1 << 20] {
      let row = table.start(&[key], 1, table.lookup(&[key]).0).unwrap();
      table.finish(row, &[key % 7]).unwrap();
    }
    assert_eq!(table.storage_usage().0, 3 * 2 * 4);
    assert_eq!(table.lookup(&[1 << 20]).1, Some(2));
    assert_eq!(table.lookup(&[(1 << 20) + 1]).1, None);
    let mut buffer = vec![];
    assert_eq!(table.output_in(2, &mut buffer), [(1 << 20) % 7]);
    assert_eq!(table.input_in(1, &mut buffer), [96]);
  }

  #[test]
  fn equal_tags_still_compare_keys() {
    let mut table = QueryTable::wide(2, 1, PrimeField::new(97).unwrap());
    // Two keys whose hashes share a tag (here the whole hash): the index
    // must tell them apart by their rows.
    let hash = 0xdead_beef_0000_0001;
    let first = table.start(&[1, 2], table.widths().1, hash).unwrap();
    table.finish(first, &[3]).unwrap();
    let second = table.start(&[2, 1], table.widths().1, hash).unwrap();
    table.finish(second, &[4]).unwrap();
    let find = |args: &[u64]| {
      table
        .index
        .find(tag(hash), |row| *table.input(row as usize) == *args)
        .map(|row| row as usize)
    };
    assert_eq!(find(&[1, 2]), Some(first));
    assert_eq!(find(&[2, 1]), Some(second));
    assert_eq!(find(&[1, 1]), None);
    assert_eq!(*table.output(second).output, [4]);
  }

  #[test]
  fn pending_rows_survive_growth_and_counts_do_not_wrap() {
    let mut table = QueryTable::wide(1, 1, PrimeField::new(97).unwrap());
    let first =
      table.start(&[0], table.widths().1, table.lookup(&[0]).0).unwrap();
    for i in 1..10_000 {
      let (hash, found) = table.lookup(&[i]);
      assert!(found.is_none());
      let row = table.start(&[i], table.widths().1, hash).unwrap();
      table.finish(row, &[i + 1]).unwrap();
    }
    assert_eq!(table.lookup(&[0]).1, Some(first));
    assert_eq!(table.count(first), 0);
    table.finish(first, &[42]).unwrap();
    assert_eq!(*table.output(first).output, [42]);
    table.meta.row_mut(first)[0] = u32::MAX;
    assert_eq!(table.bump(first), None);
    assert_eq!(table.count(first), u64::from(u32::MAX));
  }
}
