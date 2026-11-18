//! Append-only rows of a fixed stride, stored in chunks of a bounded number
//! of rows. Growth never moves a full chunk, so no allocation is ever copied
//! to twice its size and the capacity beyond the live rows is at most one
//! chunk. The first chunk grows by doubling until it is full, so a small
//! store stays small.
//!
//! A full chunk holds as many rows as fit a power of two bytes, not a power
//! of two rows. mimalloc rounds a block up to its size class (up to 25%
//! above the request between powers of two) and packs whole blocks into its
//! 512 KiB and 4 MiB pages, leaving the page's tail unused; with transparent
//! huge pages that rounding and tail are resident although never written
//! or charged. A power-of-two block is its own size class and divides its
//! page, so a full chunk wastes less than one row.
//!
//! Once a store holds a full chunk of at least [`PREFETCH_BYTES`], it asks
//! [`crate::prefetch`] for its next chunk while it fills the current one.
//! That allocation is charged when requested and counts as capacity, so
//! during execution a store may hold one chunk more than the bound above;
//! [`Chunks::drop_prefetched`] restores it.
use crate::budget::{Budget, BudgetError};
use crate::prefetch::Pending;

/// Rows the first chunk starts with.
const FIRST_ROWS: usize = 16;

/// The smallest chunk worth faulting in ahead of use.
const PREFETCH_BYTES: usize = 1 << 16;

#[derive(Debug)]
pub(crate) struct Chunks<T> {
  chunks: Vec<Vec<T>>,
  stride: usize,
  // Rows per full chunk.
  rows: usize,
  // `2^64 / rows` rounded up: a row below `fast_below` divides by `rows`
  // as a multiply. `fast_below` is `2^32`, or zero when `rows` is 1 or not
  // below `2^32`.
  magic: u64,
  fast_below: usize,
  len: usize,
  next: Option<Pending<T>>,
}

// A clone holds only the live chunks: a pending allocation is not copied.
impl<T: Clone> Clone for Chunks<T> {
  fn clone(&self) -> Self {
    Self {
      chunks: self.chunks.clone(),
      stride: self.stride,
      rows: self.rows,
      magic: self.magic,
      fast_below: self.fast_below,
      len: self.len,
      next: None,
    }
  }
}

impl<T: Copy> Chunks<T> {
  /// Rows of `stride` values in chunks of as many rows as fit the largest
  /// power of two bytes not above `chunk_bytes` (one row, if a row is
  /// larger).
  pub(crate) fn new(stride: usize, chunk_bytes: usize) -> Self {
    let row_bytes = stride * size_of::<T>().max(1);
    // A zero stride keeps every row in one empty chunk.
    let rows = if stride == 0 {
      usize::MAX
    } else {
      let bytes = 1 << chunk_bytes.max(1).ilog2();
      (bytes / row_bytes).max(1)
    };
    let (magic, fast_below) = if (2..1 << 32).contains(&rows) {
      (u64::MAX / rows as u64 + 1, 1 << 32)
    } else {
      (0, 0)
    };
    Self { chunks: vec![], stride, rows, magic, fast_below, len: 0, next: None }
  }

  /// A row's chunk and its place there.
  #[inline(always)]
  #[allow(clippy::cast_possible_truncation)] // the quotient is below `2^32`
  fn locate(&self, row: usize) -> (usize, usize) {
    let chunk = if row < self.fast_below {
      // Exact for a row and a divisor both below `2^32` (Lemire, Kaser and
      // Kurz, "Faster remainder by direct computation", 2019).
      ((u128::from(self.magic) * row as u128) >> 64) as usize
    } else {
      row / self.rows
    };
    (chunk, row - chunk * self.rows)
  }

  #[inline(always)]
  pub(crate) fn len(&self) -> usize {
    self.len
  }

  #[inline(always)]
  pub(crate) fn row(&self, row: usize) -> &[T] {
    let (chunk, at) = self.locate(row);
    let start = at * self.stride;
    &self.chunks[chunk][start..start + self.stride]
  }

  #[inline(always)]
  pub(crate) fn row_mut(&mut self, row: usize) -> &mut [T] {
    let (chunk, at) = self.locate(row);
    let start = at * self.stride;
    &mut self.chunks[chunk][start..start + self.stride]
  }

  #[inline(always)]
  pub(crate) fn at(&self, row: usize) -> &T {
    debug_assert_eq!(self.stride, 1);
    let (chunk, at) = self.locate(row);
    &self.chunks[chunk][at]
  }

  /// Make room for one more row, charging any allocation, so the next
  /// [`Self::push`] cannot fail.
  #[inline]
  pub(crate) fn reserve(&mut self, budget: &Budget) -> Result<(), BudgetError> {
    let chunk = self.locate(self.len).0;
    if chunk == self.chunks.len() {
      self.grow(chunk, budget)?;
    }
    let last = &mut self.chunks[chunk];
    if last.len() + self.stride > last.capacity() {
      let rows = (last.capacity() / self.stride * 2).min(self.rows);
      budget.resize(last, rows * self.stride)?;
      if rows == self.rows {
        self.prefetch(budget);
      }
    }
    Ok(())
  }

  /// Start chunk `chunk`, taking the prefetched allocation if it is ready.
  #[cold]
  fn grow(&mut self, chunk: usize, budget: &Budget) -> Result<(), BudgetError> {
    let rows = if chunk == 0 { FIRST_ROWS.min(self.rows) } else { self.rows };
    let capacity = rows * self.stride;
    budget.vector(&mut self.chunks, 1)?;
    let prefetched = match &self.next {
      Some(next) if next.capacity() == capacity => match next.take() {
        Ok(values) => Some(values),
        Err(failed) => {
          if failed {
            self.next = None;
            budget.release(capacity * size_of::<T>());
          }
          None
        },
      },
      _ => None,
    };
    if let Some(values) = prefetched {
      // Charged when it was requested.
      self.next = None;
      self.chunks.push(values);
    } else {
      budget.reserve(capacity * size_of::<T>())?;
      self.chunks.push(Vec::with_capacity(capacity));
    }
    if rows == self.rows {
      self.prefetch(budget);
    }
    Ok(())
  }

  /// Request the next full chunk, if none is pending and the budget admits
  /// it.
  fn prefetch(&mut self, budget: &Budget) {
    let capacity = self.rows * self.stride;
    let bytes = capacity * size_of::<T>();
    if self.next.is_some() || bytes < PREFETCH_BYTES {
      return;
    }
    if budget.reserve(bytes).is_ok() {
      self.next = Pending::new(capacity);
      if self.next.is_none() {
        budget.release(bytes);
      }
    }
  }

  /// Give up the prefetched chunk, if any, and its charge: a finished
  /// record keeps only the chunks it filled.
  pub(crate) fn drop_prefetched(&mut self, budget: &Budget) {
    if let Some(next) = self.next.take() {
      let bytes = next.capacity() * size_of::<T>();
      drop(next);
      budget.release(bytes);
    }
  }

  /// Append one row of `stride` values into room made by [`Self::reserve`].
  #[inline]
  pub(crate) fn push(&mut self, values: &[T]) {
    debug_assert_eq!(values.len(), self.stride);
    let chunk = self.locate(self.len).0;
    let last = &mut self.chunks[chunk];
    debug_assert!(last.len() + self.stride <= last.capacity());
    last.extend_from_slice(values);
    self.len += 1;
  }

  /// Append a row of `values` followed by copies of `pad`, into room made
  /// by [`Self::reserve`].
  #[inline]
  pub(crate) fn push_padded(&mut self, values: &[T], pad: T) {
    debug_assert!(values.len() <= self.stride);
    let chunk = self.locate(self.len).0;
    let last = &mut self.chunks[chunk];
    debug_assert!(last.len() + self.stride <= last.capacity());
    let end = last.len() + self.stride;
    last.extend_from_slice(values);
    last.resize(end, pad);
    self.len += 1;
  }

  /// Append a row of copies of `pad`, into room made by [`Self::reserve`],
  /// and return it.
  #[inline(always)]
  pub(crate) fn push_row(&mut self, pad: T) -> &mut [T] {
    let chunk = self.locate(self.len).0;
    let last = &mut self.chunks[chunk];
    debug_assert!(last.len() + self.stride <= last.capacity());
    let end = last.len() + self.stride;
    last.resize(end, pad);
    self.len += 1;
    &mut last[end - self.stride..]
  }

  /// Drop the last row, keeping its storage.
  #[inline]
  pub(crate) fn pop(&mut self) {
    debug_assert!(self.len > 0);
    self.len -= 1;
    let chunk = self.locate(self.len).0;
    let last = &mut self.chunks[chunk];
    last.truncate(last.len() - self.stride);
  }

  /// The chunks in order, each but the last holding
  /// [`Self::rows_per_chunk`] rows.
  #[cfg_attr(not(feature = "cuda"), allow(dead_code))]
  pub(crate) fn chunks(&self) -> &[Vec<T>] {
    &self.chunks
  }

  #[cfg_attr(not(feature = "cuda"), allow(dead_code))]
  pub(crate) fn rows_per_chunk(&self) -> usize {
    self.rows
  }

  /// Bytes of the live rows.
  pub(crate) fn payload_bytes(&self) -> usize {
    self.len * self.stride * size_of::<T>()
  }

  /// Bytes allocated, as charged.
  pub(crate) fn capacity_bytes(&self) -> usize {
    (self.chunks.iter().map(Vec::capacity).sum::<usize>()
      + self.next.as_ref().map_or(0, Pending::capacity))
      * size_of::<T>()
      + self.chunks.capacity() * size_of::<Vec<T>>()
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::budget::RecordPool;

  #[test]
  fn rows_stay_in_place_and_capacity_is_charged() {
    let pool = RecordPool::new(1 << 24, 8);
    let reservation = pool.try_admit().unwrap().unwrap();
    let budget = Budget(Some(reservation.clone()));
    let mut rows = Chunks::<u64>::new(3, 256);
    let mut empty = Chunks::<u64>::new(0, 256);
    for i in 0..1000u64 {
      rows.reserve(&budget).unwrap();
      rows.push(&[i, i + 1, i + 2]);
      empty.reserve(&budget).unwrap();
      empty.push(&[]);
    }
    assert_eq!(rows.len(), 1000);
    assert_eq!(empty.len(), 1000);
    for i in 0..1000 {
      assert_eq!(rows.row(i), [i as u64, i as u64 + 1, i as u64 + 2]);
      assert!(empty.row(i).is_empty());
    }
    rows.row_mut(7)[1] = 0;
    assert_eq!(rows.row(7), [7, 0, 9]);
    // 10 rows of 24 bytes fit a 256-byte chunk.
    assert_eq!(rows.rows_per_chunk(), 10);
    assert_eq!(rows.payload_bytes(), 24_000);
    assert!(rows.capacity_bytes() - rows.payload_bytes() < 10 * 24 + 128 * 24);
    assert_eq!(
      reservation.bytes(),
      rows.capacity_bytes() + empty.capacity_bytes()
    );
  }

  #[test]
  fn rows_locate_by_division() {
    for row_bytes in [1, 8, 16, 24, 72, 88, 4096, 1 << 19, 1 << 20, (1 << 19) + 8] {
      let rows = Chunks::<u8>::new(row_bytes, 1 << 19);
      assert_eq!(rows.rows_per_chunk(), ((1 << 19) / row_bytes).max(1));
      let n = rows.rows_per_chunk();
      for k in [0, 1, 2, 1000, (1 << 32) / n - 1, (1 << 32) / n, 1 << 40] {
        for row in [k * n, k * n + n / 2, (k + 1) * n - 1] {
          assert_eq!(rows.locate(row), (row / n, row % n), "{row_bytes} {row}");
        }
      }
    }
    // The largest power of two not above `chunk_bytes` bounds a chunk.
    assert_eq!(Chunks::<u32>::new(3, 300).rows_per_chunk(), 21);
  }

  #[test]
  fn prefetched_chunks_are_charged_and_used_in_order() {
    let pool = RecordPool::new(1 << 26, 8);
    let reservation = pool.try_admit().unwrap().unwrap();
    let budget = Budget(Some(reservation.clone()));
    let mut rows = Chunks::<u64>::new(2, PREFETCH_BYTES);
    let per_chunk = rows.rows_per_chunk() as u64;
    for i in 0..per_chunk * 9 + 3 {
      rows.reserve(&budget).unwrap();
      rows.push(&[i, !i]);
      assert_eq!(reservation.bytes(), rows.capacity_bytes());
      if i % per_chunk == per_chunk / 2 {
        std::thread::sleep(std::time::Duration::from_millis(1));
      }
    }
    for i in 0..per_chunk * 9 + 3 {
      assert_eq!(rows.row(usize::try_from(i).unwrap()), [i, !i]);
    }
    let copy = rows.clone();
    assert_eq!(copy.len(), rows.len());
    drop(rows);
    assert_eq!(copy.row(5), [5, !5]);
  }
}
