//! Lossless, per-column byte/u32/full-field query storage. Encoding is selected
//! from actual canonical values, never trusted type/name metadata. Widening
//! copies only the active segment and preserves row indices and memo hashes.

use super::{G, HugeVec, SEG_BITS, SEG_ENTRIES, SEG_MASK};
use multi_stark::p3_field::{PrimeCharacteristicRing, PrimeField64};

/// A packed row borrows its segment's immutable layout. All accesses decode
/// through checked byte slices, including unaligned u32/full-field columns.
#[derive(Clone, Copy, Debug)]
pub struct PackedRow<'a> {
  bytes: &'a [u8],
  layout: &'a MixedLayout,
}

impl PackedRow<'_> {
  fn at(self, i: usize) -> G {
    let column = &self.layout.columns[i];
    let bytes =
      &self.bytes[column.offset..column.offset + column.width.bytes()];
    match column.width {
      Width::Byte => G::from_u8(bytes[0]),
      Width::U32 => G::from_u32(u32::from_le_bytes(bytes.try_into().unwrap())),
      Width::Field => {
        G::from_u64(u64::from_le_bytes(bytes.try_into().unwrap()))
      },
    }
  }
}

/// Read-only field view. No second full-width copy is retained and generated
/// cache hits decode straight into stack arrays. Value represents a memory
/// pointer reconstructed from the insertion index, not a stored output.
#[derive(Clone, Copy, Debug)]
pub enum QuerySlice<'a> {
  Fields(&'a [G]),
  Bytes(&'a [u8]),
  Packed(PackedRow<'a>),
  Value(G),
}

impl QuerySlice<'_> {
  pub fn len(self) -> usize {
    match self {
      Self::Fields(xs) => xs.len(),
      Self::Bytes(xs) => xs.len(),
      Self::Packed(row) => row.layout.columns.len(),
      Self::Value(_) => 1,
    }
  }

  pub fn is_empty(self) -> bool {
    self.len() == 0
  }

  #[inline]
  pub fn at(self, i: usize) -> G {
    match self {
      Self::Fields(xs) => xs[i],
      Self::Bytes(xs) => G::from_u8(xs[i]),
      Self::Packed(row) => row.at(i),
      Self::Value(value) => {
        assert_eq!(i, 0);
        value
      },
    }
  }

  pub fn iter(self) -> impl ExactSizeIterator<Item = G> + DoubleEndedIterator {
    (0..self.len()).map(move |i| self.at(i))
  }

  #[inline]
  pub fn matches(self, other: &[G]) -> bool {
    match self {
      Self::Fields(xs) => xs == other,
      Self::Bytes(xs) => {
        xs.len() == other.len()
          && xs
            .iter()
            .zip(other)
            .all(|(&a, b)| u64::from(a) == b.as_canonical_u64())
      },
      _ => {
        self.len() == other.len()
          && self.iter().zip(other).all(|(a, b)| a == *b)
      },
    }
  }

  #[inline]
  pub fn copy_to_slice(self, dst: &mut [G]) {
    assert_eq!(self.len(), dst.len(), "query slice width mismatch");
    match self {
      Self::Fields(xs) => dst.copy_from_slice(xs),
      _ => {
        for (out, value) in dst.iter_mut().zip(self.iter()) {
          *out = value;
        }
      },
    }
  }

  #[inline]
  pub fn to_array<const N: usize>(self) -> [G; N] {
    assert_eq!(self.len(), N, "query array width mismatch");
    match self {
      Self::Fields(xs) => xs.try_into().expect("width checked above"),
      _ => std::array::from_fn(|i| self.at(i)),
    }
  }

  pub fn to_vec(self) -> Vec<G> {
    match self {
      Self::Fields(xs) => xs.to_vec(),
      _ => self.iter().collect(),
    }
  }
}

impl PartialEq for QuerySlice<'_> {
  fn eq(&self, other: &Self) -> bool {
    match (*self, *other) {
      (Self::Fields(a), b) | (b, Self::Fields(a)) => b.matches(a),
      (Self::Bytes(a), Self::Bytes(b)) => a == b,
      (a, b) => a.len() == b.len() && a.iter().eq(b.iter()),
    }
  }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Width {
  Byte,
  U32,
  Field,
}

impl Width {
  fn needed(value: G) -> Self {
    let value = value.as_canonical_u64();
    if u8::try_from(value).is_ok() {
      Self::Byte
    } else if u32::try_from(value).is_ok() {
      Self::U32
    } else {
      Self::Field
    }
  }

  fn bytes(self) -> usize {
    match self {
      Self::Byte => 1,
      Self::U32 => 4,
      Self::Field => 8,
    }
  }

  fn fits(self, value: G) -> bool {
    match self {
      Self::Byte => u8::try_from(value.as_canonical_u64()).is_ok(),
      Self::U32 => u32::try_from(value.as_canonical_u64()).is_ok(),
      Self::Field => true,
    }
  }
}

#[derive(Clone, Debug)]
struct Column {
  offset: usize,
  width: Width,
}

#[derive(Clone, Debug)]
struct MixedLayout {
  columns: Vec<Column>,
  bytes: usize,
}

#[derive(Clone)]
enum Layout {
  Bytes(usize),
  Fields(usize),
  Mixed(MixedLayout),
}

impl Layout {
  fn new(stride: usize, compact: bool) -> Self {
    if compact { Self::Bytes(stride) } else { Self::Fields(stride) }
  }

  fn bytes(&self) -> usize {
    match self {
      Self::Bytes(n) => *n,
      Self::Fields(n) => {
        n.checked_mul(size_of::<G>()).expect("query row overflow")
      },
      Self::Mixed(layout) => layout.bytes,
    }
  }

  fn fits(&self, vals: &[G]) -> bool {
    match self {
      Self::Bytes(_) => vals.iter().all(|&v| Width::Byte.fits(v)),
      Self::Fields(_) => true,
      Self::Mixed(layout) => {
        layout.columns.iter().zip(vals).all(|(c, &v)| c.width.fits(v))
      },
    }
  }

  /// Called only on initial width inference or a range miss. No per-row heap
  /// allocation on the ordinary insertion path. Column widths never shrink.
  fn widened(&self, vals: &[G]) -> Self {
    let mut bytes = 0usize;
    let mut all_bytes = true;
    let mut all_fields = true;
    let columns = vals
      .iter()
      .enumerate()
      .map(|(i, &v)| {
        let old = match self {
          Self::Bytes(_) => Width::Byte,
          Self::Fields(_) => Width::Field,
          Self::Mixed(layout) => layout.columns[i].width,
        };
        let width = old.max(Width::needed(v));
        all_bytes &= width == Width::Byte;
        all_fields &= width == Width::Field;
        let offset = bytes;
        bytes = bytes.checked_add(width.bytes()).expect("query row overflow");
        Column { offset, width }
      })
      .collect();
    if all_bytes {
      Self::Bytes(vals.len())
    } else if all_fields {
      Self::Fields(vals.len())
    } else {
      Self::Mixed(MixedLayout { columns, bytes })
    }
  }
}

enum Segment {
  Bytes(HugeVec<u8>),
  Fields(HugeVec<G>),
  Mixed { data: HugeVec<u8>, layout: MixedLayout },
}

impl Segment {
  fn new(layout: &Layout) -> Self {
    let capacity = |width: usize| {
      SEG_ENTRIES.checked_mul(width).expect("query segment overflow")
    };
    match layout {
      Layout::Bytes(n) => Self::Bytes(HugeVec::with_capacity(capacity(*n))),
      Layout::Fields(n) => Self::Fields(HugeVec::with_capacity(capacity(*n))),
      Layout::Mixed(layout) => Self::Mixed {
        data: HugeVec::with_capacity(capacity(layout.bytes)),
        layout: layout.clone(),
      },
    }
  }

  fn at(&self, row: usize, stride: usize) -> QuerySlice<'_> {
    match self {
      Self::Bytes(xs) => QuerySlice::Bytes(xs.slice(row * stride, stride)),
      Self::Fields(xs) => QuerySlice::Fields(xs.slice(row * stride, stride)),
      Self::Mixed { data, layout } => QuerySlice::Packed(PackedRow {
        bytes: data.slice(row * layout.bytes, layout.bytes),
        layout,
      }),
    }
  }

  fn push(&mut self, row: QuerySlice<'_>) {
    match self {
      Self::Bytes(xs) => match row {
        QuerySlice::Bytes(bytes) => xs.extend_from_slice(bytes),
        _ => {
          for v in row.iter() {
            xs.extend_from_slice(&[
              u8::try_from(v.as_canonical_u64()).expect("byte width checked")
            ]);
          }
        },
      },
      Self::Fields(xs) => match row {
        QuerySlice::Fields(fields) => xs.extend_from_slice(fields),
        _ => {
          for v in row.iter() {
            xs.extend_from_slice(&[v]);
          }
        },
      },
      Self::Mixed { data, layout } => {
        assert_eq!(row.len(), layout.columns.len());
        for (column, value) in layout.columns.iter().zip(row.iter()) {
          // Check again at the encoding boundary: no unchecked narrowing or
          // type-based trust, even if an internal caller supplied a bad plan.
          assert!(column.width.fits(value), "packed column width checked");
          let bytes = value.as_canonical_u64().to_le_bytes();
          data.extend_from_slice(&bytes[..column.width.bytes()]);
        }
      },
    }
  }
}

pub(super) struct AppendPlan {
  layout: Option<Layout>,
  pub storage_after: u64,
  /// Old pages coexist with their replacement while the active segment widens.
  pub transient: u64,
  payload_after: usize,
}

pub(super) struct PackedStore {
  pub stride: usize,
  entries: usize,
  segs: Vec<Segment>,
  layout: Layout,
  storage: u64,
  payload: usize,
}

impl PackedStore {
  pub(super) fn new(stride: usize, compact: bool) -> Self {
    Self {
      stride,
      entries: 0,
      segs: Vec::new(),
      layout: Layout::new(stride, compact),
      storage: 0,
      payload: 0,
    }
  }

  #[inline]
  pub(super) fn at(&self, i: usize) -> QuerySlice<'_> {
    assert!(i < self.entries, "query index out of bounds");
    if self.stride == 0 {
      return QuerySlice::Fields(&[]);
    }
    self.segs[i >> SEG_BITS].at(i & SEG_MASK, self.stride)
  }

  /// Plan growth without changing data or the current layout. Refused budget
  /// reservations leave rows, indices, multiplicities and encoding untouched.
  pub(super) fn plan(&self, vals: &[G]) -> AppendPlan {
    assert!(self.entries == 0 || vals.len() == self.stride);
    let layout = if (self.entries == 0 && vals.len() != self.stride)
      || !self.layout.fits(vals)
    {
      Some(self.layout.widened(vals))
    } else {
      None
    };
    let next_layout = layout.as_ref().unwrap_or(&self.layout);
    let tail = self.entries & SEG_MASK;
    let old =
      if tail == 0 { 0 } else { segment_bytes(tail, self.layout.bytes()) };
    let next = segment_bytes(tail + 1, next_layout.bytes());
    let promote = tail != 0 && layout.is_some();
    let payload_after = self
      .payload
      .saturating_add(next_layout.bytes())
      .saturating_add(if promote {
        tail.saturating_mul(next_layout.bytes() - self.layout.bytes())
      } else {
        0
      });
    AppendPlan {
      layout,
      storage_after: self.storage.saturating_sub(old).saturating_add(next),
      transient: if promote { old } else { 0 },
      payload_after,
    }
  }

  pub(super) fn push(&mut self, vals: &[G], plan: AppendPlan) {
    if self.entries == 0 {
      self.stride = vals.len();
    }
    assert_eq!(vals.len(), self.stride);
    let changed = plan.layout.is_some();
    if let Some(layout) = plan.layout {
      self.layout = layout;
    }
    if self.stride != 0 {
      let tail = self.entries & SEG_MASK;
      if tail == 0 {
        self.segs.push(Segment::new(&self.layout));
      } else if changed {
        let old = self.segs.last().unwrap();
        let mut next = Segment::new(&self.layout);
        for row in 0..tail {
          next.push(old.at(row, self.stride));
        }
        *self.segs.last_mut().unwrap() = next;
      }
      self.segs.last_mut().unwrap().push(QuerySlice::Fields(vals));
    }
    self.entries += 1;
    self.storage = plan.storage_after;
    self.payload = plan.payload_after;
  }

  pub(super) fn accounted_bytes(&self) -> u64 {
    self.storage
  }
  pub(super) fn retained_bytes(&self) -> usize {
    self.payload
  }
  pub(super) fn retained_elems(&self) -> usize {
    self.entries * self.stride
  }
  pub(super) fn clear_storage(&mut self) {
    self.segs.clear();
  }
}

pub(super) fn segment_bytes(entries: usize, row_bytes: usize) -> u64 {
  if entries == 0 || row_bytes == 0 {
    return 0;
  }
  #[cfg(target_os = "linux")]
  {
    (entries as u64)
      .saturating_mul(row_bytes as u64)
      .div_ceil(1 << 21)
      .saturating_mul(1 << 21)
  }
  #[cfg(not(target_os = "linux"))]
  {
    let _ = entries;
    (SEG_ENTRIES as u64).saturating_mul(row_bytes as u64)
  }
}
