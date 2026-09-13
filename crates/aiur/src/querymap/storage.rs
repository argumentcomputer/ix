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
  #[inline]
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
/// cache hits decode straight into stack arrays.
#[derive(Clone, Copy, Debug)]
pub enum QuerySlice<'a> {
  Fields(&'a [G]),
  Bytes(&'a [u8]),
  Packed(PackedRow<'a>),
}

impl QuerySlice<'_> {
  pub fn len(self) -> usize {
    match self {
      Self::Fields(xs) => xs.len(),
      Self::Bytes(xs) => xs.len(),
      Self::Packed(row) => row.layout.columns.len(),
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

pub(super) struct PackedStore {
  pub stride: usize,
  entries: usize,
  segs: Vec<Segment>,
  layout: Layout,
  payload: usize,
}

impl PackedStore {
  pub(super) fn new(stride: usize, compact: bool) -> Self {
    Self {
      stride,
      entries: 0,
      segs: Vec::new(),
      layout: Layout::new(stride, compact),
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

  pub(super) fn push(&mut self, vals: &[G]) {
    assert!(self.entries == 0 || vals.len() == self.stride);
    let tail = self.entries & SEG_MASK;
    let old_width = self.layout.bytes();
    let widen = (self.entries == 0 && vals.len() != self.stride)
      || !self.layout.fits(vals);
    if widen {
      self.layout = self.layout.widened(vals);
    }
    if self.entries == 0 {
      self.stride = vals.len();
    }
    if self.stride != 0 {
      if tail == 0 {
        self.segs.push(Segment::new(&self.layout));
      } else if widen {
        // Views of earlier segments keep their original layout. Only the
        // active segment is copied, before replacing and dropping its pages.
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
    self.payload += self.layout.bytes();
    if widen && tail != 0 {
      self.payload += tail * (self.layout.bytes() - old_width);
    }
  }

  pub(super) fn retained_bytes(&self) -> usize {
    self.payload
  }

  pub(super) fn retained_elems(&self) -> usize {
    self.entries * self.stride
  }
}
