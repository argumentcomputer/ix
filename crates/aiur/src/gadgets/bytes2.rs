use multi_stark::{
  expr::Expr,
  lookup::{Lookup, LookupValues},
  p3_field::{PrimeCharacteristicRing, PrimeField64},
  p3_matrix::dense::RowMajorMatrix,
};

use crate::{
  G, execute::QueryRecord, gadgets::AiurGadget, u8_add_channel, u8_mul_channel,
  u8_range_check_channel, u8_sub_channel, u8_xor_channel,
  u8_xor_split4_channel, u8_xor_split7_channel,
};

/// Number of columns in the trace with multiplicities for
/// - xor
/// - overflowing add
/// - overflowing sub
/// - range_check
/// - mul
/// - xor_split7
/// - xor_split4
const TRACE_WIDTH: usize = 7;

/// Number of columns in the preprocessed trace:
/// - first raw byte value
/// - second raw byte value
/// - xor result
/// - add result (low byte only; the carry is derived in-circuit as
///   `(x + y - z) / 256`, so it needs no column or lookup)
/// - sub result (low byte only; the borrow is derived in-circuit as
///   `(z + y - x) / 256`, so it needs no column or lookup)
/// - mul low byte
/// - mul high byte
/// - xor_split7 high and shifted-low outputs
/// - xor_split4 high and shifted-low outputs
const PREPROCESSED_TRACE_WIDTH: usize = 11;

/// AIR implementer for arity 2 byte-related lookups.
///
/// AND and OR reuse XOR through `a + b - 2*and` and `2*or - a - b`.
/// Comparison reuses subtraction through `a - b + 256*less_than`.
/// The caller keeps its original output column; these derived arguments
/// need neither additional witnesses nor separate table multiplicities.
pub struct Bytes2;

pub enum Bytes2Op {
  Xor,
  Add,
  Mul,
  Sub,
  And,
  Or,
  LessThan,
  XorSplit7,
  XorSplit4,
}

impl AiurGadget for Bytes2 {
  type Op = Bytes2Op;

  fn output_size(&self, op: &Bytes2Op) -> usize {
    match op {
      Bytes2Op::Xor
      | Bytes2Op::And
      | Bytes2Op::Or
      | Bytes2Op::LessThan
      | Bytes2Op::Add
      | Bytes2Op::Sub => 1,
      Bytes2Op::Mul | Bytes2Op::XorSplit7 | Bytes2Op::XorSplit4 => 2,
    }
  }

  fn main_width(&self) -> usize {
    TRACE_WIDTH
  }

  /// Builds the preprocessed trace over all 256 byte values.
  fn preprocessed(&self) -> Option<RowMajorMatrix<G>> {
    let mut trace_values =
      Vec::with_capacity(256 * 256 * PREPROCESSED_TRACE_WIDTH);
    for i in 0..=u8::MAX {
      for j in 0..=u8::MAX {
        // Raw bytes
        trace_values.push(G::from_u8(i));
        trace_values.push(G::from_u8(j));

        // Xor
        trace_values.push(G::from_u8(i ^ j));

        // Add low byte (carry derived in-circuit, no column)
        trace_values.push(G::from_u8(i.wrapping_add(j)));

        // Sub low byte (borrow derived in-circuit, no column)
        trace_values.push(G::from_u8(i.wrapping_sub(j)));

        // Mul (low byte, high byte)
        let p = u16::from(i) * u16::from(j);
        trace_values.push(G::from_u8((p & 0xff) as u8));
        trace_values.push(G::from_u8((p >> 8) as u8));

        let (hi, lo) = Self::xor_split7_u8(i, j);
        trace_values.extend([G::from_u8(hi), G::from_u8(lo)]);
        let (hi, lo) = Self::xor_split4_u8(i, j);
        trace_values.extend([G::from_u8(hi), G::from_u8(lo)]);
      }
    }
    Some(RowMajorMatrix::new(trace_values, PREPROCESSED_TRACE_WIDTH))
  }

  fn execute(
    &self,
    op: &Bytes2Op,
    input: &[G],
    record: &mut QueryRecord,
  ) -> Vec<G> {
    let i = &input[0];
    let j = &input[1];
    match op {
      Bytes2Op::Xor => {
        record.bytes2_queries.bump_xor(i, j);
        vec![Self::xor(i, j)]
      },
      Bytes2Op::Add => {
        record.bytes2_queries.bump_add(i, j);
        let (r, _o) = Self::add(i, j);
        vec![r]
      },
      Bytes2Op::Mul => {
        record.bytes2_queries.bump_mul(i, j);
        let (lo, hi) = Self::mul(i, j);
        vec![lo, hi]
      },
      Bytes2Op::Sub => {
        record.bytes2_queries.bump_sub(i, j);
        let (r, _u) = Self::sub(i, j);
        vec![r]
      },
      Bytes2Op::And => {
        record.bytes2_queries.bump_and(i, j);
        vec![Self::and(i, j)]
      },
      Bytes2Op::Or => {
        record.bytes2_queries.bump_or(i, j);
        vec![Self::or(i, j)]
      },
      Bytes2Op::LessThan => {
        record.bytes2_queries.bump_less_than(i, j);
        vec![Self::less_than(i, j)]
      },
      Bytes2Op::XorSplit7 => {
        record.bytes2_queries.bump_xor_split7(i, j);
        let (hi, lo) = Self::xor_split7(i, j);
        vec![hi, lo]
      },
      Bytes2Op::XorSplit4 => {
        record.bytes2_queries.bump_xor_split4(i, j);
        let (hi, lo) = Self::xor_split4(i, j);
        vec![hi, lo]
      },
    }
  }

  fn lookups(&self) -> Vec<Lookup<Expr<G>>> {
    // Channels
    let xor_channel = Expr::constant(u8_xor_channel());
    let add_channel = Expr::constant(u8_add_channel());
    let sub_channel = Expr::constant(u8_sub_channel());
    let range_check_channel = Expr::constant(u8_range_check_channel());
    let mul_channel = Expr::constant(u8_mul_channel());
    let xor_split7_channel = Expr::constant(u8_xor_split7_channel());
    let xor_split4_channel = Expr::constant(u8_xor_split4_channel());

    // Multiplicity columns
    let xor_multiplicity = Expr::main(0);
    let add_multiplicity = Expr::main(1);
    let sub_multiplicity = Expr::main(2);
    let range_check_multiplicity = Expr::main(3);
    let mul_multiplicity = Expr::main(4);
    let xor_split7_multiplicity = Expr::main(5);
    let xor_split4_multiplicity = Expr::main(6);

    // Preprocessed columns
    let i = Expr::preprocessed(0);
    let j = Expr::preprocessed(1);
    let xor = Expr::preprocessed(2);
    let add_r = Expr::preprocessed(3);
    let sub_r = Expr::preprocessed(4);
    let mul_lo = Expr::preprocessed(5);
    let mul_hi = Expr::preprocessed(6);
    let xor_split7_hi = Expr::preprocessed(7);
    let xor_split7_lo = Expr::preprocessed(8);
    let xor_split4_hi = Expr::preprocessed(9);
    let xor_split4_lo = Expr::preprocessed(10);

    // pull = negated multiplicity.
    let pull_xor = Lookup {
      multiplicity: -xor_multiplicity,
      args: vec![xor_channel, i.clone(), j.clone(), xor],
    };

    let pull_add = Lookup {
      multiplicity: -add_multiplicity,
      args: vec![add_channel, i.clone(), j.clone(), add_r],
    };

    let pull_sub = Lookup {
      multiplicity: -sub_multiplicity,
      args: vec![sub_channel, i.clone(), j.clone(), sub_r],
    };

    let pull_mul = Lookup {
      multiplicity: -mul_multiplicity,
      args: vec![mul_channel, i.clone(), j.clone(), mul_lo, mul_hi],
    };

    let pull_range_check = Lookup {
      multiplicity: -range_check_multiplicity,
      args: vec![range_check_channel, i.clone(), j.clone()],
    };

    let pull_xor_split7 = Lookup {
      multiplicity: -xor_split7_multiplicity,
      args: vec![
        xor_split7_channel,
        i.clone(),
        j.clone(),
        xor_split7_hi,
        xor_split7_lo,
      ],
    };
    let pull_xor_split4 = Lookup {
      multiplicity: -xor_split4_multiplicity,
      args: vec![xor_split4_channel, i, j, xor_split4_hi, xor_split4_lo],
    };

    vec![
      pull_xor,
      pull_add,
      pull_sub,
      pull_range_check,
      pull_mul,
      pull_xor_split7,
      pull_xor_split4,
    ]
  }

  fn witness_data(
    &self,
    record: &QueryRecord,
    slot_arg_widths: &[usize],
  ) -> (RowMajorMatrix<G>, LookupValues<G>) {
    let mut rows = vec![G::ZERO; 256 * 256 * TRACE_WIDTH];
    let mut builder = LookupValues::builder(256 * 256, slot_arg_widths);
    let mut row_writers = builder.rows_mut();
    for (((row_idx, row), counts), row_lookups) in rows
      .as_chunks_mut::<TRACE_WIDTH>()
      .0
      .iter_mut()
      .enumerate()
      .zip(&record.bytes2_queries.0)
      .zip(row_writers.iter_mut())
    {
      let [xor, add, sub, range_check, mul, xor_split7, xor_split4] = *counts;
      let i = G::from_usize(row_idx / 256);
      let j = G::from_usize(row_idx % 256);
      row.copy_from_slice(counts);

      // AND and OR queries also pull XOR; comparisons also pull subtraction.
      row_lookups.pull(0, xor, &[u8_xor_channel(), i, j, Self::xor(&i, &j)]);
      let (r, _) = Self::add(&i, &j);
      row_lookups.pull(1, add, &[u8_add_channel(), i, j, r]);
      let (r, _) = Self::sub(&i, &j);
      row_lookups.pull(2, sub, &[u8_sub_channel(), i, j, r]);
      row_lookups.pull(
        Self::RANGE_CHECK_COLUMN,
        range_check,
        &[u8_range_check_channel(), i, j],
      );
      let (lo, hi) = Self::mul(&i, &j);
      row_lookups.pull(4, mul, &[u8_mul_channel(), i, j, lo, hi]);
      let (hi, lo) = Self::xor_split7(&i, &j);
      row_lookups.pull(5, xor_split7, &[u8_xor_split7_channel(), i, j, hi, lo]);
      let (hi, lo) = Self::xor_split4(&i, &j);
      row_lookups.pull(6, xor_split4, &[u8_xor_split4_channel(), i, j, hi, lo]);
    }
    drop(row_writers);
    (RowMajorMatrix::new(rows, TRACE_WIDTH), builder.finish())
  }
}

/// Accumulator of queries performed against `Bytes2`.
pub struct Bytes2Queries(Box<[[G; TRACE_WIDTH]]>);

impl Bytes2Queries {
  #[inline]
  pub(crate) fn new() -> Self {
    Self(vec![[G::ZERO; TRACE_WIDTH]; 256 * 256].into_boxed_slice())
  }

  pub(crate) fn bump_xor(&mut self, i: &G, j: &G) {
    self.bump_multiplicity_for(i, j, 0)
  }

  pub(crate) fn bump_add(&mut self, i: &G, j: &G) {
    self.bump_multiplicity_for(i, j, 1)
  }

  pub(crate) fn bump_sub(&mut self, i: &G, j: &G) {
    self.bump_multiplicity_for(i, j, 2)
  }

  pub(crate) fn bump_and(&mut self, i: &G, j: &G) {
    self.bump_xor(i, j)
  }

  pub(crate) fn bump_or(&mut self, i: &G, j: &G) {
    self.bump_xor(i, j)
  }

  pub(crate) fn bump_less_than(&mut self, i: &G, j: &G) {
    self.bump_sub(i, j)
  }

  pub fn bump_range_check(&mut self, i: &G, j: &G) {
    self.bump_multiplicity_for(i, j, Bytes2::RANGE_CHECK_COLUMN)
  }

  pub(crate) fn add_rank_ranges(
    &mut self,
    ranges: crate::call_order::RankRanges,
  ) {
    for ([i, j], count) in ranges {
      self.0[256 * usize::from(i) + usize::from(j)]
        [Bytes2::RANGE_CHECK_COLUMN] += count;
    }
  }

  pub(crate) fn bump_mul(&mut self, i: &G, j: &G) {
    self.bump_multiplicity_for(i, j, 4)
  }

  pub(crate) fn bump_xor_split7(&mut self, i: &G, j: &G) {
    self.bump_multiplicity_for(i, j, 5)
  }

  pub(crate) fn bump_xor_split4(&mut self, i: &G, j: &G) {
    self.bump_multiplicity_for(i, j, 6)
  }

  pub(crate) fn bump_multiplicity_for(&mut self, i: &G, j: &G, col: usize) {
    let i = usize::try_from(i.as_canonical_u64()).unwrap();
    let j = usize::try_from(j.as_canonical_u64()).unwrap();
    let row = 256 * i + j;
    self.0[row][col] += G::ONE;
  }
}

impl Bytes2 {
  /// Shared row and lookup-slot index of the byte-pair range channel.
  pub(crate) const RANGE_CHECK_COLUMN: usize = 3;

  #[inline]
  pub fn xor(i: &G, j: &G) -> G {
    let i: u8 = i.as_canonical_u64().try_into().unwrap();
    let j: u8 = j.as_canonical_u64().try_into().unwrap();
    G::from_u8(i ^ j)
  }

  #[inline]
  pub fn add(i: &G, j: &G) -> (G, G) {
    let i: u8 = i.as_canonical_u64().try_into().unwrap();
    let j: u8 = j.as_canonical_u64().try_into().unwrap();
    let (r, o) = i.overflowing_add(j);
    (G::from_u8(r), G::from_bool(o))
  }

  #[inline]
  pub fn and(i: &G, j: &G) -> G {
    let i: u8 = i.as_canonical_u64().try_into().unwrap();
    let j: u8 = j.as_canonical_u64().try_into().unwrap();
    G::from_u8(i & j)
  }

  #[inline]
  pub fn or(i: &G, j: &G) -> G {
    let i: u8 = i.as_canonical_u64().try_into().unwrap();
    let j: u8 = j.as_canonical_u64().try_into().unwrap();
    G::from_u8(i | j)
  }

  #[inline]
  pub fn sub(i: &G, j: &G) -> (G, G) {
    let i: u8 = i.as_canonical_u64().try_into().unwrap();
    let j: u8 = j.as_canonical_u64().try_into().unwrap();
    let (r, u) = i.overflowing_sub(j);
    (G::from_u8(r), G::from_bool(u))
  }

  #[inline]
  pub fn less_than(i: &G, j: &G) -> G {
    let i: u8 = i.as_canonical_u64().try_into().unwrap();
    let j: u8 = j.as_canonical_u64().try_into().unwrap();
    G::from_bool(i < j)
  }

  /// `u8 * u8 -> (low byte, high byte)`. The product fits in 16 bits.
  #[inline]
  pub fn mul(i: &G, j: &G) -> (G, G) {
    let i: u8 = i.as_canonical_u64().try_into().unwrap();
    let j: u8 = j.as_canonical_u64().try_into().unwrap();
    let p = u16::from(i) * u16::from(j);
    (G::from_u8((p & 0xff) as u8), G::from_u8((p >> 8) as u8))
  }

  /// Building block for a right-rotation by 7 bits over little-endian bytes:
  /// the xor `x = i ^ j` split as `(x >> 7, x << 1)` (shift mod 256).
  #[inline]
  pub fn xor_split7_u8(i: u8, j: u8) -> (u8, u8) {
    let x = i ^ j;
    (x >> 7, x << 1)
  }

  /// Building block for a right-rotation by 4 bits over little-endian bytes:
  /// the xor `x = i ^ j` split as `(x >> 4, x << 4)` (shifts mod 256).
  #[inline]
  pub fn xor_split4_u8(i: u8, j: u8) -> (u8, u8) {
    let x = i ^ j;
    (x >> 4, x << 4)
  }

  #[inline]
  pub fn xor_split7(i: &G, j: &G) -> (G, G) {
    let (hi, lo) = Self::xor_split7_u8(
      u8::try_from(i.as_canonical_u64()).expect("byte-table input"),
      u8::try_from(j.as_canonical_u64()).expect("byte-table input"),
    );
    (G::from_u8(hi), G::from_u8(lo))
  }

  #[inline]
  pub fn xor_split4(i: &G, j: &G) -> (G, G) {
    let (hi, lo) = Self::xor_split4_u8(
      u8::try_from(i.as_canonical_u64()).expect("byte-table input"),
      u8::try_from(j.as_canonical_u64()).expect("byte-table input"),
    );
    (G::from_u8(hi), G::from_u8(lo))
  }
}
