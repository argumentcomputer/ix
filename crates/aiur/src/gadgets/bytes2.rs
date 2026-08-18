use multi_stark::{
  expr::Expr,
  lookup::{Lookup, LookupValues},
  p3_field::{PrimeCharacteristicRing, PrimeField64},
  p3_matrix::dense::RowMajorMatrix,
};

use crate::{
  G, execute::QueryRecord, gadgets::AiurGadget, u8_add_channel, u8_and_channel,
  u8_less_than_channel, u8_mul_channel, u8_or_channel, u8_range_check_channel,
  u8_sub_channel, u8_xor_channel, u8_xor_split4_channel, u8_xor_split7_channel,
};

/// Number of columns in the trace with multiplicities for
/// - xor
/// - overflowing add
/// - overflowing sub
/// - and
/// - or
/// - less_than
/// - range_check
/// - mul
/// - xor_split7
/// - xor_split4
const TRACE_WIDTH: usize = 10;

/// Number of columns in the preprocessed trace:
/// - first raw byte value
/// - second raw byte value
/// - xor result
/// - add result (low byte only; the carry is derived in-circuit as
///   `(x + y - z) / 256`, so it needs no column or lookup)
/// - sub result (low byte only; the borrow is derived in-circuit as
///   `(z + y - x) / 256`, so it needs no column or lookup)
/// - and result
/// - or result
/// - less_than result
/// - mul low byte
/// - mul high byte
/// - xor_split7 high and shifted-low outputs
/// - xor_split4 high and shifted-low outputs
const PREPROCESSED_TRACE_WIDTH: usize = 14;

/// AIR implementer for arity 2 byte-related lookups.
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

        // And
        trace_values.push(G::from_u8(i & j));

        // Or
        trace_values.push(G::from_u8(i | j));

        // Less than
        trace_values.push(G::from_bool(i < j));

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
    record: &QueryRecord,
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
    let and_channel = Expr::constant(u8_and_channel());
    let or_channel = Expr::constant(u8_or_channel());
    let less_than_channel = Expr::constant(u8_less_than_channel());
    let range_check_channel = Expr::constant(u8_range_check_channel());
    let mul_channel = Expr::constant(u8_mul_channel());
    let xor_split7_channel = Expr::constant(u8_xor_split7_channel());
    let xor_split4_channel = Expr::constant(u8_xor_split4_channel());

    // Multiplicity columns
    let xor_multiplicity = Expr::main(0);
    let add_multiplicity = Expr::main(1);
    let sub_multiplicity = Expr::main(2);
    let and_multiplicity = Expr::main(3);
    let or_multiplicity = Expr::main(4);
    let less_than_multiplicity = Expr::main(5);
    let range_check_multiplicity = Expr::main(6);
    let mul_multiplicity = Expr::main(7);
    let xor_split7_multiplicity = Expr::main(8);
    let xor_split4_multiplicity = Expr::main(9);

    // Preprocessed columns
    let i = Expr::preprocessed(0);
    let j = Expr::preprocessed(1);
    let xor = Expr::preprocessed(2);
    let add_r = Expr::preprocessed(3);
    let sub_r = Expr::preprocessed(4);
    let and = Expr::preprocessed(5);
    let or = Expr::preprocessed(6);
    let less_than = Expr::preprocessed(7);
    let mul_lo = Expr::preprocessed(8);
    let mul_hi = Expr::preprocessed(9);
    let xor_split7_hi = Expr::preprocessed(10);
    let xor_split7_lo = Expr::preprocessed(11);
    let xor_split4_hi = Expr::preprocessed(12);
    let xor_split4_lo = Expr::preprocessed(13);

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

    let pull_and = Lookup {
      multiplicity: -and_multiplicity,
      args: vec![and_channel, i.clone(), j.clone(), and],
    };

    let pull_or = Lookup {
      multiplicity: -or_multiplicity,
      args: vec![or_channel, i.clone(), j.clone(), or],
    };

    let pull_less_than = Lookup {
      multiplicity: -less_than_multiplicity,
      args: vec![less_than_channel, i.clone(), j.clone(), less_than],
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
      pull_and,
      pull_or,
      pull_less_than,
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

    // There are `TRACE_WIDTH` lookups per row, one for each multiplicity.
    let mut builder = LookupValues::builder(256 * 256, slot_arg_widths);
    let mut row_writers = builder.rows_mut();

    let xor_channel = u8_xor_channel();
    let add_channel = u8_add_channel();
    let sub_channel = u8_sub_channel();
    let and_channel = u8_and_channel();
    let or_channel = u8_or_channel();
    let less_than_channel = u8_less_than_channel();
    let range_check_channel = u8_range_check_channel();
    let mul_channel = u8_mul_channel();
    let xor_split7_channel = u8_xor_split7_channel();
    let xor_split4_channel = u8_xor_split4_channel();

    rows
      .chunks_exact_mut(TRACE_WIDTH)
      .enumerate()
      .zip(&record.bytes2_queries.0)
      .zip(row_writers.iter_mut())
      .for_each(
        |(
          (
            (row_idx, row),
            &[
              xor,
              add,
              sub,
              and,
              or,
              less_than,
              range_check,
              mul,
              xor_split7,
              xor_split4,
            ],
          ),
          row_lookups,
        )| {
          let i = G::from_usize(row_idx / 256);
          let j = G::from_usize(row_idx % 256);

          row[0] = xor;
          row[1] = add;
          row[2] = sub;
          row[3] = and;
          row[4] = or;
          row[5] = less_than;
          row[6] = range_check;
          row[7] = mul;
          row[8] = xor_split7;
          row[9] = xor_split4;

          // Pull xor.
          row_lookups.pull(0, xor, &[xor_channel, i, j, Self::xor(&i, &j)]);

          // Pull add (low byte only; carry derived in-circuit).
          let (r, _o) = Self::add(&i, &j);
          row_lookups.pull(1, add, &[add_channel, i, j, r]);

          // Pull sub (low byte only; borrow derived in-circuit).
          let (r, _u) = Self::sub(&i, &j);
          row_lookups.pull(2, sub, &[sub_channel, i, j, r]);

          // Pull and.
          row_lookups.pull(3, and, &[and_channel, i, j, Self::and(&i, &j)]);

          // Pull or.
          row_lookups.pull(4, or, &[or_channel, i, j, Self::or(&i, &j)]);

          // Pull less_than.
          row_lookups.pull(
            5,
            less_than,
            &[less_than_channel, i, j, Self::less_than(&i, &j)],
          );
          // Pull range_check.
          row_lookups.pull(6, range_check, &[range_check_channel, i, j]);

          // Pull mul.
          let (lo, hi) = Self::mul(&i, &j);
          row_lookups.pull(7, mul, &[mul_channel, i, j, lo, hi]);

          // Pull xor_split7.
          let (hi, lo) = Self::xor_split7(&i, &j);
          row_lookups.pull(8, xor_split7, &[xor_split7_channel, i, j, hi, lo]);

          // Pull xor_split4.
          let (hi, lo) = Self::xor_split4(&i, &j);
          row_lookups.pull(9, xor_split4, &[xor_split4_channel, i, j, hi, lo]);
        },
      );
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

  pub(crate) fn bump_xor(&self, i: &G, j: &G) {
    self.bump_multiplicity_for(i, j, 0)
  }

  pub(crate) fn bump_add(&self, i: &G, j: &G) {
    self.bump_multiplicity_for(i, j, 1)
  }

  pub(crate) fn bump_sub(&self, i: &G, j: &G) {
    self.bump_multiplicity_for(i, j, 2)
  }

  pub(crate) fn bump_and(&self, i: &G, j: &G) {
    self.bump_multiplicity_for(i, j, 3)
  }

  pub(crate) fn bump_or(&self, i: &G, j: &G) {
    self.bump_multiplicity_for(i, j, 4)
  }

  pub(crate) fn bump_less_than(&self, i: &G, j: &G) {
    self.bump_multiplicity_for(i, j, 5)
  }

  pub fn bump_range_check(&self, i: &G, j: &G) {
    self.bump_multiplicity_for(i, j, 6)
  }

  pub(crate) fn bump_mul(&self, i: &G, j: &G) {
    self.bump_multiplicity_for(i, j, 7)
  }

  pub(crate) fn bump_xor_split7(&self, i: &G, j: &G) {
    self.bump_multiplicity_for(i, j, 8)
  }

  pub(crate) fn bump_xor_split4(&self, i: &G, j: &G) {
    self.bump_multiplicity_for(i, j, 9)
  }

  /// Read counter cell `[256*i + j][col]` (relaxed; used by the
  /// derived-multiplicity differential check in `trace.rs`).
  pub(crate) fn count(&self, cell: usize, col: usize) -> u64 {
    use std::sync::atomic::{AtomicU64, Ordering};
    let c: &G = &self.0[cell][col];
    unsafe { AtomicU64::from_ptr((c as *const G as *mut G).cast()) }
      .load(Ordering::Relaxed)
  }

  /// Overwrite counter cell (seal-time application of derived
  /// multiplicities; see `trace::apply_multiplicities`).
  pub(crate) fn set_count(&self, cell: usize, col: usize, v: u64) {
    use std::sync::atomic::{AtomicU64, Ordering};
    let cell: &G = &self.0[cell][col];
    unsafe { AtomicU64::from_ptr((cell as *const G as *mut G).cast()) }
      .store(v, Ordering::Relaxed);
  }

  /// Relaxed atomic bump on the counter cell (see
  /// `Bytes1Queries::bump_multiplicity_for` for why `u64` addition is
  /// field addition here).
  pub(crate) fn bump_multiplicity_for(&self, i: &G, j: &G, col: usize) {
    use std::sync::atomic::{AtomicU64, Ordering};
    let i = usize::try_from(i.as_canonical_u64()).unwrap();
    let j = usize::try_from(j.as_canonical_u64()).unwrap();
    let cell: &G = &self.0[256 * i + j][col];
    unsafe { AtomicU64::from_ptr((cell as *const G as *mut G).cast()) }
      .fetch_add(1, Ordering::Relaxed);
  }
}

impl Bytes2 {
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
