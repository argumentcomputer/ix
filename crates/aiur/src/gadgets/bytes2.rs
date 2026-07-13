use multi_stark::{
  builder::symbolic::{SymbolicExpression, preprocessed_var, var},
  lookup::Lookup,
  p3_air::{Air, AirBuilder, BaseAir},
  p3_field::{PrimeCharacteristicRing, PrimeField64},
  p3_matrix::dense::RowMajorMatrix,
};

use crate::{
  G, execute::QueryRecord, gadgets::AiurGadget, u8_add_channel, u8_and_channel,
  u8_chain_rotr_channel, u8_less_than_channel, u8_mul_channel, u8_or_channel,
  u8_range_check_channel, u8_sub_channel, u8_xor_channel,
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
/// - chain_rotr1 .. chain_rotr7 (one column per rotation amount)
const TRACE_WIDTH: usize = 15;

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
/// - for each k in 1..=7, chain_rotr{k} outputs 0..2:
///   (`i >> k + j << (8-k)`, `j >> k`, `i << (8-k)`)
const PREPROCESSED_TRACE_WIDTH: usize = 10 + 3 * 7;

/// Column index of the `chain_rotr{k}` multiplicity in the main trace.
#[inline]
const fn chain_rotr_trace_col(k: u8) -> usize {
  7 + k as usize
}

/// Column index of `chain_rotr{k}` output 0 in the preprocessed trace
/// (outputs 1 and 2 follow contiguously).
#[inline]
const fn chain_rotr_preprocessed_col(k: u8) -> usize {
  10 + 3 * (k as usize - 1)
}

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
  /// Chainable right-rotation by `k` bits (1..=7) over a byte pair.
  ChainRotr(u8),
}

impl BaseAir<G> for Bytes2 {
  fn width(&self) -> usize {
    TRACE_WIDTH
  }

  /// Builds the preprocessed trace over all 256 byte values.
  fn preprocessed_trace(&self) -> Option<RowMajorMatrix<G>> {
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

        // Chain rotr{k} (combined byte, j high part, i low part)
        for k in 1..=7 {
          let (o0, o1, o2) = Self::chain_rotr_u8(k, i, j);
          trace_values.push(G::from_u8(o0));
          trace_values.push(G::from_u8(o1));
          trace_values.push(G::from_u8(o2));
        }
      }
    }
    Some(RowMajorMatrix::new(trace_values, PREPROCESSED_TRACE_WIDTH))
  }
}

impl<AB: AirBuilder<F = G>> Air<AB> for Bytes2 {
  /// A no-op, since all constraints are enforced through lookups.
  fn eval(&self, _builder: &mut AB) {}
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
      Bytes2Op::Mul => 2,
      Bytes2Op::ChainRotr(_) => 3,
    }
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
      Bytes2Op::ChainRotr(k) => {
        record.bytes2_queries.bump_chain_rotr(*k, i, j);
        let (o0, o1, o2) = Self::chain_rotr(*k, i, j);
        vec![o0, o1, o2]
      },
    }
  }

  fn lookups(&self) -> Vec<Lookup<SymbolicExpression<G>>> {
    // Channels
    let xor_channel = u8_xor_channel().into();
    let add_channel = u8_add_channel().into();
    let sub_channel = u8_sub_channel().into();
    let and_channel = u8_and_channel().into();
    let or_channel = u8_or_channel().into();
    let less_than_channel = u8_less_than_channel().into();
    let range_check_channel = u8_range_check_channel().into();
    let mul_channel = u8_mul_channel().into();

    // Multiplicity columns
    let xor_multiplicity = var(0);
    let add_multiplicity = var(1);
    let sub_multiplicity = var(2);
    let and_multiplicity = var(3);
    let or_multiplicity = var(4);
    let less_than_multiplicity = var(5);
    let range_check_multiplicity = var(6);
    let mul_multiplicity = var(7);

    // Preprocessed columns
    let i = preprocessed_var(0);
    let j = preprocessed_var(1);
    let xor = preprocessed_var(2);
    let add_r = preprocessed_var(3);
    let sub_r = preprocessed_var(4);
    let and = preprocessed_var(5);
    let or = preprocessed_var(6);
    let less_than = preprocessed_var(7);
    let mul_lo = preprocessed_var(8);
    let mul_hi = preprocessed_var(9);

    let pull_xor = Lookup::pull(
      xor_multiplicity,
      vec![xor_channel, i.clone(), j.clone(), xor],
    );

    let pull_add = Lookup::pull(
      add_multiplicity,
      vec![add_channel, i.clone(), j.clone(), add_r],
    );

    let pull_sub = Lookup::pull(
      sub_multiplicity,
      vec![sub_channel, i.clone(), j.clone(), sub_r],
    );

    let pull_and = Lookup::pull(
      and_multiplicity,
      vec![and_channel, i.clone(), j.clone(), and],
    );

    let pull_or =
      Lookup::pull(or_multiplicity, vec![or_channel, i.clone(), j.clone(), or]);

    let pull_less_than = Lookup::pull(
      less_than_multiplicity,
      vec![less_than_channel, i.clone(), j.clone(), less_than],
    );

    let pull_mul = Lookup::pull(
      mul_multiplicity,
      vec![mul_channel, i.clone(), j.clone(), mul_lo, mul_hi],
    );

    let pull_range_check = Lookup::pull(
      range_check_multiplicity,
      vec![range_check_channel, i.clone(), j.clone()],
    );

    let pull_chain_rotrs = (1..=7u8).map(|k| {
      let col = chain_rotr_preprocessed_col(k);
      Lookup::pull(
        var(chain_rotr_trace_col(k)),
        vec![
          u8_chain_rotr_channel(k).into(),
          i.clone(),
          j.clone(),
          preprocessed_var(col),
          preprocessed_var(col + 1),
          preprocessed_var(col + 2),
        ],
      )
    });

    let mut lookups = vec![
      pull_xor,
      pull_add,
      pull_sub,
      pull_and,
      pull_or,
      pull_less_than,
      pull_range_check,
      pull_mul,
    ];
    lookups.extend(pull_chain_rotrs);
    lookups
  }

  fn witness_data(
    &self,
    record: &QueryRecord,
  ) -> (RowMajorMatrix<G>, Vec<Vec<Lookup<G>>>) {
    let mut rows = vec![G::ZERO; 256 * 256 * TRACE_WIDTH];

    // There are `TRACE_WIDTH` lookups per row, one for each multiplicity.
    let mut lookups = vec![vec![Lookup::empty(); TRACE_WIDTH]; 256 * 256];

    let xor_channel = u8_xor_channel();
    let add_channel = u8_add_channel();
    let sub_channel = u8_sub_channel();
    let and_channel = u8_and_channel();
    let or_channel = u8_or_channel();
    let less_than_channel = u8_less_than_channel();
    let range_check_channel = u8_range_check_channel();
    let mul_channel = u8_mul_channel();

    rows
      .chunks_exact_mut(TRACE_WIDTH)
      .enumerate()
      .zip(&record.bytes2_queries.0)
      .zip(&mut lookups)
      .for_each(|(((row_idx, row), multiplicities), row_lookups)| {
        let [xor, add, sub, and, or, less_than, range_check, mul, ..] =
          *multiplicities;
        let i = G::from_usize(row_idx / 256);
        let j = G::from_usize(row_idx % 256);

        row.copy_from_slice(multiplicities);

        // Pull xor.
        row_lookups[0] =
          Lookup::pull(xor, vec![xor_channel, i, j, Self::xor(&i, &j)]);

        // Pull add (low byte only; carry derived in-circuit).
        let (r, _o) = Self::add(&i, &j);
        row_lookups[1] = Lookup::pull(add, vec![add_channel, i, j, r]);

        // Pull sub (low byte only; borrow derived in-circuit).
        let (r, _u) = Self::sub(&i, &j);
        row_lookups[2] = Lookup::pull(sub, vec![sub_channel, i, j, r]);

        // Pull and.
        row_lookups[3] =
          Lookup::pull(and, vec![and_channel, i, j, Self::and(&i, &j)]);

        // Pull or.
        row_lookups[4] =
          Lookup::pull(or, vec![or_channel, i, j, Self::or(&i, &j)]);

        // Pull less_than.
        row_lookups[5] = Lookup::pull(
          less_than,
          vec![less_than_channel, i, j, Self::less_than(&i, &j)],
        );

        // Pull range_check.
        row_lookups[6] =
          Lookup::pull(range_check, vec![range_check_channel, i, j]);

        // Pull mul.
        let (lo, hi) = Self::mul(&i, &j);
        row_lookups[7] = Lookup::pull(mul, vec![mul_channel, i, j, lo, hi]);

        // Pull chain_rotr{k}.
        for k in 1..=7u8 {
          let col = chain_rotr_trace_col(k);
          let (o0, o1, o2) = Self::chain_rotr(k, &i, &j);
          row_lookups[col] = Lookup::pull(
            multiplicities[col],
            vec![u8_chain_rotr_channel(k), i, j, o0, o1, o2],
          );
        }
      });
    (RowMajorMatrix::new(rows, TRACE_WIDTH), lookups)
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
    self.bump_multiplicity_for(i, j, 3)
  }

  pub(crate) fn bump_or(&mut self, i: &G, j: &G) {
    self.bump_multiplicity_for(i, j, 4)
  }

  pub(crate) fn bump_less_than(&mut self, i: &G, j: &G) {
    self.bump_multiplicity_for(i, j, 5)
  }

  pub fn bump_range_check(&mut self, i: &G, j: &G) {
    self.bump_multiplicity_for(i, j, 6)
  }

  pub(crate) fn bump_mul(&mut self, i: &G, j: &G) {
    self.bump_multiplicity_for(i, j, 7)
  }

  pub(crate) fn bump_chain_rotr(&mut self, k: u8, i: &G, j: &G) {
    self.bump_multiplicity_for(i, j, chain_rotr_trace_col(k))
  }

  pub(crate) fn bump_multiplicity_for(&mut self, i: &G, j: &G, col: usize) {
    let i = usize::try_from(i.as_canonical_u64()).unwrap();
    let j = usize::try_from(j.as_canonical_u64()).unwrap();
    let row = 256 * i + j;
    self.0[row][col] += G::ONE;
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

  /// Chainable building block for a right-rotation by `k` bits (1..=7) over a
  /// sequence of little-endian bytes. Given adjacent bytes `i`, `j`, returns
  /// `(i>>k + j<<(8-k), j>>k, i<<(8-k))` where shifts are taken mod 256.
  /// Chaining the outputs across all adjacent byte pairs yields a `rotr{k}`
  /// of any width (u16, u32, u64, ...): e.g. the u32 `rotr7` of
  /// `[b0,b1,b2,b3]` is `[A0, A1+B2, B0, B1+A2]` for `A = chain_rotr7(b0,b1)`,
  /// `B = chain_rotr7(b2,b3)`.
  #[inline]
  pub fn chain_rotr_u8(k: u8, i: u8, j: u8) -> (u8, u8, u8) {
    debug_assert!((1..=7).contains(&k));
    ((i >> k) + (j << (8 - k)), j >> k, i << (8 - k))
  }

  #[inline]
  pub fn chain_rotr(k: u8, i: &G, j: &G) -> (G, G, G) {
    let i: u8 = i.as_canonical_u64().try_into().unwrap();
    let j: u8 = j.as_canonical_u64().try_into().unwrap();
    let (o0, o1, o2) = Self::chain_rotr_u8(k, i, j);
    (G::from_u8(o0), G::from_u8(o1), G::from_u8(o2))
  }

  /// Legacy fixed-amount aliases, used by the codegen'd IxVM kernel.
  #[inline]
  pub fn chain_rotr7(i: &G, j: &G) -> (G, G, G) {
    Self::chain_rotr(7, i, j)
  }

  #[inline]
  pub fn chain_rotr4(i: &G, j: &G) -> (G, G, G) {
    Self::chain_rotr(4, i, j)
  }
}
