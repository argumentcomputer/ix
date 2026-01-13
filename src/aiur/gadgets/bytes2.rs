use multi_stark::{
  builder::symbolic::{SymbolicExpression, preprocessed_var, var},
  lookup::Lookup,
  p3_air::{Air, AirBuilder, BaseAir},
  p3_field::{PrimeCharacteristicRing, PrimeField64},
  p3_matrix::dense::RowMajorMatrix,
};

use crate::aiur::{
  G, execute::QueryRecord, gadgets::AiurGadget, u8_add_channel, u8_and_channel,
  u8_or_channel, u8_xor_channel,
};

/// Number of columns in the trace with multiplicities for
/// - xor
/// - overflowing add
/// - and
/// - or
const TRACE_WIDTH: usize = 4;

/// Number of columns in the preprocessed trace:
/// - first raw byte value
/// - second raw byte value
/// - xor result
/// - add result
/// - add overflow
/// - and result
/// - or result
const PREPROCESSED_TRACE_WIDTH: usize = 7;

/// AIR implementer for arity 2 byte-related lookups.
pub(crate) struct Bytes2;

pub(crate) enum Bytes2Op {
  Xor,
  Add,
  And,
  Or,
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

        // Overflowing add
        let (r, o) = i.overflowing_add(j);
        trace_values.push(G::from_u8(r));
        trace_values.push(G::from_bool(o));

        // And
        trace_values.push(G::from_u8(i & j));

        // Or
        trace_values.push(G::from_u8(i | j));
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
      Bytes2Op::Xor => 1,
      Bytes2Op::Add => 2,
      Bytes2Op::And => 1,
      Bytes2Op::Or => 1,
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
        let (r, o) = Self::add(i, j);
        vec![r, o]
      },
      Bytes2Op::And => {
        record.bytes2_queries.bump_and(i, j);
        vec![Self::and(i, j)]
      },
      Bytes2Op::Or => {
        record.bytes2_queries.bump_or(i, j);
        vec![Self::or(i, j)]
      },
    }
  }

  fn lookups(&self) -> Vec<Lookup<SymbolicExpression<G>>> {
    // Channels
    let xor_channel = u8_xor_channel().into();
    let add_channel = u8_add_channel().into();
    let and_channel = u8_and_channel().into();
    let or_channel = u8_or_channel().into();

    // Multiplicity columns
    let xor_multiplicity = var(0);
    let add_multiplicity = var(1);
    let and_multiplicity = var(2);
    let or_multiplicity = var(3);

    // Preprocessed columns
    let i = preprocessed_var(0);
    let j = preprocessed_var(1);
    let xor = preprocessed_var(2);
    let add_r = preprocessed_var(3);
    let add_o = preprocessed_var(4);
    let and = preprocessed_var(5);
    let or = preprocessed_var(6);

    let pull_xor = Lookup::pull(
      xor_multiplicity,
      vec![xor_channel, i.clone(), j.clone(), xor],
    );

    let pull_add = Lookup::pull(
      add_multiplicity,
      vec![add_channel, i.clone(), j.clone(), add_r, add_o],
    );

    let pull_and = Lookup::pull(
      and_multiplicity,
      vec![and_channel, i.clone(), j.clone(), and],
    );

    let pull_or =
      Lookup::pull(or_multiplicity, vec![or_channel, i, j, or]);

    vec![pull_xor, pull_add, pull_and, pull_or]
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
    let and_channel = u8_and_channel();
    let or_channel = u8_or_channel();

    rows
      .chunks_exact_mut(TRACE_WIDTH)
      .enumerate()
      .zip(&record.bytes2_queries.0)
      .zip(&mut lookups)
      .for_each(|(((row_idx, row), &[xor, add, and, or]), row_lookups)| {
        let i = G::from_usize(row_idx / 256);
        let j = G::from_usize(row_idx % 256);

        row[0] = xor;
        row[1] = add;
        row[2] = and;
        row[3] = or;

        // Pull xor.
        row_lookups[0] =
          Lookup::pull(xor, vec![xor_channel, i, j, Self::xor(&i, &j)]);

        // Pull add.
        let (r, o) = Self::add(&i, &j);
        row_lookups[1] = Lookup::pull(add, vec![add_channel, i, j, r, o]);

        // Pull and.
        row_lookups[2] =
          Lookup::pull(and, vec![and_channel, i, j, Self::and(&i, &j)]);

        // Pull or.
        row_lookups[3] =
          Lookup::pull(or, vec![or_channel, i, j, Self::or(&i, &j)]);
      });
    (RowMajorMatrix::new(rows, TRACE_WIDTH), lookups)
  }
}

/// Accumulator of queries performed against `Bytes1`.
pub(crate) struct Bytes2Queries(Box<[[G; TRACE_WIDTH]]>);

impl Bytes2Queries {
  #[inline]
  pub(crate) fn new() -> Self {
    Self(vec![[G::ZERO; TRACE_WIDTH]; 256 * 256].into_boxed_slice())
  }

  fn bump_xor(&mut self, i: &G, j: &G) {
    self.bump_multiplicity_for(i, j, 0)
  }

  fn bump_add(&mut self, i: &G, j: &G) {
    self.bump_multiplicity_for(i, j, 1)
  }

  fn bump_and(&mut self, i: &G, j: &G) {
    self.bump_multiplicity_for(i, j, 2)
  }

  fn bump_or(&mut self, i: &G, j: &G) {
    self.bump_multiplicity_for(i, j, 3)
  }

  fn bump_multiplicity_for(&mut self, i: &G, j: &G, col: usize) {
    let i = usize::try_from(i.as_canonical_u64()).unwrap();
    let j = usize::try_from(j.as_canonical_u64()).unwrap();
    let row = 256 * i + j;
    self.0[row][col] += G::ONE;
  }
}

impl Bytes2 {
  #[inline]
  pub(crate) fn xor(i: &G, j: &G) -> G {
    let i: u8 = i.as_canonical_u64().try_into().unwrap();
    let j: u8 = j.as_canonical_u64().try_into().unwrap();
    G::from_u8(i ^ j)
  }

  #[inline]
  pub(crate) fn add(i: &G, j: &G) -> (G, G) {
    let i: u8 = i.as_canonical_u64().try_into().unwrap();
    let j: u8 = j.as_canonical_u64().try_into().unwrap();
    let (r, o) = i.overflowing_add(j);
    (G::from_u8(r), G::from_bool(o))
  }

  #[inline]
  pub(crate) fn and(i: &G, j: &G) -> G {
    let i: u8 = i.as_canonical_u64().try_into().unwrap();
    let j: u8 = j.as_canonical_u64().try_into().unwrap();
    G::from_u8(i & j)
  }

  #[inline]
  pub(crate) fn or(i: &G, j: &G) -> G {
    let i: u8 = i.as_canonical_u64().try_into().unwrap();
    let j: u8 = j.as_canonical_u64().try_into().unwrap();
    G::from_u8(i | j)
  }
}
