use multi_stark::{
  builder::symbolic::{SymbolicExpression, preprocessed_var, var},
  lookup::Lookup,
  p3_air::{Air, AirBuilder, BaseAir},
  p3_field::{PrimeCharacteristicRing, PrimeField64},
  p3_matrix::dense::RowMajorMatrix,
};

use crate::aiur::{
  G, execute::QueryRecord, gadgets::AiurGadget, u8_add_channel, u8_and_channel,
  u8_less_than_channel, u8_or_channel, u8_sub_channel, u8_xor_channel,
};

/// Number of columns in the trace with multiplicities for
/// - xor
/// - overflowing add
/// - overflowing sub
/// - and
/// - or
/// - less_than
const TRACE_WIDTH: usize = 6;

/// Number of columns in the preprocessed trace:
/// - first raw byte value
/// - second raw byte value
/// - xor result
/// - add result
/// - add overflow
/// - sub result
/// - sub underflow
/// - and result
/// - or result
/// - less_than result
const PREPROCESSED_TRACE_WIDTH: usize = 10;

/// AIR implementer for arity 2 byte-related lookups.
pub(crate) struct Bytes2;

pub(crate) enum Bytes2Op {
  Xor,
  Add,
  Sub,
  And,
  Or,
  LessThan,
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

        // Overflowing sub
        let (r, u) = i.overflowing_sub(j);
        trace_values.push(G::from_u8(r));
        trace_values.push(G::from_bool(u));

        // And
        trace_values.push(G::from_u8(i & j));

        // Or
        trace_values.push(G::from_u8(i | j));

        // Less than
        trace_values.push(G::from_bool(i < j));
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
      Bytes2Op::Xor | Bytes2Op::And | Bytes2Op::Or | Bytes2Op::LessThan => 1,
      Bytes2Op::Add | Bytes2Op::Sub => 2,
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
      Bytes2Op::Sub => {
        record.bytes2_queries.bump_sub(i, j);
        let (r, u) = Self::sub(i, j);
        vec![r, u]
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

    // Multiplicity columns
    let xor_multiplicity = var(0);
    let add_multiplicity = var(1);
    let sub_multiplicity = var(2);
    let and_multiplicity = var(3);
    let or_multiplicity = var(4);
    let less_than_multiplicity = var(5);

    // Preprocessed columns
    let i = preprocessed_var(0);
    let j = preprocessed_var(1);
    let xor = preprocessed_var(2);
    let add_r = preprocessed_var(3);
    let add_o = preprocessed_var(4);
    let sub_r = preprocessed_var(5);
    let sub_u = preprocessed_var(6);
    let and = preprocessed_var(7);
    let or = preprocessed_var(8);
    let less_than = preprocessed_var(9);

    let pull_xor = Lookup::pull(
      xor_multiplicity,
      vec![xor_channel, i.clone(), j.clone(), xor],
    );

    let pull_add = Lookup::pull(
      add_multiplicity,
      vec![add_channel, i.clone(), j.clone(), add_r, add_o],
    );

    let pull_sub = Lookup::pull(
      sub_multiplicity,
      vec![sub_channel, i.clone(), j.clone(), sub_r, sub_u],
    );

    let pull_and = Lookup::pull(
      and_multiplicity,
      vec![and_channel, i.clone(), j.clone(), and],
    );

    let pull_or =
      Lookup::pull(or_multiplicity, vec![or_channel, i.clone(), j.clone(), or]);

    let pull_less_than = Lookup::pull(
      less_than_multiplicity,
      vec![less_than_channel, i, j, less_than],
    );

    vec![pull_xor, pull_add, pull_sub, pull_and, pull_or, pull_less_than]
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

    rows
      .chunks_exact_mut(TRACE_WIDTH)
      .enumerate()
      .zip(&record.bytes2_queries.0)
      .zip(&mut lookups)
      .for_each(
        |(
          ((row_idx, row), &[xor, add, sub, and, or, less_than]),
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

          // Pull xor.
          row_lookups[0] =
            Lookup::pull(xor, vec![xor_channel, i, j, Self::xor(&i, &j)]);

          // Pull add.
          let (r, o) = Self::add(&i, &j);
          row_lookups[1] = Lookup::pull(add, vec![add_channel, i, j, r, o]);

          // Pull sub.
          let (r, u) = Self::sub(&i, &j);
          row_lookups[2] = Lookup::pull(sub, vec![sub_channel, i, j, r, u]);

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
        },
      );
    (RowMajorMatrix::new(rows, TRACE_WIDTH), lookups)
  }
}

/// Accumulator of queries performed against `Bytes2`.
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

  fn bump_sub(&mut self, i: &G, j: &G) {
    self.bump_multiplicity_for(i, j, 2)
  }

  fn bump_and(&mut self, i: &G, j: &G) {
    self.bump_multiplicity_for(i, j, 3)
  }

  fn bump_or(&mut self, i: &G, j: &G) {
    self.bump_multiplicity_for(i, j, 4)
  }

  fn bump_less_than(&mut self, i: &G, j: &G) {
    self.bump_multiplicity_for(i, j, 5)
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

  #[inline]
  pub(crate) fn sub(i: &G, j: &G) -> (G, G) {
    let i: u8 = i.as_canonical_u64().try_into().unwrap();
    let j: u8 = j.as_canonical_u64().try_into().unwrap();
    let (r, u) = i.overflowing_sub(j);
    (G::from_u8(r), G::from_bool(u))
  }

  #[inline]
  pub(crate) fn less_than(i: &G, j: &G) -> G {
    let i: u8 = i.as_canonical_u64().try_into().unwrap();
    let j: u8 = j.as_canonical_u64().try_into().unwrap();
    G::from_bool(i < j)
  }
}
