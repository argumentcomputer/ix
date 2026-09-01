use multi_stark::{
  expr::Expr,
  lookup::{Lookup, LookupValues},
  p3_matrix::dense::RowMajorMatrix,
};

use crate::{
  AiurField, G, execute::QueryRecord, gadgets::AiurGadget,
  u8_bit_decomposition_channel, u8_shift_left_channel, u8_shift_right_channel,
};

/// Number of columns in the trace with multiplicities for
/// - bit decomposition
/// - shift-left
/// - shift-right
const TRACE_WIDTH: usize = 3;

/// Number of columns in the preprocessed trace:
/// - raw byte value
/// - 8 bits in LE
/// - value shifted left
/// - value shifted right
const PREPROCESSED_TRACE_WIDTH: usize = 11;

/// AIR implementer for arity 1 byte-related lookups.
pub struct Bytes1;

pub enum Bytes1Op {
  BitDecomposition,
  ShiftLeft,
  ShiftRight,
}

impl<F: AiurField> AiurGadget<F> for Bytes1 {
  type Op = Bytes1Op;

  fn output_size(&self, op: &Bytes1Op) -> usize {
    match op {
      Bytes1Op::BitDecomposition => 8,
      Bytes1Op::ShiftLeft | Bytes1Op::ShiftRight => 1,
    }
  }

  fn main_width(&self) -> usize {
    TRACE_WIDTH
  }

  /// Builds the preprocessed trace over all 256 byte values.
  fn preprocessed(&self) -> Option<RowMajorMatrix<F>> {
    let mut values = vec![F::ZERO; 256 * PREPROCESSED_TRACE_WIDTH];
    values.chunks_exact_mut(PREPROCESSED_TRACE_WIDTH).enumerate().for_each(
      |(i, row)| {
        let byte = F::from_usize(i);

        // Raw byte value
        row[0] = byte;

        // 8 bits in LE
        for (row_elt, bit) in
          row[1..].iter_mut().zip(Self::bit_decompose(&byte))
        {
          *row_elt = bit;
        }

        // Byte shifted left
        row[9] = Self::shift_left(&byte);

        // Byte shifted right
        row[10] = Self::shift_right(&byte);
      },
    );
    Some(RowMajorMatrix::new(values, PREPROCESSED_TRACE_WIDTH))
  }

  fn execute(
    &self,
    op: &Bytes1Op,
    input: &[F],
    record: &mut QueryRecord<F>,
  ) -> Vec<F> {
    let byte = &input[0];
    match op {
      Bytes1Op::BitDecomposition => {
        record.bytes1_queries.bump_bit_decomposition(byte);
        Self::bit_decompose(byte)
      },
      Bytes1Op::ShiftLeft => {
        record.bytes1_queries.bump_shift_left(byte);
        vec![Self::shift_left(byte)]
      },
      Bytes1Op::ShiftRight => {
        record.bytes1_queries.bump_shift_right(byte);
        vec![Self::shift_right(byte)]
      },
    }
  }

  fn lookups(&self) -> Vec<Lookup<Expr<F>>> {
    // Channels
    let bit_decomposition_channel =
      Expr::constant(u8_bit_decomposition_channel());
    let shift_left_channel = Expr::constant(u8_shift_left_channel());
    let shift_right_channel = Expr::constant(u8_shift_right_channel());

    // Multiplicity columns
    let bit_decomposition_multiplicity = Expr::main(0);
    let shift_left_multiplicity = Expr::main(1);
    let shift_right_multiplicity = Expr::main(2);

    // Preprocessed columns
    let byte = Expr::preprocessed(0);
    let byte_bit0 = Expr::preprocessed(1);
    let byte_bit1 = Expr::preprocessed(2);
    let byte_bit2 = Expr::preprocessed(3);
    let byte_bit3 = Expr::preprocessed(4);
    let byte_bit4 = Expr::preprocessed(5);
    let byte_bit5 = Expr::preprocessed(6);
    let byte_bit6 = Expr::preprocessed(7);
    let byte_bit7 = Expr::preprocessed(8);
    let byte_left_shifted = Expr::preprocessed(9);
    let byte_right_shifted = Expr::preprocessed(10);

    // pull = negated multiplicity.
    let pull_bit_decomposition = Lookup {
      multiplicity: -bit_decomposition_multiplicity,
      args: vec![
        bit_decomposition_channel,
        byte.clone(),
        byte_bit0,
        byte_bit1,
        byte_bit2,
        byte_bit3,
        byte_bit4,
        byte_bit5,
        byte_bit6,
        byte_bit7,
      ],
    };

    let pull_shift_left = Lookup {
      multiplicity: -shift_left_multiplicity,
      args: vec![shift_left_channel, byte.clone(), byte_left_shifted],
    };

    let pull_shift_right = Lookup {
      multiplicity: -shift_right_multiplicity,
      args: vec![shift_right_channel, byte, byte_right_shifted],
    };

    vec![pull_bit_decomposition, pull_shift_left, pull_shift_right]
  }

  fn witness_data(
    &self,
    record: &QueryRecord<F>,
    slot_arg_widths: &[usize],
  ) -> (RowMajorMatrix<F>, LookupValues<F>) {
    let mut rows = vec![F::ZERO; 256 * TRACE_WIDTH];

    // There are `TRACE_WIDTH` lookups per row, one for each multiplicity.
    let mut builder = LookupValues::builder(256, slot_arg_widths);
    let mut row_writers = builder.rows_mut();

    let bit_decomposition_channel = u8_bit_decomposition_channel();
    let shift_left_channel = u8_shift_left_channel();
    let shift_right_channel = u8_shift_right_channel();

    // There are at most 256 rows so parallelism is not necessay.
    rows
      .chunks_exact_mut(TRACE_WIDTH)
      .enumerate()
      .zip(&record.bytes1_queries.0)
      .zip(row_writers.iter_mut())
      .for_each(|(((byte, row), &[bd, shl, shr]), row_lookups)| {
        let byte = F::from_usize(byte);
        row[0] = bd;
        row[1] = shl;
        row[2] = shr;

        // Pull bit decomposition.
        let mut bit_decomposition_args = Vec::with_capacity(10);
        bit_decomposition_args.extend([bit_decomposition_channel, byte]);
        bit_decomposition_args.extend(Self::bit_decompose(&byte));
        row_lookups.pull(0, bd, &bit_decomposition_args);

        // Pull shift left.
        row_lookups.pull(
          1,
          shl,
          &[shift_left_channel, byte, Self::shift_left(&byte)],
        );

        // Pull shift right.
        row_lookups.pull(
          2,
          shr,
          &[shift_right_channel, byte, Self::shift_right(&byte)],
        );
      });
    drop(row_writers);
    (RowMajorMatrix::new(rows, TRACE_WIDTH), builder.finish())
  }
}

/// Accumulator of queries performed against `Bytes1`.
pub struct Bytes1Queries<F = G>([[F; TRACE_WIDTH]; 256]);

impl<F: AiurField> Bytes1Queries<F> {
  #[inline]
  pub(crate) fn new() -> Self {
    Self([[F::ZERO; TRACE_WIDTH]; 256])
  }

  pub(crate) fn bump_bit_decomposition(&mut self, byte: &F) {
    self.bump_multiplicity_for(byte, 0)
  }

  pub(crate) fn bump_shift_left(&mut self, byte: &F) {
    self.bump_multiplicity_for(byte, 1)
  }

  pub(crate) fn bump_shift_right(&mut self, byte: &F) {
    self.bump_multiplicity_for(byte, 2)
  }

  pub(crate) fn bump_multiplicity_for(&mut self, byte: &F, col: usize) {
    let row = usize::try_from(byte.as_canonical_u64()).unwrap();
    self.0[row][col] += F::ONE;
  }
}

impl Bytes1 {
  #[inline]
  pub fn bit_decompose<F: AiurField>(byte: &F) -> Vec<F> {
    let byte_u64 = byte.as_canonical_u64();
    (0..8).map(|i| F::from_bool((byte_u64 >> i) & 1 == 1)).collect()
  }

  #[inline]
  pub fn shift_left<F: AiurField>(byte: &F) -> F {
    F::from_u64((byte.as_canonical_u64() << 1) & 255)
  }

  #[inline]
  pub fn shift_right<F: AiurField>(byte: &F) -> F {
    F::from_u64(byte.as_canonical_u64() >> 1)
  }
}
