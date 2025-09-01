use multi_stark::{
    builder::symbolic::{SymbolicExpression, preprocessed_var, var},
    lookup::Lookup,
    p3_air::{Air, AirBuilder, BaseAir},
    p3_field::{PrimeCharacteristicRing, PrimeField64},
    p3_matrix::dense::RowMajorMatrix,
};

use crate::aiur::{
    G, execute::QueryRecord, gadgets::AiurGadget, u8_bit_decomposition_channel,
    u8_shift_left_channel, u8_shift_right_channel,
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
pub(crate) struct Bytes1;

pub(crate) enum Bytes1Op {
    BitDecomposition,
    ShiftLeft,
    ShiftRight,
}

impl BaseAir<G> for Bytes1 {
    fn width(&self) -> usize {
        TRACE_WIDTH
    }

    /// Builds the preprocessed trace over all 256 byte values.
    fn preprocessed_trace(&self) -> Option<RowMajorMatrix<G>> {
        let mut values = vec![G::ZERO; 256 * PREPROCESSED_TRACE_WIDTH];
        values
            .chunks_exact_mut(PREPROCESSED_TRACE_WIDTH)
            .enumerate()
            .for_each(|(i, row)| {
                let byte = G::from_usize(i);

                // Raw byte value
                row[0] = byte;

                // 8 bits in LE
                for (row_elt, bit) in row[1..].iter_mut().zip(Self::bit_decompose(&byte)) {
                    *row_elt = bit;
                }

                // Byte shifted left
                row[9] = Self::shift_left(&byte);

                // Byte shifted right
                row[10] = Self::shift_right(&byte);
            });
        Some(RowMajorMatrix::new(values, PREPROCESSED_TRACE_WIDTH))
    }
}

impl<AB: AirBuilder<F = G>> Air<AB> for Bytes1 {
    /// A no-op, since all constraints are enforced through lookups.
    fn eval(&self, _builder: &mut AB) {}
}

impl AiurGadget for Bytes1 {
    type Op = Bytes1Op;

    fn output_size(&self, op: &Bytes1Op) -> usize {
        match op {
            Bytes1Op::BitDecomposition => 8,
            Bytes1Op::ShiftLeft | Bytes1Op::ShiftRight => 1,
        }
    }

    fn execute(&self, op: &Bytes1Op, input: &[G], record: &mut QueryRecord) -> Vec<G> {
        let byte = &input[0];
        match op {
            Bytes1Op::BitDecomposition => {
                record.bytes1_queries.bump_bit_decomposition(byte);
                Self::bit_decompose(byte)
            }
            Bytes1Op::ShiftLeft => {
                record.bytes1_queries.bump_shift_left(byte);
                vec![Self::shift_left(byte)]
            }
            Bytes1Op::ShiftRight => {
                record.bytes1_queries.bump_shift_right(byte);
                vec![Self::shift_right(byte)]
            }
        }
    }

    fn lookups(&self) -> Vec<Lookup<SymbolicExpression<G>>> {
        // Channels
        let bit_decomposition_channel = u8_bit_decomposition_channel().into();
        let shift_left_channel = u8_shift_left_channel().into();
        let shift_right_channel = u8_shift_right_channel().into();

        // Multiplicity columns
        let bit_decomposition_multiplicity = var(0);
        let shift_left_multiplicity = var(1);
        let shift_right_multiplicity = var(2);

        // Preprocessed columns
        let byte = preprocessed_var(0);
        let byte_bit0 = preprocessed_var(1);
        let byte_bit1 = preprocessed_var(2);
        let byte_bit2 = preprocessed_var(3);
        let byte_bit3 = preprocessed_var(4);
        let byte_bit4 = preprocessed_var(5);
        let byte_bit5 = preprocessed_var(6);
        let byte_bit6 = preprocessed_var(7);
        let byte_bit7 = preprocessed_var(8);
        let byte_left_shifted = preprocessed_var(9);
        let byte_right_shifted = preprocessed_var(10);

        let pull_bit_decomposition = Lookup::pull(
            bit_decomposition_multiplicity,
            vec![
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
        );

        let pull_shift_left = Lookup::pull(
            shift_left_multiplicity,
            vec![shift_left_channel, byte.clone(), byte_left_shifted],
        );

        let pull_shift_right = Lookup::pull(
            shift_right_multiplicity,
            vec![shift_right_channel, byte, byte_right_shifted],
        );

        vec![pull_bit_decomposition, pull_shift_left, pull_shift_right]
    }

    fn witness_data(&self, record: &QueryRecord) -> (RowMajorMatrix<G>, Vec<Vec<Lookup<G>>>) {
        let mut rows = vec![G::ZERO; 256 * TRACE_WIDTH];

        // There are `TRACE_WIDTH` lookups per row, one for each multiplicity.
        let mut lookups = vec![vec![Lookup::empty(); TRACE_WIDTH]; 256];

        let bit_decomposition_channel = u8_bit_decomposition_channel();
        let shift_left_channel = u8_shift_left_channel();
        let shift_right_channel = u8_shift_right_channel();

        // There are at most 256 rows so parallelism is not necessay.
        rows.chunks_exact_mut(TRACE_WIDTH)
            .enumerate()
            .zip(&record.bytes1_queries.0)
            .zip(&mut lookups)
            .for_each(|(((byte, row), &[bd, shl, shr]), row_lookups)| {
                let byte = G::from_usize(byte);
                row[0] = bd;
                row[1] = shl;
                row[2] = shr;

                // Pull bit decomposition.
                let mut bit_decomposition_args = Vec::with_capacity(10);
                bit_decomposition_args.extend([bit_decomposition_channel, byte]);
                bit_decomposition_args.extend(Self::bit_decompose(&byte));
                row_lookups[0] = Lookup::pull(bd, bit_decomposition_args);

                // Pull shift left.
                row_lookups[1] =
                    Lookup::pull(shl, vec![shift_left_channel, byte, Self::shift_left(&byte)]);

                // Pull shift right.
                row_lookups[2] = Lookup::pull(
                    shr,
                    vec![shift_right_channel, byte, Self::shift_right(&byte)],
                );
            });
        (RowMajorMatrix::new(rows, TRACE_WIDTH), lookups)
    }
}

/// Accumulator of queries performed against `Bytes1`.
pub(crate) struct Bytes1Queries([[G; TRACE_WIDTH]; 256]);

impl Bytes1Queries {
    #[inline]
    pub(crate) fn new() -> Self {
        Self([[G::ZERO; TRACE_WIDTH]; 256])
    }

    fn bump_bit_decomposition(&mut self, byte: &G) {
        self.bump_multiplicity_for(byte, 0)
    }

    fn bump_shift_left(&mut self, byte: &G) {
        self.bump_multiplicity_for(byte, 1)
    }

    fn bump_shift_right(&mut self, byte: &G) {
        self.bump_multiplicity_for(byte, 2)
    }

    fn bump_multiplicity_for(&mut self, byte: &G, col: usize) {
        let row = usize::try_from(byte.as_canonical_u64()).unwrap();
        self.0[row][col] += G::ONE;
    }
}

impl Bytes1 {
    #[inline]
    pub(crate) fn bit_decompose(byte: &G) -> Vec<G> {
        let byte_u64 = byte.as_canonical_u64();
        (0..8)
            .map(|i| G::from_bool((byte_u64 >> i) & 1 == 1))
            .collect()
    }

    #[inline]
    pub(crate) fn shift_left(byte: &G) -> G {
        G::from_u64((byte.as_canonical_u64() << 1) & 255)
    }

    #[inline]
    pub(crate) fn shift_right(byte: &G) -> G {
        G::from_u64(byte.as_canonical_u64() >> 1)
    }
}
