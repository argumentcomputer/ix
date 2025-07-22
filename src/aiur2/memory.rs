use multi_stark::{
    builder::symbolic::SymbolicExpression,
    lookup::Lookup,
    p3_air::{Air, AirBuilder, BaseAir},
    p3_field::PrimeCharacteristicRing,
    p3_matrix::{Matrix, dense::RowMajorMatrix},
};
use rayon::{
    iter::{
        IndexedParallelIterator, IntoParallelRefIterator, IntoParallelRefMutIterator,
        ParallelIterator,
    },
    slice::ParallelSliceMut,
};

use crate::{
    aiur2::{G, execute::QueryRecord, trace::Channel},
    sym_var,
};

pub struct Memory {
    size: usize,
}

impl Memory {
    pub(super) fn lookup(multiplicity: G, size: G, ptr: G, values: &[G]) -> Lookup<G> {
        let mut args = vec![Channel::Memory.to_field(), size, ptr];
        args.extend(values);
        Lookup { multiplicity, args }
    }

    fn width(size: usize) -> usize {
        // multiplicity, selector, pointer and values
        3 + size
    }

    pub fn build(size: usize) -> (Self, Lookup<SymbolicExpression<G>>) {
        let multiplicity = sym_var!(0);
        let selector = sym_var!(1);
        let pointer = sym_var!(2);
        let mut args = Vec::with_capacity(3 + size);
        args.push(selector.clone() * Channel::Memory.to_field());
        args.push(selector.clone() * G::from_usize(size));
        args.push(selector.clone() * pointer);
        for val_idx in 0..size {
            args.push(selector.clone() * sym_var!(3 + val_idx));
        }
        (Self { size }, Lookup { multiplicity, args })
    }

    pub fn generate_trace(
        size: usize,
        record: &QueryRecord,
    ) -> (RowMajorMatrix<G>, Vec<Vec<Lookup<G>>>) {
        let queries = record.memory_queries.get(&size).expect("Invalid size");
        let width = Self::width(size);
        let height_no_padding = queries.len();
        let height = height_no_padding.next_power_of_two();

        let mut rows = vec![G::ZERO; height * width];
        let rows_no_padding = &mut rows[0..height_no_padding * width];

        let empty_lookup = Lookup {
            multiplicity: G::ZERO,
            args: vec![],
        };
        let mut lookups = vec![vec![empty_lookup]; height];
        let lookups_no_padding = &mut lookups[0..height_no_padding];

        rows_no_padding
            .par_chunks_mut(width)
            .zip(queries.par_iter())
            .zip(lookups_no_padding.par_iter_mut())
            .enumerate()
            .for_each(|(i, ((row, (values, result)), row_lookups))| {
                row[0] = -result.multiplicity;
                row[1] = G::ONE;
                row[2] = G::from_usize(i);
                row[3..].copy_from_slice(values);

                row_lookups[0] = Self::lookup(row[0], G::from_usize(size), row[2], &row[3..]);
            });

        let trace = RowMajorMatrix::new(rows, width);
        (trace, lookups)
    }
}

impl BaseAir<G> for Memory {
    fn width(&self) -> usize {
        Self::width(self.size)
    }
}

impl<AB> Air<AB> for Memory
where
    AB: AirBuilder<F = G>,
{
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let local: &[AB::Var] = &main.row_slice(0).unwrap();
        let next: &[AB::Var] = &main.row_slice(1).unwrap();

        let (is_real, ptr) = (local[1].clone(), local[2].clone());
        let (is_real_next, ptr_next) = (next[1].clone(), next[2].clone());

        builder.assert_bool(is_real.clone());

        // Whether the next row is real.
        let is_real_transition = is_real_next * builder.is_transition();

        // If the next row is real, the current row is real.
        builder.when(is_real_transition.clone()).assert_one(is_real);

        // Is this necessary?
        // builder.when_first_row().when(is_real).assert_zero(ptr);

        // Pointer increases by one
        builder
            .when(is_real_transition)
            .assert_eq(ptr + AB::Expr::ONE, ptr_next);
    }
}
