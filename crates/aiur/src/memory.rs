use multi_stark::{
  expr::Expr,
  lookup::{Lookup, LookupValues},
  p3_field::PrimeCharacteristicRing,
  p3_matrix::dense::RowMajorMatrix,
};
use rayon::{
  iter::{
    IndexedParallelIterator, IntoParallelRefMutIterator, ParallelIterator,
  },
  slice::ParallelSliceMut,
};

use crate::{G, execute::QueryRecord, memory_channel};

pub struct Memory {
  pub(crate) width: usize,
}

impl Memory {
  pub(super) fn lookup_args(size: G, ptr: G, values: &[G]) -> Vec<G> {
    let mut args = Vec::with_capacity(3 + values.len());
    args.extend([memory_channel(), size, ptr]);
    args.extend(values);
    args
  }

  /// [`Self::lookup_args`] into a reusable buffer — the row replay is
  /// allocation-free.
  pub(super) fn lookup_args_into(
    buf: &mut Vec<G>,
    size: G,
    ptr: G,
    values: &[G],
  ) {
    buf.clear();
    buf.extend([memory_channel(), size, ptr]);
    buf.extend_from_slice(values);
  }

  fn width(size: usize) -> usize {
    // Multiplicity, selector, pointer and values.
    3 + size
  }

  /// Returns the memory circuit together with its base-field constraints and
  /// its (single) lookup.
  pub fn build(size: usize) -> (Self, Vec<Expr<G>>, Vec<Lookup<Expr<G>>>) {
    let multiplicity = Expr::main(0);
    let selector = Expr::main(1);
    let pointer = Expr::main(2);
    let mut args = Vec::with_capacity(3 + size);
    args.push(selector.clone() * Expr::constant(memory_channel()));
    args.push(selector.clone() * Expr::constant(G::from_usize(size)));
    args.push(selector.clone() * pointer);
    for val_idx in 0..size {
      let col = u32::try_from(3 + val_idx).expect("column index exceeds u32");
      args.push(selector.clone() * Expr::main(col));
    }
    let width = Self::width(size);
    // pull = negated multiplicity.
    let lookups = vec![Lookup { multiplicity: -multiplicity, args }];

    // Transition constraints (formerly the `Air::eval` body): the selector is
    // boolean; a real next row implies a real current row; and the pointer
    // increments by one across a real transition.
    let is_real = Expr::main(1);
    let is_real_next = Expr::main_next(1);
    let ptr = Expr::main(2);
    let ptr_next = Expr::main_next(2);
    let one = || Expr::constant(G::ONE);
    let is_real_transition = is_real_next * Expr::IsTransition;
    let constraints = vec![
      is_real.clone() * (is_real.clone() - one()),
      is_real_transition.clone() * (is_real - one()),
      is_real_transition * (ptr + one() - ptr_next),
    ];

    (Self { width }, constraints, lookups)
  }

  pub fn witness_data(
    size: usize,
    record: &QueryRecord,
    slot_arg_widths: &[usize],
  ) -> (RowMajorMatrix<G>, LookupValues<G>) {
    let queries = record.memory_queries.get(&size).expect("Invalid size");
    let width = Self::width(size);
    let height_no_padding = queries.len();
    // An unqueried memory table yields an EMPTY trace: the prover
    // deactivates it, so it is neither committed nor opened.
    let height = if height_no_padding == 0 {
      0
    } else {
      height_no_padding.next_power_of_two()
    };

    let mut rows = vec![G::ZERO; height * width];
    let rows_no_padding = &mut rows[0..height_no_padding * width];

    // Builder rows start zeroed (`Lookup::empty()`), so padding rows need no
    // writes at all.
    let mut builder = LookupValues::builder(height, slot_arg_widths);
    let mut row_writers = builder.rows_mut();

    rows_no_padding
      .par_chunks_mut(width)
      .zip(row_writers[..height_no_padding].par_iter_mut())
      .enumerate()
      .for_each(|(i, (row, row_lookups))| {
        let (values, result) = queries.get_index(i).expect("index in range");
        row[0] = result.multiplicity;
        row[1] = G::ONE;
        row[2] = G::from_usize(i);
        row[3..].copy_from_slice(values);

        let args = Self::lookup_args(G::from_usize(size), row[2], &row[3..]);
        row_lookups.pull(0, row[0], &args);
      });
    drop(row_writers);

    let trace = RowMajorMatrix::new(rows, width);
    (trace, builder.finish())
  }
}
