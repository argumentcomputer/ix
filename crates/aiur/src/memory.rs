use std::ops::Range;

use multi_stark::{
  expr::Expr,
  lookup::{Lookup, LookupRowMut, LookupValues},
  p3_field::PrimeCharacteristicRing,
  p3_matrix::dense::RowMajorMatrix,
};
use rayon::{
  iter::{
    IndexedParallelIterator, IntoParallelRefMutIterator, ParallelIterator,
  },
  slice::ParallelSliceMut,
};

use crate::{G, execute::QueryRecord, memory_channel, memseg_channel};

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

  /// The segment-boundary message for pointer `ptr` of the width-`size` table.
  pub fn memseg_args(size: G, ptr: G) -> [G; 3] {
    [memseg_channel(), size, ptr]
  }

  fn width(size: usize) -> usize {
    // Multiplicity, selector, pointer and values.
    3 + size
  }

  /// Returns the memory circuit together with its base-field constraints and
  /// its lookups: the value pull on the memory channel, and the two
  /// segment-boundary lookups on the `memseg` channel.
  pub fn build(size: usize) -> (Self, Vec<Expr<G>>, Vec<Lookup<Expr<G>>>) {
    let multiplicity = Expr::main(0);
    let selector = Expr::main(1);
    let pointer = Expr::main(2);
    let mut args = Vec::with_capacity(3 + size);
    args.push(selector.clone() * Expr::constant(memory_channel()));
    args.push(selector.clone() * Expr::constant(G::from_usize(size)));
    args.push(selector.clone() * pointer.clone());
    for val_idx in 0..size {
      let col = u32::try_from(3 + val_idx).expect("column index exceeds u32");
      args.push(selector.clone() * Expr::main(col));
    }
    let width = Self::width(size);
    // The pull is selector-gated like its arguments: a padding row must not
    // contribute even the zero message with a multiplicity of its own.
    let value_pull =
      Lookup { multiplicity: -(selector.clone() * multiplicity), args };

    // Segment boundaries. Every real row pushes `(memseg, size, ptr)` and
    // pulls `(memseg, size, ptr + 1)`, both with multiplicity `sel`. With
    // pointers incrementing across real rows, the interior terms telescope
    // and the circuit contributes exactly one push of its first pointer and
    // one pull of one past its last: the two end points of the table
    // segment this trace holds, without any boundary column. The selector
    // gates the multiplicities (not the Lagrange selectors, which are
    // unnormalized and would weight the end points by the trace height).
    let memseg = |ptr: Expr<G>| {
      vec![
        selector.clone() * Expr::constant(memseg_channel()),
        selector.clone() * Expr::constant(G::from_usize(size)),
        selector.clone() * ptr,
      ]
    };
    let one = || Expr::constant(G::ONE);
    let segment_start =
      Lookup { multiplicity: selector.clone(), args: memseg(pointer.clone()) };
    let segment_end =
      Lookup { multiplicity: -selector.clone(), args: memseg(pointer + one()) };
    let lookups = vec![value_pull, segment_start, segment_end];

    // Transition constraints (formerly the `Air::eval` body): the selector is
    // boolean; a real next row implies a real current row; and the pointer
    // increments by one across a real transition.
    let is_real = Expr::main(1);
    let is_real_next = Expr::main_next(1);
    let ptr = Expr::main(2);
    let ptr_next = Expr::main_next(2);
    let is_real_transition = is_real_next * Expr::IsTransition;
    let constraints = vec![
      is_real.clone() * (is_real.clone() - one()),
      is_real_transition.clone() * (is_real - one()),
      is_real_transition * (ptr + one() - ptr_next),
    ];

    (Self { width }, constraints, lookups)
  }

  /// The whole width-`size` table as one trace: [`Self::witness_data_range`]
  /// over every pointer.
  pub fn witness_data(
    size: usize,
    record: &QueryRecord,
    slot_arg_widths: &[usize],
  ) -> (RowMajorMatrix<G>, LookupValues<G>) {
    let len = record.memory_queries.get(&size).map_or(0, |m| m.len());
    Self::witness_data_range(size, record, slot_arg_widths, 0..len)
  }

  /// The rows of the width-`size` table at table indices `range`, as a trace
  /// whose row `i` carries pointer `record.pointer_base + range.start + i`.
  /// An empty range yields an EMPTY trace: the prover deactivates the
  /// circuit, so it is neither committed nor opened.
  pub fn witness_data_range(
    size: usize,
    record: &QueryRecord,
    slot_arg_widths: &[usize],
    range: Range<usize>,
  ) -> (RowMajorMatrix<G>, LookupValues<G>) {
    let width = Self::width(size);
    let height_no_padding = range.len();
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

    if height_no_padding > 0 {
      let queries = record.memory_queries.get(&size).expect("Invalid size");
      let size_g = G::from_usize(size);
      let populate =
        |i: usize,
         row: &mut [G],
         row_lookups: Option<&mut LookupRowMut<'_, G>>| {
          let index = range.start + i;
          let (values, result) =
            queries.get_index(index).expect("pointer in range");
          row[0] = result.multiplicity;
          row[1] = G::ONE;
          row[2] = G::from_usize(record.pointer_base + index);
          row[3..].copy_from_slice(values);

          let Some(row_lookups) = row_lookups else { return };
          let args = Self::lookup_args(size_g, row[2], &row[3..]);
          row_lookups.pull(0, row[0], &args);
          row_lookups.push(1, G::ONE, &Self::memseg_args(size_g, row[2]));
          row_lookups.pull(
            2,
            G::ONE,
            &Self::memseg_args(size_g, row[2] + G::ONE),
          );
        };
      if crate::trace::trace_only_lookups() {
        rows_no_padding
          .par_chunks_mut(width)
          .enumerate()
          .for_each(|(i, row)| populate(i, row, None));
      } else {
        let mut row_writers = builder.rows_mut();
        rows_no_padding
          .par_chunks_mut(width)
          .zip(row_writers[..height_no_padding].par_iter_mut())
          .enumerate()
          .for_each(|(i, (row, row_lookups))| {
            populate(i, row, Some(row_lookups))
          });
      }
    }

    let trace = RowMajorMatrix::new(rows, width);
    (trace, builder.finish())
  }
}
