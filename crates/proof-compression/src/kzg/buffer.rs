//! Parallel first-touch initialization of large field buffers.

use p3_maybe_rayon::prelude::*;

pub(super) fn generate<T: Copy + Send>(
  len: usize,
  value: impl Fn(usize) -> T + Sync,
) -> Vec<T> {
  let mut output: Vec<T> = Vec::with_capacity(len);
  output.spare_capacity_mut()[..len]
    .par_chunks_mut(1 << 14)
    .enumerate()
    .for_each(|(tile, chunk)| {
      for (offset, slot) in chunk.iter_mut().enumerate() {
        slot.write(value((tile << 14) + offset));
      }
    });
  // Every slot is initialized after the parallel iterator joins. T is Copy,
  // so a panic during initialization cannot leak partially constructed values.
  unsafe { output.set_len(len) };
  output
}
