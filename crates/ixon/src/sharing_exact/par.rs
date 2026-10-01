//! Deterministic task splitting for the parallel paths of the tiered
//! construction. Results always come back in index order, so the callers
//! combine them exactly as the sequential path does.

use std::ops::Range;

/// Split `0..n` into at most `budget` contiguous ranges of nearly equal
/// length (none empty).
pub(crate) fn split(n: usize, budget: usize) -> Vec<Range<usize>> {
  let tasks = budget.clamp(1, n.max(1));
  let size = n.div_ceil(tasks).max(1);
  (0..n).step_by(size).map(|s| s..(s + size).min(n)).collect()
}

/// Run `f` on the ranges of [`split`]`(n, budget)`, in parallel on the
/// current rayon pool when `budget > 1`, and concatenate the results in
/// range order. With `budget <= 1` (or without rayon) this is `f(0..n)`.
pub(crate) fn map_ranges<R, F>(n: usize, budget: usize, f: F) -> Vec<R>
where
  R: Send,
  F: Fn(Range<usize>) -> Vec<R> + Sync,
{
  if budget <= 1 || n <= 1 {
    return f(0..n);
  }
  #[cfg(not(target_arch = "riscv64"))]
  {
    use rayon::prelude::*;
    let parts: Vec<Vec<R>> = split(n, budget).into_par_iter().map(&f).collect();
    parts.into_iter().flatten().collect()
  }
  #[cfg(target_arch = "riscv64")]
  {
    f(0..n)
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn split_covers_in_order() {
    for n in 0..40 {
      for b in 0..12 {
        let r = split(n, b);
        let flat: Vec<usize> = r.iter().cloned().flatten().collect();
        assert_eq!(flat, (0..n).collect::<Vec<_>>());
        assert!(r.len() <= b.max(1));
        assert!(r.iter().all(|x| !x.is_empty()));
      }
    }
    let v = map_ranges(37, 5, |r| r.map(|i| i * 2).collect());
    assert_eq!(v, (0..37).map(|i| i * 2).collect::<Vec<_>>());
  }
}
