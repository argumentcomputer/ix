//! Equal-height packing of one commitment round. Rounds separated by
//! Fiat–Shamir challenges are planned independently.
//!
//! Each matrix carries a prover-declared next-row class from its commitment
//! shape. Columns of the two classes never share a pack, so a pack of
//! current-row-only columns opens at one point and needs no extra values.
//! The class only changes which columns share a pack: a pack still opens
//! every member at the union of the members' points, so a wrong
//! declaration costs extra values, never soundness.

use std::collections::BTreeMap;
use std::ops::Range;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Columns {
  pub matrix: usize,
  pub source: Range<usize>,
}

/// One pack: `width` columns of `height` coefficients, `width·height ≤ cap`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Pack {
  pub height: usize,
  pub width: usize,
  pub columns: Vec<Columns>,
}

/// `(height, width, next_row)` of one matrix.
pub type Dimension = (usize, usize, bool);

/// Ascending height, then next-row matrices before current-row-only ones.
fn class(height: usize, next_row: bool) -> (usize, bool) {
  (height, !next_row)
}

/// Every column of every nonempty matrix occurs exactly once. Packs are
/// ordered by height, then next-row class (next-row readers first), then by
/// source matrix and column; each class fills `cap / height` columns per pack
/// before starting the next.
pub fn plan(dimensions: &[Dimension], cap: usize) -> Result<Vec<Pack>, String> {
  if !cap.is_power_of_two() {
    return Err("packed capacity must be a power of two".into());
  }
  let mut by_class = BTreeMap::<(usize, bool), Vec<(usize, usize)>>::new();
  for (matrix, &(height, width, next_row)) in dimensions.iter().enumerate() {
    if !height.is_power_of_two() || height > cap || width == 0 {
      return Err("invalid packed matrix dimensions".into());
    }
    by_class.entry(class(height, next_row)).or_default().push((matrix, width));
  }
  let mut packs = vec![];
  for ((height, _), matrices) in by_class {
    let capacity = cap / height;
    let mut pack = Pack { height, width: 0, columns: vec![] };
    for (matrix, width) in matrices {
      let mut start = 0;
      while start != width {
        let take = (width - start).min(capacity - pack.width);
        pack.columns.push(Columns { matrix, source: start..start + take });
        pack.width += take;
        start += take;
        if pack.width == capacity {
          packs.push(pack);
          pack = Pack { height, width: 0, columns: vec![] };
        }
      }
    }
    if pack.width != 0 {
      packs.push(pack);
    }
  }
  Ok(packs)
}

/// Pack count implied by the shapes alone.
pub fn count(dimensions: &[Dimension], cap: usize) -> Option<usize> {
  let mut widths = BTreeMap::<(usize, bool), usize>::new();
  for &(height, width, next_row) in dimensions {
    let total = widths.entry(class(height, next_row)).or_default();
    *total = total.checked_add(width)?;
  }
  widths.into_iter().try_fold(0usize, |n, ((height, _), width)| {
    n.checked_add(width.div_ceil(cap / height))
  })
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn plan_covers_columns_once_within_capacity() {
    let dimensions = [
      (4, 3, true),
      (8, 5, false),
      (4, 9, true),
      (16, 1, true),
      (8, 2, true),
      (4, 2, false),
    ];
    let packs = plan(&dimensions, 16).unwrap();
    assert_eq!(packs.len(), count(&dimensions, 16).unwrap());
    let mut seen: Vec<Vec<bool>> =
      dimensions.iter().map(|&(_, w, _)| vec![false; w]).collect();
    for pack in &packs {
      assert!(pack.width * pack.height <= 16);
      let next_row = dimensions[pack.columns[0].matrix].2;
      for columns in &pack.columns {
        assert_eq!(dimensions[columns.matrix].0, pack.height);
        assert_eq!(dimensions[columns.matrix].2, next_row);
        for c in columns.source.clone() {
          assert!(!std::mem::replace(&mut seen[columns.matrix][c], true));
        }
      }
    }
    assert!(seen.iter().flatten().all(|&s| s));
    assert!(plan(&[(32, 1, true)], 16).is_err());
    // Classes are packed apart: 3 + 9 next-row columns of height 4 take three
    // packs, the 2 current-row-only columns a fourth.
    assert_eq!(packs.iter().filter(|p| p.height == 4).count(), 4);
  }
}
