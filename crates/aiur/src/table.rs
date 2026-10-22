//! Immutable table indexes. Complete Cartesian domains use direct addressing;
//! arbitrary tables retain a hash index. Row order is never assumed.
use crate::field::{FieldBackend, PrimeField};
use rustc_hash::FxHashMap;

#[derive(Clone, Debug)]
pub(crate) enum TableIndex<B: FieldBackend = PrimeField> {
  Dense { bounds: Vec<u64>, rows: Vec<usize>, field: B },
  Sparse(FxHashMap<Vec<B::Element>, usize>),
}

fn position<B: FieldBackend>(
  bounds: &[u64],
  key: &[B::Element],
  field: B,
) -> Option<usize> {
  if bounds.len() != key.len() {
    return None;
  }
  let mut index = 0;
  for (&bound, &word) in bounds.iter().zip(key) {
    let word = field.to_u64(word);
    if word >= bound {
      return None;
    }
    // The product of bounds was checked to equal the table length.
    index = index * bound as usize + word as usize;
  }
  Some(index)
}

impl<B: FieldBackend> TableIndex<B> {
  pub(crate) fn new(
    rows: &[Vec<B::Element>],
    field: B,
  ) -> Result<Self, String> {
    let mut bounds = vec![0; rows.first().map_or(0, Vec::len)];
    for row in rows {
      for (bound, word) in bounds.iter_mut().zip(row) {
        *bound = (*bound).max(field.to_u64(*word).saturating_add(1));
      }
    }
    let size = bounds.iter().try_fold(1usize, |n, &bound| {
      n.checked_mul(usize::try_from(bound).ok()?)
    });
    if size == Some(rows.len()) && !rows.is_empty() {
      let mut positions = vec![usize::MAX; rows.len()];
      for (row, key) in rows.iter().enumerate() {
        let index =
          position(&bounds, key, field).ok_or("invalid dense table key")?;
        if positions[index] != usize::MAX {
          return Err("duplicate map input row".into());
        }
        positions[index] = row;
      }
      Ok(Self::Dense { bounds, rows: positions, field })
    } else {
      let mut index = FxHashMap::default();
      for (i, row) in rows.iter().enumerate() {
        if index.insert(row.clone(), i).is_some() {
          return Err("duplicate map input row".into());
        }
      }
      Ok(Self::Sparse(index))
    }
  }

  pub(crate) fn get(&self, key: &[B::Element]) -> Option<usize> {
    match self {
      Self::Dense { bounds, rows, field } => {
        position(bounds, key, *field).map(|i| rows[i])
      },
      Self::Sparse(index) => index.get(key).copied(),
    }
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn preserves_row_order_domains_and_uniqueness() {
    for rows in [
      vec![vec![1, 1], vec![0, 1], vec![1, 0], vec![0, 0]],
      vec![vec![4], vec![0], vec![2]],
      vec![vec![]],
      vec![],
    ] {
      let index = TableIndex::new(&rows, PrimeField::new(97).unwrap()).unwrap();
      for (i, row) in rows.iter().enumerate() {
        assert_eq!(index.get(row), Some(i));
      }
      for key in [vec![2, 0], vec![0, 2], vec![3], vec![u64::MAX]] {
        assert_eq!(index.get(&key), rows.iter().position(|row| row == &key));
      }
    }
    for rows in
      [vec![vec![0], vec![0]], vec![vec![1], vec![1]], vec![vec![], vec![]]]
    {
      assert!(TableIndex::new(&rows, PrimeField::new(97).unwrap()).is_err());
    }
  }
}
