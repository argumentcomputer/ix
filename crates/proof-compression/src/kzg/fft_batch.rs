use super::coefficients::Column;
use ark_bls12_381::Fr;
use ark_ff::{AdditiveGroup, Zero};
use ark_poly::{EvaluationDomain, Radix2EvaluationDomain};
use p3_maybe_rayon::prelude::*;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct Pair(pub(super) [Fr; 2]);
impl std::ops::Add for Pair {
  type Output = Self;
  fn add(mut self, rhs: Self) -> Self {
    self += rhs;
    self
  }
}
impl std::ops::Sub for Pair {
  type Output = Self;
  fn sub(mut self, rhs: Self) -> Self {
    self -= rhs;
    self
  }
}
impl std::ops::AddAssign for Pair {
  fn add_assign(&mut self, rhs: Self) {
    for (a, b) in self.0.iter_mut().zip(rhs.0) {
      *a += b;
    }
  }
}
impl std::ops::SubAssign for Pair {
  fn sub_assign(&mut self, rhs: Self) {
    for (a, b) in self.0.iter_mut().zip(rhs.0) {
      *a -= b;
    }
  }
}
impl std::ops::MulAssign<Fr> for Pair {
  fn mul_assign(&mut self, rhs: Fr) {
    for a in &mut self.0 {
      *a *= rhs;
    }
  }
}
impl Zero for Pair {
  fn zero() -> Self {
    Self([Fr::ZERO; 2])
  }
  fn is_zero(&self) -> bool {
    self.0.iter().all(Zero::is_zero)
  }
}

// Two columns share FFT roots and permutation passes, using one extra column
// of scratch. The underlying transform remains arkworks' FFT.
pub(super) fn evaluate(
  columns: &[&Column],
  domain: Radix2EvaluationDomain<Fr>,
) -> Vec<Pair> {
  assert_eq!(columns.len(), 2);
  assert_eq!(columns[0].len(), columns[1].len());
  let mut rows = vec![Pair::zero(); columns[0].len()];
  for (index, column) in columns.iter().enumerate() {
    column
      .visit(|start, chunk| {
        rows[start..start + chunk.len()]
          .par_iter_mut()
          .zip(chunk)
          .for_each(|(row, value)| row.0[index] = *value);
      })
      .expect("coefficient checkpoint");
  }
  if rows.iter().skip(1).all(Zero::is_zero) {
    let value = rows.first().copied().unwrap_or_else(Pair::zero);
    rows.resize(domain.size(), value);
    rows.fill(value);
  } else {
    domain.fft_in_place(&mut rows);
  }
  rows
}
