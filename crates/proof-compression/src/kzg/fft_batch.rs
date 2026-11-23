use super::coefficients::Column;
use super::curve::KzgCurve;
use ark_ff::Zero;
use ark_poly::{EvaluationDomain, Radix2EvaluationDomain};
use p3_maybe_rayon::prelude::*;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct Pair<C: KzgCurve>(pub(super) [C::Fr; 2]);
impl<C: KzgCurve> std::ops::Add for Pair<C> {
  type Output = Self;
  fn add(mut self, rhs: Self) -> Self {
    self += rhs;
    self
  }
}
impl<C: KzgCurve> std::ops::Sub for Pair<C> {
  type Output = Self;
  fn sub(mut self, rhs: Self) -> Self {
    self -= rhs;
    self
  }
}
impl<C: KzgCurve> std::ops::AddAssign for Pair<C> {
  fn add_assign(&mut self, rhs: Self) {
    for (a, b) in self.0.iter_mut().zip(rhs.0) {
      *a += b;
    }
  }
}
impl<C: KzgCurve> std::ops::SubAssign for Pair<C> {
  fn sub_assign(&mut self, rhs: Self) {
    for (a, b) in self.0.iter_mut().zip(rhs.0) {
      *a -= b;
    }
  }
}
impl<C: KzgCurve> std::ops::MulAssign<C::Fr> for Pair<C> {
  fn mul_assign(&mut self, rhs: C::Fr) {
    for a in &mut self.0 {
      *a *= rhs;
    }
  }
}
impl<C: KzgCurve> Zero for Pair<C> {
  fn zero() -> Self {
    Self([C::FR_ZERO; 2])
  }
  fn is_zero(&self) -> bool {
    self.0.iter().all(Zero::is_zero)
  }
}

// Two columns share FFT roots and permutation passes, using one extra column
// of scratch. The underlying transform remains arkworks' FFT.
pub(super) fn evaluate<C: KzgCurve>(
  columns: &[&Column<C>],
  domain: Radix2EvaluationDomain<C::Fr>,
) -> Vec<Pair<C>> {
  assert_eq!(columns.len(), 2);
  assert_eq!(columns[0].len(), columns[1].len());
  if let (
    Column::Constant { value: a, .. },
    Column::Constant { value: b, .. },
  ) = (columns[0], columns[1])
  {
    return vec![Pair([*a, *b]); domain.size()];
  }
  let mut rows = vec![Pair::<C>::zero(); columns[0].len()];
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
