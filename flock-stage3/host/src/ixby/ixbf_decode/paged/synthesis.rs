pub(super) use super::super::synthesis::{Bits, Builder};
use crate::ixby::bits::{add, subtract};
pub(super) fn word(i: usize) -> Bits {
  (128 * i..128 * (i + 1)).collect()
}
pub(super) fn eqc(b: &mut Builder, x: &[usize], v: u64) -> usize {
  b.equal(x, &b.constant(x.len(), v))
}
pub(super) fn same(b: &mut Builder, on: usize, x: &[usize], y: &[usize]) {
  let good = b.equal(x, y);
  b.require(on, good);
}
pub(super) fn lt(b: &mut Builder, x: &[usize], y: &[usize]) -> usize {
  subtract(&mut b.b, b.one, b.zero, x, y).1
}
pub(super) fn le(b: &mut Builder, on: usize, x: &[usize], y: &[usize]) {
  let wrong = lt(b, y, x);
  b.require_zero(on, &[wrong]);
}
pub(super) fn bound(b: &mut Builder, on: usize, x: &[usize], maximum: u64) {
  le(b, on, x, &b.constant(x.len(), maximum));
}
pub(super) fn minus(
  b: &mut Builder,
  on: usize,
  x: &[usize],
  y: &[usize],
) -> Bits {
  let (v, carry) = subtract(&mut b.b, b.one, b.zero, x, y);
  b.require_zero(on, &[carry]);
  v
}
pub(super) fn plus(
  b: &mut Builder,
  on: usize,
  x: &[usize],
  y: &[usize],
) -> Bits {
  let (v, carry) = add(&mut b.b, b.one, b.zero, x, y);
  b.require_zero(on, &[carry]);
  v
}
pub(super) fn mask(b: &mut Builder, on: usize, x: &[usize]) -> Bits {
  x.iter().map(|&bit| b.b.and(on, bit)).collect()
}
pub(super) fn choose(
  b: &mut Builder,
  on: usize,
  yes: &[usize],
  no: &[usize],
) -> Bits {
  assert_eq!(yes.len(), no.len());
  yes
    .iter()
    .zip(no)
    .map(|(&y, &n)| {
      let d = b.b.product_of_parities(&[on], &[y, n]);
      b.sum(&[n, d])
    })
    .collect()
}
pub(super) fn select(
  b: &mut Builder,
  choices: &[(usize, Bits)],
  width: usize,
) -> Bits {
  (0..width)
    .map(|bit| {
      let terms =
        choices.iter().map(|(on, v)| b.b.and(*on, v[bit])).collect::<Vec<_>>();
      b.sum(&terms)
    })
    .collect()
}
