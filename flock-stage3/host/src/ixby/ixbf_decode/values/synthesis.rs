pub(super) use super::super::synthesis::{Bits, Builder};
use crate::ixby::bits::{add, subtract};
pub(super) fn word(i: usize) -> Bits {
  (128 * i..128 * (i + 1)).collect()
}
pub(super) fn eqc(b: &mut Builder, x: &[usize], v: u64) -> usize {
  b.equal(x, &b.constant(x.len(), v))
}
pub(super) fn flag(b: &mut Builder, i: usize) -> usize {
  b.require_zero(b.one, &word(i)[1..]);
  word(i)[0]
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
pub(super) fn minus(
  b: &mut Builder,
  on: usize,
  x: &[usize],
  y: &[usize],
) -> Bits {
  let (v, borrow) = subtract(&mut b.b, b.one, b.zero, x, y);
  b.require_zero(on, &[borrow]);
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
  x.iter().map(|bit| b.b.and(on, *bit)).collect()
}
pub(super) fn choose(
  b: &mut Builder,
  on: usize,
  yes: &[usize],
  no: &[usize],
) -> Bits {
  yes
    .iter()
    .zip(no)
    .map(|(y, n)| {
      let d = b.b.product_of_parities(&[on], &[*y, *n]);
      b.sum(&[*n, d])
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
      let t: Vec<_> =
        choices.iter().map(|(on, v)| b.b.and(*on, v[bit])).collect();
      b.sum(&t)
    })
    .collect()
}
pub(super) fn events(
  b: &mut Builder,
  committed: usize,
  tag: usize,
) -> (usize, Vec<usize>) {
  let commit = flag(b, committed);
  let tags: Vec<_> = (0..18).map(|i| eqc(b, &word(tag), i)).collect();
  let valid = b.any(&tags);
  b.require(b.one, valid);
  let optional = b.any(&[tags[15], tags[17]]);
  let required = b.not(optional);
  b.require(required, commit);
  b.require_zero(tags[17], &[commit]);
  (commit, tags)
}
