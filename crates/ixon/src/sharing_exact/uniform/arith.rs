//! The integers of the phase-1 optimizer, in two representations.
//!
//! Lean computes phase 1 with `Nat` and `Int`. Its values are lengths,
//! lower bounds and occurrence-weighted sums, which are nonnegative, and
//! differences of them. Intermediate values can be exponential in the size
//! of the input while the chosen encoding stays small: with no uncertain
//! term stored, `x_(i+1) = App(x_i, x_i)` unfolds to about `2^i` bytes.
//!
//! [`Fast`] computes in `u128` and `i128`. Nonnegative sums saturate at
//! `u128::MAX`; saturation is monotone, so a saturated summand can lose a
//! comparison but a value that is not `u128::MAX` is exact, and the
//! optimizer reports [`FormatBound::LengthOverflow`] as soon as a value it
//! keeps is `u128::MAX`. Signed operations and conversions are checked and
//! report the same error. [`Exact`] computes the same values as [`Nat`] and
//! [`Int`], unbounded, and never overflows.
//!
//! The optimizer runs with [`Fast`] and, if that run reports
//! `LengthOverflow`, runs again from the same meter with [`Exact`]
//! (`family::optimize_at`). A [`Fast`] run that succeeds computed every value
//! exactly, so its result is the [`Exact`] one: the representation changes
//! the time, never a successful result.

use std::borrow::Cow;
use std::cmp::Ordering;
use std::fmt;

use num_bigint::{BigInt, BigUint, Sign};

use super::{FormatBound, SharingError};

fn overflow() -> SharingError {
  SharingError::FormatBound(FormatBound::LengthOverflow)
}

/// A natural number: inline below `2^128`, a `BigUint` from there.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Nat {
  Small(u128),
  /// At least `2^128`.
  Big(Box<BigUint>),
}

impl Nat {
  fn of_big(x: BigUint) -> Nat {
    match u128::try_from(&x) {
      Ok(v) => Nat::Small(v),
      Err(_) => Nat::Big(Box::new(x)),
    }
  }

  fn as_big(&self) -> Cow<'_, BigUint> {
    match self {
      Nat::Small(v) => Cow::Owned(BigUint::from(*v)),
      Nat::Big(b) => Cow::Borrowed(b),
    }
  }
}

impl Default for Nat {
  fn default() -> Self {
    Nat::Small(0)
  }
}

impl Ord for Nat {
  fn cmp(&self, other: &Self) -> Ordering {
    match (self, other) {
      (Nat::Small(a), Nat::Small(b)) => a.cmp(b),
      (Nat::Small(_), Nat::Big(_)) => Ordering::Less,
      (Nat::Big(_), Nat::Small(_)) => Ordering::Greater,
      (Nat::Big(a), Nat::Big(b)) => a.cmp(b),
    }
  }
}

impl PartialOrd for Nat {
  fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
    Some(self.cmp(other))
  }
}

/// An integer: inline inside `i128`, a `BigInt` outside it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Int {
  Small(i128),
  /// Outside `i128`.
  Big(Box<BigInt>),
}

impl Int {
  fn of_big(x: BigInt) -> Int {
    match i128::try_from(&x) {
      Ok(v) => Int::Small(v),
      Err(_) => Int::Big(Box::new(x)),
    }
  }

  fn as_big(&self) -> Cow<'_, BigInt> {
    match self {
      Int::Small(v) => Cow::Owned(BigInt::from(*v)),
      Int::Big(b) => Cow::Borrowed(b),
    }
  }

  /// `op` on two inline values when it does not overflow, else `big`.
  fn combine(
    &self,
    b: &Int,
    op: fn(i128, i128) -> Option<i128>,
    big: fn(&BigInt, &BigInt) -> BigInt,
  ) -> Int {
    if let (Int::Small(x), Int::Small(y)) = (self, b)
      && let Some(v) = op(*x, *y)
    {
      return Int::Small(v);
    }
    Int::of_big(big(&self.as_big(), &b.as_big()))
  }
}

impl Default for Int {
  fn default() -> Self {
    Int::Small(0)
  }
}

impl Ord for Int {
  fn cmp(&self, other: &Self) -> Ordering {
    let big_side = |b: &BigInt| {
      if b.sign() == Sign::Minus { Ordering::Less } else { Ordering::Greater }
    };
    match (self, other) {
      (Int::Small(a), Int::Small(b)) => a.cmp(b),
      (Int::Small(_), Int::Big(b)) => big_side(b).reverse(),
      (Int::Big(a), Int::Small(_)) => big_side(a),
      (Int::Big(a), Int::Big(b)) => a.cmp(b),
    }
  }
}

impl PartialOrd for Int {
  fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
    Some(self.cmp(other))
  }
}

/// Signed differences of lengths.
pub(crate) trait Delta:
  Clone + Ord + Default + fmt::Debug + 'static
{
  fn of(x: i128) -> Self;
  /// `self + b`; `LengthOverflow` outside the representation.
  fn plus(&self, b: &Self) -> Result<Self, SharingError>;
  /// `self - b`; `LengthOverflow` outside the representation.
  fn minus(&self, b: &Self) -> Result<Self, SharingError>;
  /// `self * b`; `LengthOverflow` outside the representation.
  fn times(&self, b: &Self) -> Result<Self, SharingError>;
  /// The value, if it is a `u64`.
  fn to_u64(&self) -> Option<u64>;
  /// The exact value.
  #[cfg(test)]
  fn to_big(&self) -> BigInt;
}

impl Delta for i128 {
  #[inline]
  fn of(x: i128) -> Self {
    x
  }

  #[inline]
  fn plus(&self, b: &Self) -> Result<Self, SharingError> {
    self.checked_add(*b).ok_or_else(overflow)
  }

  #[inline]
  fn minus(&self, b: &Self) -> Result<Self, SharingError> {
    self.checked_sub(*b).ok_or_else(overflow)
  }

  #[inline]
  fn times(&self, b: &Self) -> Result<Self, SharingError> {
    self.checked_mul(*b).ok_or_else(overflow)
  }

  #[inline]
  fn to_u64(&self) -> Option<u64> {
    u64::try_from(*self).ok()
  }

  #[cfg(test)]
  fn to_big(&self) -> BigInt {
    BigInt::from(*self)
  }
}

impl Delta for Int {
  fn of(x: i128) -> Self {
    Int::Small(x)
  }

  fn plus(&self, b: &Self) -> Result<Self, SharingError> {
    Ok(self.combine(b, i128::checked_add, |x, y| x + y))
  }

  fn minus(&self, b: &Self) -> Result<Self, SharingError> {
    Ok(self.combine(b, i128::checked_sub, |x, y| x - y))
  }

  fn times(&self, b: &Self) -> Result<Self, SharingError> {
    Ok(self.combine(b, i128::checked_mul, |x, y| x * y))
  }

  fn to_u64(&self) -> Option<u64> {
    match self {
      Int::Small(v) => u64::try_from(*v).ok(),
      Int::Big(_) => None,
    }
  }

  #[cfg(test)]
  fn to_big(&self) -> BigInt {
    self.as_big().into_owned()
  }
}

/// A representation of the phase-1 integers: nonnegative values `U` and
/// their differences `S`.
pub(crate) trait Arith: 'static {
  type U: Clone + Ord + Default + fmt::Debug + 'static;
  type S: Delta;
  fn u(x: u64) -> Self::U;
  fn count(x: u128) -> Self::U;
  /// `a + b`; [`Fast`] saturates.
  fn add(a: &Self::U, b: &Self::U) -> Self::U;
  /// `a * b`; [`Fast`] saturates.
  fn mul(a: &Self::U, b: &Self::U) -> Self::U;
  /// `a - b`, for `b <= a`.
  fn sub(a: &Self::U, b: &Self::U) -> Self::U;
  /// Whether `a` may have saturated; never for [`Exact`].
  fn saturated(a: &Self::U) -> bool;
  /// `a` as a difference; `LengthOverflow` outside the representation.
  fn signed(a: &Self::U) -> Result<Self::S, SharingError>;
}

/// `u128` and `i128`, saturating or checked.
#[derive(Clone, Copy, Debug, Default)]
pub(crate) struct Fast;

/// [`Nat`] and [`Int`].
#[derive(Clone, Copy, Debug, Default)]
pub(crate) struct Exact;

impl Arith for Fast {
  type U = u128;
  type S = i128;

  #[inline]
  fn u(x: u64) -> u128 {
    u128::from(x)
  }

  #[inline]
  fn count(x: u128) -> u128 {
    x
  }

  #[inline]
  fn add(a: &u128, b: &u128) -> u128 {
    a.saturating_add(*b)
  }

  #[inline]
  fn mul(a: &u128, b: &u128) -> u128 {
    a.saturating_mul(*b)
  }

  #[inline]
  fn sub(a: &u128, b: &u128) -> u128 {
    if Self::saturated(a) || Self::saturated(b) {
      u128::MAX
    } else {
      a - b
    }
  }

  #[inline]
  fn saturated(a: &u128) -> bool {
    *a == u128::MAX
  }

  #[inline]
  fn signed(a: &u128) -> Result<i128, SharingError> {
    i128::try_from(*a).map_err(|_e| overflow())
  }
}

impl Arith for Exact {
  type U = Nat;
  type S = Int;

  fn u(x: u64) -> Nat {
    Nat::Small(u128::from(x))
  }

  fn count(x: u128) -> Nat {
    Nat::Small(x)
  }

  fn add(a: &Nat, b: &Nat) -> Nat {
    if let (Nat::Small(x), Nat::Small(y)) = (a, b)
      && let Some(v) = x.checked_add(*y)
    {
      return Nat::Small(v);
    }
    Nat::of_big(&*a.as_big() + &*b.as_big())
  }

  fn mul(a: &Nat, b: &Nat) -> Nat {
    if let (Nat::Small(x), Nat::Small(y)) = (a, b)
      && let Some(v) = x.checked_mul(*y)
    {
      return Nat::Small(v);
    }
    Nat::of_big(&*a.as_big() * &*b.as_big())
  }

  fn sub(a: &Nat, b: &Nat) -> Nat {
    if let (Nat::Small(x), Nat::Small(y)) = (a, b) {
      return Nat::Small(x - y);
    }
    Nat::of_big(&*a.as_big() - &*b.as_big())
  }

  fn saturated(_a: &Nat) -> bool {
    false
  }

  fn signed(a: &Nat) -> Result<Int, SharingError> {
    Ok(match a {
      Nat::Small(v) => i128::try_from(*v)
        .map_or_else(|_e| Int::Big(Box::new(BigInt::from(*v))), Int::Small),
      Nat::Big(b) => Int::Big(Box::new(BigInt::from((**b).clone()))),
    })
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  fn nat(x: &BigUint) -> Nat {
    Nat::of_big(x.clone())
  }

  /// The two representations agree wherever the fast one succeeds, the
  /// fast one refuses (never wraps) where its range ends, and the exact
  /// one is `BigUint`/`BigInt` arithmetic across the inline boundary.
  #[test]
  fn fast_matches_exact_and_exact_matches_big_integers() {
    let mut us: Vec<BigUint> =
      [0u64, 1, 2, 7, 255, 1 << 32, u64::MAX - 1, u64::MAX]
        .iter()
        .map(|&x| BigUint::from(x))
        .collect();
    let edge = BigUint::from(u128::MAX);
    us.extend([&edge - 1u32, edge.clone(), &edge + 1u32, &edge * &edge]);
    for a in &us {
      for b in &us {
        let (ea, eb) = (nat(a), nat(b));
        assert_eq!(ea.cmp(&eb), a.cmp(b));
        assert_eq!(Exact::add(&ea, &eb), nat(&(a + b)));
        assert_eq!(Exact::mul(&ea, &eb), nat(&(a * b)));
        if b <= a {
          assert_eq!(Exact::sub(&ea, &eb), nat(&(a - b)));
        }
        if let (Ok(x), Ok(y)) = (u128::try_from(a), u128::try_from(b)) {
          let sum = Fast::add(&x, &y);
          assert_eq!(Fast::saturated(&sum), a + b >= edge);
          if !Fast::saturated(&sum) {
            assert_eq!(BigUint::from(sum), a + b);
          }
          if b <= a {
            let diff = Fast::sub(&x, &y);
            assert_eq!(
              Fast::saturated(&diff),
              Fast::saturated(&x) || Fast::saturated(&y)
            );
            if !Fast::saturated(&diff) {
              assert_eq!(BigUint::from(diff), a - b);
            }
          }
        }
      }
      let signed = Exact::signed(&nat(a)).unwrap();
      assert_eq!(signed.to_big(), BigInt::from(a.clone()));
      if let Ok(x) = u128::try_from(a) {
        if i128::try_from(x).is_ok() {
          assert_eq!(Fast::signed(&x).unwrap().to_big(), signed.to_big());
        } else {
          assert_eq!(Fast::signed(&x), Err(overflow()));
        }
      }
    }
    let mut ss: Vec<BigInt> = [i128::MIN, -3, -1, 0, 1, 5, i128::MAX]
      .iter()
      .map(|&x| BigInt::from(x))
      .collect();
    ss.extend([
      BigInt::from(i128::MIN) - 1,
      BigInt::from(i128::MAX) + 1,
      BigInt::from(i128::MAX) * BigInt::from(i128::MAX),
      -(BigInt::from(i128::MAX) * BigInt::from(7)),
    ]);
    for a in &ss {
      for b in &ss {
        let (ia, ib) = (Int::of_big(a.clone()), Int::of_big(b.clone()));
        assert_eq!(ia.cmp(&ib), a.cmp(b), "{a} {b}");
        let fit = |r: Result<i128, SharingError>, e: &BigInt| match r {
          Ok(v) => assert_eq!(&BigInt::from(v), e),
          Err(err) => {
            assert_eq!(err, overflow());
            assert!(i128::try_from(e).is_err());
          },
        };
        assert_eq!(ia.plus(&ib).unwrap().to_big(), a + b);
        assert_eq!(ia.minus(&ib).unwrap().to_big(), a - b);
        assert_eq!(ia.times(&ib).unwrap().to_big(), a * b);
        if let (Ok(x), Ok(y)) = (i128::try_from(a), i128::try_from(b)) {
          fit(x.plus(&y), &(a + b));
          fit(x.minus(&y), &(a - b));
          fit(x.times(&y), &(a * b));
        }
      }
    }
    assert_eq!(Int::of(-1).to_u64(), None);
    assert_eq!(Int::of(i128::from(u64::MAX)).to_u64(), Some(u64::MAX));
    assert_eq!(Int::of_big(BigInt::from(i128::MAX) + 1).to_u64(), None);
    assert_eq!((i128::from(u64::MAX) + 1).to_u64(), None);
  }
}
