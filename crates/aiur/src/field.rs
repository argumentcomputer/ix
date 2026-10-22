//! Field backends for execution and witness population. Native backends retain
//! field elements in registers, records and callbacks. Canonical integers are
//! used only at interchange boundaries and when an operation needs an index.
use serde::Serialize;
use std::{
  fmt::{Debug, Display},
  hash::Hash,
  marker::PhantomData,
};

// Use the same field contract as our maintained proving library. No concrete
// field is selected by the interpreter, and no direct Plonky3 dependency is
// needed here.
pub use multi_stark::p3_field::{Field, PrimeCharacteristicRing, PrimeField64};

/// Arithmetic and integer-boundary conversions. The associated element is the
/// actual value stored by the VM, not an encoding chosen by the VM. This small
/// adapter also lets the Lean FFI retain its runtime-selected prime backend.
/// Implementations must preserve arithmetic modulo `modulus()`, use field-value
/// equality/hash, and make `from_u64` reduce integers while `to_u64` returns the
/// canonical representative. `decode` rejects noncanonical wire integers before
/// conversion. All valid native representations may be accepted by `valid`.
pub trait FieldBackend: Copy + Debug + Send + Sync + 'static {
  type Element: Copy
    + Eq
    + Hash
    + Debug
    + Display
    + Serialize
    + Send
    + Sync
    + 'static;
  /// Every value of Element passes `valid`. This permits omitting redundant
  /// host-output checks for native field types, but never enum/tag checks.
  const ALL_ELEMENTS_VALID: bool = false;
  fn modulus(self) -> u64;
  #[allow(
    clippy::wrong_self_convention,
    reason = "conversion needs the selected runtime backend"
  )]
  fn from_u64(self, value: u64) -> Self::Element;
  fn to_u64(self, value: Self::Element) -> u64;
  fn add(self, a: Self::Element, b: Self::Element) -> Self::Element;
  fn sub(self, a: Self::Element, b: Self::Element) -> Self::Element;
  fn neg(self, a: Self::Element) -> Self::Element;
  fn mul(self, a: Self::Element, b: Self::Element) -> Self::Element;
  fn inverse(self, a: Self::Element) -> Option<Self::Element>;
  fn valid(self, _value: Self::Element) -> bool {
    true
  }
  fn zero(self) -> Self::Element {
    self.from_u64(0)
  }
  fn one(self) -> Self::Element {
    self.from_u64(1)
  }
  fn contains(self, word: u64) -> bool {
    word < self.modulus()
  }
  fn decode(self, words: &[u64]) -> Result<Vec<Self::Element>, String> {
    words
      .iter()
      .map(|&word| {
        if self.contains(word) {
          Ok(self.from_u64(word))
        } else {
          Err("noncanonical field element".into())
        }
      })
      .collect()
  }
}

/// Zero-sized, statically dispatched adapter for any field implementing
/// multi-stark's prime-field traits. Its values are F itself, including in host
/// hint/table closures. The wire format currently supports 64-bit prime fields.
#[derive(Clone, Copy, Debug, Default)]
pub struct NativeField<F>(PhantomData<F>);
impl<F> NativeField<F> {
  pub const fn new() -> Self {
    Self(PhantomData)
  }
}
impl<F: PrimeField64> FieldBackend for NativeField<F> {
  type Element = F;
  const ALL_ELEMENTS_VALID: bool = true;
  #[inline]
  fn modulus(self) -> u64 {
    F::ORDER_U64
  }
  #[inline]
  fn from_u64(self, value: u64) -> F {
    F::from_u64(value)
  }
  #[inline]
  fn to_u64(self, value: F) -> u64 {
    value.as_canonical_u64()
  }
  #[inline]
  fn add(self, a: F, b: F) -> F {
    a + b
  }
  #[inline]
  fn sub(self, a: F, b: F) -> F {
    a - b
  }
  #[inline]
  fn neg(self, a: F) -> F {
    -a
  }
  #[inline]
  fn mul(self, a: F, b: F) -> F {
    a * b
  }
  #[inline]
  fn inverse(self, a: F) -> Option<F> {
    a.try_inverse()
  }
}

#[derive(Clone, Copy, Debug)]
pub struct PrimeField {
  modulus: u64,
}

impl PrimeField {
  pub fn new(modulus: u64) -> Result<Self, String> {
    if !is_prime(modulus) {
      return Err(format!("field modulus {modulus} is not prime"));
    }
    Ok(Self { modulus })
  }

  pub fn modulus(self) -> u64 {
    self.modulus
  }
  pub fn contains(self, value: u64) -> bool {
    value < self.modulus
  }
  #[inline]
  pub fn add(self, a: u64, b: u64) -> u64 {
    ((u128::from(a) + u128::from(b)) % u128::from(self.modulus)) as u64
  }
  pub fn sub(self, a: u64, b: u64) -> u64 {
    if a >= b { a - b } else { self.modulus - (b - a) }
  }
  pub fn neg(self, a: u64) -> u64 {
    if a == 0 { 0 } else { self.modulus - a }
  }
  #[inline]
  pub fn mul(self, a: u64, b: u64) -> u64 {
    ((u128::from(a) * u128::from(b)) % u128::from(self.modulus)) as u64
  }
  pub fn inverse(self, a: u64) -> Option<u64> {
    (a != 0).then(|| self.pow(a, self.modulus - 2))
  }
  fn pow(self, mut base: u64, mut power: u64) -> u64 {
    let mut result = 1;
    while power != 0 {
      if power & 1 != 0 {
        result = self.mul(result, base);
      }
      base = self.mul(base, base);
      power >>= 1;
    }
    result
  }
}

impl FieldBackend for PrimeField {
  type Element = u64;
  fn modulus(self) -> u64 {
    self.modulus
  }
  fn from_u64(self, value: u64) -> u64 {
    value % self.modulus
  }
  fn to_u64(self, value: u64) -> u64 {
    value
  }
  fn add(self, a: u64, b: u64) -> u64 {
    self.add(a, b)
  }
  fn sub(self, a: u64, b: u64) -> u64 {
    self.sub(a, b)
  }
  fn neg(self, a: u64) -> u64 {
    self.neg(a)
  }
  fn mul(self, a: u64, b: u64) -> u64 {
    self.mul(a, b)
  }
  fn inverse(self, a: u64) -> Option<u64> {
    self.inverse(a)
  }
  fn valid(self, value: u64) -> bool {
    self.contains(value)
  }
}

fn is_prime(n: u64) -> bool {
  for p in [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37] {
    if n == p {
      return true;
    }
    if n < 2 || n.is_multiple_of(p) {
      return false;
    }
  }
  // These Miller–Rabin bases cover the entire u64 range.
  let field = PrimeField { modulus: n };
  let shifts = (n - 1).trailing_zeros();
  let odd = (n - 1) >> shifts;
  for base in [2, 325, 9_375, 28_178, 450_775, 9_780_504, 1_795_265_022] {
    let base = base % n;
    if base == 0 {
      continue;
    }
    let mut x = field.pow(base, odd);
    if x == 1 || x == n - 1 {
      continue;
    }
    let mut passed = false;
    for _ in 1..shifts {
      x = field.mul(x, x);
      if x == n - 1 {
        passed = true;
        break;
      }
    }
    if !passed {
      return false;
    }
  }
  true
}

#[cfg(test)]
mod tests {
  use super::*;
  const GOLDILOCKS: u64 = 0xffff_ffff_0000_0001;
  #[test]
  fn specialized_arithmetic_matches_integer_reduction() {
    for p in [2, 97, 65_537, GOLDILOCKS, 18_446_744_073_709_551_557] {
      let field = PrimeField::new(p).unwrap();
      let mut state = 0x1234_5678_9abc_def0u64;
      let edges = [0, 1, 2, p / 2, p - 2, p - 1];
      let check = |a: u64, b: u64| {
        let (a, b) = (a % p, b % p);
        let modulus = u128::from(p);
        assert_eq!(
          field.add(a, b),
          ((u128::from(a) + u128::from(b)) % modulus) as u64
        );
        assert_eq!(
          field.sub(a, b),
          ((u128::from(a) + modulus - u128::from(b)) % modulus) as u64
        );
        assert_eq!(
          field.mul(a, b),
          ((u128::from(a) * u128::from(b)) % modulus) as u64
        );
        if let Some(inverse) = field.inverse(a) {
          assert!(inverse < p);
          assert_eq!((u128::from(a) * u128::from(inverse)) % modulus, 1);
        } else {
          assert_eq!(a, 0);
        }
      };
      for a in edges {
        for b in edges {
          check(a, b);
        }
      }
      for _ in 0..4096 {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        let a = state;
        state = state.wrapping_mul(0xd134_2543_de82_ef95).wrapping_add(1);
        check(a, state);
      }
    }
  }
  #[test]
  fn arithmetic_at_word_boundary() {
    let p = 18_446_744_069_414_584_321;
    let f = PrimeField::new(p).unwrap();
    assert_eq!(f.add(p - 1, p - 1), p - 2);
    assert_eq!(f.mul(p - 1, p - 1), 1);
    assert_eq!(f.sub(0, p - 1), 1);
    assert_eq!(f.inverse(0), None);
    for a in [1, 2, 7, p - 2, p - 1] {
      assert_eq!(f.mul(a, f.inverse(a).unwrap()), 1);
    }
  }
  #[test]
  fn rejects_composites_including_pseudoprimes() {
    for n in [0, 1, 4, 561, 3_215_031_751, 341_550_071_728_321, u64::MAX] {
      assert!(PrimeField::new(n).is_err(), "{n}");
    }
    for n in [2, 3, 7, 97, 65_537, 18_446_744_073_709_551_557] {
      assert!(PrimeField::new(n).is_ok(), "{n}");
    }
  }
}
