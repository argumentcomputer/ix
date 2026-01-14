//! Universe levels.

use std::sync::Arc;

use super::tag::Tag2;

/// Universe levels for Lean's type system.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Univ {
  /// Universe zero (Prop/Type 0)
  Zero,
  /// Successor universe
  Succ(Arc<Univ>),
  /// Maximum of two universes
  Max(Arc<Univ>, Arc<Univ>),
  /// Impredicative maximum (IMax u v = 0 if v = 0, else Max u v)
  IMax(Arc<Univ>, Arc<Univ>),
  /// Universe parameter (de Bruijn index)
  Var(u64),
}

impl Univ {
  /// Tag2 flags for universe variants.
  pub const FLAG_ZERO_SUCC: u8 = 0; // size=0 for Zero, size=1 for Succ
  pub const FLAG_MAX: u8 = 1;
  pub const FLAG_IMAX: u8 = 2;
  pub const FLAG_VAR: u8 = 3;

  pub fn zero() -> Arc<Self> {
    Arc::new(Univ::Zero)
  }

  pub fn succ(u: Arc<Self>) -> Arc<Self> {
    Arc::new(Univ::Succ(u))
  }

  pub fn max(a: Arc<Self>, b: Arc<Self>) -> Arc<Self> {
    Arc::new(Univ::Max(a, b))
  }

  pub fn imax(a: Arc<Self>, b: Arc<Self>) -> Arc<Self> {
    Arc::new(Univ::IMax(a, b))
  }

  pub fn var(idx: u64) -> Arc<Self> {
    Arc::new(Univ::Var(idx))
  }
}

/// Serialize a universe to bytes (iterative to avoid stack overflow).
pub fn put_univ(u: &Univ, buf: &mut Vec<u8>) {
  let mut stack: Vec<&Univ> = vec![u];

  while let Some(curr) = stack.pop() {
    match curr {
      Univ::Zero => {
        Tag2::new(Univ::FLAG_ZERO_SUCC, 0).put(buf);
      }
      Univ::Succ(inner) => {
        // Count the number of successors for telescope compression
        let mut count = 1u64;
        let mut base = inner.as_ref();
        while let Univ::Succ(next) = base {
          count += 1;
          base = next.as_ref();
        }
        Tag2::new(Univ::FLAG_ZERO_SUCC, count).put(buf);
        stack.push(base);
      }
      Univ::Max(a, b) => {
        Tag2::new(Univ::FLAG_MAX, 0).put(buf);
        stack.push(b); // Process b after a
        stack.push(a);
      }
      Univ::IMax(a, b) => {
        Tag2::new(Univ::FLAG_IMAX, 0).put(buf);
        stack.push(b); // Process b after a
        stack.push(a);
      }
      Univ::Var(idx) => {
        Tag2::new(Univ::FLAG_VAR, *idx).put(buf);
      }
    }
  }
}

/// Frame for iterative universe deserialization.
enum GetUnivFrame {
  /// Parse a universe from the buffer
  Parse,
  /// Wrap the top result in `count` Succs
  WrapSuccs(u64),
  /// Pop two results (b then a) and push Max(a, b)
  BuildMax,
  /// Pop two results (b then a) and push IMax(a, b)
  BuildIMax,
}

/// Deserialize a universe from bytes (iterative to avoid stack overflow).
pub fn get_univ(buf: &mut &[u8]) -> Result<Arc<Univ>, String> {
  let mut work: Vec<GetUnivFrame> = vec![GetUnivFrame::Parse];
  let mut results: Vec<Arc<Univ>> = Vec::new();

  while let Some(frame) = work.pop() {
    match frame {
      GetUnivFrame::Parse => {
        let tag = Tag2::get(buf)?;
        match tag.flag {
          Univ::FLAG_ZERO_SUCC => {
            if tag.size == 0 {
              results.push(Univ::zero());
            } else {
              // Parse inner, then wrap in Succs
              work.push(GetUnivFrame::WrapSuccs(tag.size));
              work.push(GetUnivFrame::Parse);
            }
          }
          Univ::FLAG_MAX => {
            // Parse a, parse b, then build Max(a, b)
            work.push(GetUnivFrame::BuildMax);
            work.push(GetUnivFrame::Parse); // b
            work.push(GetUnivFrame::Parse); // a
          }
          Univ::FLAG_IMAX => {
            // Parse a, parse b, then build IMax(a, b)
            work.push(GetUnivFrame::BuildIMax);
            work.push(GetUnivFrame::Parse); // b
            work.push(GetUnivFrame::Parse); // a
          }
          Univ::FLAG_VAR => {
            results.push(Univ::var(tag.size));
          }
          f => return Err(format!("get_univ: invalid flag {f}")),
        }
      }
      GetUnivFrame::WrapSuccs(count) => {
        let mut result = results.pop().ok_or("get_univ: missing result for WrapSuccs")?;
        for _ in 0..count {
          result = Univ::succ(result);
        }
        results.push(result);
      }
      GetUnivFrame::BuildMax => {
        let b = results.pop().ok_or("get_univ: missing b for Max")?;
        let a = results.pop().ok_or("get_univ: missing a for Max")?;
        results.push(Univ::max(a, b));
      }
      GetUnivFrame::BuildIMax => {
        let b = results.pop().ok_or("get_univ: missing b for IMax")?;
        let a = results.pop().ok_or("get_univ: missing a for IMax")?;
        results.push(Univ::imax(a, b));
      }
    }
  }

  results.pop().ok_or_else(|| "get_univ: no result".to_string())
}

#[cfg(test)]
pub mod tests {
  use super::*;
  use crate::ix::ixon::tests::{gen_range, next_case};
  use quickcheck::{Arbitrary, Gen};
  use std::ptr;

  #[derive(Clone, Copy)]
  enum Case { Zero, Succ, Max, IMax, Var }

  /// Generate an arbitrary Univ using pointer-tree technique (no stack overflow)
  pub fn arbitrary_univ(g: &mut Gen) -> Arc<Univ> {
    let mut root = Univ::Zero;
    let mut stack = vec![&mut root as *mut Univ];

    while let Some(ptr) = stack.pop() {
      let gens = [(100, Case::Zero), (100, Case::Var), (50, Case::Succ), (30, Case::Max), (20, Case::IMax)];
      match next_case(g, &gens) {
        Case::Zero => unsafe { ptr::write(ptr, Univ::Zero); },
        Case::Var => unsafe { ptr::write(ptr, Univ::Var(gen_range(g, 0..16) as u64)); },
        Case::Succ => {
          let mut inner = Arc::new(Univ::Zero);
          let inner_ptr = Arc::get_mut(&mut inner).unwrap() as *mut Univ;
          unsafe { ptr::write(ptr, Univ::Succ(inner)); }
          stack.push(inner_ptr);
        }
        Case::Max => {
          let mut a = Arc::new(Univ::Zero);
          let mut b = Arc::new(Univ::Zero);
          let (a_ptr, b_ptr) = (Arc::get_mut(&mut a).unwrap() as *mut Univ, Arc::get_mut(&mut b).unwrap() as *mut Univ);
          unsafe { ptr::write(ptr, Univ::Max(a, b)); }
          stack.push(b_ptr); stack.push(a_ptr);
        }
        Case::IMax => {
          let mut a = Arc::new(Univ::Zero);
          let mut b = Arc::new(Univ::Zero);
          let (a_ptr, b_ptr) = (Arc::get_mut(&mut a).unwrap() as *mut Univ, Arc::get_mut(&mut b).unwrap() as *mut Univ);
          unsafe { ptr::write(ptr, Univ::IMax(a, b)); }
          stack.push(b_ptr); stack.push(a_ptr);
        }
      }
    }
    Arc::new(root)
  }

  #[derive(Clone, Debug)]
  struct ArbitraryUniv(Arc<Univ>);

  impl Arbitrary for ArbitraryUniv {
    fn arbitrary(g: &mut Gen) -> Self { ArbitraryUniv(arbitrary_univ(g)) }
  }

  fn roundtrip(u: &Univ) -> bool {
    let mut buf = Vec::new();
    put_univ(u, &mut buf);
    match get_univ(&mut buf.as_slice()) { Ok(result) => result.as_ref() == u, Err(_) => false }
  }

  #[quickcheck]
  fn prop_univ_roundtrip(u: ArbitraryUniv) -> bool { roundtrip(&u.0) }

  #[test]
  fn test_univ_zero() { assert!(roundtrip(&Univ::Zero)); }

  #[test]
  fn test_univ_succ() {
    assert!(roundtrip(&Univ::Succ(Univ::zero())));
    assert!(roundtrip(&Univ::Succ(Arc::new(Univ::Succ(Arc::new(Univ::Succ(Univ::zero())))))));
  }

  #[test]
  fn test_univ_max() { assert!(roundtrip(&Univ::Max(Univ::var(0), Univ::var(1)))); }

  #[test]
  fn test_univ_var() { assert!(roundtrip(&Univ::Var(0))); assert!(roundtrip(&Univ::Var(100))); }

  #[test]
  fn test_univ_succ_telescope() { assert!(roundtrip(&Univ::succ(Univ::succ(Univ::succ(Univ::zero()))))); }
}
