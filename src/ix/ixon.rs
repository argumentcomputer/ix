//! Ixon: Content-addressed serialization format for Lean kernel types.
//!
//! This module provides:
//! - Alpha-invariant representations of Lean expressions and constants
//! - Compact tag-based serialization (Tag4 for exprs, Tag2 for univs, Tag0 for ints)
//! - Content-addressed storage with sharing support
//! - Cryptographic commitments for ZK proofs

pub mod comm;
pub mod constant;
pub mod env;
pub mod error;
pub mod expr;
pub mod metadata;
pub mod serialize;
pub mod sharing;
pub mod tag;
pub mod univ;

// Re-export main types
pub use comm::Comm;
pub use constant::{
  Axiom, Constant, ConstantInfo, Constructor, ConstructorProj, DefKind,
  Definition, DefinitionProj, Inductive, InductiveProj, MutConst, Quotient,
  Recursor, RecursorProj, RecursorRule,
};
pub use env::{Env, Named};
pub use error::{CompileError, DecompileError, SerializeError};
pub use expr::Expr;
pub use metadata::{
  ConstantMeta, CtorMeta, DataValue, ExprMeta, ExprMetas, KVMap, NameIndex,
  NameReverseIndex,
};
pub use tag::{Tag0, Tag2, Tag4};
pub use univ::Univ;

/// Shared test utilities for ixon modules.
#[cfg(test)]
pub mod tests {
  use quickcheck::{Arbitrary, Gen};
  use std::ops::Range;

  pub fn gen_range(g: &mut Gen, range: Range<usize>) -> usize {
    let res: usize = Arbitrary::arbitrary(g);
    if range.is_empty() {
      0
    } else {
      (res % (range.end - range.start)) + range.start
    }
  }

  pub fn next_case<A: Copy>(g: &mut Gen, gens: &[(usize, A)]) -> A {
    let sum: usize = gens.iter().map(|x| x.0).sum();
    let mut weight: usize = gen_range(g, 1..(sum + 1));
    for (n, case) in gens {
      if *n == 0 {
        continue;
      }
      match weight.checked_sub(*n) {
        None | Some(0) => return *case,
        _ => weight -= *n,
      }
    }
    gens.last().unwrap().1
  }

  pub fn gen_vec<A, F>(g: &mut Gen, size: usize, mut f: F) -> Vec<A>
  where
    F: FnMut(&mut Gen) -> A,
  {
    let len = gen_range(g, 0..size);
    (0..len).map(|_| f(g)).collect()
  }
}
