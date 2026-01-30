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
pub mod proof;
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
  ConstantMeta, DataValue, ExprMeta, ExprMetaData, KVMap, NameIndex,
  NameReverseIndex,
};
pub use proof::{CheckClaim, Claim, EvalClaim, Proof};
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

/// Tests verifying the byte-level examples in docs/Ixon.md are correct.
#[cfg(test)]
mod doc_examples {
  use super::*;
  use crate::ix::address::Address;

  // =========================================================================
  // Tag4 examples (docs section "Tag4 (4-bit flag)")
  // =========================================================================

  #[test]
  fn tag4_small_value() {
    // Tag4 { flag: 0x1, size: 5 }
    // Header: 0b0001_0_101 = 0x15
    let tag = Tag4::new(0x1, 5);
    let mut buf = Vec::new();
    tag.put(&mut buf);
    assert_eq!(buf, vec![0x15], "Tag4 {{ flag: 1, size: 5 }} should be 0x15");
  }

  #[test]
  fn tag4_large_value() {
    // Tag4 { flag: 0x2, size: 256 }
    // Header: 0b0010_1_001 = 0x29 (large=1, 2 bytes follow)
    // Bytes: 0x00 0x01 (256 in little-endian)
    let tag = Tag4::new(0x2, 256);
    let mut buf = Vec::new();
    tag.put(&mut buf);
    assert_eq!(
      buf,
      vec![0x29, 0x00, 0x01],
      "Tag4 {{ flag: 2, size: 256 }} should be [0x29, 0x00, 0x01]"
    );
  }

  // =========================================================================
  // Tag2 examples (docs section "Tag2 (2-bit flag)")
  // =========================================================================

  #[test]
  fn tag2_small_value() {
    // Tag2 { flag: 0, size: 15 }
    // Header: 0b00_0_01111 = 0x0F
    let tag = Tag2::new(0, 15);
    let mut buf = Vec::new();
    tag.put(&mut buf);
    assert_eq!(buf, vec![0x0F], "Tag2 {{ flag: 0, size: 15 }} should be 0x0F");
  }

  #[test]
  fn tag2_large_value() {
    // Tag2 { flag: 3, size: 100 }
    // 100 doesn't fit in 5 bits, needs 1 byte to encode
    // Header: 0b11_1_00000 = 0xE0 (flag=3, large=1, byte_count-1=0)
    // Bytes: 0x64 (100)
    let tag = Tag2::new(3, 100);
    let mut buf = Vec::new();
    tag.put(&mut buf);
    assert_eq!(
      buf,
      vec![0xE0, 0x64],
      "Tag2 {{ flag: 3, size: 100 }} should be [0xE0, 0x64]"
    );
  }

  // =========================================================================
  // Tag0 examples (docs section "Tag0 (no flag)")
  // =========================================================================

  #[test]
  fn tag0_small_value() {
    // Tag0 { size: 42 }
    // Header: 0b0_0101010 = 0x2A
    let tag = Tag0::new(42);
    let mut buf = Vec::new();
    tag.put(&mut buf);
    assert_eq!(buf, vec![0x2A], "Tag0 {{ size: 42 }} should be 0x2A");
  }

  #[test]
  fn tag0_large_value() {
    // Tag0 { size: 1000 }
    // 1000 = 0x3E8, needs 2 bytes to encode
    // Header: 0b1_0000001 = 0x81 (large=1, byte_count-1=1)
    // Bytes: 0xE8 0x03 (1000 in little-endian)
    let tag = Tag0::new(1000);
    let mut buf = Vec::new();
    tag.put(&mut buf);
    assert_eq!(
      buf,
      vec![0x81, 0xE8, 0x03],
      "Tag0 {{ size: 1000 }} should be [0x81, 0xE8, 0x03]"
    );
  }

  // =========================================================================
  // Universe examples (docs section "Universes")
  // =========================================================================

  #[test]
  fn univ_zero() {
    // Univ::Zero -> Tag2 { flag: 0, size: 0 } -> 0x00
    let mut buf = Vec::new();
    univ::put_univ(&Univ::zero(), &mut buf);
    assert_eq!(buf, vec![0x00], "Univ::Zero should be 0x00");
  }

  #[test]
  fn univ_succ_zero() {
    // Univ::Succ(Zero) uses telescope compression:
    // Tag2 { flag: 0, size: 1 } (succ_count=1) + base (Zero)
    // = 0b00_0_00001 = 0x01, then Zero = 0x00
    let mut buf = Vec::new();
    univ::put_univ(&Univ::succ(Univ::zero()), &mut buf);
    assert_eq!(buf, vec![0x01, 0x00], "Univ::Succ(Zero) should be [0x01, 0x00]");
  }

  #[test]
  fn univ_var_1() {
    // Univ::Var(1) -> Tag2 { flag: 3, size: 1 }
    // = 0b11_0_00001 = 0xC1
    let mut buf = Vec::new();
    univ::put_univ(&Univ::var(1), &mut buf);
    assert_eq!(buf, vec![0xC1], "Univ::Var(1) should be 0xC1");
  }

  #[test]
  fn univ_max_zero_var1() {
    // Univ::Max(Zero, Var(1)) -> Tag2 { flag: 1, size: 0 } + Zero + Var(1)
    // = 0b01_0_00000 = 0x40, then 0x00 (Zero), then 0xC1 (Var(1))
    let mut buf = Vec::new();
    univ::put_univ(&Univ::max(Univ::zero(), Univ::var(1)), &mut buf);
    assert_eq!(
      buf,
      vec![0x40, 0x00, 0xC1],
      "Univ::Max(Zero, Var(1)) should be [0x40, 0x00, 0xC1]"
    );
  }

  // =========================================================================
  // Expression examples (docs section "Expression Examples")
  // =========================================================================

  #[test]
  fn expr_var_0() {
    // Expr::Var(0) -> Tag4 { flag: 0x1, size: 0 } -> 0x10
    let mut buf = Vec::new();
    serialize::put_expr(&Expr::Var(0), &mut buf);
    assert_eq!(buf, vec![0x10], "Expr::Var(0) should be 0x10");
  }

  #[test]
  fn expr_sort_0() {
    // Expr::Sort(0) -> Tag4 { flag: 0x0, size: 0 } -> 0x00
    let mut buf = Vec::new();
    serialize::put_expr(&Expr::Sort(0), &mut buf);
    assert_eq!(buf, vec![0x00], "Expr::Sort(0) should be 0x00");
  }

  #[test]
  fn expr_ref_no_univs() {
    // Expr::Ref(0, []) -> Tag4 { flag: 0x2, size: 0 } + idx(0)
    // = 0x20 + 0x00
    let mut buf = Vec::new();
    serialize::put_expr(&Expr::Ref(0, vec![]), &mut buf);
    assert_eq!(buf, vec![0x20, 0x00], "Expr::Ref(0, []) should be [0x20, 0x00]");
  }

  #[test]
  fn expr_share_5() {
    // Expr::Share(5) -> Tag4 { flag: 0xB, size: 5 } -> 0xB5
    let mut buf = Vec::new();
    serialize::put_expr(&Expr::Share(5), &mut buf);
    assert_eq!(buf, vec![0xB5], "Expr::Share(5) should be 0xB5");
  }

  #[test]
  fn expr_app_telescope() {
    // App(App(App(f, a), b), c) with f=Var(3), a=Var(2), b=Var(1), c=Var(0)
    // -> Tag4 { flag: 0x7, size: 3 } + f + a + b + c
    // = 0x73 + 0x13 + 0x12 + 0x11 + 0x10
    let expr = Expr::app(
      Expr::app(Expr::app(Expr::var(3), Expr::var(2)), Expr::var(1)),
      Expr::var(0),
    );
    let mut buf = Vec::new();
    serialize::put_expr(&expr, &mut buf);
    assert_eq!(
      buf,
      vec![0x73, 0x13, 0x12, 0x11, 0x10],
      "App telescope should be [0x73, 0x13, 0x12, 0x11, 0x10]"
    );
  }

  #[test]
  fn expr_lam_telescope() {
    // Lam(t1, Lam(t2, Lam(t3, body))) with all types Sort(0) and body Var(0)
    // -> Tag4 { flag: 0x8, size: 3 } + t1 + t2 + t3 + body
    // = 0x83 + 0x00 + 0x00 + 0x00 + 0x10
    let ty = Expr::sort(0);
    let expr = Expr::lam(
      ty.clone(),
      Expr::lam(ty.clone(), Expr::lam(ty.clone(), Expr::var(0))),
    );
    let mut buf = Vec::new();
    serialize::put_expr(&expr, &mut buf);
    assert_eq!(
      buf,
      vec![0x83, 0x00, 0x00, 0x00, 0x10],
      "Lam telescope should be [0x83, 0x00, 0x00, 0x00, 0x10]"
    );
  }

  // =========================================================================
  // Claim/Proof examples (docs section "Proofs")
  // =========================================================================

  #[test]
  fn eval_claim_tag() {
    // EvalClaim -> Tag4 { flag: 0xF, size: 0 } -> 0xF0
    let claim = proof::Claim::Evals(proof::EvalClaim {
      lvls: Address::hash(b"lvls"),
      typ: Address::hash(b"typ"),
      input: Address::hash(b"input"),
      output: Address::hash(b"output"),
    });
    let mut buf = Vec::new();
    claim.put(&mut buf);
    assert_eq!(buf[0], 0xF0, "EvalClaim should start with 0xF0");
    assert_eq!(buf.len(), 1 + 128, "EvalClaim should be 1 + 4*32 = 129 bytes");
  }

  #[test]
  fn eval_proof_tag() {
    // EvalProof -> Tag4 { flag: 0xF, size: 1 } -> 0xF1
    let proof = proof::Proof::new(
      proof::Claim::Evals(proof::EvalClaim {
        lvls: Address::hash(b"lvls"),
        typ: Address::hash(b"typ"),
        input: Address::hash(b"input"),
        output: Address::hash(b"output"),
      }),
      vec![1, 2, 3, 4],
    );
    let mut buf = Vec::new();
    proof.put(&mut buf);
    assert_eq!(buf[0], 0xF1, "EvalProof should start with 0xF1");
    // 1 (tag) + 128 (addresses) + 1 (len=4) + 4 (proof bytes) = 134
    assert_eq!(buf.len(), 134, "EvalProof with 4 bytes should be 134 bytes");
    assert_eq!(buf[129], 0x04, "proof.len should be 0x04");
    assert_eq!(&buf[130..134], &[1, 2, 3, 4], "proof bytes should be [1,2,3,4]");
  }

  #[test]
  fn check_claim_tag() {
    // CheckClaim -> Tag4 { flag: 0xF, size: 2 } -> 0xF2
    let claim = proof::Claim::Checks(proof::CheckClaim {
      lvls: Address::hash(b"lvls"),
      typ: Address::hash(b"typ"),
      value: Address::hash(b"value"),
    });
    let mut buf = Vec::new();
    claim.put(&mut buf);
    assert_eq!(buf[0], 0xF2, "CheckClaim should start with 0xF2");
    assert_eq!(buf.len(), 1 + 96, "CheckClaim should be 1 + 3*32 = 97 bytes");
  }

  #[test]
  fn check_proof_tag() {
    // CheckProof -> Tag4 { flag: 0xF, size: 3 } -> 0xF3
    let proof = proof::Proof::new(
      proof::Claim::Checks(proof::CheckClaim {
        lvls: Address::hash(b"lvls"),
        typ: Address::hash(b"typ"),
        value: Address::hash(b"value"),
      }),
      vec![5, 6, 7],
    );
    let mut buf = Vec::new();
    proof.put(&mut buf);
    assert_eq!(buf[0], 0xF3, "CheckProof should start with 0xF3");
  }

  // =========================================================================
  // Definition packed byte example (docs "Comprehensive Worked Example")
  // =========================================================================

  #[test]
  fn definition_packed_kind_safety() {
    // DefKind::Definition = 0, DefinitionSafety::Safe = 1
    // Packed: (0 << 2) | 1 = 0x01
    use crate::ix::env::DefinitionSafety;
    use constant::{DefKind, Definition};

    let def = Definition {
      kind: DefKind::Definition,
      safety: DefinitionSafety::Safe,
      lvls: 0,
      typ: Expr::sort(0),
      value: Expr::var(0),
    };
    let mut buf = Vec::new();
    def.put(&mut buf);
    assert_eq!(buf[0], 0x01, "Definition(Safe) packed byte should be 0x01");
  }

  #[test]
  fn definition_opaque_unsafe() {
    // DefKind::Opaque = 1, DefinitionSafety::Unsafe = 0
    // Packed: (1 << 2) | 0 = 0x04
    use crate::ix::env::DefinitionSafety;
    use constant::{DefKind, Definition};

    let def = Definition {
      kind: DefKind::Opaque,
      safety: DefinitionSafety::Unsafe,
      lvls: 0,
      typ: Expr::sort(0),
      value: Expr::var(0),
    };
    let mut buf = Vec::new();
    def.put(&mut buf);
    assert_eq!(buf[0], 0x04, "Opaque(Unsafe) packed byte should be 0x04");
  }

  #[test]
  fn definition_theorem_partial() {
    // DefKind::Theorem = 2, DefinitionSafety::Partial = 2
    // Packed: (2 << 2) | 2 = 0x0A
    use crate::ix::env::DefinitionSafety;
    use constant::{DefKind, Definition};

    let def = Definition {
      kind: DefKind::Theorem,
      safety: DefinitionSafety::Partial,
      lvls: 0,
      typ: Expr::sort(0),
      value: Expr::var(0),
    };
    let mut buf = Vec::new();
    def.put(&mut buf);
    assert_eq!(buf[0], 0x0A, "Theorem(Partial) packed byte should be 0x0A");
  }

  // =========================================================================
  // Constant tag examples
  // =========================================================================

  #[test]
  fn constant_defn_tag() {
    // Constant with Defn -> Tag4 { flag: 0xD, size: 0 } -> 0xD0
    use crate::ix::env::DefinitionSafety;
    use constant::{Constant, ConstantInfo, DefKind, Definition};

    let constant = Constant::new(ConstantInfo::Defn(Definition {
      kind: DefKind::Definition,
      safety: DefinitionSafety::Safe,
      lvls: 0,
      typ: Expr::sort(0),
      value: Expr::var(0),
    }));
    let mut buf = Vec::new();
    constant.put(&mut buf);
    assert_eq!(buf[0], 0xD0, "Constant(Defn) should start with 0xD0");
  }

  #[test]
  fn constant_muts_tag() {
    // Muts with 3 entries -> Tag4 { flag: 0xC, size: 3 } -> 0xC3
    use crate::ix::env::DefinitionSafety;
    use constant::{Constant, ConstantInfo, DefKind, Definition, MutConst};

    let def = Definition {
      kind: DefKind::Definition,
      safety: DefinitionSafety::Safe,
      lvls: 0,
      typ: Expr::sort(0),
      value: Expr::var(0),
    };
    let constant = Constant::new(ConstantInfo::Muts(vec![
      MutConst::Defn(def.clone()),
      MutConst::Defn(def.clone()),
      MutConst::Defn(def),
    ]));
    let mut buf = Vec::new();
    constant.put(&mut buf);
    assert_eq!(buf[0], 0xC3, "Muts with 3 entries should start with 0xC3");
  }

  // =========================================================================
  // Environment tag
  // =========================================================================

  #[test]
  fn env_tag() {
    // Env -> Tag4 { flag: 0xE, size: VERSION=2 } -> 0xE2
    let env = env::Env::new();
    let mut buf = Vec::new();
    env.put(&mut buf);
    assert_eq!(buf[0], 0xE2, "Env should start with 0xE2 (flag=E, version=2)");
  }
}
