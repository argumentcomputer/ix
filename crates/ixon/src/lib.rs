//! Ixon: Content-addressed serialization format for Lean kernel types.
//!
//! This module provides:
//! - Alpha-invariant representations of Lean expressions and constants
//! - Compact TagN integer serialization (4-bit flag for exprs, 2-bit for univs, none for ints)
//! - Content-addressed storage with sharing support
//! - Cryptographic commitments for ZK proofs

pub mod assumption_tree;
pub mod canon_univ;
pub mod catalog;
pub mod comm;
pub mod constant;
pub mod contract;
#[cfg(not(target_arch = "riscv64"))]
pub mod diff;
pub mod env;
pub mod error;
pub mod expr;
pub mod lazy;
pub mod map;
pub mod merkle;
pub mod metadata;
pub mod proof;
pub mod resource;
pub mod serialize;
pub mod shard_claim;
pub mod sharing_exact;
pub mod syntax;
pub mod tag;
pub mod univ;

/// Stable identifier for the Ixon wire format, version 4
/// (`Env::VERSION`). Mirrors `Ixon.wireFormatId`.
pub const WIRE_FORMAT_ID: &str = "ixon-v4";

// Re-export main types
pub use comm::Comm;
pub use constant::{
  Axiom, Constant, ConstantInfo, Constructor, ConstructorProj, DefKind,
  Definition, DefinitionProj, Inductive, InductiveProj, MutConst, Quotient,
  Recursor, RecursorProj, RecursorRule,
};
#[cfg(not(target_arch = "riscv64"))]
pub use diff::{
  DiffPhase, EnvDiff, EnvStats, JoinProgress, LazySide, NamedChange,
  diff_env_bytes, diff_envs, diff_envs_lazy, diff_envs_with,
};
pub use env::{Env, Named};
pub use error::{CompileError, DecompileError, SerializeError};
pub use expr::Expr;
pub use lazy::LazyConstant;
pub use metadata::{
  ConstantMeta, DataValue, ExprMeta, ExprMetaData, KVMap, NameIndex,
  NameReverseIndex,
};
pub use proof::{
  Claim, Proof, RevealConstantInfo, RevealConstructorInfo, RevealMutConstInfo,
  RevealRecursorRule,
};
pub use tag::TagN;
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
  use ix_common::address::Address;

  // =========================================================================
  // TagN examples (docs section "TagN"): f = 4, 2, 0 flag bits
  // =========================================================================

  fn tagn(f: u32, flag: u8, value: u64) -> Vec<u8> {
    let mut buf = Vec::new();
    TagN::put(f, flag, value, &mut buf);
    buf
  }

  #[test]
  fn tagn4_small_value() {
    // f = 4, flag 0x1, value 5: rung 1 (value < 8), header 0b0001_0_101.
    assert_eq!(tagn(4, 0x1, 5), vec![0x15]);
  }

  #[test]
  fn tagn4_two_byte_value() {
    // f = 4, flag 0x2, value 256: rung 2 ([8, 1032)), 256 - 8 = 248 = 0x0F8:
    // header 0b0010_10_00 (L = 1, M = 0, high bits 0), then 0xF8.
    assert_eq!(tagn(4, 0x2, 256), vec![0x28, 0xF8]);
  }

  #[test]
  fn tagn2_small_value() {
    // f = 2, flag 0, value 15: rung 1 (value < 32), header 0b00_0_01111.
    assert_eq!(tagn(2, 0, 15), vec![0x0F]);
  }

  #[test]
  fn tagn2_two_byte_value() {
    // f = 2, flag 3, value 100: rung 2 ([32, 4128)), 100 - 32 = 68 = 0x44:
    // header 0b11_10_0000, then 0x44.
    assert_eq!(tagn(2, 3, 100), vec![0xE0, 0x44]);
  }

  #[test]
  fn tagn0_small_value() {
    // f = 0, value 42: rung 1 (value < 128), header 0b0_0101010.
    assert_eq!(tagn(0, 0, 42), vec![0x2A]);
  }

  #[test]
  fn tagn0_two_byte_value() {
    // f = 0, value 1000: rung 2 ([128, 16512)), 1000 - 128 = 872 = 0x368:
    // header 0b10_000011 (high bits 3), then 0x68.
    assert_eq!(tagn(0, 0, 1000), vec![0x83, 0x68]);
  }

  // =========================================================================
  // Universe examples (docs section "Universes")
  // =========================================================================

  #[test]
  fn univ_zero() {
    // Univ::Zero -> TagN(2, 0, 0) -> 0x00
    let mut buf = Vec::new();
    univ::put_univ(&Univ::zero(), &mut buf);
    assert_eq!(buf, vec![0x00], "Univ::Zero should be 0x00");
  }

  #[test]
  fn univ_succ_zero() {
    // Univ::Succ(Zero) uses telescope compression:
    // TagN(2, 0, 1) (succ_count=1) + base (Zero)
    // = 0b00_0_00001 = 0x01, then Zero = 0x00
    let mut buf = Vec::new();
    univ::put_univ(&Univ::succ(Univ::zero()), &mut buf);
    assert_eq!(
      buf,
      vec![0x01, 0x00],
      "Univ::Succ(Zero) should be [0x01, 0x00]"
    );
  }

  #[test]
  fn univ_var_1() {
    // Univ::Var(1) -> TagN(2, 3, 1)
    // = 0b11_0_00001 = 0xC1
    let mut buf = Vec::new();
    univ::put_univ(&Univ::var(1), &mut buf);
    assert_eq!(buf, vec![0xC1], "Univ::Var(1) should be 0xC1");
  }

  #[test]
  fn univ_max_zero_var1() {
    // Univ::Max(Zero, Var(1)) -> TagN(2, 1, 0) + Zero + Var(1)
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
    // Expr::Var(0) -> TagN(4, 0x1, 0) -> 0x10
    let mut buf = Vec::new();
    serialize::put_expr(&Expr::Var(0), &mut buf);
    assert_eq!(buf, vec![0x10], "Expr::Var(0) should be 0x10");
  }

  #[test]
  fn expr_sort_0() {
    // Expr::Sort(0) -> TagN(4, 0x0, 0) -> 0x00
    let mut buf = Vec::new();
    serialize::put_expr(&Expr::Sort(0), &mut buf);
    assert_eq!(buf, vec![0x00], "Expr::Sort(0) should be 0x00");
  }

  #[test]
  fn expr_ref_no_univs() {
    // Expr::Ref(0, []) -> TagN(4, 0x2, 0) + idx(0)
    // = 0x20 + 0x00
    let mut buf = Vec::new();
    serialize::put_expr(&Expr::Ref(0, vec![]), &mut buf);
    assert_eq!(
      buf,
      vec![0x20, 0x00],
      "Expr::Ref(0, []) should be [0x20, 0x00]"
    );
  }

  #[test]
  fn expr_share_5() {
    // Expr::Share(5) -> TagN(4, 0xB, 5) -> 0xB5
    let mut buf = Vec::new();
    serialize::put_expr(&Expr::Share(5), &mut buf);
    assert_eq!(buf, vec![0xB5], "Expr::Share(5) should be 0xB5");
  }

  #[test]
  fn expr_app_telescope() {
    // App(App(App(f, a), b), c) with f=Var(3), a=Var(2), b=Var(1), c=Var(0)
    // -> TagN(4, 0x7, 3) + f + a + b + c
    let expr = Expr::app(
      Expr::app(Expr::app(Expr::var(3), Expr::var(2)), Expr::var(1)),
      Expr::var(0),
    );
    let mut buf = Vec::new();
    serialize::put_expr(&expr, &mut buf);
    assert_eq!(
      buf,
      vec![0x73, 0x13, 0x12, 0x11, 0x10],
      "App telescope contains its ordinary arguments"
    );
  }

  #[test]
  fn expr_lam_telescope() {
    // Lam(t1, Lam(t2, Lam(t3, body))) with all types Sort(0) and body Var(0)
    // Each binder uses one byte: many (3), shared (bit 2), unrestricted.
    // Its domain follows; the body follows all three binders.
    let ty = Expr::sort(0);
    let expr = Expr::lam(
      ty.clone(),
      Expr::lam(ty.clone(), Expr::lam(ty.clone(), Expr::var(0))),
    );
    let mut buf = Vec::new();
    serialize::put_expr(&expr, &mut buf);
    assert_eq!(
      buf,
      vec![0x83, 0x07, 0x00, 0x07, 0x00, 0x07, 0x00, 0x10],
      "Lam telescope carries explicit input contracts"
    );
  }

  // =========================================================================
  // Claim/Proof examples (docs section "Proofs")
  // =========================================================================

  #[test]
  fn eval_claim_tag() {
    // Eval claim -> TagN(4, 0xE, 3) -> 0xE3 (single byte)
    let claim = Claim::Eval {
      input: Address::hash(b"input"),
      output: Address::hash(b"output"),
      assumptions: None,
    };
    let mut buf = Vec::new();
    claim.put(&mut buf);
    assert_eq!(buf[0], 0xE3, "Eval claim should start with 0xE3");
    // 1 (tag) + 64 (addresses) + 1 (opt=None) = 66
    assert_eq!(buf.len(), 1 + 2 + 64 + 1, "Eval claim no-asm = 68 bytes");
  }

  #[test]
  fn eval_proof_tag() {
    // Eval proof -> TagN(4, 0xF, 0) -> 0xF0 (single byte)
    let proof = Proof::new(
      Claim::Eval {
        input: Address::hash(b"input"),
        output: Address::hash(b"output"),
        assumptions: None,
      },
      vec![1, 2, 3, 4],
    );
    let mut buf = Vec::new();
    proof.put(&mut buf);
    assert_eq!(buf[0], 0xF0, "Eval proof should start with 0xF0");
    // 1 (tag) + 64 (addresses) + 1 (opt) + 1 (len=4) + 4 (proof) = 71
    assert_eq!(buf.len(), 73, "Eval proof no-asm + 4 proof bytes = 73 bytes");
    assert_eq!(buf[68], 0x04, "proof.len byte should be 0x04");
    assert_eq!(&buf[69..73], &[1, 2, 3, 4], "proof bytes should be [1,2,3,4]");
  }

  #[test]
  fn check_claim_tag() {
    // Check claim -> TagN(4, 0xE, 4) -> 0xE4
    let claim =
      Claim::Check { const_addr: Address::hash(b"value"), assumptions: None };
    let mut buf = Vec::new();
    claim.put(&mut buf);
    assert_eq!(buf[0], 0xE4, "Check claim should start with 0xE4");
    assert_eq!(buf.len(), 1 + 2 + 32 + 1, "Check claim no-asm = 36 bytes");
  }

  #[test]
  fn check_proof_tag() {
    // Check proof -> TagN(4, 0xF, 1) -> 0xF1
    let proof = Proof::new(
      Claim::Check { const_addr: Address::hash(b"value"), assumptions: None },
      vec![5, 6, 7],
    );
    let mut buf = Vec::new();
    proof.put(&mut buf);
    assert_eq!(buf[0], 0xF1, "Check proof should start with 0xF1");
  }

  // =========================================================================
  // Definition packed byte example (docs "Comprehensive Worked Example")
  // =========================================================================

  #[test]
  fn definition_packed_kind_safety() {
    // DefKind::Definition = 0, DefinitionSafety::Safe = 1
    // Packed: (0 << 2) | 1 = 0x01
    use constant::{DefKind, Definition};
    use ix_common::env::DefinitionSafety;

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
    use constant::{DefKind, Definition};
    use ix_common::env::DefinitionSafety;

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
    use constant::{DefKind, Definition};
    use ix_common::env::DefinitionSafety;

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
    // Constant with Defn -> TagN(4, 0xD, 0) -> 0xD0
    use constant::{Constant, ConstantInfo, DefKind, Definition};
    use ix_common::env::DefinitionSafety;

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
    // Muts with 3 entries -> TagN(4, 0xC, 3) -> 0xC3
    use constant::{Constant, ConstantInfo, DefKind, Definition, MutConst};
    use ix_common::env::DefinitionSafety;

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
    // Env -> TagN(4, 0xE, VERSION) -> 0xE4 for version 4
    let env = Env::new();
    let mut buf = Vec::new();
    env.put(&mut buf).unwrap();
    let header = (Env::FLAG << 4) | u8::try_from(Env::VERSION).unwrap();
    assert_eq!(
      buf[0], header,
      "Env should start with {header:#04X} (flag=E, value=format version)"
    );
  }
}
