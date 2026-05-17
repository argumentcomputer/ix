//! High-level claim builders that combine kernel results with the
//! transitive-dep walker and the merkle root.
//!
//! `TypeChecker::check_const` stays pure (`Result<(), TcError>`); these
//! builders sit above it. They take an `Env` so they can compute the
//! `assumptions` merkle root over the constant's transitive deps.
//!
//! All builders default to the *canonical* merkle builder (sorted +
//! deduped leaves) — when recursive aggregation lands, free-form roots
//! from `merkle_join` will also be acceptable, but builders that start
//! from an env always produce canonical roots.

use rustc_hash::FxHashSet;

use crate::ix::address::Address;
use crate::ix::ixon::constant::ConstantInfo;
use crate::ix::ixon::env::Env;
use crate::ix::ixon::merkle::merkle_root_canonical;
use crate::ix::ixon::proof::Claim;

/// Canonical merkle root over the env's `consts.keys()`. Also called
/// from the env serializer. Returns `None` for an empty const set.
pub fn env_merkle_root(env: &Env) -> Option<Address> {
  let mut addrs: Vec<Address> =
    env.consts.iter().map(|e| e.key().clone()).collect();
  addrs.sort_unstable();
  merkle_root_canonical(&addrs)
}

/// Build a check claim for the constant at `const_addr` in `env`.
///
/// Sets `assumptions: None` when the constant has no transitive deps,
/// else `Some(root)` where `root` is the canonical merkle root over
/// those deps.
pub fn build_check_claim(env: &Env, const_addr: Address) -> Claim {
  let deps = env.transitive_deps_excl(&const_addr);
  let assumptions = merkle_root_canonical(&deps);
  Claim::Check { const_addr, assumptions }
}

/// Build an eval claim for the pair `(input, output)` in `env`.
///
/// Assumptions = canonical merkle root over `transitive_deps(input) ∪
/// transitive_deps(output) \ {input, output}`. `None` if that set is
/// empty.
pub fn build_eval_claim(
  env: &Env,
  input: Address,
  output: Address,
) -> Claim {
  let mut set: FxHashSet<Address> =
    env.transitive_deps_excl(&input).into_iter().collect();
  set.extend(env.transitive_deps_excl(&output));
  set.remove(&input);
  set.remove(&output);
  let mut deps: Vec<Address> = set.into_iter().collect();
  deps.sort_unstable();
  let assumptions = merkle_root_canonical(&deps);
  Claim::Eval { input, output, assumptions }
}

/// Build a whole-env check claim. Subject is the env's canonical merkle
/// root; assumptions are the env's axiom leaves.
///
/// Returns `None` if the env has an empty const set (no subject root
/// can be formed).
pub fn build_check_env_claim(env: &Env) -> Option<Claim> {
  let root = env_merkle_root(env)?;
  let mut axioms: Vec<Address> = env
    .consts
    .iter()
    .filter_map(|e| match &e.value().info {
      ConstantInfo::Axio(_) => Some(e.key().clone()),
      _ => None,
    })
    .collect();
  axioms.sort_unstable();
  let assumptions = merkle_root_canonical(&axioms);
  Some(Claim::CheckEnv { root, assumptions })
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
  use super::*;
  use crate::ix::env::DefinitionSafety;
  use crate::ix::ixon::constant::{
    Axiom, Constant, DefKind, Definition, ConstantInfo,
  };
  use crate::ix::ixon::expr::Expr;
  use crate::ix::ixon::merkle::leaf_hash;
  use std::sync::Arc;

  fn axiom_const(refs: Vec<Address>) -> Constant {
    Constant::with_tables(
      ConstantInfo::Axio(Axiom {
        is_unsafe: false,
        lvls: 0,
        typ: Arc::new(Expr::Sort(0)),
      }),
      Vec::new(),
      refs,
      Vec::new(),
    )
  }

  fn defn_const(refs: Vec<Address>) -> Constant {
    Constant::with_tables(
      ConstantInfo::Defn(Definition {
        kind: DefKind::Definition,
        safety: DefinitionSafety::Safe,
        lvls: 0,
        typ: Expr::sort(0),
        value: Expr::var(0),
      }),
      Vec::new(),
      refs,
      Vec::new(),
    )
  }

  #[test]
  fn check_no_deps_assumptions_none() {
    let env = Env::new();
    let a = Address::hash(b"a");
    env.store_const(a.clone(), defn_const(vec![]));
    match build_check_claim(&env, a.clone()) {
      Claim::Check { const_addr, assumptions: None } => {
        assert_eq!(const_addr, a);
      },
      other => panic!("expected Check {{ assumptions: None }}, got {other:?}"),
    }
  }

  #[test]
  fn check_with_one_axiom_dep_assumptions_some() {
    let env = Env::new();
    let a = Address::hash(b"a");
    let ax = Address::hash(b"ax");
    env.store_const(a.clone(), defn_const(vec![ax.clone()]));
    env.store_const(ax.clone(), axiom_const(vec![]));
    match build_check_claim(&env, a.clone()) {
      Claim::Check { const_addr, assumptions: Some(asm) } => {
        assert_eq!(const_addr, a);
        assert_eq!(asm, leaf_hash(&ax));
      },
      other => panic!("expected Check Some, got {other:?}"),
    }
  }

  #[test]
  fn check_excludes_subject_from_assumptions() {
    // a -> b -> a (cycle). Subject `a` must not be in its own assumption set.
    let env = Env::new();
    let a = Address::hash(b"a");
    let b = Address::hash(b"b");
    env.store_const(a.clone(), defn_const(vec![b.clone()]));
    env.store_const(b.clone(), defn_const(vec![a.clone()]));
    match build_check_claim(&env, a.clone()) {
      Claim::Check { const_addr, assumptions: Some(asm) } => {
        assert_eq!(const_addr, a);
        assert_eq!(asm, leaf_hash(&b));
      },
      other => panic!("expected Check Some, got {other:?}"),
    }
  }

  #[test]
  fn eval_no_deps_assumptions_none() {
    let env = Env::new();
    let i = Address::hash(b"i");
    let o = Address::hash(b"o");
    env.store_const(i.clone(), defn_const(vec![]));
    env.store_const(o.clone(), defn_const(vec![]));
    match build_eval_claim(&env, i.clone(), o.clone()) {
      Claim::Eval { input, output, assumptions: None } => {
        assert_eq!(input, i);
        assert_eq!(output, o);
      },
      other => panic!("expected Eval None, got {other:?}"),
    }
  }

  #[test]
  fn eval_excludes_both_endpoints_from_assumptions() {
    // i -> d, o -> d. The set is {d}, not containing i or o.
    let env = Env::new();
    let i = Address::hash(b"i");
    let o = Address::hash(b"o");
    let d = Address::hash(b"d");
    env.store_const(i.clone(), defn_const(vec![d.clone()]));
    env.store_const(o.clone(), defn_const(vec![d.clone()]));
    env.store_const(d.clone(), defn_const(vec![]));
    match build_eval_claim(&env, i.clone(), o.clone()) {
      Claim::Eval { input, output, assumptions: Some(asm) } => {
        assert_eq!(input, i);
        assert_eq!(output, o);
        assert_eq!(asm, leaf_hash(&d));
      },
      other => panic!("expected Eval Some, got {other:?}"),
    }
  }

  #[test]
  fn check_env_axiom_free_assumptions_none() {
    let env = Env::new();
    let a = Address::hash(b"a");
    env.store_const(a.clone(), defn_const(vec![]));
    match build_check_env_claim(&env).unwrap() {
      Claim::CheckEnv { root, assumptions: None } => {
        assert_eq!(Some(root), env_merkle_root(&env));
      },
      other => panic!("expected CheckEnv None, got {other:?}"),
    }
  }

  #[test]
  fn check_env_with_axioms_assumptions_some() {
    let env = Env::new();
    let a = Address::hash(b"a");
    let ax = Address::hash(b"ax");
    env.store_const(a.clone(), defn_const(vec![ax.clone()]));
    env.store_const(ax.clone(), axiom_const(vec![]));
    match build_check_env_claim(&env).unwrap() {
      Claim::CheckEnv { root, assumptions: Some(asm) } => {
        assert_eq!(Some(root), env_merkle_root(&env));
        assert_eq!(asm, leaf_hash(&ax));
      },
      other => panic!("expected CheckEnv Some, got {other:?}"),
    }
  }

  #[test]
  fn check_env_empty_returns_none() {
    let env = Env::new();
    assert!(build_check_env_claim(&env).is_none());
  }

  #[test]
  fn env_merkle_root_invariant_under_insertion_order() {
    let env1 = Env::new();
    let env2 = Env::new();
    let a = Address::hash(b"a");
    let b = Address::hash(b"b");
    let c = Address::hash(b"c");
    env1.store_const(a.clone(), defn_const(vec![]));
    env1.store_const(b.clone(), defn_const(vec![]));
    env1.store_const(c.clone(), defn_const(vec![]));
    // Insert in reverse order.
    env2.store_const(c, defn_const(vec![]));
    env2.store_const(b, defn_const(vec![]));
    env2.store_const(a, defn_const(vec![]));
    assert_eq!(env_merkle_root(&env1), env_merkle_root(&env2));
  }

  #[test]
  fn env_merkle_root_changes_with_extra_const() {
    let env = Env::new();
    let a = Address::hash(b"a");
    env.store_const(a.clone(), defn_const(vec![]));
    let root1 = env_merkle_root(&env).unwrap();
    let b = Address::hash(b"b");
    env.store_const(b, defn_const(vec![]));
    let root2 = env_merkle_root(&env).unwrap();
    assert_ne!(root1, root2);
  }

  #[test]
  fn build_claims_are_deterministic() {
    let env = Env::new();
    let a = Address::hash(b"a");
    let b = Address::hash(b"b");
    env.store_const(a.clone(), defn_const(vec![b.clone()]));
    env.store_const(b, defn_const(vec![]));
    let c1 = build_check_claim(&env, a.clone());
    let c2 = build_check_claim(&env, a);
    assert_eq!(c1, c2);
  }
}
