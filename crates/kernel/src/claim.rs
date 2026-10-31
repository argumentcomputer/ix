//! High-level claim builders that combine kernel results with the
//! transitive-dep walker and the merkle root.
//!
//! `TypeChecker::check_const` stays pure (`Result<(), TcError>`); these
//! builders sit above it. They take an `Env` so they can compute the
//! `assumptions` merkle root over the constant's transitive deps.
//!
//! These env-derived builders intentionally use the *canonical* merkle builder
//! (sorted + deduped leaves). `Claim::CheckEnv` itself treats its root as an
//! opaque Merkle commitment and already accepts free-form roots produced by
//! recursive `merkle_join`; there is no canonical-root validator on claims.

use ix_common::address::Address;
use ixon::env::Env;
use ixon::merkle::merkle_root_canonical;
use ixon::proof::{Claim, ClaimContext};

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
pub fn build_check_claim(
  ctx: &ClaimContext,
  env: &Env,
  const_addr: Address,
) -> Claim {
  let deps = env.transitive_deps_excl(&const_addr);
  let assumptions = merkle_root_canonical(&deps);
  Claim::Check { ctx: ctx.clone(), const_addr, assumptions }
}

/// Build an eval claim for the pair `(input, output)` in `env`.
///
/// Only the input's dependency closure needs typing assumptions. The output
/// definition's type and body are established by the evaluation claim.
pub fn build_eval_claim(
  ctx: &ClaimContext,
  env: &Env,
  input: Address,
  output: Address,
) -> Claim {
  let deps = env.transitive_deps_excl(&input);
  let assumptions = merkle_root_canonical(&deps);
  Claim::Eval { ctx: ctx.clone(), input, output, assumptions }
}

/// Build a shard `CheckEnv` claim under the SHARD PROTOCOL convention:
/// root over the owned set, assumptions over the THIN frontier (direct
/// out-of-owned walk edges). Delegates to [`ixon::shard_claim`] — the
/// single source of truth shared with the Aiur witness builders, so
/// digests reproduce across the Rust and Aiur pipelines. The
/// claim-exact check set (asm-cutoff walk + strict owned-membership)
/// is [`ixon::shard_claim::walk_check_set`]; a native checker
/// validating such a claim must check exactly that set — checking the
/// whole env eagerly is a sound superset for DEV use but does not
/// certify the claim (it misses the strict-membership coverage rule).
pub fn build_shard_check_env_claim(
  ctx: &ClaimContext,
  env: &Env,
  owned: &[Address],
) -> Option<(Claim, Vec<Address>)> {
  ixon::shard_claim::shard_check_env_claim(ctx, env, owned)
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
  use super::*;
  use ix_common::env::DefinitionSafety;
  use ixon::constant::{Axiom, Constant, ConstantInfo, DefKind, Definition};
  use ixon::expr::Expr;
  use ixon::merkle::leaf_hash;
  use std::sync::Arc;

  fn ctx() -> ClaimContext {
    ClaimContext {
      spec: ixon::proof::spec_digest(),
      binding: Address::hash(b"binding"),
      axioms: None,
      binding_assumed: false,
      literal_class: false,
    }
  }

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

  /// A definition whose value NAMES every one of its `refs` entries via a
  /// `Ref` node. The claim walk admits an index only when some Expr uses
  /// it as a constant, so a fixture whose Exprs ignore `refs` produces no
  /// edges and every frontier comes back empty.
  fn defn_const(refs: Vec<Address>) -> Constant {
    let mut value = Expr::var(0);
    for i in 0..refs.len() {
      value = Expr::app(value, Expr::reference(i as u64, Vec::new()));
    }
    Constant::with_tables(
      ConstantInfo::Defn(Definition {
        kind: DefKind::Definition,
        safety: DefinitionSafety::Safe,
        lvls: 0,
        typ: Expr::sort(0),
        value,
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
    match build_check_claim(&ctx(), &env, a.clone()) {
      Claim::Check { const_addr, assumptions: None, .. } => {
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
    match build_check_claim(&ctx(), &env, a.clone()) {
      Claim::Check { const_addr, assumptions: Some(asm), .. } => {
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
    match build_check_claim(&ctx(), &env, a.clone()) {
      Claim::Check { const_addr, assumptions: Some(asm), .. } => {
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
    match build_eval_claim(&ctx(), &env, i.clone(), o.clone()) {
      Claim::Eval { input, output, assumptions: None, .. } => {
        assert_eq!(input, i);
        assert_eq!(output, o);
      },
      other => panic!("expected Eval None, got {other:?}"),
    }
  }

  #[test]
  fn eval_assumptions_come_only_from_input() {
    // Output-only dependencies are not input typing assumptions.
    let env = Env::new();
    let i = Address::hash(b"i");
    let o = Address::hash(b"o");
    let d = Address::hash(b"d");
    env.store_const(i.clone(), defn_const(vec![d.clone()]));
    env.store_const(o.clone(), defn_const(vec![Address::hash(b"output-only")]));
    env.store_const(d.clone(), defn_const(vec![]));
    match build_eval_claim(&ctx(), &env, i.clone(), o.clone()) {
      Claim::Eval { input, output, assumptions: Some(asm), .. } => {
        assert_eq!(input, i);
        assert_eq!(output, o);
        assert_eq!(asm, leaf_hash(&d));
      },
      other => panic!("expected Eval Some, got {other:?}"),
    }
  }

  #[test]
  fn eval_keeps_output_when_it_is_an_input_dependency() {
    let env = Env::new();
    let input = Address::hash(b"input");
    let output = Address::hash(b"output");
    env.store_const(input.clone(), defn_const(vec![output.clone()]));
    env.store_const(output.clone(), defn_const(vec![]));
    assert_eq!(
      build_eval_claim(&ctx(), &env, input.clone(), output.clone()),
      Claim::Eval {
        ctx: ctx(),
        input,
        assumptions: Some(leaf_hash(&output)),
        output
      }
    );
  }

  #[test]
  fn shard_check_env_claim_is_thin_frontier() {
    // a -> b -> c: owned {a} gives frontier {b} only — c is below the
    // first layer and must NOT enter the asm set.
    let env = Env::new();
    let a = Address::hash(b"a");
    let b = Address::hash(b"b");
    let c = Address::hash(b"c");
    env.store_const(a.clone(), defn_const(vec![b.clone()]));
    env.store_const(b.clone(), defn_const(vec![c.clone()]));
    env.store_const(c.clone(), defn_const(vec![]));
    let (claim, frontier) =
      build_shard_check_env_claim(&ctx(), &env, std::slice::from_ref(&a))
        .unwrap();
    assert_eq!(frontier, vec![b.clone()]);
    match claim {
      Claim::CheckEnv { root, assumptions: Some(asm), .. } => {
        assert_eq!(root, leaf_hash(&a));
        assert_eq!(asm, leaf_hash(&b));
      },
      other => panic!("expected CheckEnv Some, got {other:?}"),
    }
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
    let c1 = build_check_claim(&ctx(), &env, a.clone());
    let c2 = build_check_claim(&ctx(), &env, a);
    assert_eq!(c1, c2);
  }
}
