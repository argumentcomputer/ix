//! Shard `CheckEnv` claim convention — the single source of truth shared
//! by every builder (Lean `IxVM.ClaimHarness.shardCheckEnvClaim`,
//! `ixvm-codegen::aiur_ixvm_witness::build_shard_check_env_witness`,
//! `ix-kernel::claim`). Any change here changes claim digests; keep the
//! Lean mirror in lockstep.
//!
//! Semantics (mirrors the Aiur kernel's `env_walk`):
//!
//! - **Walk edge relation**: a constant's `refs`, plus — for a
//!   projection wrapper (IPrj/CPrj/RPrj/DPrj) — its `block` pointer.
//!   NOT `Env::closure_edges`: that also derives Muts member-projection
//!   addresses, which the claim walk does not traverse (a Muts block's
//!   members are checked in place; recursion leaves the block only
//!   through its `refs`).
//! - **Walk**: start from every owned constant; skip addrs absent from
//!   `env.consts` (blob payloads); stop at any asm member (assumed
//!   well-typed by its owning shard — not checked, not recursed).
//! - **Strict membership**: a walk-reachable constant in neither
//!   `owned` nor `asm` means the owned tree does not cover its own
//!   closure (bad frontier) — hard error, never silently absorbed.
//! - **Thin frontier**: the asm set is the DIRECT out-of-owned walk
//!   edges of the owned constants. The walk can only exit the shard
//!   through one of these, so anything below the first layer is dead
//!   weight in the asm tree. Sub-frontier constants are covered
//!   transitively by the frontier members' own shard claims.
//! - **Byte scope ≠ check scope**: delta unfolding in the kernel reads
//!   through the frontier (a frontier Defn's body may reference
//!   sub-frontier constants at any depth), so a WITNESS must ship the
//!   full dependency closure of `owned` — see `Env::bfs_closure` — even
//!   though only the strict-membership set gets checked.

use rustc_hash::FxHashSet;

use crate::constant::{Constant, ConstantInfo};
use crate::env::Env;
use crate::merkle::merkle_root_canonical;
use crate::proof::Claim;
use ix_common::address::Address;

/// The claim walk's edge relation: `refs` + projection `block`.
pub fn walk_edges(c: &Constant, edges: &mut Vec<Address>) {
  edges.extend(c.refs.iter().cloned());
  match &c.info {
    ConstantInfo::IPrj(p) => edges.push(p.block.clone()),
    ConstantInfo::CPrj(p) => edges.push(p.block.clone()),
    ConstantInfo::RPrj(p) => edges.push(p.block.clone()),
    ConstantInfo::DPrj(p) => edges.push(p.block.clone()),
    _ => {},
  }
}

/// The THIN frontier: direct out-of-owned walk edges of the owned
/// constants, restricted to addrs present in `env.consts` (the walk's
/// blob sentinel fires before its membership test, so blob addrs never
/// consult the asm set). Sorted for canonical tree construction.
pub fn thin_frontier(env: &Env, owned: &[Address]) -> Vec<Address> {
  let owned_set: FxHashSet<&Address> = owned.iter().collect();
  let mut frontier: FxHashSet<Address> = FxHashSet::default();
  for o in owned {
    let Some(c) = env.get_const(o) else {
      continue;
    };
    let mut edges = Vec::new();
    walk_edges(&c, &mut edges);
    for e in edges {
      if !owned_set.contains(&e) && env.consts.get(&e).is_some() {
        frontier.insert(e);
      }
    }
  }
  let mut v: Vec<Address> = frontier.into_iter().collect();
  v.sort_unstable();
  v
}

/// Build the shard `CheckEnv` claim: root over the (sorted) owned set,
/// assumptions over the thin frontier. Returns the claim plus the
/// frontier leaves (the caller ships the asm tree it commits to).
/// `None` on an empty owned set.
pub fn shard_check_env_claim(
  env: &Env,
  owned: &[Address],
) -> Option<(Claim, Vec<Address>)> {
  let mut owned_sorted: Vec<Address> = owned.to_vec();
  owned_sorted.sort_unstable();
  let root = merkle_root_canonical(&owned_sorted)?;
  let frontier = thin_frontier(env, owned);
  let assumptions = merkle_root_canonical(&frontier);
  Some((Claim::CheckEnv { root, assumptions }, frontier))
}

/// Error from `walk_check_set`: a walk-reachable constant in neither
/// `owned` nor `asm` — the claim's owned tree does not cover its own
/// closure up to the given frontier.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StrictMembershipError {
  pub addr: Address,
}

/// The claim-exact CHECK set: exactly the constants a `CheckEnv { root
/// over owned, assumptions over asm }` claim requires well-typed in
/// THIS shard. Walk from every owned constant over `walk_edges`,
/// skipping blob addrs, stopping at asm members; every visited
/// constant must be owned (strict membership) or the walk errors.
///
/// Checker-agnostic: the Aiur kernel interleaves this walk with
/// checking (`env_walk`); a native checker can compute the set
/// first and then check each member. Both must agree on the SET — that
/// is the claim semantics.
pub fn walk_check_set(
  env: &Env,
  owned: &[Address],
  asm: &[Address],
) -> Result<Vec<Address>, StrictMembershipError> {
  let owned_set: FxHashSet<&Address> = owned.iter().collect();
  let asm_set: FxHashSet<&Address> = asm.iter().collect();
  let mut visited: FxHashSet<Address> = FxHashSet::default();
  let mut out: Vec<Address> = Vec::new();
  let mut stack: Vec<Address> = owned.to_vec();
  while let Some(addr) = stack.pop() {
    if visited.contains(&addr) {
      continue;
    }
    // Blob sentinel first: absent-from-consts addrs are payloads, not
    // constants — never checked, never consulted for membership.
    let Some(c) = env.get_const(&addr) else {
      visited.insert(addr);
      continue;
    };
    // Asm cutoff: assumed well-typed elsewhere; no check, no recursion.
    if asm_set.contains(&addr) {
      visited.insert(addr);
      continue;
    }
    if !owned_set.contains(&addr) {
      return Err(StrictMembershipError { addr });
    }
    visited.insert(addr.clone());
    out.push(addr);
    let mut edges = Vec::new();
    walk_edges(&c, &mut edges);
    for e in edges {
      if !visited.contains(&e) {
        stack.push(e);
      }
    }
  }
  out.sort_unstable();
  Ok(out)
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
  use super::*;
  use crate::constant::{Axiom, Constant, ConstantInfo};
  use crate::expr::Expr;
  use std::sync::Arc;

  fn const_with_refs(refs: Vec<Address>) -> Constant {
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

  /// a -> b -> c, d isolated.
  fn chain_env() -> (Env, Address, Address, Address, Address) {
    let env = Env::new();
    let a = Address::hash(b"a");
    let b = Address::hash(b"b");
    let c = Address::hash(b"c");
    let d = Address::hash(b"d");
    env.store_const(a.clone(), const_with_refs(vec![b.clone()]));
    env.store_const(b.clone(), const_with_refs(vec![c.clone()]));
    env.store_const(c.clone(), const_with_refs(vec![]));
    env.store_const(d.clone(), const_with_refs(vec![]));
    (env, a, b, c, d)
  }

  #[test]
  fn thin_frontier_is_first_layer_only() {
    let (env, a, b, c, _) = chain_env();
    // owned = {a}: frontier is {b}, NOT {b, c}.
    let f = thin_frontier(&env, &[a]);
    assert_eq!(f, vec![b]);
    assert!(!f.contains(&c));
  }

  #[test]
  fn thin_frontier_excludes_owned_and_absent() {
    let (env, a, b, _, _) = chain_env();
    let blob = Address::hash(b"blob-not-in-env");
    env.store_const(a.clone(), const_with_refs(vec![b.clone(), blob.clone()]));
    let f = thin_frontier(&env, &[a.clone(), b.clone()]);
    // b is owned; blob is absent; a's only external const edge is c via b.
    assert!(!f.contains(&a));
    assert!(!f.contains(&b));
    assert!(!f.contains(&blob));
  }

  #[test]
  fn walk_check_set_stops_at_frontier() {
    let (env, a, b, c, _) = chain_env();
    // owned = {a}, asm = {b}: check exactly {a}; c never visited.
    let set = walk_check_set(&env, std::slice::from_ref(&a), &[b]).unwrap();
    assert_eq!(set, vec![a]);
    assert!(!set.contains(&c));
  }

  #[test]
  fn walk_check_set_strict_membership_errors() {
    let (env, a, b, _, _) = chain_env();
    // owned = {a}, asm = {} — b is reachable but in neither set.
    let err = walk_check_set(&env, &[a], &[]).unwrap_err();
    assert_eq!(err.addr, b);
  }

  #[test]
  fn walk_check_set_self_contained_checks_all() {
    let (env, a, b, c, _) = chain_env();
    let set =
      walk_check_set(&env, &[a.clone(), b.clone(), c.clone()], &[]).unwrap();
    let mut expected = vec![a, b, c];
    expected.sort_unstable();
    assert_eq!(set, expected);
  }

  #[test]
  fn claim_deterministic_and_thin() {
    let (env, a, b, _, _) = chain_env();
    let (claim1, f1) =
      shard_check_env_claim(&env, std::slice::from_ref(&a)).unwrap();
    let (claim2, f2) = shard_check_env_claim(&env, &[a]).unwrap();
    assert_eq!(claim1, claim2);
    assert_eq!(f1, f2);
    assert_eq!(f1, vec![b]);
  }

  #[test]
  fn byte_scope_goes_below_frontier() {
    let (env, a, _, c, _) = chain_env();
    // Byte scope includes c even though the check walk (asm = {b})
    // never visits it.
    let cl = env.bfs_closure(&[a]);
    assert!(cl.contains(&c));
  }
}
