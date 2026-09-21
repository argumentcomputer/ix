use super::{
  expected_from_manifest,
  plan::{ReplayPlan, build_specs, plan_replay},
  prepare::prepare_run,
  protocol::cache_key,
  prove::structural_path_advice,
  statement::{CanonicalTree, ShardSet, SubjectTree, merge_sorted},
};
use aiur::G;
use ix_common::address::Address;
use ix_kernel::shard::{AggNode, ShardInfo, ShardManifest};
use ixon::{Constant, ConstantInfo};
use multi_stark::p3_field::PrimeCharacteristicRing;
use std::sync::Arc;

use ixon::{Axiom, Expr};

fn addr(label: &str) -> Address {
  Address::hash(label.as_bytes())
}

#[test]
fn sorted_merge_is_a_set_union() {
  let a = addr("a");
  let b = addr("b");
  let c = addr("c");
  let mut left = vec![a.clone(), c.clone()];
  let mut right = vec![b.clone(), c.clone()];
  left.sort_unstable();
  right.sort_unstable();
  let merged = merge_sorted(&left, &right);
  assert_eq!(merged.len(), 3);
  assert!(merged.windows(2).all(|window| window[0] < window[1]));
}

#[test]
fn cached_canonical_path_matches_root() {
  let mut leaves: Vec<Address> =
    (0..17).map(|index| addr(&format!("leaf-{index}"))).collect();
  leaves.sort_unstable();
  let tree = CanonicalTree::from_sorted(leaves.clone()).unwrap().unwrap();
  for leaf in leaves {
    let path = tree.merkle_proof(&leaf).expect("member path");
    assert!(ixon::merkle::verify_merkle_proof(&tree.root, &leaf, &path));
  }
}

#[test]
fn structural_path_uses_cached_child_roots() {
  let mut left_leaves = vec![addr("a"), addr("b")];
  let mut right_leaves = vec![addr("c"), addr("d")];
  left_leaves.sort_unstable();
  right_leaves.sort_unstable();
  let left =
    SubjectTree::canonical(left_leaves.clone(), ShardSet::singleton(0, 2))
      .unwrap();
  let right =
    SubjectTree::canonical(right_leaves.clone(), ShardSet::singleton(1, 2))
      .unwrap();
  let joined = SubjectTree::structural(left, right);
  for leaf in left_leaves.iter().chain(&right_leaves) {
    let owner = usize::from(right_leaves.contains(leaf));
    let path = joined.merkle_proof(leaf, owner).expect("member path");
    assert!(ixon::merkle::verify_merkle_proof(&joined.root, leaf, &path));
  }
}

#[test]
fn cache_key_has_a_stable_test_vector() {
  let claim = vec![G::from_u64(1), G::from_u64(2), G::from_u64(3)];
  let key = cache_key(b"vk", &[7; 40], &claim);
  assert_eq!(
    key.hex(),
    "86ed059157e2915fe0a83f1afd58f31f7553659ad778669f6b795e1473e7afe0"
  );
}

fn store_axiom(env: &ixon::Env, typ: Arc<Expr>, refs: Vec<Address>) -> Address {
  let constant = Constant {
    info: ConstantInfo::Axio(Axiom { is_unsafe: false, lvls: 0, typ }),
    sharing: Vec::new(),
    refs,
    univs: Vec::new(),
  };
  let mut bytes = Vec::new();
  constant.put(&mut bytes);
  let address = Address::hash(&bytes);
  env.store_const(address.clone(), constant);
  address
}

fn shard(id: u32, block: Address) -> ShardInfo {
  ShardInfo {
    id,
    blocks: vec![block],
    heartbeats: 0,
    own_size: 0,
    foreign_blocks: Vec::new(),
    cross_ingress: 0,
    assumption_root: None,
    measured_peak_bytes: 0,
  }
}

#[test]
fn native_preparation_and_structural_fold_discharge_a_frontier() {
  let env = ixon::Env::new();
  let dependency = store_axiom(&env, Expr::sort(0), Vec::new());
  let consumer =
    store_axiom(&env, Expr::reference(0, Vec::new()), vec![dependency.clone()]);
  let reference_frontier =
    ixon::shard_claim::thin_frontier(&env, std::slice::from_ref(&consumer));
  let manifest = ShardManifest {
    num_shards: 2,
    shards: vec![shard(0, consumer.clone()), shard(1, dependency.clone())],
    total_cross_ingress: 0,
    tree: Some(AggNode::Internal(
      Box::new(AggNode::Leaf(0)),
      Box::new(AggNode::Leaf(1)),
    )),
  };
  let prepared = prepare_run(&env, &manifest).expect("native preparation");
  assert_eq!(
    prepared.shards[0]
      .statement
      .assumptions
      .as_ref()
      .expect("cross-shard frontier")
      .leaves
      .as_ref(),
    reference_frontier
  );
  let specs = build_specs(
    &prepared,
    3,
    5,
    0,
    false,
    b"aggregate-vk",
    b"allowed",
    &[0; 40],
  )
  .expect("native specs");
  assert_eq!(specs.len(), 3);
  assert!(specs[2].structural);
  assert_eq!(specs[2].subject_count, 2);
  assert!(specs[2].statement.assumptions.is_none());
  let (expected, constant_count) =
    expected_from_manifest(&env, &manifest, 0).expect("native expected root");
  assert_eq!(constant_count, 2);
  assert_eq!(expected.claim, specs[2].statement.claim);
  let (flat_expected, flat_count) =
    expected_from_manifest(&env, &manifest, 8).expect("flat expected root");
  assert_eq!(flat_count, 2);
  assert_ne!(flat_expected.claim, expected.claim);
  assert_eq!(
    plan_replay(&specs, 0).unwrap(),
    ReplayPlan { children: Vec::new(), needs_input_proofs: true }
  );
  assert_eq!(
    plan_replay(&specs, 2).unwrap(),
    ReplayPlan { children: vec![0, 1], needs_input_proofs: false }
  );
  assert!(plan_replay(&specs, 3).unwrap_err().contains("out of range"));

  let direct_specs = build_specs(
    &prepared,
    3,
    5,
    0,
    true,
    b"aggregate-vk",
    b"allowed",
    &[0; 40],
  )
  .expect("direct native specs");
  assert!(plan_replay(&direct_specs, 0).unwrap_err().contains("raw IxVM leaf"));
  assert!(plan_replay(&direct_specs, 2).unwrap().needs_input_proofs);
  let paths = structural_path_advice(
    &specs[0].statement,
    &specs[1].statement,
    &specs[2].statement,
    &prepared.owner_by_address,
  )
  .expect("structural paths");
  assert_eq!(paths.len(), 1);
  assert_eq!(paths[0].0, dependency);
  assert_eq!(paths[0].1.first(), Some(&1));
}
