use super::{
  expected_from_manifest,
  plan::build_statement_specs,
  plan::{FoldPolicy, PlanIdentity, ReplayPlan, build_specs, plan_replay},
  prepare::prepare_run,
  prepare::{
    EXTERNAL_OWNER, RootAssumptions, prepare_run_with_base,
    validate_root_statement,
  },
  protocol::cache_key,
  prove::{rebase_path_advice, structural_path_advice},
  rebase::{Base, plan_rebase},
  statement::{CanonicalTree, ShardSet, Statement, SubjectTree, merge_sorted},
};
use aiur::G;
use ix_common::address::Address;
use ix_kernel::shard::{AggNode, ShardInfo, ShardManifest};
use ixon::{Constant, ConstantInfo};
use multi_stark::p3_field::PrimeCharacteristicRing;
use std::sync::Arc;

use ixon::{Axiom, Expr};

mod plan;
mod prepare;
mod scheduler;
mod store;

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
    PlanIdentity {
      verify_idx: 3,
      aggr_idx: 5,
      aggr_vk: b"aggregate-vk",
      allowed: b"allowed",
      cache_fri_bytes: &[0; 40],
    },
    FoldPolicy { structural_above: 0, direct_joins: false },
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
    PlanIdentity {
      verify_idx: 3,
      aggr_idx: 5,
      aggr_vk: b"aggregate-vk",
      allowed: b"allowed",
      cache_fri_bytes: &[0; 40],
    },
    FoldPolicy { structural_above: 0, direct_joins: true },
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

/// A closed two-constant base, split over two shards, and an extension
/// environment holding both base constants plus `user`, which references the
/// right one, and `top`, which references `user` and the left one.
struct Extension {
  base_env: ixon::Env,
  base_manifest: ShardManifest,
  env: ixon::Env,
  left: Address,
  right: Address,
  user: Address,
  top: Address,
}

fn two_shards(left: Address, right: Address) -> ShardManifest {
  ShardManifest {
    num_shards: 2,
    shards: vec![shard(0, left), shard(1, right)],
    total_cross_ingress: 0,
    tree: Some(AggNode::Internal(
      Box::new(AggNode::Leaf(0)),
      Box::new(AggNode::Leaf(1)),
    )),
  }
}

fn extension() -> Extension {
  let base_env = ixon::Env::new();
  let left = store_axiom(&base_env, Expr::sort(0), Vec::new());
  let right = store_axiom(&base_env, Expr::sort(1), Vec::new());
  let base_manifest = two_shards(left.clone(), right.clone());
  let env = ixon::Env::new();
  store_axiom(&env, Expr::sort(0), Vec::new());
  store_axiom(&env, Expr::sort(1), Vec::new());
  let user =
    store_axiom(&env, Expr::reference(0, Vec::new()), vec![right.clone()]);
  let top = store_axiom(
    &env,
    Expr::app(Expr::reference(0, Vec::new()), Expr::reference(1, Vec::new())),
    vec![user.clone(), left.clone()],
  );
  Extension { base_env, base_manifest, env, left, right, user, top }
}

fn prepare_base(
  env: &ixon::Env,
  manifest: &ShardManifest,
  structural_above: usize,
) -> Result<
  (super::prepare::PreparedRun, Arc<Statement>, rustc_hash::FxHashSet<Address>),
  String,
> {
  let Base { prepared, root, constants } =
    Base::prepare(env, manifest, structural_above)?;
  Ok((prepared, root, constants))
}

fn sorted(mut addresses: Vec<Address>) -> Vec<Address> {
  addresses.sort_unstable();
  addresses
}

#[test]
fn extension_preparation_keeps_base_constants_external() {
  let ext = extension();
  let (_, _, base_constants) =
    prepare_base(&ext.base_env, &ext.base_manifest, 0).expect("base root");
  let manifest = two_shards(ext.user.clone(), ext.top.clone());
  let prepared =
    prepare_run_with_base(&ext.env, &manifest, Some(&base_constants))
      .expect("extension preparation");
  assert_eq!(prepared.env_count, 2);
  assert_eq!(prepared.owner_by_address[&ext.left], EXTERNAL_OWNER);
  assert_eq!(prepared.owner_by_address[&ext.right], EXTERNAL_OWNER);
  let assumptions = |shard: usize| {
    prepared.shards[shard]
      .statement
      .assumptions
      .as_ref()
      .expect("shard assumptions")
      .leaves
      .to_vec()
  };
  assert_eq!(assumptions(0), vec![ext.right.clone()]);
  assert_eq!(assumptions(1), sorted(vec![ext.user.clone(), ext.left.clone()]));

  // Flat and structural folds both discharge the cross-shard edge and keep
  // exactly the referenced base constants.
  for structural_above in [0, 8] {
    let root = build_statement_specs(&prepared, structural_above)
      .expect("extension specs")
      .last()
      .expect("extension root")
      .statement
      .clone();
    assert_eq!(
      root.assumptions.as_ref().expect("base assumptions").leaves.to_vec(),
      sorted(vec![ext.left.clone(), ext.right.clone()])
    );
    validate_root_statement(&prepared, &root, RootAssumptions::External)
      .expect("extension root");
    assert!(
      validate_root_statement(&prepared, &root, RootAssumptions::Closed)
        .unwrap_err()
        .contains("undischarged assumptions")
    );
  }

  // Without the base, the same environment is not fully owned.
  assert!(
    prepare_run_with_base(&ext.env, &manifest, None)
      .err()
      .unwrap()
      .contains("no owning manifest shard")
  );
}

#[test]
fn extension_preparation_rejects_a_base_constant_in_its_manifest() {
  let ext = extension();
  let (_, _, base_constants) =
    prepare_base(&ext.base_env, &ext.base_manifest, 0).expect("base root");
  let mut manifest = two_shards(ext.user.clone(), ext.top.clone());
  manifest.shards[1].blocks.push(ext.left.clone());
  assert!(
    prepare_run_with_base(&ext.env, &manifest, Some(&base_constants))
      .err()
      .unwrap()
      .contains("already a base constant")
  );
}

#[test]
fn extension_root_validation_rejects_non_base_assumptions_and_subjects() {
  let ext = extension();
  let (_, _, base_constants) =
    prepare_base(&ext.base_env, &ext.base_manifest, 0).expect("base root");
  let manifest = two_shards(ext.user.clone(), ext.top.clone());
  let prepared =
    prepare_run_with_base(&ext.env, &manifest, Some(&base_constants))
      .expect("extension preparation");
  let root = build_statement_specs(&prepared, 8)
    .unwrap()
    .last()
    .unwrap()
    .statement
    .clone();
  let local = Statement::new(
    root.subjects.clone(),
    CanonicalTree::from_sorted(vec![ext.user.clone()]).unwrap(),
  );
  assert!(
    validate_root_statement(&prepared, &local, RootAssumptions::External)
      .unwrap_err()
      .contains("not a base constant")
  );
  let base_subject = Statement::new(
    SubjectTree::canonical(
      sorted(vec![ext.left.clone(), ext.user.clone()]),
      root.subjects.shards.clone(),
    )
    .unwrap(),
    None,
  );
  assert!(
    validate_root_statement(
      &prepared,
      &base_subject,
      RootAssumptions::External
    )
    .unwrap_err()
    .contains("foreign subject")
  );
}

#[test]
fn rebase_paths_discharge_every_extension_assumption_into_the_base_root() {
  let ext = extension();
  let (base_prepared, base, base_constants) =
    prepare_base(&ext.base_env, &ext.base_manifest, 0).expect("base root");
  let manifest = two_shards(ext.user.clone(), ext.top.clone());
  let prepared =
    prepare_run_with_base(&ext.env, &manifest, Some(&base_constants))
      .expect("extension preparation");
  let child = build_statement_specs(&prepared, 0)
    .unwrap()
    .last()
    .unwrap()
    .statement
    .clone();

  let paths =
    rebase_path_advice(&child, &base.subjects, &base_prepared.owner_by_address)
      .expect("rebase paths");
  assert_eq!(
    paths.iter().map(|(leaf, _)| leaf.clone()).collect::<Vec<_>>(),
    sorted(vec![ext.left.clone(), ext.right.clone()])
  );
  for (leaf, payload) in &paths {
    assert_eq!(payload[0], 1);
    let path: Vec<(Address, bool)> = payload[2..]
      .chunks(33)
      .map(|step| {
        (Address::from_slice(&step[1..]).expect("sibling"), step[0] == 0)
      })
      .collect();
    assert_eq!(path.len(), usize::from(payload[1]));
    assert!(ixon::merkle::verify_merkle_proof(
      &base.subjects.root,
      leaf,
      &path
    ));
  }
  let rebased = Statement::rebased(child.subjects.clone(), &base.subjects.root);
  validate_root_statement(
    &prepared,
    &rebased,
    RootAssumptions::Base(&base.subjects.root),
  )
  .expect("rebased root");

  let foreign = Statement::new(
    child.subjects.clone(),
    CanonicalTree::from_sorted(vec![addr("foreign")]).unwrap(),
  );
  assert!(
    rebase_path_advice(
      &foreign,
      &base.subjects,
      &base_prepared.owner_by_address
    )
    .unwrap_err()
    .contains("not a base subject")
  );
}

#[test]
fn rebase_plan_states_the_rebased_root_and_rejects_closed_extensions() {
  let ext = extension();
  let base = Base::prepare(&ext.base_env, &ext.base_manifest, 0).unwrap();
  let manifest = two_shards(ext.user.clone(), ext.top.clone());
  let plan = plan_rebase(&ext.env, &manifest, 0, &base).expect("rebase plan");
  assert_eq!(plan.subject_count(), 2);
  assert_eq!(plan.output().assumptions_root(), Some(base.subjects_root()));

  // An extension that references no base constant has nothing to rebase.
  let env = ixon::Env::new();
  let lone = store_axiom(&env, Expr::sort(2), Vec::new());
  let lone_manifest = ShardManifest {
    num_shards: 1,
    shards: vec![shard(0, lone)],
    total_cross_ingress: 0,
    tree: Some(AggNode::Leaf(0)),
  };
  assert!(
    plan_rebase(&env, &lone_manifest, 0, &base)
      .err()
      .unwrap()
      .contains("needs no rebase")
  );
}
