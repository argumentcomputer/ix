use ix_kernel::shard::{AggNode, ShardManifest};
use ixon::Expr;

use super::super::{
  expected_from_manifest,
  prepare::{prepare_run, validate_root_statement},
  statement::{CanonicalTree, ShardSet, Statement, SubjectTree},
};
use super::{addr, shard, store_axiom};

fn singleton() -> (ixon::Env, ShardManifest) {
  let env = ixon::Env::new();
  let address = store_axiom(&env, Expr::sort(0), vec![]);
  let manifest = ShardManifest {
    num_shards: 1,
    shards: vec![shard(7, address)],
    total_cross_ingress: 0,
    tree: Some(AggNode::Leaf(7)),
  };
  (env, manifest)
}

#[test]
fn pruning_preserves_the_singleton_statement_and_original_shard_id() {
  let (env, mut manifest) = singleton();
  let (before, count) = expected_from_manifest(&env, &manifest, 0).unwrap();
  manifest.shards.insert(0, shard(3, addr("absent-block")));
  manifest.num_shards = 2;
  manifest.tree = Some(AggNode::Internal(
    Box::new(AggNode::Leaf(3)),
    Box::new(AggNode::Leaf(7)),
  ));
  let prepared = prepare_run(&env, &manifest).unwrap();
  assert_eq!(prepared.shards.len(), 1);
  assert_eq!(prepared.shards[0].original_id, 7);
  let (after, after_count) =
    expected_from_manifest(&env, &manifest, 0).unwrap();
  assert_eq!(count, 1);
  assert_eq!(count, after_count);
  assert_eq!(before.claim_bytes, after.claim_bytes);
}

#[test]
fn preparation_rejects_duplicate_ownership_ids_and_coverage_gaps() {
  let (env, mut manifest) = singleton();
  manifest.shards.push(shard(8, manifest.shards[0].blocks[0].clone()));
  manifest.num_shards = 2;
  assert!(
    prepare_run(&env, &manifest).err().unwrap().contains("owned by shards")
  );
  manifest.shards[1].blocks.clear();
  manifest.shards[1].id = 7;
  assert!(
    prepare_run(&env, &manifest).err().unwrap().contains("repeats shard id")
  );
  manifest.shards.pop();
  manifest.shards[0].blocks.clear();
  assert!(
    prepare_run(&env, &manifest)
      .err()
      .unwrap()
      .contains("no owning manifest shard")
  );
}

#[test]
fn root_validation_rejects_foreign_subjects_and_surviving_assumptions() {
  let (env, manifest) = singleton();
  let prepared = prepare_run(&env, &manifest).unwrap();
  let valid = &prepared.shards[0].statement;
  validate_root_statement(&prepared, valid).unwrap();
  let foreign = Statement::new(
    SubjectTree::canonical(vec![addr("foreign")], ShardSet::singleton(0, 1))
      .unwrap(),
    None,
  );
  assert!(
    validate_root_statement(&prepared, &foreign)
      .unwrap_err()
      .contains("foreign subject")
  );
  let residual = Statement::new(
    valid.subjects.clone(),
    CanonicalTree::from_sorted(vec![addr("assumption")]).unwrap(),
  );
  assert!(
    validate_root_statement(&prepared, &residual)
      .unwrap_err()
      .contains("undischarged assumptions")
  );
}
