use ixon::Expr;
use ixon::shard::{AggNode, ShardManifest};

use super::{addr, ctx, shard, store_axiom};
use crate::{
  expected_from_manifest,
  prepare::{prepare_run, validate_root_statement},
  statement::{CanonicalTree, ShardSet, Statement, SubjectTree},
};

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
  let (before, count) =
    expected_from_manifest(&ctx(), &env, &manifest, 0).unwrap();
  manifest.shards.insert(0, shard(3, addr("absent-block")));
  manifest.num_shards = 2;
  manifest.tree = Some(AggNode::Internal(
    Box::new(AggNode::Leaf(3)),
    Box::new(AggNode::Leaf(7)),
  ));
  let prepared = prepare_run(&ctx(), &env, &manifest).unwrap();
  assert_eq!(prepared.shards.len(), 1);
  assert_eq!(prepared.shards[0].original_id, 7);
  let (after, after_count) =
    expected_from_manifest(&ctx(), &env, &manifest, 0).unwrap();
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
    prepare_run(&ctx(), &env, &manifest)
      .err()
      .unwrap()
      .contains("owned by shards")
  );
  manifest.shards[1].blocks.clear();
  manifest.shards[1].id = 7;
  assert!(
    prepare_run(&ctx(), &env, &manifest)
      .err()
      .unwrap()
      .contains("repeats shard id")
  );
  manifest.shards.pop();
  manifest.shards[0].blocks.clear();
  assert!(
    prepare_run(&ctx(), &env, &manifest)
      .err()
      .unwrap()
      .contains("no owning manifest shard")
  );
}

#[test]
fn root_validation_rejects_foreign_subjects_and_surviving_assumptions() {
  let (env, manifest) = singleton();
  let prepared = prepare_run(&ctx(), &env, &manifest).unwrap();
  let valid = &prepared.shards[0].statement;
  validate_root_statement(&prepared, valid).unwrap();
  let foreign = Statement::new(
    ctx(),
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
    ctx(),
    valid.subjects.clone(),
    CanonicalTree::from_sorted(vec![addr("assumption")]).unwrap(),
  );
  assert!(
    validate_root_statement(&prepared, &residual)
      .unwrap_err()
      .contains("undischarged assumptions")
  );
}

fn store_outside_logic(env: &ixon::Env) -> Vec<ix_common::address::Address> {
  use ix_common::env::DefinitionSafety;
  use ixon::{Axiom, Constant, ConstantInfo, DefKind, Definition, MutConst};
  let unsafe_axiom = addr("unsafe-axiom");
  env.store_const(
    unsafe_axiom.clone(),
    Constant::with_tables(
      ConstantInfo::Axio(Axiom {
        is_unsafe: true,
        lvls: 0,
        typ: Expr::sort(0),
      }),
      vec![],
      vec![],
      vec![],
    ),
  );
  let block = addr("partial-block");
  env.store_const(
    block.clone(),
    Constant::with_tables(
      ConstantInfo::Muts(vec![MutConst::Defn(Definition {
        kind: DefKind::Definition,
        safety: DefinitionSafety::Partial,
        lvls: 0,
        typ: Expr::sort(0),
        value: Expr::sort(0),
      })]),
      vec![],
      vec![],
      vec![],
    ),
  );
  let projection = addr("partial-projection");
  env.store_const(
    projection.clone(),
    Constant::with_tables(
      ConstantInfo::DPrj(ixon::DefinitionProj { idx: 0, block: block.clone() }),
      vec![],
      vec![],
      vec![],
    ),
  );
  vec![unsafe_axiom, block, projection]
}

#[test]
fn preparation_matches_claim_builder_for_unsafe_partial_and_projected_constants()
 {
  let (env, mut manifest) = singleton();
  let safe = manifest.shards[0].blocks[0].clone();
  let outside = store_outside_logic(&env);
  manifest.shards[0].blocks.extend_from_slice(&outside[..2]);
  let prepared = prepare_run(&ctx(), &env, &manifest).unwrap();
  assert_eq!(prepared.env_count, 1);
  assert_eq!(prepared.owner_by_address.len(), 4);
  let mut owned = vec![safe];
  owned.extend(outside);
  let (expected, _) =
    ixon::shard_claim::shard_check_env_claim(&ctx(), &env, &owned).unwrap();
  assert_eq!(prepared.shards[0].statement.claim, expected);
  let (root, count) =
    expected_from_manifest(&ctx(), &env, &manifest, 0).unwrap();
  assert_eq!(count, 1);
  assert_eq!(root.claim, expected);
  validate_root_statement(&prepared, &root).unwrap();
}

#[test]
fn preparation_requires_ownership_of_excluded_constants_and_rejects_empty_typing_claims()
 {
  let (env, mut manifest) = singleton();
  let outside = store_outside_logic(&env);
  assert!(
    prepare_run(&ctx(), &env, &manifest)
      .err()
      .unwrap()
      .contains("no owning manifest shard")
  );
  manifest.shards.push(shard(8, outside[0].clone()));
  manifest.shards[1].blocks.push(outside[1].clone());
  manifest.num_shards = 2;
  manifest.tree = Some(AggNode::Internal(
    Box::new(AggNode::Leaf(7)),
    Box::new(AggNode::Leaf(8)),
  ));
  assert!(
    prepare_run(&ctx(), &env, &manifest)
      .err()
      .unwrap()
      .contains("outside Lean's logic")
  );
}
