//! Actual owned-worker and physical/semantic identity boundaries.

use std::sync::Arc;

use ix_common::address::Address;
use ix_common::env::Name;
use ix_kernel::anon_work::{build_artifact_work, closure_addrs};
use ix_kernel::artifact_checker::ArtifactChecker;
use ix_kernel::mode::{Anon, Meta};
use ix_kernel::role_admission::ArtifactSource;
use ixon::constant::{
  Constant, ConstantInfo, MutConst, defn_proj_address, defn_proj_constant,
};
use ixon::env::{Env, Named, RoleBinding};
use ixon::metadata::{ConstantMeta, ConstantMetaInfo, ExprMeta};
use ixon::role_table::RoleTable;

const GOOD: &[u8] =
  include_bytes!("fixtures/serialized_units/homogeneous-good.ixe");
const BAD: &[u8] =
  include_bytes!("fixtures/serialized_units/homogeneous-bad-sibling.ixe");

fn loaded(bytes: &[u8]) -> Env {
  let mut input = bytes;
  let env = Env::get(&mut input).unwrap();
  assert!(input.is_empty());
  env
}

fn owner(env: &Env) -> (Address, Arc<Constant>) {
  env
    .consts
    .iter()
    .find_map(|entry| {
      let record = entry.value().get().unwrap();
      matches!(record.info, ConstantInfo::Muts(_))
        .then(|| (entry.key().clone(), record))
    })
    .unwrap()
}

fn empty_binding(env: &mut Env) {
  let raw = RoleTable { version: 2, bound: vec![], evidence: vec![] }
    .to_bytes()
    .unwrap();
  env.role_binding =
    Some(RoleBinding { address: Address::hash(&raw), bytes: raw.into() });
}

fn name(label: &str) -> Name {
  Name::str(Name::anon(), label.into())
}
fn name_address(value: &Name) -> Address {
  Address::from_blake3_hash(*value.get_hash())
}

fn name_definitions(
  env: &Env,
  owner: &Address,
  record: &Constant,
  prefix: &str,
) -> Vec<Name> {
  let ConstantInfo::Muts(members) = &record.info else {
    panic!("expected owner")
  };
  let names: Vec<_> =
    (0..members.len()).map(|i| name(&format!("{prefix}{i}"))).collect();
  let addresses: Vec<_> = names.iter().map(name_address).collect();
  for (i, member) in members.iter().enumerate() {
    assert!(matches!(member, MutConst::Defn(_)));
    env.store_name(addresses[i].clone(), names[i].clone());
    env.register_name(
      names[i].clone(),
      Named::new(
        defn_proj_address(u64::try_from(i).unwrap(), owner),
        ConstantMeta {
          info: ConstantMetaInfo::Def {
            name: addresses[i].clone(),
            lvls: vec![],
            all: addresses.clone(),
            ctx: addresses.clone(),
            arena: ExprMeta::default(),
            type_root: 0,
            value_root: 0,
          },
          ..ConstantMeta::default()
        },
      ),
    );
  }
  let root = name(&format!("{prefix}Owner"));
  env.store_name(name_address(&root), root.clone());
  env.register_name(
    root,
    Named::new(
      owner.clone(),
      ConstantMeta {
        info: ConstantMetaInfo::Muts {
          all: addresses.into_iter().map(|a| vec![a]).collect(),
          aux_layout: None,
        },
        ..ConstantMeta::default()
      },
    ),
  );
  names
}

#[test]
fn metadata_cannot_relabel_a_real_owner_payload_as_another_units_member() {
  let mut env = loaded(GOOD);
  let bad = loaded(BAD);
  let (good_owner, good_record) = owner(&env);
  let (bad_owner, bad_record) = owner(&bad);
  assert_ne!(good_owner, bad_owner);
  for entry in &bad.consts {
    env.consts.insert(entry.key().clone(), entry.value().clone());
  }
  let good_names = name_definitions(&env, &good_owner, &good_record, "good");
  let bad_names = name_definitions(&env, &bad_owner, &bad_record, "bad");
  empty_binding(&mut env);
  let baseline = ArtifactSource::snapshot(&env).unwrap();
  let mut baseline = ArtifactChecker::<Meta>::from_named_source(Ok(baseline));
  assert!(baseline.check_name(&good_names[0]).is_ok());
  assert!(baseline.check_name(&bad_names[1]).is_err());

  let mut forged = env.lookup_name(&good_names[1]).unwrap();
  forged.addr = defn_proj_address(1, &bad_owner);
  env.register_name(good_names[1].clone(), forged);
  let source = ArtifactSource::snapshot(&env).unwrap();
  let cold = ArtifactChecker::<Meta>::from_named_source(Ok(source.clone()))
    .check_name(&good_names[1])
    .is_ok();
  let mut warm = ArtifactChecker::<Meta>::from_named_source(Ok(source));
  let primed = warm.check_name(&good_names[0]).is_ok();
  let after_prime = warm.check_name(&good_names[1]).is_ok();
  eprintln!(
    "metadata substitution: cold={cold}, prime={primed}, after_prime={after_prime}"
  );
  assert!(!cold, "invalid actual target unexpectedly checks cold");
  assert!(!primed, "optional metadata relabeled a member of another raw owner");
  assert!(
    !after_prime,
    "a relabeled payload contaminated the same-source declaration cache"
  );
}

#[test]
fn owner_checks_accept_each_physical_projection_subset() {
  for retained in [vec![], vec![1], vec![0, 1]] {
    let mut env = loaded(GOOD);
    let (owner, _) = owner(&env);
    let targets = [defn_proj_address(0, &owner), defn_proj_address(1, &owner)];
    for (index, target) in targets.iter().enumerate() {
      if !retained.contains(&index) {
        env.consts.remove(target);
      }
    }
    empty_binding(&mut env);
    let source = ArtifactSource::snapshot(&env).unwrap();
    let work = build_artifact_work(&source).unwrap();
    assert_eq!(work.len(), 1);
    assert_eq!(work[0].targets(), targets);
    let mut checker = ArtifactChecker::<Anon>::from_source(Ok(source.clone()));
    for (index, target) in targets.iter().enumerate() {
      if !retained.contains(&index) {
        assert!(source.record(target).is_err());
        assert!(checker.check_const(target).is_err());
      }
    }
    checker.check_work(&work[0]).unwrap();
    checker.check_work(&work[0]).unwrap();
    for (index, target) in targets.iter().enumerate() {
      if !retained.contains(&index) {
        assert!(checker.check_const(target).is_err());
      }
    }
  }
}

#[test]
fn physical_coverage_rejects_orphans_and_invalid_carried_projections() {
  let mut orphan = loaded(GOOD);
  let (owner, _) = owner(&orphan);
  orphan.consts.remove(&owner);
  empty_binding(&mut orphan);
  assert!(
    build_artifact_work(&ArtifactSource::snapshot(&orphan).unwrap()).is_err()
  );

  let mut env = loaded(GOOD);
  let invalid = defn_proj_constant(99, owner);
  let address = invalid.commit().0;
  env.store_const(address, invalid);
  empty_binding(&mut env);
  assert!(
    build_artifact_work(&ArtifactSource::snapshot(&env).unwrap()).is_err()
  );
}

#[test]
fn selected_closure_keeps_the_owners_other_projection_edges() {
  let mut env = loaded(GOOD);
  let (owner, _) = owner(&env);
  let primary = defn_proj_address(0, &owner);
  let other = defn_proj_address(1, &owner);
  empty_binding(&mut env);
  let source = ArtifactSource::snapshot(&env).unwrap();
  let roots = [other];
  let expected = closure_addrs(&env, &roots);
  let actual = source.closure(&roots).unwrap();
  assert!(actual.contains(&owner) && actual.contains(&primary));
  assert_eq!(actual.len(), expected.len());
  assert!(expected.iter().all(|address| actual.contains(address)));
}

#[test]
fn cached_owner_members_do_not_authorize_absent_external_references() {
  for carry_projection in [true, false] {
    let mut env = loaded(GOOD);
    let (owner, record) = owner(&env);
    let ConstantInfo::Muts(members) = &record.info else { unreachable!() };
    let MutConst::Defn(definition) = &members[0] else { unreachable!() };
    assert_eq!(definition.lvls, 0);
    let target = defn_proj_address(0, &owner);
    let mut dependent = definition.clone();
    dependent.value = Arc::new(ixon::expr::Expr::Ref(
      u64::try_from(record.refs.len()).unwrap(),
      vec![],
    ));
    let mut dependent = Constant::new(ConstantInfo::Defn(dependent));
    dependent.refs = record.refs.clone();
    dependent.refs.push(target.clone());
    dependent.univs = record.univs.clone();
    dependent.sharing = record.sharing.clone();
    let address = dependent.commit().0;
    env.store_const(address.clone(), dependent);
    if !carry_projection {
      env.consts.remove(&target);
    }
    empty_binding(&mut env);
    let source = ArtifactSource::snapshot(&env).unwrap();
    let mut checker = ArtifactChecker::<Anon>::from_source(Ok(source));
    checker.check_owner(&owner).unwrap();
    assert_eq!(checker.check_const(&address).is_ok(), carry_projection);
  }
}
