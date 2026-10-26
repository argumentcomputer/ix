//! Actual owned-worker and physical/semantic identity boundaries.

use std::sync::Arc;

use ix_common::address::Address;
use ix_common::env::Name;
use ix_kernel::artifact_checker::ArtifactChecker;
use ix_kernel::mode::Meta;
use ix_kernel::role_admission::ArtifactSource;
use ixon::constant::{Constant, ConstantInfo, MutConst, defn_proj_address};
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
