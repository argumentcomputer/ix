//! Complete-unit validation for canonical serialized mutual blocks.
use ix_common::address::Address;
use ix_common::env::Name;
use ix_kernel::anon_work::{AnonWorkItem, build_anon_work};
use ix_kernel::env::KEnv;
use ix_kernel::ingress::{
  build_ixon_ingress_lookups, ingress_anon_block,
  ingress_const_shallow_into_kenv_with_lookups,
};
use ix_kernel::ixon_checker::IxonChecker;
use ix_kernel::mode::{Anon, Meta};
use ix_kernel::tc::TypeChecker;
use ixon::constant::{
  Constant, ConstantInfo, Constructor, MutConst, ctor_proj_constant,
  defn_proj_constant, indc_proj_constant, recr_proj_constant,
};
use ixon::env::{Env, Named};
use ixon::expr::Expr;
use ixon::metadata::{ConstantMeta, ConstantMetaInfo, ExprMeta};

const GOOD: &[u8] =
  include_bytes!("fixtures/serialized_units/homogeneous-good.ixe");
const BAD: &[u8] =
  include_bytes!("fixtures/serialized_units/homogeneous-bad-sibling.ixe");
const FAMILY: &[u8] =
  include_bytes!("fixtures/serialized_units/family-good.ixe");
const BAD_RECURSOR: &[u8] =
  include_bytes!("fixtures/serialized_units/family-bad-recursor.ixe");
const MIXES: [&[u8]; 3] = [
  include_bytes!("fixtures/serialized_units/mixed-good.ixe"),
  include_bytes!("fixtures/serialized_units/mixed-bad-primary.ixe"),
  include_bytes!("fixtures/serialized_units/mixed-bad-sibling.ixe"),
];

fn load(bytes: &[u8]) -> (Env, Address, Constant, Vec<Address>) {
  let mut input = bytes;
  let env = Env::get(&mut input).unwrap();
  assert!(input.is_empty());
  let mut roundtrip = Vec::new();
  env.put(&mut roundtrip).unwrap();
  assert_eq!(roundtrip, bytes);
  assert!(
    env.named.is_empty() && env.blobs.is_empty() && env.assumptions.is_empty()
  );
  let (address, block) = env
    .consts
    .iter()
    .find_map(|entry| {
      let value = entry.get().unwrap();
      matches!(value.info, ConstantInfo::Muts(_))
        .then(|| (entry.key().clone(), (*value).clone()))
    })
    .unwrap();
  let ConstantInfo::Muts(members) = &block.info else { unreachable!() };
  let targets = members
    .iter()
    .enumerate()
    .map(|(i, member)| {
      match member {
        MutConst::Defn(_) => defn_proj_constant(i as u64, address.clone()),
        MutConst::Indc(_) => indc_proj_constant(i as u64, address.clone()),
        MutConst::Recr(_) => recr_proj_constant(i as u64, address.clone()),
      }
      .commit()
      .0
    })
    .collect();
  (env, address, block, targets)
}

fn check_every_target(env: &Env, targets: &[Address], accepts: bool) {
  for first in targets {
    let mut reused = IxonChecker::new(env);
    assert_eq!(reused.check_const(first).is_ok(), accepts);
    for target in targets {
      assert_eq!(reused.check_const(target).is_ok(), accepts);
      assert_eq!(IxonChecker::new(env).check_const(target).is_ok(), accepts);
    }
  }
}

fn add_metadata(
  env: &Env,
  block_addr: &Address,
  block: &Constant,
  targets: &[Address],
) -> Vec<Name> {
  let ConstantInfo::Muts(members) = &block.info else { unreachable!() };
  let names: Vec<_> = (0..members.len())
    .map(|i| Name::str(Name::anon(), format!("member{i}")))
    .collect();
  let name_addr = |n: &Name| Address::from_blake3_hash(*n.get_hash());
  let addresses: Vec<_> = names.iter().map(name_addr).collect();
  let universe = Name::str(Name::anon(), "u".into());
  env.store_name(name_addr(&universe), universe.clone());
  for (i, (name, member)) in names.iter().zip(members).enumerate() {
    let info = match member {
      MutConst::Defn(_) => ConstantMetaInfo::Def {
        name: addresses[i].clone(),
        lvls: vec![],
        all: addresses.clone(),
        ctx: addresses.clone(),
        arena: ExprMeta::default(),
        type_root: 0,
        value_root: 0,
      },
      MutConst::Indc(_) => ConstantMetaInfo::Indc {
        name: addresses[i].clone(),
        lvls: vec![],
        ctors: vec![],
        all: vec![addresses[i].clone()],
        ctx: addresses.clone(),
        arena: ExprMeta::default(),
        type_root: 0,
      },
      MutConst::Recr(_) => ConstantMetaInfo::Rec {
        name: addresses[i].clone(),
        lvls: vec![name_addr(&universe)],
        rules: vec![],
        all: vec![addresses[0].clone()],
        ctx: addresses.clone(),
        arena: ExprMeta::default(),
        type_root: 0,
        rule_roots: vec![],
      },
    };
    env.store_name(addresses[i].clone(), name.clone());
    env.register_name(
      name.clone(),
      Named::new(
        targets[i].clone(),
        ConstantMeta { info, ..ConstantMeta::default() },
      ),
    );
  }
  let root = Name::str(Name::anon(), "family".into());
  env.store_name(name_addr(&root), root.clone());
  env.register_name(
    root,
    Named::new(
      block_addr.clone(),
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
fn unsupported_serialized_mixtures_fail_before_publication_or_work() {
  for bytes in MIXES {
    let (env, address, block, targets) = load(bytes);
    assert!(build_anon_work(&env).unwrap_err().contains("definitions mixed"));
    check_every_target(&env, &targets, false);
    let mut anon = KEnv::<Anon>::new();
    assert!(
      ingress_anon_block(&mut anon, &env, &block, &address)
        .unwrap_err()
        .contains("definitions mixed")
    );
    assert!(anon.consts.is_empty() && anon.blocks.is_empty());
    let names = add_metadata(&env, &address, &block, &targets);
    let lookups = build_ixon_ingress_lookups(&env);
    let mut meta = KEnv::<Meta>::new();
    assert!(
      ingress_const_shallow_into_kenv_with_lookups(
        &mut meta, &env, &lookups, &names[0]
      )
      .unwrap_err()
      .contains("definitions mixed")
    );
    assert!(meta.consts.is_empty() && meta.blocks.is_empty());
  }
}

#[test]
fn homogeneous_and_inductive_recursor_units_check_all_targets() {
  for (bytes, accepts) in
    [(GOOD, true), (BAD, false), (FAMILY, true), (BAD_RECURSOR, false)]
  {
    let (env, address, block, targets) = load(bytes);
    let work = build_anon_work(&env).unwrap();
    assert_eq!(work.len(), 1);
    let AnonWorkItem::Block { targets: actual, .. } = &work[0] else {
      panic!("block")
    };
    assert_eq!(actual, &targets);
    assert_eq!(work[0].proven_targets().len(), targets.len() + 1);
    check_every_target(&env, &targets, accepts);
    let names = add_metadata(&env, &address, &block, &targets);
    let lookups = build_ixon_ingress_lookups(&env);
    for name in &names {
      let mut kernel = KEnv::<Meta>::new();
      let id = ingress_const_shallow_into_kenv_with_lookups(
        &mut kernel,
        &env,
        &lookups,
        name,
      )
      .unwrap();
      let mut checker =
        TypeChecker::new_with_lazy_ixon(&mut kernel, &env, &lookups);
      assert_eq!(checker.check_ixon_const(&id).is_ok(), accepts);
    }
  }
}

#[test]
fn empty_units_and_well_scoped_invalid_recursors_do_not_gain_coverage() {
  let empty = Env::new();
  let block = Constant::new(ConstantInfo::Muts(vec![]));
  let address = block.commit().0;
  empty.store_const(address.clone(), block.clone());
  assert!(build_anon_work(&empty).unwrap_err().contains("empty serialized"));
  let mut kernel = KEnv::<Anon>::new();
  assert!(ingress_anon_block(&mut kernel, &empty, &block, &address).is_err());
  assert!(kernel.consts.is_empty());

  let (_, _, mut block, _) = load(FAMILY);
  let ConstantInfo::Muts(members) = &mut block.info else { unreachable!() };
  let MutConst::Recr(recursor) = &mut members[1] else { unreachable!() };
  recursor.typ = Expr::sort(1); // scoped, but not the required recursor type.
  let env = Env::new();
  let address = block.commit().0;
  env.store_const(address.clone(), block);
  let mut targets = Vec::new();
  for c in
    [indc_proj_constant(0, address.clone()), recr_proj_constant(1, address)]
  {
    let a = c.commit().0;
    targets.push(a.clone());
    env.store_const(a, c);
  }
  assert_eq!(build_anon_work(&env).unwrap().len(), 1);
  check_every_target(&env, &targets, false);
}

#[test]
fn constructor_target_cannot_skip_the_family_recursor() {
  let (_, _, mut block, _) = load(FAMILY);
  let ConstantInfo::Muts(members) = &mut block.info else { unreachable!() };
  let MutConst::Indc(inductive) = &mut members[0] else { unreachable!() };
  inductive.ctors.push(Constructor {
    is_unsafe: false,
    lvls: 0,
    cidx: 0,
    params: 0,
    fields: 0,
    typ: Expr::rec(0, vec![]),
  });
  // The retained recursor is scoped but still claims the empty family schema.
  let env = Env::new();
  let address = block.commit().0;
  env.store_const(address.clone(), block);
  let mut targets = Vec::new();
  for constant in [
    indc_proj_constant(0, address.clone()),
    ctor_proj_constant(0, 0, address.clone()),
    recr_proj_constant(1, address),
  ] {
    let target = constant.commit().0;
    targets.push(target.clone());
    env.store_const(target, constant);
  }
  let work = build_anon_work(&env).unwrap();
  assert_eq!(work.len(), 1);
  assert_eq!(work[0].targets(), targets);
  assert_eq!(work[0].proven_targets().len(), 4);
  let block_address = match &work[0] {
    AnonWorkItem::Block { block_addr, .. } => block_addr,
    _ => unreachable!(),
  };
  let mut kernel = KEnv::<Anon>::new();
  ingress_anon_block(
    &mut kernel,
    &env,
    &env.get_const(block_address).unwrap(),
    block_address,
  )
  .unwrap();
  let mut member_checker = TypeChecker::new(&mut kernel);
  for target in &targets[..2] {
    member_checker
      .check_const(&ix_kernel::id::KId::new(target.clone(), ()))
      .unwrap();
  }
  check_every_target(&env, &targets, false);
}
