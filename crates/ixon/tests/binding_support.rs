//! Availability controls. Synthetic roles/records are not semantic certificates;
//! native Lean controls check actual generated packages at the certified entry.

use ix_common::address::Address;
use ix_common::env::{DefinitionSafety, Name};
use ixon::constant::{
  Constant, ConstantInfo as CI, DefKind, Definition, Inductive, MutConst,
  Recursor, indc_proj_constant,
};
use ixon::contract::{BinderContract, ValueContract};
use ixon::env::{Env, Named, RoleBinding};
use ixon::expr::Expr;
use ixon::metadata::{ConstantMeta, ConstantMetaInfo, ExprMeta};
use ixon::role_table::{Evidence, Role, RoleTable};
use ixon::univ::Univ;
use rustc_hash::FxHashSet;
use std::sync::Arc;

fn store(env: &Env, c: Constant) -> Address {
  let address = c.commit().0;
  env.store_const(address.clone(), c);
  address
}
fn definition(refs: Vec<Address>, discriminator: u64) -> Constant {
  let mut c = Constant::new(CI::Defn(Definition {
    kind: DefKind::Definition,
    safety: DefinitionSafety::Safe,
    lvls: discriminator,
    typ: Expr::sort(0),
    value: Expr::var(0),
  }));
  c.refs = refs;
  c.univs.push(Univ::zero());
  c
}
fn bind(
  env: &mut Env,
  mut bound: Vec<(Role, Address)>,
  evidence: Vec<(Role, Vec<Evidence>)>,
) {
  bound.sort_by_key(|(r, _)| *r);
  let bytes = RoleTable { version: 2, bound, evidence }.to_bytes().unwrap();
  env.role_binding =
    Some(RoleBinding { address: Address::hash(&bytes), bytes: bytes.into() });
}
fn encode(env: &Env) -> Result<Vec<u8>, String> {
  let mut bytes = Vec::new();
  env.put(&mut bytes)?;
  Ok(bytes)
}
fn modes(
  env: &Env,
  main: &Address,
  assumed: &FxHashSet<Address>,
) -> [Result<Env, String>; 3] {
  let streamed = (|| {
    let bytes = encode(env)?;
    let (index, names) = Env::parse_lazy_index_with_names(&bytes)?;
    let lazy = Env::from_lazy_index(&index, &bytes)?;
    lazy.prune_to_closure_streaming(&index, &bytes, &names, main, assumed)
  })();
  [
    env.prune_to_closure(main, assumed),
    streamed,
    env.prune_to_closure_anon(main, assumed),
  ]
}
fn all_fail(
  env: &Env,
  main: &Address,
  assumed: &FxHashSet<Address>,
  text: &str,
) {
  for result in modes(env, main, assumed) {
    let error = result.unwrap_err();
    assert!(error.contains(text), "{error}");
  }
}
fn all(domain: Arc<Expr>, body: Arc<Expr>) -> Arc<Expr> {
  Arc::new(Expr::All(
    BinderContract::default(),
    ValueContract::shared(),
    domain,
    body,
  ))
}

struct Fixture {
  env: Env,
  main: Address,
  role: Address,
  proof: Address,
  proof_dep: Address,
  block: Address,
  projection: Address,
  recursor: Address,
  unrelated: Address,
}
fn fixture() -> Fixture {
  let mut env = Env::new();
  let role = store(&env, definition(vec![], 1));
  let proof_dep = store(&env, definition(vec![], 2));
  let mut proof_c = definition(vec![proof_dep.clone()], 0);
  if let CI::Defn(d) = &mut proof_c.info {
    d.kind = DefKind::Theorem;
  }
  let proof = store(&env, proof_c);
  bind(
    &mut env,
    vec![(Role::True, role.clone())],
    vec![(Role::True, vec![Evidence::Proof(proof.clone())])],
  );
  let mut ind = Constant::new(CI::Muts(vec![MutConst::Indc(Inductive {
    is_unsafe: false,
    lvls: 0,
    params: 0,
    indices: 0,
    typ: Expr::sort(0),
    ctors: vec![],
  })]));
  ind.univs.push(Univ::zero());
  let block = store(&env, ind);
  let projection = store(&env, indc_proj_constant(0, block.clone()));
  let mut rec = Constant::new(CI::Recr(Recursor {
    k: false,
    is_unsafe: false,
    lvls: 0,
    params: 0,
    motives: 1,
    minors: 0,
    indices: 0,
    typ: all(
      all(Expr::reference(0, vec![]), Expr::sort(0)),
      all(Expr::reference(0, vec![]), Expr::var(1)),
    ),
    rules: vec![],
  }));
  rec.refs.push(projection.clone());
  rec.univs.push(Univ::zero());
  let recursor = store(&env, rec);
  let main = store(&env, definition(vec![projection.clone()], 3));
  let unrelated = store(&env, definition(vec![], 99));
  Fixture {
    env,
    main,
    role,
    proof,
    proof_dep,
    block,
    projection,
    recursor,
    unrelated,
  }
}

#[test]
fn binding_proofs_and_reverse_recursors_reach_a_real_fixed_point() {
  let f = fixture();
  assert!(
    !f.env.bfs_closure(std::slice::from_ref(&f.main)).contains(&f.recursor)
  );
  let results =
    modes(&f.env, &f.main, &FxHashSet::default()).map(Result::unwrap);
  assert_eq!(encode(&results[0]).unwrap(), encode(&results[1]).unwrap());
  for packed in results {
    assert_eq!(packed.role_binding, f.env.role_binding);
    assert_eq!(packed.main, Some(f.main.clone()));
    for address in [
      &f.main,
      &f.role,
      &f.proof,
      &f.proof_dep,
      &f.block,
      &f.projection,
      &f.recursor,
    ] {
      assert_eq!(
        packed.get_const_bytes(address),
        f.env.get_const_bytes(address)
      );
    }
    assert!(!packed.consts.contains_key(&f.unrelated));
    packed.validate_closed().unwrap();
  }
}

#[test]
fn bound_support_keeps_original_provenance_and_anonymous_policy() {
  let f = fixture();
  let original_address = definition(vec![], 42).commit().0;
  assert!(!f.env.consts.contains_key(&original_address));
  let name = Name::str(Name::anon(), "BoundRoot".into());
  f.env.store_name(Address::from_blake3_hash(*name.get_hash()), name.clone());
  let mut named = Named::new(f.main.clone(), ConstantMeta::default());
  named.set_original(original_address.clone(), ConstantMeta::default());
  f.env.register_name(name.clone(), named);
  let packed =
    modes(&f.env, &f.main, &FxHashSet::default()).map(Result::unwrap);
  assert_eq!(encode(&packed[0]).unwrap(), encode(&packed[1]).unwrap());
  for output in &packed[..2] {
    assert!(!output.consts.contains_key(&original_address));
    assert_eq!(
      output.named.get(&name).unwrap().original().map(|(a, _)| a),
      Some(original_address.clone())
    );
  }
  assert!(packed[2].named.is_empty() && packed[2].names.is_empty());
}

#[test]
fn missing_bound_members_proofs_owners_recursors_and_proof_support_refuse() {
  let f = fixture();
  for address in [&f.role, &f.proof, &f.proof_dep, &f.block, &f.recursor] {
    let bad = f.env.clone();
    bad.consts.remove(address);
    all_fail(&bad, &f.main, &FxHashSet::default(), "binding support:");
  }
}

#[test]
fn binding_wire_hash_and_mandatory_cut_failures_do_not_publish() {
  let f = fixture();
  let mut bad_hash = f.env.clone();
  bad_hash.role_binding.as_mut().unwrap().address = Address::hash(b"wrong");
  all_fail(&bad_hash, &f.main, &FxHashSet::default(), "role binding:");
  let mut malformed = f.env.clone();
  let mut bytes = malformed.role_binding.as_ref().unwrap().bytes.to_vec();
  bytes.push(0);
  malformed.role_binding =
    Some(RoleBinding { address: Address::hash(&bytes), bytes: bytes.into() });
  all_fail(&malformed, &f.main, &FxHashSet::default(), "role table:");
  for address in [&f.role, &f.proof, &f.proof_dep, &f.block, &f.recursor] {
    all_fail(
      &f.env,
      &f.main,
      &[address.clone()].into_iter().collect(),
      "cannot be assumed",
    );
  }
}

#[test]
fn literal_roles_slots_and_dual_constant_blob_payloads_are_preserved() {
  for string in [false, true] {
    let mut env = Env::new();
    let roles = [
      Role::Nat,
      Role::NatZero,
      Role::NatSucc,
      Role::String,
      Role::StringOfList,
      Role::List,
      Role::ListNil,
      Role::ListCons,
      Role::Char,
      Role::CharOfNat,
    ];
    let bound: Vec<_> = roles
      .iter()
      .enumerate()
      .map(|(i, r)| (*r, store(&env, definition(vec![], i as u64 + 1))))
      .collect();
    bind(&mut env, bound.clone(), vec![]);
    let dual = bound[0].1.clone();
    let blob = if string {
      env.store_blob(b"hello".to_vec())
    } else {
      env
        .blobs
        .insert(dual.clone(), env.get_const_bytes(&dual).unwrap().to_vec());
      dual.clone()
    };
    let mut literal = definition(vec![blob.clone()], 0);
    if let CI::Defn(d) = &mut literal.info {
      d.value = Arc::new(if string { Expr::Str(0) } else { Expr::Nat(0) });
    }
    let main = store(&env, literal.clone());
    for packed in modes(&env, &main, &FxHashSet::default()).map(Result::unwrap)
    {
      assert_eq!(packed.get_blob(&blob), env.get_blob(&blob));
      assert!(packed.consts.contains_key(&dual));
    }
    all_fail(
      &env,
      &main,
      &[blob.clone()].into_iter().collect(),
      "cannot be assumed",
    );
    let missing_blob = env.clone();
    missing_blob.blobs.remove(&blob);
    all_fail(
      &missing_blob,
      &main,
      &FxHashSet::default(),
      "missing literal blob",
    );
    let mut missing_role = env.clone();
    let mut partial = bound;
    partial.remove(if string { 4 } else { 1 });
    bind(&mut missing_role, partial, vec![]);
    all_fail(
      &missing_role,
      &main,
      &FxHashSet::default(),
      "missing literal role",
    );
    if let CI::Defn(d) = &mut literal.info {
      d.value = Arc::new(if string { Expr::Str(99) } else { Expr::Nat(99) });
    }
    let invalid = store(&env, literal);
    all_fail(
      &env,
      &invalid,
      &FxHashSet::default(),
      "missing literal reference slot",
    );
  }
}

#[test]
fn legacy_literal_blob_survives_an_identical_constant_address() {
  let env = Env::new();
  let dual = store(&env, definition(vec![], 1));
  let bytes = env.get_const_bytes(&dual).unwrap();
  env.blobs.insert(dual.clone(), bytes.to_vec());
  let mut literal = definition(vec![dual.clone()], 0);
  if let CI::Defn(d) = &mut literal.info {
    d.value = Arc::new(Expr::Nat(0));
  }
  let main = store(&env, literal);
  assert_eq!(env.envelope_version(), 4);
  for packed in modes(&env, &main, &FxHashSet::default()).map(Result::unwrap) {
    assert!(packed.role_binding.is_none());
    assert_eq!(packed.get_const_bytes(&dual), Some(bytes.clone()));
    assert_eq!(packed.get_blob(&dual), Some(bytes.to_vec()));
    assert_eq!(packed.envelope_version(), 4);
    packed.validate_closed().unwrap();
  }
}

#[test]
fn metadata_discovered_support_cannot_reuse_an_earlier_assumption_cut() {
  let f = fixture();
  let cut = store(&f.env, definition(vec![], 23));
  let mut extra_rec = f.env.get_const(&f.recursor).unwrap().as_ref().clone();
  extra_rec.refs.push(cut.clone());
  let second = store(&f.env, extra_rec);
  let main = store(&f.env, definition(vec![cut.clone()], 24));
  let root_name = Name::str(Name::anon(), "Root".into());
  let late_name = Name::str(Name::anon(), "Late".into());
  let root_hash = Address::from_blake3_hash(*root_name.get_hash());
  let late_hash = Address::from_blake3_hash(*late_name.get_hash());
  f.env.store_name(root_hash.clone(), root_name.clone());
  f.env.store_name(late_hash.clone(), late_name.clone());
  f.env.register_name(
    root_name,
    Named::new(
      main.clone(),
      ConstantMeta::new(ConstantMetaInfo::Def {
        name: root_hash,
        lvls: vec![],
        all: vec![late_hash],
        ctx: vec![],
        arena: ExprMeta::default(),
        type_root: 0,
        value_root: 0,
      }),
    ),
  );
  f.env.register_name(
    late_name,
    Named::new(f.projection.clone(), ConstantMeta::default()),
  );
  let results = modes(&f.env, &main, &[cut.clone()].into_iter().collect());
  for result in &results[..2] {
    assert!(result.as_ref().unwrap_err().contains("cannot be assumed"));
  }
  let anon = results[2].as_ref().unwrap();
  assert!(anon.assumptions.contains(&cut));
  assert!(!anon.consts.contains_key(&f.block));
  let complete =
    modes(&f.env, &main, &FxHashSet::default()).map(Result::unwrap);
  assert_eq!(encode(&complete[0]).unwrap(), encode(&complete[1]).unwrap());
  for packed in &complete[..2] {
    assert!(packed.consts.contains_key(&f.recursor));
    assert!(packed.consts.contains_key(&second)); // No new ambiguity rejection.
  }
}

#[test]
fn unused_malformed_recursors_do_not_drive_count_sized_scans() {
  let f = fixture();
  let mut c = f.env.get_const(&f.recursor).unwrap().as_ref().clone();
  if let CI::Recr(r) = &mut c.info {
    r.params = u64::MAX - 2;
    r.typ = Arc::new(Expr::Share(0));
  }
  c.sharing = vec![all(Expr::sort(0), Arc::new(Expr::Share(0)))];
  let unused = store(&f.env, c);
  for packed in
    modes(&f.env, &f.main, &FxHashSet::default()).map(Result::unwrap)
  {
    assert!(!packed.consts.contains_key(&unused));
  }
}
