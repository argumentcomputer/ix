use super::*;
use ixon::constant::{Axiom, defn_proj_constant};
use ixon::expr::Expr;
use ixon::univ::Univ;

fn record(marker: u64, theorem: bool) -> Constant {
  let info = if theorem {
    ConstantInfo::Defn(Definition {
      kind: DefKind::Theorem,
      safety: DefinitionSafety::Safe,
      lvls: marker,
      typ: Arc::new(Expr::Sort(0)),
      value: Arc::new(Expr::Var(0)),
    })
  } else {
    ConstantInfo::Axio(Axiom {
      is_unsafe: false,
      lvls: marker,
      typ: Arc::new(Expr::Sort(0)),
    })
  };
  let mut c = Constant::new(info);
  c.univs.push(Arc::new(Univ::Zero));
  c
}

fn store(env: &Env, c: Constant) -> Address {
  let (address, bytes) = c.commit();
  env
    .consts
    .insert(address.clone(), LazyConstant::from_serialized(c, bytes, true));
  address
}

fn bind(env: &mut Env, table: &RoleTable) {
  let bytes = table.to_bytes().unwrap();
  env.role_binding =
    Some(RoleBinding { address: Address::hash(&bytes), bytes: bytes.into() });
}

// Authentic, canonical records deliberately do NOT satisfy the role types or
// theorem propositions. Candidate collection cannot stand in for admission.
fn full_candidate() -> (Env, RoleTable) {
  let mut env = Env::new();
  let bound: Vec<_> = Role::ALL
    .into_iter()
    .map(|role| (role, store(&env, record(u64::from(role.index()), false))))
    .collect();
  let proof = store(&env, record(100, true));
  let evidence = Role::ALL
    .into_iter()
    .filter_map(|role| {
      let allowed = evidence_allowed(role);
      (!allowed.is_empty()).then(|| {
        (
          role,
          allowed
            .iter()
            .map(|kind| match kind {
              Some(false) => Evidence::Proof(proof.clone()),
              _ => Evidence::DefEq,
            })
            .collect(),
        )
      })
    })
    .collect();
  let table = RoleTable { version: SPEC_VERSION, bound, evidence };
  bind(&mut env, &table);
  (env, table)
}

#[test]
fn candidates_preserve_exact_binding_without_admitting_role_types() {
  let (env, table) = full_candidate();
  let raw = env.role_binding.clone().unwrap();
  let source = ArtifactSource::prepare(env).unwrap();
  let candidate = source.binding().unwrap();
  assert_eq!(candidate.bytes(), raw.bytes.as_ref());
  assert_eq!(candidate.address(), &raw.address);
  for (role, address) in table.bound {
    assert_eq!(candidate.required(role).unwrap(), &address);
    assert!(matches!(
      source.record(&address).unwrap().constant().info,
      ConstantInfo::Axio(_)
    ));
  }
  let proof = match &candidate.evidence(Role::NatDiv).unwrap()[0] {
    Evidence::Proof(a) => a,
    Evidence::DefEq => panic!("wrong evidence kind"),
  };
  assert!(matches!(
    source.proof_record(proof).unwrap().definition().unwrap().value.as_ref(),
    Expr::Var(0)
  ));
}

#[test]
fn table_shape_matches_current_lean_specification_for_all_roles() {
  let mut actual = format!(
    "# Role.block/deps and Spec.evidenceAllowed, version{SPEC_VERSION}\n"
  );
  let indices = |roles: &[Role]| {
    roles.iter().map(|r| r.index().to_string()).collect::<Vec<_>>().join(",")
  };
  for role in Role::ALL {
    let kinds = evidence_allowed(role)
      .iter()
      .map(|kind| match kind {
        Some(true) => "defeq",
        Some(false) => "proof",
        None => "either",
      })
      .collect::<Vec<_>>()
      .join(",");
    actual.push_str(&format!(
      "{}\t{}\t{}\t{kinds}\n",
      role.index(),
      indices(block(role)),
      indices(dependencies(role))
    ));
  }
  assert_eq!(
    actual,
    include_str!("../../../../Tests/Fixtures/role-binding-v2/spec-shape.tsv")
  );
}

#[test]
fn bound_empty_and_unbound_are_distinct_and_neither_fills_absent_roles() {
  let mut env = Env::new();
  let table =
    RoleTable { version: SPEC_VERSION, bound: vec![], evidence: vec![] };
  let unbound = ArtifactSource::snapshot(&env).unwrap();
  assert!(unbound.binding().is_none());
  assert!(matches!(unbound.required_role(Role::Nat), Err(Error::Unbound)));
  bind(&mut env, &table);
  let bound = ArtifactSource::prepare(env).unwrap();
  assert!(bound.binding().unwrap().role(Role::Nat).is_none());
  assert!(matches!(
    bound.required_role(Role::Nat),
    Err(Error::MissingRole(Role::Nat))
  ));
}

#[test]
fn canonical_wire_tables_still_need_current_well_formedness() {
  let (env, table) = full_candidate();
  let mut variants = vec![];
  let mut bad = table.clone();
  bad.version += 1;
  variants.push(bad);
  let mut bad = table.clone();
  bad.bound[1].1 = bad.bound[0].1.clone();
  variants.push(bad);
  let mut bad = table.clone();
  bad.bound.retain(|(r, _)| *r != Role::NatRec);
  variants.push(bad);
  let mut bad = table.clone();
  bad.bound.retain(|(r, _)| *r != Role::Char);
  variants.push(bad);
  let mut bad = table.clone();
  bad.evidence.retain(|(r, _)| *r != Role::NatAdd);
  variants.push(bad);
  let mut bad = table.clone();
  bad.evidence.iter_mut().find(|(r, _)| *r == Role::NatDiv).unwrap().1 =
    vec![Evidence::DefEq; 3];
  variants.push(bad);
  let mut bad = table.clone();
  bad.evidence.iter_mut().find(|(r, _)| *r == Role::NatPred).unwrap().1.pop();
  variants.push(bad);
  let mut bad = table.clone();
  bad.evidence.insert(0, (Role::Nat, vec![Evidence::DefEq]));
  variants.push(bad);
  let mut bad = table.clone();
  bad.bound.retain(|(r, _)| *r != Role::NatShiftLeft);
  variants.push(bad);
  for table in variants {
    let mut input = env.clone();
    bind(&mut input, &table);
    assert!(
      RoleTable::from_bytes(&input.role_binding.as_ref().unwrap().bytes)
        .is_ok()
    );
    assert!(matches!(ArtifactSource::prepare(input), Err(Error::Binding(_))));
  }
  let mut bad = env.clone();
  bad.role_binding.as_mut().unwrap().address =
    Address::hash(b"wrong binding key");
  assert!(matches!(ArtifactSource::prepare(bad), Err(Error::Binding(_))));
  let mut bad = env;
  let binding = bad.role_binding.as_mut().unwrap();
  let mut bytes = binding.bytes.to_vec();
  bytes.push(0);
  binding.address = Address::hash(&bytes);
  binding.bytes = bytes.into();
  assert!(matches!(ArtifactSource::prepare(bad), Err(Error::Binding(_))));
}

#[test]
fn missing_role_proof_and_owner_bytes_refuse_before_admission() {
  let (env, _) = full_candidate();
  let role = env.role_binding.as_ref().unwrap();
  let table = RoleTable::from_bytes(&role.bytes).unwrap();
  let target = table.bound[0].1.clone();
  let missing = env.clone();
  missing.consts.remove(&target);
  assert!(matches!(
    ArtifactSource::prepare(missing),
    Err(Error::MissingRecord(_))
  ));
  let proof = match &table
    .evidence
    .iter()
    .find(|(r, _)| *r == Role::NatDiv)
    .unwrap()
    .1[0]
  {
    Evidence::Proof(a) => a.clone(),
    Evidence::DefEq => panic!("missing proof fixture"),
  };
  let missing = env.clone();
  missing.consts.remove(&proof);
  assert!(matches!(
    ArtifactSource::prepare(missing),
    Err(Error::MissingRecord(_))
  ));
  let bad = env.clone();
  bad.consts.insert(target, LazyConstant::from_constant(record(900, false)));
  assert!(matches!(ArtifactSource::prepare(bad), Err(Error::Record(_, _))));
  let mut bad_table = table;
  for (_, entries) in &mut bad_table.evidence {
    for e in entries {
      if matches!(e, Evidence::Proof(_)) {
        *e = Evidence::Proof(bad_table.bound[0].1.clone());
      }
    }
  }
  let mut bad = env;
  bind(&mut bad, &bad_table);
  assert!(matches!(ArtifactSource::prepare(bad), Err(Error::NotTheorem(_))));
}

#[test]
fn every_transitive_record_and_blob_read_authenticates_its_own_bytes() {
  let env = Env::new();
  let bad = Address::hash(b"forged record address");
  env.consts.insert(bad.clone(), LazyConstant::from_constant(record(0, false)));
  let mut parent = record(1, false);
  parent.refs.push(bad.clone());
  let root = store(&env, parent);
  let bad_blob = Address::hash(b"forged blob address");
  env.blobs.insert(bad_blob.clone(), b"other bytes".to_vec());
  let source = ArtifactSource::prepare(env).unwrap();
  let parent = source.record(&root).unwrap();
  assert_eq!(parent.constant().refs.as_slice(), std::slice::from_ref(&bad));
  assert!(matches!(source.record(&bad), Err(Error::Record(_, _))));
  assert!(matches!(source.blob(&bad_blob), Err(Error::BlobHash(_))));
  let missing = Address::hash(b"not present");
  assert!(matches!(source.record(&missing), Err(Error::MissingRecord(_))));
  assert!(matches!(source.blob(&missing), Err(Error::MissingBlob(_))));
}

#[test]
fn snapshot_owns_maps_and_shares_raw_buffers_between_workers() {
  let env = Env::new();
  let address = store(&env, record(0, false));
  let bytes = b"literal bytes".to_vec();
  let blob = Address::hash(&bytes);
  env.blobs.insert(blob.clone(), bytes.clone());
  let source = ArtifactSource::snapshot(&env).unwrap();
  let worker = source.clone();
  let captured = source.record(&address).unwrap();
  env.consts.remove(&address);
  env.blobs.insert(blob.clone(), vec![0]);
  assert!(source.same_source(&worker));
  assert_eq!(
    captured.bytes().as_ptr(),
    worker.record(&address).unwrap().bytes().as_ptr()
  );
  let left = source.blob(&blob).unwrap();
  let right = worker.blob(&blob).unwrap();
  assert_eq!(left.bytes(), bytes);
  assert!(Arc::ptr_eq(&left.bytes, &right.bytes));
  assert!(!source.same_source(&ArtifactSource::prepare(Env::new()).unwrap()));
}

#[test]
fn projected_proofs_keep_exact_record_owner_and_member_provenance() {
  let env = Env::new();
  let ConstantInfo::Defn(theorem) = record(0, true).info else {
    unreachable!()
  };
  let mut block =
    Constant::new(ConstantInfo::Muts(vec![MutConst::Defn(theorem)]));
  block.univs.push(Arc::new(Univ::Zero));
  let owner = store(&env, block);
  let projection = store(&env, defn_proj_constant(0, owner.clone()));
  let source = ArtifactSource::snapshot(&env).unwrap();
  let proof = source.proof_record(&projection).unwrap();
  assert_eq!(proof.record().address(), &projection);
  assert_eq!(proof.owner().unwrap().address(), &owner);
  assert_eq!(proof.index(), Some(0));
  assert_eq!(proof.constructor_index(), None);
  assert_eq!(Address::hash(proof.owner().unwrap().bytes()), owner);
  let bad_projection = store(&env, defn_proj_constant(1, owner.clone()));
  assert!(matches!(
    ArtifactSource::snapshot(&env).unwrap().member(&bad_projection),
    Err(Error::Member(_, _))
  ));
  env.consts.remove(&owner);
  assert!(matches!(
    ArtifactSource::prepare(env).unwrap().member(&projection),
    Err(Error::MissingRecord(_))
  ));
  assert!(source.proof_record(&projection).is_ok());
}

#[test]
fn work_enumeration_decodes_each_wide_owner_a_bounded_number_of_times() {
  let env = Env::new();
  let member = MutConst::Defn(Definition {
    kind: DefKind::Definition,
    safety: DefinitionSafety::Safe,
    lvls: 0,
    typ: Arc::new(Expr::Sort(1)),
    value: Arc::new(Expr::Sort(0)),
  });
  let owner = store(
    &env,
    Constant::with_tables(
      ConstantInfo::Muts(vec![member; 512]),
      vec![],
      vec![],
      vec![Univ::zero(), Univ::succ(Univ::zero())],
    ),
  );
  for i in 0..512 {
    store(&env, defn_proj_constant(i, owner.clone()));
  }
  let source = ArtifactSource::prepare(env).unwrap();
  let work = crate::anon_work::build_artifact_work(&source).unwrap();
  assert_eq!(work.len(), 1);
  assert_eq!(work[0].targets().len(), 512);
  // If a projection sorts before its owner, its layout is decoded first;
  // scheduling the owner itself then needs one more payload decoding.
  assert!(
    source.0.owner_decodes.load(std::sync::atomic::Ordering::Relaxed) <= 2
  );
  let before =
    source.0.owner_decodes.load(std::sync::atomic::Ordering::Relaxed);
  let worker = source.clone();
  for target in work[0].targets() {
    worker.authenticate_reference(target).unwrap();
    assert!(!worker.in_safety_tier(target));
  }
  assert_eq!(
    source.0.owner_decodes.load(std::sync::atomic::Ordering::Relaxed),
    before
  );
}

#[test]
fn cached_projection_validation_preserves_every_owner_shape_refusal() {
  use ixon::constant::{
    Constructor, Inductive, Recursor, ctor_proj_constant, indc_proj_constant,
    recr_proj_constant,
  };
  let env = Env::new();
  let ConstantInfo::Defn(definition) = record(0, true).info else {
    unreachable!()
  };
  let ctor = |cidx| Constructor {
    is_unsafe: false,
    lvls: 0,
    cidx,
    params: 0,
    fields: 0,
    typ: Arc::new(Expr::Sort(0)),
  };
  let owner = store(
    &env,
    Constant::with_tables(
      ConstantInfo::Muts(vec![
        MutConst::Defn(definition),
        MutConst::Indc(Inductive {
          is_unsafe: true,
          lvls: 0,
          params: 0,
          indices: 0,
          typ: Arc::new(Expr::Sort(0)),
          ctors: vec![ctor(0), ctor(7)],
        }),
        MutConst::Recr(Recursor {
          k: false,
          is_unsafe: false,
          lvls: 0,
          params: 0,
          indices: 0,
          motives: 0,
          minors: 0,
          typ: Arc::new(Expr::Sort(0)),
          rules: vec![],
        }),
      ]),
      vec![],
      vec![],
      vec![Univ::zero()],
    ),
  );
  let other = store(&env, record(0, false));
  let mut with_tables = defn_proj_constant(0, owner.clone());
  with_tables.refs.push(other.clone());
  let cases = [
    (defn_proj_constant(0, owner.clone()), true),
    (indc_proj_constant(1, owner.clone()), true),
    (ctor_proj_constant(1, 0, owner.clone()), true),
    (recr_proj_constant(2, owner.clone()), true),
    (ctor_proj_constant(1, 1, owner.clone()), false),
    (ctor_proj_constant(1, 2, owner.clone()), false),
    (defn_proj_constant(1, owner.clone()), false),
    (indc_proj_constant(0, owner.clone()), false),
    (recr_proj_constant(3, owner.clone()), false),
    (defn_proj_constant(u64::MAX, owner.clone()), false),
    (defn_proj_constant(0, other), false),
    (with_tables, false),
  ]
  .map(|(c, valid)| (store(&env, c), valid));
  let source = ArtifactSource::prepare(env).unwrap();
  // Warm the layout from authenticated bytes before trying bad projections.
  source.authenticate_reference(&cases[0].0).unwrap();
  for (address, valid) in cases {
    let payload = source.member(&address).map(|_| ());
    let cached = source.authenticate_reference(&address);
    assert_eq!(payload, cached);
    assert_eq!(cached.is_ok(), valid);
  }
  assert!(
    source.in_safety_tier(&ixon::constant::ctor_proj_address(1, 0, &owner))
  );
}

#[test]
fn owner_layouts_require_authentic_canonical_bytes() {
  let make_source = |owner: Address, raw: LazyConstant| {
    let env = Env::new();
    env.consts.insert(owner.clone(), raw);
    let projection = store(&env, defn_proj_constant(0, owner));
    (ArtifactSource::prepare(env).unwrap(), projection)
  };
  let ConstantInfo::Defn(d) = record(0, true).info else { unreachable!() };
  let mut block = Constant::new(ConstantInfo::Muts(vec![MutConst::Defn(d)]));
  block.univs.push(Univ::zero());
  let (_, mut bytes) = block.commit();
  let (source, projection) = make_source(
    Address::hash(b"forged owner key"),
    LazyConstant::from_constant(block),
  );
  assert!(matches!(
    source.authenticate_reference(&projection),
    Err(Error::Record(_, _))
  ));
  assert!(source.0.owner_layouts.is_empty());
  bytes.push(0);
  let (source, projection) =
    make_source(Address::hash(&bytes), LazyConstant::from_bytes(bytes.into()));
  assert!(matches!(
    source.authenticate_reference(&projection),
    Err(Error::Record(_, _))
  ));
  assert!(source.0.owner_layouts.is_empty());
}

#[test]
fn rehashed_trailing_record_bytes_are_not_canonical_records() {
  let env = Env::new();
  let (_, mut bytes) = record(0, false).commit();
  bytes.push(0);
  let address = Address::hash(&bytes);
  env.consts.insert(address.clone(), LazyConstant::from_bytes(bytes.into()));
  assert!(matches!(
    ArtifactSource::prepare(env).unwrap().record(&address),
    Err(Error::Record(_, _))
  ));
}

// from_serialized deliberately debug-asserts cache consistency. Exercise the
// release boundary without weakening that assertion or adding a forge API.
#[cfg(not(debug_assertions))]
#[test]
fn materialized_cache_cannot_replace_authenticated_payload_in_release() {
  let env = Env::new();
  for (cached, actual) in
    [(record(0, true), record(1, false)), (record(0, false), record(1, true))]
  {
    let (address, bytes) = actual.commit();
    env.consts.insert(
      address.clone(),
      LazyConstant::from_serialized(cached.clone(), bytes.clone(), true),
    );
    assert_eq!(
      env.consts.get(&address).unwrap().get().unwrap().as_ref(),
      &cached
    );
    let source = ArtifactSource::snapshot(&env).unwrap();
    let observed = source.record(&address).unwrap();
    assert_eq!(observed.bytes(), bytes);
    assert_eq!(observed.constant(), &actual);
    assert_eq!(
      source.proof_record(&address).is_ok(),
      matches!(actual.info, ConstantInfo::Defn(_))
    );
  }
}

#[test]
fn verdict_closure_includes_role_binding_support_and_evidence() {
  let (mut env, mut table) = full_candidate();
  let helper_addr = store(&env, record(200, false));

  let mut role_const = record(201, false);
  role_const.refs.push(helper_addr.clone());
  let role_addr = store(&env, role_const);
  table.bound.iter_mut().find(|(r, _)| *r == Role::Char).unwrap().1 =
    role_addr.clone();
  bind(&mut env, &table);

  let target_addr = store(&env, record(202, false));

  let source = ArtifactSource::snapshot(&env).unwrap();
  let closure =
    source.verdict_closure(std::slice::from_ref(&target_addr)).unwrap();
  assert!(closure.contains(&target_addr));
  assert!(closure.contains(&role_addr));
  assert!(closure.contains(&helper_addr));
  for (_, entries) in &table.evidence {
    for entry in entries {
      if let Evidence::Proof(proof_addr) = entry {
        assert!(closure.contains(proof_addr));
      }
    }
  }
}
