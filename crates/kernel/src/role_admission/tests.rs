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
      let (count, defeq) = evidence_shape(role);
      (count != 0).then(|| {
        (
          role,
          vec![
            if defeq {
              Evidence::DefEq
            } else {
              Evidence::Proof(proof.clone())
            };
            count
          ],
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
    "# Role.block/deps and Spec.evidenceKinds, version{SPEC_VERSION}\n"
  );
  let indices = |roles: &[Role]| {
    roles.iter().map(|r| r.index().to_string()).collect::<Vec<_>>().join(",")
  };
  for role in Role::ALL {
    let (count, defeq) = evidence_shape(role);
    let kinds = vec![if defeq { "defeq" } else { "proof" }; count].join(",");
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
  assert_eq!(parent.constant().refs, [bad.clone()]);
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
