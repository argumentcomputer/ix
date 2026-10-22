use super::*;
use ix_common::env::DefinitionSafety;
use ixon::constant::{
  ctor_proj_constant, defn_proj_constant, indc_proj_constant,
  recr_proj_constant,
};
use ixon::metadata::ConstantMeta;
use ixon::{Comm, Constructor, Definition, Expr, Inductive, Named, Recursor};

fn payload(c: &Constant) -> Payload {
  let (addr, bytes) = c.commit();
  Payload { addr, bytes: bytes.into() }
}

fn definition(kind: DefKind) -> Definition {
  Definition {
    kind,
    safety: DefinitionSafety::Safe,
    lvls: 0,
    typ: Arc::new(Expr::Sort(0)),
    value: Arc::new(Expr::Sort(0)),
  }
}

// Unavailable and explicitly absent hints are intentionally different cases.
#[allow(clippy::option_option)]
fn fixture(
  original: Payload,
  block: Option<Payload>,
  hints: Option<Option<ReducibilityHints>>,
) -> (Env, Receipt) {
  let mut env = Env::new();
  let canonical = payload(&Constant::new(ConstantInfo::Muts(vec![])));
  env
    .consts
    .insert(canonical.addr.clone(), LazyConstant::from_bytes(canonical.bytes));
  let name = Name::str(Name::anon(), "original".into());
  env.store_name(Address::from_blake3_hash(*name.get_hash()), name.clone());
  let mut named = Named::with_addr(canonical.addr.clone());
  named.set_original(original.addr.clone(), ConstantMeta::default());
  named.set_hints(Some(ReducibilityHints::Abbrev));
  env.register_name(name.clone(), named);
  env.blobs.insert(Address::hash(&[3]), vec![3]);
  env.comms.insert(
    Address::hash(b"comm"),
    Comm { secret: canonical.addr.clone(), payload: canonical.addr.clone() },
  );
  env.main = Some(canonical.addr.clone());
  env.assumptions.insert(Address::hash(b"assumed"));
  env.anon_hints.insert(canonical.addr.clone(), ReducibilityHints::Opaque);
  (env, Receipt { name, published: canonical.addr, original, hints, block })
}

fn wire(env: &Env) -> Vec<u8> {
  let mut out = Vec::new();
  env.put(&mut out).unwrap();
  out
}

#[test]
fn actual_kinds_and_every_projection_variant_are_checked() {
  for kind in [DefKind::Definition, DefKind::Theorem, DefKind::Opaque] {
    let d = definition(kind);
    let block =
      payload(&Constant::new(ConstantInfo::Muts(vec![MutConst::Defn(
        d.clone(),
      )])));
    for (original, block) in [
      (payload(&Constant::new(ConstantInfo::Defn(d))), None),
      (payload(&defn_proj_constant(0, block.addr.clone())), Some(block)),
    ] {
      let (mut env, row) = fixture(original, block, Some(None));
      let result = finalize_originals(std::slice::from_ref(&row), &mut env);
      if kind == DefKind::Definition {
        assert!(result.unwrap_err().contains("missing definition hints"));
      } else {
        result.unwrap();
        assert_eq!(
          env.original_hint_overrides.get(&row.name).map(|h| *h),
          Some(None)
        );
      }
    }
  }
  let typ = Arc::new(Expr::Sort(0));
  let ind = Inductive {
    is_unsafe: false,
    lvls: 0,
    params: 0,
    indices: 0,
    typ: typ.clone(),
    ctors: vec![Constructor {
      is_unsafe: false,
      lvls: 0,
      cidx: 0,
      params: 0,
      fields: 0,
      typ: typ.clone(),
    }],
  };
  let rec = Recursor {
    k: false,
    is_unsafe: false,
    lvls: 0,
    params: 0,
    indices: 0,
    motives: 0,
    minors: 0,
    typ,
    rules: vec![],
  };
  let block = payload(&Constant::new(ConstantInfo::Muts(vec![
    MutConst::Defn(definition(DefKind::Theorem)),
    MutConst::Indc(ind),
    MutConst::Recr(rec),
  ])));
  let ctor = |i, b| ctor_proj_constant(i, 0, b);
  let makers: [fn(u64, Address) -> Constant; 4] =
    [defn_proj_constant, indc_proj_constant, recr_proj_constant, ctor];
  for (make, correct, wrong) in
    [(makers[0], 0, 1), (makers[1], 1, 0), (makers[2], 2, 0), (makers[3], 1, 0)]
  {
    for (index, error) in [
      (correct, None),
      (wrong, Some("member kind mismatch")),
      (3, Some("projection index out of range")),
      (u64::MAX, Some("projection index out of range")),
    ] {
      let (mut env, row) = fixture(
        payload(&make(index, block.addr.clone())),
        Some(block.clone()),
        Some(None),
      );
      let result = finalize_originals(&[row], &mut env);
      match error {
        None => result.unwrap(),
        Some(message) => assert!(result.unwrap_err().contains(message)),
      }
    }
  }
  let (mut env, row) = fixture(
    payload(&ctor_proj_constant(1, 1, block.addr.clone())),
    Some(block.clone()),
    Some(None),
  );
  assert!(
    finalize_originals(&[row], &mut env)
      .unwrap_err()
      .contains("constructor index")
  );
  let (mut env, row) = fixture(
    payload(&indc_proj_constant(1, block.addr.clone())),
    None,
    Some(None),
  );
  assert!(
    finalize_originals(&[row], &mut env)
      .unwrap_err()
      .contains("missing projection block")
  );
}

#[test]
fn exact_bytes_hints_frame_and_stale_receipts() {
  let original = payload(&Constant::new(ConstantInfo::Defn(definition(
    DefKind::Definition,
  ))));
  let (base, row) =
    fixture(original, None, Some(Some(ReducibilityHints::Regular(7))));
  let mut env = base.clone();
  finalize_originals(&[row.clone(), row.clone()], &mut env).unwrap();
  assert_eq!(env.originals.len(), 1);
  assert!(!env.originals.get(&row.original.addr).unwrap().is_materialized());
  assert_eq!(
    env.original_hint_overrides.get(&row.name).map(|x| *x),
    Some(Some(ReducibilityHints::Regular(7)))
  );
  let core = env.clone();
  core.originals.clear();
  core.original_hint_overrides.clear();
  assert_eq!(wire(&core), wire(&base));
  let before = wire(&env);
  let mut bad = row.clone();
  bad.original.bytes = Arc::from([0xff]);
  for rows in [vec![row.clone(), bad.clone()], vec![bad.clone(), row.clone()]] {
    assert!(
      finalize_originals(&rows, &mut env)
        .unwrap_err()
        .contains("conflicting captured bytes")
    );
    assert_eq!(wire(&env), before);
  }
  let mut overlap = base.clone();
  overlap.consts.insert(
    row.original.addr.clone(),
    LazyConstant::from_bytes(Arc::from([0xff])),
  );
  assert!(
    finalize_originals(std::slice::from_ref(&row), &mut overlap)
      .unwrap_err()
      .contains("conflicting canonical bytes")
  );
  let mut unavailable = row.clone();
  unavailable.hints = None;
  assert!(
    finalize_originals(&[unavailable], &mut env)
      .unwrap_err()
      .contains("unavailable original hints")
  );
  let mut other_hint = row.clone();
  other_hint.hints = Some(Some(ReducibilityHints::Opaque));
  let forward =
    finalize_originals(&[row.clone(), other_hint.clone()], &mut env)
      .unwrap_err();
  assert_eq!(
    finalize_originals(&[other_hint, row.clone()], &mut env).unwrap_err(),
    forward
  );
  let mut rebound = row.clone();
  rebound.published = Address::hash(b"other publication");
  assert!(
    finalize_originals(&[rebound], &mut env)
      .unwrap_err()
      .contains("missing receipt")
  );
  let mut spoof = row.clone();
  spoof.name = Name(Arc::new(NameData::Str(
    Name::anon(),
    "spoof".into(),
    *row.name.get_hash(),
  )));
  assert!(
    finalize_originals(&[spoof], &mut env)
      .unwrap_err()
      .contains("missing receipt")
  );
  let mut withdrawn = base.clone();
  withdrawn.named.remove(&row.name);
  finalize_originals(&[bad], &mut withdrawn).unwrap();
  assert!(
    withdrawn.originals.is_empty()
      && withdrawn.original_hint_overrides.is_empty()
  );
  let mut same = row.clone();
  same.original.addr = same.published.clone();
  same.original.bytes =
    base.consts.get(&same.published).unwrap().raw_bytes().into();
  same.hints = Some(Some(ReducibilityHints::Abbrev));
  let mut unchanged = base.clone();
  unchanged
    .named
    .get_mut(&same.name)
    .unwrap()
    .set_original(same.original.addr.clone(), ConstantMeta::default());
  let legacy = wire(&unchanged);
  finalize_originals(&[same], &mut unchanged).unwrap();
  assert_eq!(wire(&unchanged), legacy);
  assert!(
    unchanged.originals.is_empty()
      && unchanged.original_hint_overrides.is_empty()
  );
}
