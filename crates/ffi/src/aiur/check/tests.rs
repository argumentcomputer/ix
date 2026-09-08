use super::*;
use ix_kernel::shard::{AggNode, ShardInfo};
use ixon::{Constant, constant::Axiom, expr::Expr};

fn store(env: &Env, constant: &Constant) -> Address {
  let mut bytes = Vec::new();
  constant.put(&mut bytes);
  let addr = Address::hash(&bytes);
  // Test the actual lazy full-parse path, not the compile-side cached value.
  env.store_const_lazy(addr.clone(), Arc::from(bytes));
  addr
}

fn axiom(env: &Env, level: u64) -> Address {
  store(
    env,
    &Constant {
      info: ConstantInfo::Axio(Axiom {
        is_unsafe: false,
        lvls: level,
        typ: Expr::sort(0),
      }),
      sharing: Vec::new(),
      refs: Vec::new(),
      univs: Vec::new(),
    },
  )
}

fn manifest(lists: Vec<Vec<Address>>) -> ShardManifest {
  ShardManifest {
    num_shards: u32::try_from(lists.len()).unwrap(),
    shards: lists
      .into_iter()
      .enumerate()
      .map(|(id, blocks)| ShardInfo {
        id: u32::try_from(id).unwrap(),
        blocks,
        heartbeats: 0,
        own_size: 0,
        foreign_blocks: Vec::new(),
        cross_ingress: 0,
        assumption_root: None,
        measured_peak_bytes: 0,
      })
      .collect(),
    total_cross_ingress: 0,
    tree: None,
  }
}

#[test]
fn native_ownership_covers_every_constant_and_preserves_empty_leaves() {
  let env = Env::new();
  let a = axiom(&env, 0);
  let b = axiom(&env, 1);
  let m = manifest(vec![vec![a.clone()], vec![], vec![b.clone()]]);
  assert_eq!(prepare_owned(&env, &m).unwrap(), vec![vec![a], vec![], vec![b]]);
}

#[test]
fn every_projection_variant_is_owned_with_its_block() {
  use ixon::constant::{
    ctor_proj_constant, defn_proj_constant, indc_proj_constant,
    recr_proj_constant,
  };
  let env = Env::new();
  // This test exercises scheduling, not semantic validity of the block.
  // Only IxVM execution may certify that the projection itself is well typed.
  let block = axiom(&env, 0);
  let projections = [
    indc_proj_constant(0, block.clone()),
    ctor_proj_constant(0, 0, block.clone()),
    recr_proj_constant(0, block.clone()),
    defn_proj_constant(0, block.clone()),
  ]
  .map(|constant| store(&env, &constant));
  let mut expected = vec![block.clone()];
  expected.extend(projections.iter().cloned());
  expected.sort_unstable();
  let owned =
    prepare_owned(&env, &manifest(vec![vec![], vec![block.clone()]])).unwrap();
  assert_eq!(owned, vec![vec![], expected]);
  // Listing wrapper addresses cannot substitute for owning their block.
  assert!(prepare_owned(&env, &manifest(vec![projections.to_vec()])).is_err());
  env.consts.remove(&block);
  assert!(prepare_owned(&env, &manifest(vec![projections.to_vec()])).is_err());
}

#[test]
fn native_ownership_rejects_duplicate_blocks_even_within_one_shard() {
  let env = Env::new();
  let a = axiom(&env, 0);
  for lists in
    [vec![vec![a.clone(), a.clone()]], vec![vec![a.clone()], vec![a]]]
  {
    assert!(
      prepare_owned(&env, &manifest(lists))
        .unwrap_err()
        .contains("owned more than once")
    );
  }
}

#[test]
fn native_ownership_rejects_gaps_empty_manifests_and_noncanonical_ids() {
  let env = Env::new();
  let a = axiom(&env, 0);
  assert!(
    prepare_owned(&env, &manifest(vec![vec![]]))
      .unwrap_err()
      .contains("no owning shard")
  );
  assert!(
    prepare_owned(&env, &manifest(vec![])).unwrap_err().contains("no shards")
  );
  let mut m = manifest(vec![vec![a]]);
  m.shards[0].id = 42;
  assert!(prepare_owned(&env, &m).unwrap_err().contains("entry 0 has id 42"));
}

#[test]
fn native_ownership_rejects_unreferenced_malformed_bodies() {
  let env = Env::new();
  let good = axiom(&env, 0);
  let bytes = vec![0xff];
  let bad = Address::hash(&bytes);
  env.store_const_lazy(bad.clone(), Arc::from(bytes));
  let error =
    prepare_owned(&env, &manifest(vec![vec![good, bad]])).unwrap_err();
  assert!(error.contains("cannot parse constant"), "{error}");
}

#[test]
fn native_ownership_rejects_hash_mismatches_and_trailing_constant_bytes() {
  let env = Env::new();
  let good = axiom(&env, 0);
  let mut bytes = env.get_const_bytes(&good).unwrap().to_vec();
  bytes.push(0);
  env.store_const_lazy(good.clone(), Arc::from(bytes.clone()));
  assert!(
    prepare_owned(&env, &manifest(vec![vec![good.clone()]]))
      .unwrap_err()
      .contains("content-address mismatch")
  );
  env.consts.remove(&good);
  let bad = Address::hash(&bytes);
  env.store_const_lazy(bad.clone(), Arc::from(bytes));
  assert!(
    prepare_owned(&env, &manifest(vec![vec![bad]]))
      .unwrap_err()
      .contains("trailing")
  );
}

#[test]
fn native_ownership_and_error_order_are_deterministic_across_pool_widths() {
  let env = Env::new();
  let mut addresses: Vec<_> = (0..40).map(|i| axiom(&env, i)).collect();
  addresses.sort_unstable();
  let m = manifest(vec![addresses.iter().cloned().rev().collect()]);
  let run = |width, manifest: &ShardManifest| {
    rayon::ThreadPoolBuilder::new()
      .num_threads(width)
      .build()
      .unwrap()
      .install(|| prepare_owned(&env, manifest))
  };
  assert_eq!(run(1, &m).unwrap(), run(4, &m).unwrap());
  assert_eq!(run(4, &m).unwrap()[0], addresses);
  let missing = manifest(vec![vec![]]);
  assert_eq!(run(1, &missing).unwrap_err(), run(4, &missing).unwrap_err());
}

#[test]
fn native_manifest_decoder_rejects_malformed_framing() {
  let env = Env::new();
  let a = axiom(&env, 0);
  let m = manifest(vec![vec![a]]);
  let valid = m.to_bytes();
  assert_eq!(ShardManifest::from_bytes(&valid).unwrap(), m);
  let mut trailing = valid.clone();
  trailing.push(0);
  assert!(ShardManifest::from_bytes(&trailing).is_err());
  // Header(28), id(4), three u64 fields(24), assumption-root tag.
  let mut bad_tag = valid.clone();
  bad_tag[56] = 2;
  assert!(ShardManifest::from_bytes(&bad_tag).is_err());
  let mut huge_count = valid.clone();
  huge_count[24..28].copy_from_slice(&u32::MAX.to_le_bytes());
  assert!(ShardManifest::from_bytes(&huge_count).is_err());
  // The writer prunes unknown tree leaves. Corrupt the bytes of a valid
  // serialized tree instead, so this actually reaches the reader's check.
  let mut with_tree = m;
  with_tree.tree = Some(AggNode::Leaf(0));
  let mut bad_tree = with_tree.to_bytes();
  let leaf_offset = bad_tree.len() - 5;
  bad_tree[leaf_offset..leaf_offset + 4].copy_from_slice(&7u32.to_le_bytes());
  assert!(ShardManifest::from_bytes(&bad_tree).is_err());
  let mut bad_presence = valid.clone();
  let tree_offset = bad_presence.len() - 2;
  bad_presence[tree_offset] = 2;
  assert!(ShardManifest::from_bytes(&bad_presence).is_err());
  let mut bad_peak_presence = valid;
  *bad_peak_presence.last_mut().unwrap() = 2;
  assert!(ShardManifest::from_bytes(&bad_peak_presence).is_err());
}

#[test]
fn native_report_keeps_claim_identity_and_rejected_leaf_details() {
  let env = Env::new();
  let address = axiom(&env, 0);
  let m = manifest(vec![vec![address.clone()]]);
  let owned = prepare_owned(&env, &m).unwrap();
  let (claim, _) =
    ixon::shard_claim::shard_check_env_claim(&env, &owned[0]).unwrap();
  let mut bytes = Vec::new();
  claim.put(&mut bytes);
  let digest = Address::hash(&bytes);
  let config = RunConfig {
    ixe: Path::new("fixture.ixe"),
    manifest: Path::new("fixture.ixes"),
    jobs: 2,
    use_bytecode: true,
    report: "report.json",
    revision: "test",
    command: "ix check",
    budget_source: "none",
  };
  let loaded = LoadedEnv {
    env,
    names: [(address.clone(), "Fixture.marker".to_owned())]
      .into_iter()
      .collect(),
    bytes: 42,
  };
  let results = [ShardCheckResult {
    error: "expected rejection".into(),
    peak_bytes: 0,
    suggested_parts: 1,
    claim: Some(digest.clone()),
  }];
  let report =
    audit_report(&config, &loaded, &m, &m.to_bytes(), &owned, &results);
  assert_eq!(report["leaves"][0]["claim"], digest.hex());
  assert_eq!(report["leaves"][0]["status"], "failed");
  assert_eq!(report["failures"][0]["block"], address.hex());
  assert_eq!(report["failures"][0]["names"][0], "Fixture.marker");
  assert_eq!(report["selected"], 1);
  assert_eq!(report["executed"], 1);
}

/// Release-mode setup benchmark for external corpora. Deliberately does not
/// execute shards: it can measure the new loader/coverage pass alongside a
/// running baseline without creating a second set of execution records.
#[test]
#[ignore = "requires IX_TEST_PARTITION_IXE and IX_TEST_PARTITION_IXES"]
fn large_fixture_setup_only() {
  let ixe =
    std::env::var("IX_TEST_PARTITION_IXE").expect("IX_TEST_PARTITION_IXE");
  let ixes =
    std::env::var("IX_TEST_PARTITION_IXES").expect("IX_TEST_PARTITION_IXES");
  let started = Instant::now();
  let manifest = ShardManifest::from_bytes(&fs::read(&ixes).unwrap()).unwrap();
  let loaded = load_env(Path::new(&ixe), true).unwrap();
  let loaded_at = Instant::now();
  let owned = prepare_owned(&loaded.env, &manifest).unwrap();
  let total: usize = owned.iter().map(Vec::len).sum();
  assert_eq!(total, loaded.env.consts.len());
  eprintln!(
    "[ixvm_setup_bench] {} constants, {} shards; load {:.3}s; coverage/ownership {:.3}s; total {:.3}s; execution NOT run",
    total,
    owned.len(),
    (loaded_at - started).as_secs_f64(),
    loaded_at.elapsed().as_secs_f64(),
    started.elapsed().as_secs_f64()
  );
}
