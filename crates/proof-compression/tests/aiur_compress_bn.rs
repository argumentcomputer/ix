use aiur::{artifact::WidePackage, field::FieldBackend};
use ark_bn254::G1Affine;
use ark_ec::AffineRepr;
use ix_proof_compression::{
  aiur_backend::{
    Bn254,
    compress_bn::{
      Accumulator, Input, PolicyDigest, PublicInputs, Stage, StatementDigest,
      TraceLimits, Wrapper,
    },
    kzg::VerifyingKey,
    kzg_advice as wire,
  },
  kzg::{KzgConfig, Scalar, Srs},
};
use multi_stark::{
  config::ProofConfig,
  expr::Expr,
  lookup::Lookup,
  system::{CircuitInputs, System, SystemWitness},
};
use p3_matrix::dense::RowMajorMatrix;
use std::{path::PathBuf, sync::Arc};

const CAP: usize = 1 << 24;

fn srs(height: usize) -> Arc<Srs> {
  Arc::new(Srs::unsafe_dev_setup_prefix(
    height,
    CAP - 1,
    b"compress-bn-host-tests",
  ))
}

struct Fixture {
  key: Vec<u8>,
  claims: Vec<u8>,
  proof: Vec<u8>,
  policy: Vec<u8>,
  public: PublicInputs,
}

impl Fixture {
  fn new() -> Self {
    let statement = StatementDigest::new(
      *blake3::hash(b"CompressBN host statement").as_bytes(),
    );
    let mut claim = vec![Bn254.one(), Bn254.from_u64(31)];
    claim.extend([Bn254.zero(); 8]);
    claim.extend(wire::digest_words(statement.as_bytes()));
    let input = CircuitInputs {
      main_width: 1,
      constraints: vec![Expr::main(0) - Expr::constant(Bn254.one())],
      lookups: vec![Lookup::pull(
        Expr::main(0),
        claim.iter().copied().map(Expr::constant).collect(),
      )],
      ..Default::default()
    };
    let (system, prover) =
      System::new(KzgConfig::with_max_trace_len(srs(64), CAP, 8), [input]);
    let witness = SystemWitness::from_stage_1(
      vec![RowMajorMatrix::new_col(vec![Bn254.one()])],
      &system,
    );
    let proof = system.prove(&prover, &claim, witness);
    system.verify(&claim, &proof).unwrap();
    let key =
      wire::key_bytes(&VerifyingKey::from_system(&system).unwrap()).unwrap();
    let digest = *blake3::hash(&key).as_bytes();
    let policy = wire::Policy::new(
      system.config.pcs().verifier_params(),
      digest,
      31,
      digest,
      31,
    )
    .unwrap();
    Self {
      key,
      claims: wire::claims_bytes(&[claim]).unwrap(),
      proof: wire::proof_bytes(&proof).unwrap(),
      policy: policy.to_bytes(),
      public: PublicInputs {
        policy: PolicyDigest::from_trusted(policy.digest()),
        stage: Stage::FIRST,
        statement,
      },
    }
  }

  fn input(&self) -> Result<Input, String> {
    Input::from_source(
      self.public,
      self.key.clone(),
      self.claims.clone(),
      self.proof.clone(),
      self.policy.clone(),
    )
  }
}

fn artifact() -> Vec<u8> {
  let path = std::env::var_os("IX_AIUR_KZG_SOURCE_ARTIFACT").map_or_else(
    || {
      PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../aiur/tests/fixtures/kzg-source.ixa")
    },
    PathBuf::from,
  );
  std::fs::read(path).unwrap()
}

#[test]
fn source_input_authenticates_policy_key_anchors_and_exact_predecessor_call() {
  let mut fixture = Fixture::new();
  fixture.input().unwrap();

  fixture.public.policy = PolicyDigest::from_trusted([0; 32]);
  assert!(fixture.input().err().unwrap().contains("trusted pin"));
  fixture.public.policy =
    PolicyDigest::from_trusted(*blake3::hash(&fixture.policy).as_bytes());
  fixture.key[0] ^= 1;
  assert!(fixture.input().err().unwrap().contains("predecessor key"));
  fixture.key[0] ^= 1;

  fixture.policy[8] ^= 1;
  fixture.public.policy =
    PolicyDigest::from_trusted(*blake3::hash(&fixture.policy).as_bytes());
  assert!(fixture.input().err().unwrap().contains("SRS anchors"));
  fixture.policy[8] ^= 1;
  fixture.public.policy =
    PolicyDigest::from_trusted(*blake3::hash(&fixture.policy).as_bytes());

  for index in [16, 48, 80, 16 + 10 * 32] {
    fixture.claims[index] ^= 1;
    assert!(fixture.input().is_err(), "accepted changed claim byte {index}");
    fixture.claims[index] ^= 1;
  }
  fixture.claims.extend([0; 32]);
  assert!(fixture.input().is_err());
  fixture.claims.truncate(fixture.claims.len() - 32);
  fixture.claims[16..48].fill(255);
  assert!(fixture.input().is_err());
}

#[test]
fn recursive_public_call_rejects_stage_gaps_and_noncanonical_accumulators() {
  let mut fixture = Fixture::new();
  fixture.public.stage = Stage::new(2).unwrap();
  let accumulator =
    Accumulator::from_points(&[G1Affine::generator(), G1Affine::identity()])
      .unwrap();
  let previous = PublicInputs { stage: Stage::FIRST, ..fixture.public };
  let mut claim = vec![Bn254.one(), Bn254.from_u64(31)];
  claim.extend(previous.arguments());
  claim.extend(accumulator.words());
  fixture.claims = wire::claims_bytes(&[claim.clone()]).unwrap();
  fixture.input().unwrap();
  fixture.public.stage = Stage::new(3).unwrap();
  assert!(fixture.input().is_err());
  fixture.public.stage = Stage::new(2).unwrap();
  claim[19] = Scalar(ark_bn254::Fr::from(u128::MAX)) + Bn254.one();
  fixture.claims = wire::claims_bytes(&[claim]).unwrap();
  assert!(fixture.input().is_err());
  assert!(Stage::new(0).is_err());
  assert!(Stage::new(u32::MAX).unwrap().next().is_err());
}

#[test]
fn native_accumulator_check_rejects_wrong_points_and_anchors() {
  let setup = srs(4);
  let config = KzgConfig::with_max_trace_len(Arc::clone(&setup), CAP, 8);
  let parameters = config.pcs().verifier_params();
  let valid = Accumulator::from_points(&[setup.g1[1], -setup.g1[0]]).unwrap();
  valid.check_pairing(parameters).unwrap();
  let invalid = Accumulator::from_points(&[setup.g1[1], setup.g1[0]]).unwrap();
  assert!(invalid.check_pairing(parameters).is_err());
  let other =
    KzgConfig::new(Arc::new(Srs::unsafe_dev_setup(4, b"other anchors")), 8);
  assert!(valid.check_pairing(other.pcs().verifier_params()).is_err());
  let mut invalid_setup = Srs::unsafe_dev_setup(4, b"invalid anchors");
  invalid_setup.g2 = ark_bn254::G2Affine::identity();
  let invalid_parameters =
    ix_proof_compression::kzg::VerifierParams::from_srs(&invalid_setup);
  assert!(valid.check_pairing(&invalid_parameters).is_err());
  Accumulator::from_points(&[G1Affine::identity(); 2])
    .unwrap()
    .check_pairing(parameters)
    .unwrap();
}

#[test]
fn wrapper_pins_artifact_bounds_execution_and_profiles_without_traces() {
  let bytes = artifact();
  assert!(Wrapper::from_bytes(&bytes, &[0; 32]).is_err());
  let wrapper =
    Wrapper::from_bytes(&bytes, blake3::hash(&bytes).as_bytes()).unwrap();
  let mut fixture = Fixture::new();
  fixture.policy[204..208]
    .copy_from_slice(&wrapper.entry().wrapping_add(1).to_le_bytes());
  fixture.public.policy =
    PolicyDigest::from_trusted(*blake3::hash(&fixture.policy).as_bytes());
  let input = fixture.input().unwrap();
  assert!(wrapper.execute(&input, 0).is_err());
  let error = wrapper.execute(&input, 1).err().unwrap();
  assert!(error.contains("limit"), "{error}");
  let execution = wrapper.execute(&input, 512 << 20).unwrap();
  let claim =
    wrapper.claim(input.public_inputs(), execution.accumulator()).unwrap();
  assert_eq!(claim.len(), 23);
  assert_eq!(claim[1], Bn254.from_u64(u64::from(wrapper.entry())));
  assert_eq!(&claim[2..19], &input.public_inputs().arguments());
  assert_eq!(&claim[19..], execution.accumulator().words());
  let profile = wrapper.profile(&execution).unwrap();
  assert!(profile.instructions > 0 && profile.main_fixed_lookup_bytes > 0);
  let limits =
    TraceLimits { max_height: 2, max_total_rows: 1, max_trace_bytes: 1 };
  let config =
    KzgConfig::with_max_trace_len(srs(64), CAP, 8).with_streaming_lookups();
  let error = limits.check(&profile, &config).unwrap_err();
  assert!(
    error.contains(&format!(
      "trace bytes {} / 1",
      profile.main_fixed_lookup_bytes
    ))
  );
  assert!(
    wrapper
      .prove(&execution, KzgConfig::with_max_trace_len(srs(64), CAP, 8), limits)
      .is_err()
  );

  let error = wrapper
    .prove(
      &execution,
      config,
      TraceLimits {
        max_height: profile.max_height,
        max_total_rows: profile.total_rows,
        max_trace_bytes: profile.main_fixed_lookup_bytes,
      },
    )
    .err()
    .unwrap();
  assert!(error.contains("proving configuration differs"), "{error}");

  let mut variant = WidePackage::decode(&bytes).unwrap();
  variant.program.tables[0].name.push_str("_metadata_variant");
  let variant = variant.encode().unwrap();
  let other =
    Wrapper::from_bytes(&variant, blake3::hash(&variant).as_bytes()).unwrap();
  assert!(other.profile(&execution).is_err());
}

#[test]
fn wrapper_preflights_proving_powers_and_materialized_lookup_storage() {
  let bytes = artifact();
  let wrapper =
    Wrapper::from_bytes(&bytes, blake3::hash(&bytes).as_bytes()).unwrap();
  let config = KzgConfig::with_max_trace_len(srs(64), CAP, 8);
  let streaming = config.clone().with_streaming_lookups();
  let verifier_only =
    KzgConfig::verifier_only(config.pcs().verifier_params().clone(), 8)
      .with_streaming_lookups();
  let error = wrapper.verifying_key(verifier_only.clone()).err().unwrap();
  assert!(error.contains("requires a loaded SRS prefix"), "{error}");
  let error = wrapper.verifying_key(streaming.clone()).err().unwrap();
  assert!(error.contains("loaded SRS prefix is too short"), "{error}");

  let mut fixture = Fixture::new();
  fixture.policy[204..208].copy_from_slice(&wrapper.entry().to_le_bytes());
  fixture.public.policy =
    PolicyDigest::from_trusted(*blake3::hash(&fixture.policy).as_bytes());
  let input = fixture.input().unwrap();
  let execution = wrapper.execute(&input, 512 << 20).unwrap();
  let profile = wrapper.profile(&execution).unwrap();
  let limits = TraceLimits {
    max_height: profile.max_height,
    max_total_rows: profile.total_rows,
    max_trace_bytes: profile.main_fixed_lookup_bytes,
  };
  let materialized = profile.trace_bytes(&config).unwrap();
  assert_eq!(
    materialized - limits.max_trace_bytes,
    profile.concrete_lookup_cells * size_of::<Scalar>()
  );
  assert!(materialized > limits.max_trace_bytes);
  limits.check(&profile, &streaming).unwrap();
  let error = wrapper.prove(&execution, config, limits).err().unwrap();
  assert!(
    error.contains(&format!(
      "trace bytes {materialized} / {}",
      limits.max_trace_bytes
    )),
    "{error}"
  );
  let error = wrapper.prove(&execution, streaming, limits).err().unwrap();
  assert!(
    error
      .contains(&format!("required {} powers, loaded 64", profile.max_height)),
    "{error}"
  );
  let error = wrapper.prove(&execution, verifier_only, limits).err().unwrap();
  assert!(error.contains("requires a loaded SRS prefix"), "{error}");
}

#[test]
#[ignore = "full source compression proof; run explicitly after trace resource preflight"]
fn wrapper_proves_and_exports_the_same_deferred_public_call() {
  let bytes = artifact();
  let wrapper =
    Wrapper::from_bytes(&bytes, blake3::hash(&bytes).as_bytes()).unwrap();
  let config = |height| {
    KzgConfig::with_max_trace_len(srs(height), CAP, 8)
      .with_streaming_lookups()
      .with_streaming_quotient()
  };
  let keys = wrapper.verifying_key(config(1 << 16)).unwrap();
  let mut fixture = Fixture::new();
  let policy = wire::Policy::new(
    config(64).pcs().verifier_params(),
    *blake3::hash(&fixture.key).as_bytes(),
    31,
    keys.source_digest(),
    keys.entry,
  )
  .unwrap();
  fixture.public.policy = PolicyDigest::from_trusted(policy.digest());
  fixture.policy = policy.to_bytes();
  let input = fixture.input().unwrap();
  let execution = wrapper.execute(&input, 4 << 30).unwrap();
  execution
    .accumulator()
    .check_pairing(config(64).pcs().verifier_params())
    .unwrap();
  let limits = TraceLimits {
    max_height: 1 << 23,
    max_total_rows: 1 << 26,
    max_trace_bytes: 16 << 30,
  };
  let profile = wrapper.preflight(&execution, &config(64), limits).unwrap();
  eprintln!(
    "CompressBN success-proof preflight: height {}, rows {}, trace bytes {}",
    profile.max_height, profile.total_rows, profile.main_fixed_lookup_bytes
  );
  let error = wrapper.prove(&execution, config(64), limits).err().unwrap();
  assert!(error.contains("loaded SRS prefix is too short"), "{error}");
  let proven = wrapper
    .prove(&execution, config(profile.max_height.max(1 << 16)), limits)
    .unwrap();
  assert_eq!(proven.keys.source, keys.source);
  let key = VerifyingKey::from_bytes(
    &keys.portable,
    blake3::hash(&keys.portable).as_bytes(),
  )
  .unwrap();
  key.verify_bytes(&proven.claim, &proven.proof).unwrap();
  proven
    .accumulator
    .check_pairing(key.system().config.pcs().verifier_params())
    .unwrap();
  let mut changed = input.public_inputs();
  changed.stage = changed.stage.next().unwrap();
  assert!(
    key
      .verify_bytes(
        &wrapper.claim(changed, &proven.accumulator).unwrap(),
        &proven.proof
      )
      .is_err()
  );
  Input::from_source(
    changed,
    proven.keys.source,
    proven.source_claims,
    proven.source_proof,
    fixture.policy,
  )
  .unwrap();
}
