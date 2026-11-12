use aiur::{
  artifact::WidePackage, field::FieldBackend, hints::HintChannels,
  maps::MapOverrides, trace::TracePlan,
};
use ark_bn254::{Bn254 as Engine, Fr, G1Affine};
use ark_ec::{AffineRepr, CurveGroup, pairing::Pairing};
use ark_ff::{BigInteger, PrimeField, Zero};
use ix_proof_compression::{
  aiur_backend::{
    Bn254, fq, g1,
    kzg::{Backend, Compiler, Proof, VerifyingKey},
    kzg_advice as wire,
  },
  kzg::{Blake3Transcript, KzgCommitment, KzgConfig, Scalar, Srs},
};
use multi_stark::{
  config::ProofConfig,
  expr::Expr,
  lookup::Lookup,
  system::{CircuitInputs, System, SystemWitness},
  traits::Transcript,
};
use p3_matrix::dense::RowMajorMatrix;
use std::{
  path::PathBuf,
  sync::{Arc, OnceLock},
};

#[path = "aiur_kzg_source/reference.rs"]
mod reference;

const VERIFIER: &str = "KzgVerifier::verify_deferred";
const COMPRESS: &str = "CompressBN::compress_v1";
const CAP: usize = 1 << 24;

fn load_plan(path: PathBuf) -> TracePlan<'static, Bn254> {
  let package = WidePackage::decode(&std::fs::read(path).unwrap()).unwrap();
  let trace = package.trace.expect("compiler trace fixture");
  let mut program = package.program.check_with(Bn254).unwrap();
  program.track_depth(&trace).unwrap();
  TracePlan::new(Arc::new(program), trace).unwrap()
}
fn plan() -> &'static TracePlan<'static, Bn254> {
  static PLAN: OnceLock<TracePlan<'static, Bn254>> = OnceLock::new();
  PLAN.get_or_init(|| {
    load_plan(
      std::env::var_os("IX_AIUR_KZG_SOURCE_ARTIFACT")
        .map(PathBuf::from)
        .unwrap_or_else(|| {
          PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("../aiur/tests/fixtures/kzg-source.ixa")
        }),
    )
  })
}
fn maps() -> &'static MapOverrides<Scalar> {
  static MAPS: OnceLock<MapOverrides<Scalar>> = OnceLock::new();
  MAPS.get_or_init(|| {
    let mut maps = MapOverrides::new();
    aiur::library::u8::register_maps(plan().program(), &mut maps).unwrap();
    maps
  })
}
fn channels(inputs: &wire::Inputs) -> HintChannels<Scalar> {
  let mut channels = HintChannels::new();
  aiur::library::u32::register(&mut channels, Bn254).unwrap();
  aiur::library::u64::register(&mut channels, Bn254).unwrap();
  fq::register(&mut channels).unwrap();
  g1::register(&mut channels).unwrap();
  wire::register(&mut channels).unwrap();
  inputs.register(&mut channels).unwrap();
  channels
}
fn execute(
  entry: &str,
  args: Vec<Scalar>,
  inputs: &wire::Inputs,
) -> Result<aiur::Execution<Bn254>, String> {
  let hints = channels(inputs);
  plan()
    .program()
    .prepare_hint_channels(&[], &hints)
    .unwrap()
    .with_map_overrides(maps())
    .unwrap()
    .execute(entry, args)
    .map_err(|error| error.to_string())
}
fn empty_inputs(key: Vec<u8>) -> wire::Inputs {
  wire::Inputs::new(key, vec![], vec![], vec![]).unwrap()
}
fn srs(height: usize) -> Arc<Srs> {
  Arc::new(Srs::unsafe_dev_setup_prefix(
    height,
    CAP - 1,
    b"aiur-kzg-source-tests",
  ))
}
fn scalar_bytes(value: Scalar) -> Vec<u8> {
  value.0.into_bigint().to_bytes_le()
}
fn digest(bytes: &[u8]) -> [u8; 32] {
  *blake3::hash(bytes).as_bytes()
}
fn verifier_args(key: &[u8], claims: &[u8]) -> Vec<Scalar> {
  wire::digest_words(&digest(key))
    .into_iter()
    .chain(wire::digest_words(&digest(claims)))
    .collect()
}
struct Native {
  system: System<KzgConfig>,
  proof: Proof,
  key: VerifyingKey,
  srs: Arc<Srs>,
  claims: Vec<Vec<Scalar>>,
}
fn constant() -> Native {
  constant_claim(vec![Bn254.from_u64(42)])
}

fn constant_claim(claim: Vec<Scalar>) -> Native {
  let srs = srs(64);
  let input = CircuitInputs {
    main_width: 1,
    constraints: vec![Expr::main(0) - Expr::constant(Bn254.one())],
    lookups: vec![Lookup::pull(
      Expr::main(0),
      claim.iter().copied().map(Expr::constant).collect(),
    )],
    ..Default::default()
  };
  let (system, key) =
    System::new(KzgConfig::with_max_trace_len(srs.clone(), CAP, 8), [input]);
  let witness = SystemWitness::from_stage_1(
    vec![RowMajorMatrix::new_col(vec![Bn254.one()])],
    &system,
  );
  let proof = system.prove(&key, &claim, witness);
  system.verify(&claim, &proof).unwrap();
  let key = VerifyingKey::from_system(&system).unwrap();
  Native { system, proof, key, srs, claims: vec![claim] }
}

fn compression_args(
  policy: &wire::Policy,
  stage: u64,
  statement: &[u8; 32],
) -> Vec<Scalar> {
  wire::digest_words(&policy.digest())
    .into_iter()
    .chain([Bn254.from_u64(stage)])
    .chain(wire::digest_words(statement))
    .collect()
}

#[test]
fn compression_policy_binds_key_entry_statement_stage_and_setup() {
  let statement = digest(b"Aiur compression policy regression");
  let mut claim = vec![Bn254.one(), Bn254.from_u64(31)];
  claim.extend([Bn254.zero(); 8]);
  claim.extend(wire::digest_words(&statement));
  let fixture = constant_claim(claim.clone());
  let key = wire::key_bytes(&fixture.key).unwrap();
  let claims = wire::claims_bytes(&fixture.claims).unwrap();
  let proof = wire::proof_bytes(&fixture.proof).unwrap();
  let parameters = fixture.key.system().config.pcs().verifier_params();
  let policy =
    wire::Policy::new(parameters, digest(&key), 31, [0; 32], 47).unwrap();
  let input = |policy: &wire::Policy| {
    wire::Inputs::new(
      key.clone(),
      claims.clone(),
      proof.clone(),
      policy.to_bytes(),
    )
    .unwrap()
  };
  let args = compression_args(&policy, 1, &statement);
  let record = execute(COMPRESS, args.clone(), &input(&policy)).unwrap();
  assert_eq!(record.output.len(), 4);
  let points = wire::decode_accumulator(&record.output).unwrap();
  assert_eq!(
    points,
    reference::accumulator(
      &fixture.system,
      &fixture.proof,
      &fixture.claims,
      fixture.srs.g1[0]
    )
  );
  assert!(pair_check(points, &fixture.srs));

  for index in [0, 7, 8, 9, 16] {
    let mut wrong = args.clone();
    wrong[index] += Bn254.one();
    assert!(
      execute(COMPRESS, wrong, &input(&policy)).is_err(),
      "accepted changed public input {index}"
    );
  }
  for stage in [0, 2, 1 << 32] {
    assert!(
      execute(
        COMPRESS,
        compression_args(&policy, stage, &statement),
        &input(&policy)
      )
      .is_err()
    );
  }
  for wrong_policy in [
    wire::Policy::new(parameters, [0; 32], 31, [0; 32], 47).unwrap(),
    wire::Policy::new(parameters, digest(&key), 32, [0; 32], 47).unwrap(),
    wire::Policy::new(
      &ix_proof_compression::kzg::VerifierParams::from_srs(
        &Srs::unsafe_dev_setup(64, b"different-policy-anchors"),
      ),
      digest(&key),
      31,
      [0; 32],
      47,
    )
    .unwrap(),
  ] {
    assert!(
      execute(
        COMPRESS,
        compression_args(&wrong_policy, 1, &statement),
        &input(&wrong_policy)
      )
      .is_err()
    );
  }
  let mut trailing_policy = policy.to_bytes();
  trailing_policy.push(0);
  let mut trailing_args = args.clone();
  trailing_args[..8]
    .copy_from_slice(&wire::digest_words(&digest(&trailing_policy)));
  assert!(
    execute(
      COMPRESS,
      trailing_args,
      &wire::Inputs::new(key, claims, proof, trailing_policy,).unwrap()
    )
    .is_err()
  );

  for index in [0, 2] {
    let mut malformed_claim = claim.clone();
    malformed_claim[index] += Bn254.one();
    let malformed = constant_claim(malformed_claim);
    let key = wire::key_bytes(&malformed.key).unwrap();
    let policy =
      wire::Policy::new(parameters, digest(&key), 31, [0; 32], 47).unwrap();
    let inputs = wire::Inputs::new(
      key,
      wire::claims_bytes(&malformed.claims).unwrap(),
      wire::proof_bytes(&malformed.proof).unwrap(),
      policy.to_bytes(),
    )
    .unwrap();
    assert!(
      execute(COMPRESS, compression_args(&policy, 1, &statement), &inputs)
        .is_err()
    );
  }
}
fn nonconstant() -> Native {
  let srs = srs(64);
  let circuit = |height| CircuitInputs {
    main_width: 1,
    preprocessed: Some(RowMajorMatrix::new_col(
      (1..=height).map(|value| Bn254.from_u64(value)).collect(),
    )),
    constraints: vec![
      Expr::main(0) - Expr::preprocessed(0),
      Expr::IsTransition
        * (Expr::main_next(0) - Expr::main(0) - Expr::constant(Bn254.one())),
    ],
    lookups: vec![
      Lookup::push(Expr::constant(Bn254.one()), vec![Expr::main(0)]),
      Lookup::pull(Expr::constant(Bn254.one()), vec![Expr::main(0)]),
    ],
    lookup_group_size: 2,
    ..Default::default()
  };
  let dormant = CircuitInputs {
    main_width: 1,
    constraints: vec![Expr::main(0)],
    ..Default::default()
  };
  let (system, key) = System::new(
    KzgConfig::with_max_trace_len(srs.clone(), CAP, 8),
    [circuit(2), dormant, circuit(4)],
  );
  let traces = vec![
    RowMajorMatrix::new_col(
      (1..=2).map(|value| Bn254.from_u64(value)).collect(),
    ),
    RowMajorMatrix::new(vec![], 1),
    RowMajorMatrix::new_col(
      (1..=4).map(|value| Bn254.from_u64(value)).collect(),
    ),
  ];
  let proof = system.prove_multiple_claims(
    &key,
    &[],
    SystemWitness::from_stage_1(traces, &system),
  );
  system.verify_multiple_claims(&[], &proof).unwrap();
  assert_eq!(proof.active, [true, false, true]);
  assert_eq!(proof.log_degrees, [1, 2]);
  let key = VerifyingKey::from_system(&system).unwrap();
  Native { system, proof, key, srs, claims: vec![] }
}
fn pair_check(points: [G1Affine; 2], srs: &Srs) -> bool {
  Engine::multi_pairing(points, [srs.g2, srs.tau_g2]).is_zero()
}

#[test]
fn canonical_scalar_transcript_window_msm_and_chunk_transport_match_native() {
  let a = Scalar(-Fr::from(1));
  let b = Scalar(Fr::from(9));
  for value in [Bn254.zero(), Bn254.one(), a, b] {
    let bytes = scalar_bytes(value);
    assert_eq!(
      execute("KzgTest::read_scalar", vec![], &empty_inputs(bytes.clone()))
        .unwrap()
        .output,
      [value]
    );
    let expected: Vec<_> =
      bytes.into_iter().map(|byte| Bn254.from_u64(u64::from(byte))).collect();
    assert_eq!(
      execute("KzgTest::scalar_bytes", vec![value], &empty_inputs(vec![]))
        .unwrap()
        .output,
      expected
    );
  }
  assert!(
    execute(
      "KzgTest::read_scalar",
      vec![],
      &empty_inputs(Fr::MODULUS.to_bytes_le())
    )
    .is_err()
  );
  let mut trailing = scalar_bytes(a);
  trailing.push(0);
  assert!(
    execute("KzgTest::read_scalar", vec![], &empty_inputs(trailing)).is_err()
  );
  let g = G1Affine::generator();
  let rows = KzgCommitment(vec![vec![g, -g], vec![G1Affine::identity()]]);
  for seed in
    [vec![], b"multi-stark/kzg/bn254/blake3/v1".to_vec(), vec![19u8; 1025]]
  {
    let mut t = Blake3Transcript::new();
    t.observe_bytes(&seed);
    t.observe_field(a);
    t.observe_field(b);
    let beta = t.sample_challenge();
    t.observe_field(beta);
    let gamma = t.sample_challenge();
    t.observe_field(gamma);
    t.observe_commitment(rows.clone());
    t.observe_canonical(&0u64);
    t.observe_canonical(&28u64);
    let alpha = t.sample_challenge();
    for value in [beta, gamma, alpha] {
      t.observe_field(value);
    }
    let zeta = t.sample_challenge();
    assert_eq!(
      execute("KzgTest::transcript", vec![a, b], &empty_inputs(seed))
        .unwrap()
        .output,
      [beta, gamma, alpha, zeta]
    );
  }
  let h = (g * Fr::from(7)).into_affine();
  let args = g1::encode(g)
    .into_iter()
    .chain([a])
    .chain(g1::encode(h))
    .chain([b])
    .collect();
  assert_eq!(
    execute("KzgTest::msm2", args, &empty_inputs(vec![])).unwrap().output,
    g1::encode((g * a.0 + h * b.0).into_affine())
  );
  let pair = [g, -g];
  let words = wire::accumulator_words(&pair).unwrap();
  assert_eq!(
    execute("KzgTest::accumulator", words.to_vec(), &empty_inputs(vec![]))
      .unwrap()
      .output,
    words
  );
  let mut bad = words;
  bad[0] = Bn254.from_word(aiur::FieldWord::from_limbs_le([0, 0, 1, 0]));
  assert!(
    execute("KzgTest::accumulator", bad.to_vec(), &empty_inputs(vec![]))
      .is_err()
  );
}

#[test]
fn source_verifier_matches_native_pcs_and_rejects_key_claim_proof_tampering() {
  for fixture in [constant(), nonconstant()] {
    let key = wire::key_bytes(&fixture.key).unwrap();
    let claims = wire::claims_bytes(&fixture.claims).unwrap();
    let proof = wire::proof_bytes(&fixture.proof).unwrap();
    let args = verifier_args(&key, &claims);
    let inputs =
      wire::Inputs::new(key.clone(), claims.clone(), proof.clone(), vec![])
        .unwrap();
    let record = execute(VERIFIER, args.clone(), &inputs).unwrap();
    let points = wire::decode_accumulator(&record.output).unwrap();
    assert_eq!(
      points,
      reference::accumulator(
        &fixture.system,
        &fixture.proof,
        &fixture.claims,
        fixture.srs.g1[0]
      )
    );
    assert!(pair_check(points, &fixture.srs));
    if fixture.claims.is_empty() {
      assert!(!points[1].infinity);
    }
    drop(record);
    let mut bad_key = key.clone();
    bad_key[8] ^= 1;
    assert!(
      execute(
        VERIFIER,
        args.clone(),
        &wire::Inputs::new(bad_key, claims.clone(), proof.clone(), vec![])
          .unwrap()
      )
      .is_err()
    );
    let mut bad = fixture.proof.clone();
    bad.quotient_opened_values[0][0][0] += Bn254.one();
    assert!(
      execute(
        VERIFIER,
        args.clone(),
        &wire::Inputs::new(
          key.clone(),
          claims.clone(),
          wire::proof_bytes(&bad).unwrap(),
          vec![]
        )
        .unwrap()
      )
      .is_err()
    );
    let mut bad = fixture.proof.clone();
    bad.opening_proof.0[0] =
      (bad.opening_proof.0[0] + G1Affine::generator()).into_affine();
    let record = execute(
      VERIFIER,
      args.clone(),
      &wire::Inputs::new(
        key.clone(),
        claims.clone(),
        wire::proof_bytes(&bad).unwrap(),
        vec![],
      )
      .unwrap(),
    )
    .unwrap();
    let points = wire::decode_accumulator(&record.output).unwrap();
    assert_eq!(
      points,
      reference::accumulator(
        &fixture.system,
        &bad,
        &fixture.claims,
        fixture.srs.g1[0]
      )
    );
    assert!(
      !pair_check(points, &fixture.srs),
      "deferred opening forgery passed terminal pairing"
    );
    if !fixture.claims.is_empty() {
      let bad_claims = wire::claims_bytes(&[vec![Bn254.from_u64(43)]]).unwrap();
      assert!(
        execute(
          VERIFIER,
          verifier_args(&key, &bad_claims),
          &wire::Inputs::new(key, bad_claims, proof, vec![]).unwrap()
        )
        .is_err()
      );
    }
  }
}

#[test]
#[ignore = "full source-verifier execution proof; run explicitly after count preflight"]
fn source_verifier_execution_is_proven_by_kzg() {
  let fixture = nonconstant();
  let key = wire::key_bytes(&fixture.key).unwrap();
  let claims = wire::claims_bytes(&fixture.claims).unwrap();
  let args = verifier_args(&key, &claims);
  let inputs = wire::Inputs::new(
    key,
    claims,
    wire::proof_bytes(&fixture.proof).unwrap(),
    vec![],
  )
  .unwrap();
  let record = execute(VERIFIER, args.clone(), &inputs).unwrap();
  assert!(pair_check(
    wire::decode_accumulator(&record.output).unwrap(),
    &fixture.srs
  ));
  let compiler = Compiler::new(plan()).unwrap();
  let heights = compiler.row_counts(&record).unwrap();
  let cells: usize = heights
    .iter()
    .zip(compiler.inputs())
    .map(|(height, input)| height * input.main_width)
    .sum();
  let height = *heights.iter().max().unwrap();
  eprintln!(
    "Aiur KZG verifier proof preflight: {cells} main cells, max height {height}"
  );
  assert!(
    height <= 1 << 20 && cells <= 100_000_000,
    "source verifier proof exceeds focused test capacity"
  );
  drop(compiler);
  let backend =
    Backend::new(plan(), KzgConfig::with_max_trace_len(srs(height), CAP, 8))
      .unwrap();
  let witness = backend.generate(&record, VERIFIER, &args).unwrap();
  let proof = backend.prove(VERIFIER, &args, &record.output, witness).unwrap();
  backend.verify(VERIFIER, &args, &record.output, &proof).unwrap();
  let mut changed = record.output.clone();
  changed[0] += Bn254.one();
  assert!(backend.verify(VERIFIER, &args, &changed, &proof).is_err());
}

#[test]
fn source_fold_matches_domain_bound_native_challenge() {
  let g = G1Affine::generator();
  let previous = [g, -g];
  let current =
    [(g * Fr::from(7u8)).into_affine(), (g * Fr::from(11u8)).into_affine()];
  let policy = digest(b"fold policy");
  let statement = digest(b"fold statement");
  let key = digest(b"fold key");
  let proof = digest(b"fold proof");
  let weight = wire::fold_challenge(
    &policy, &statement, 2, &key, &proof, &previous, &current,
  )
  .unwrap();
  let args = wire::digest_words(&policy)
    .into_iter()
    .chain(wire::digest_words(&statement))
    .chain([Bn254.from_u64(2)])
    .chain(wire::digest_words(&key))
    .chain(wire::digest_words(&proof))
    .chain(previous.into_iter().flat_map(g1::encode))
    .chain(current.into_iter().flat_map(g1::encode))
    .collect();
  let record = execute("KzgTest::fold", args, &empty_inputs(vec![])).unwrap();
  assert_eq!(
    wire::decode_accumulator(&record.output).unwrap(),
    [
      (current[0] + previous[0] * weight.0).into_affine(),
      (current[1] + previous[1] * weight.0).into_affine(),
    ]
  );
}

