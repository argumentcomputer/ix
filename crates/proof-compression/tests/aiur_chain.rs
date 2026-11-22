use aiur::trace::stark::Parameters;
use ark_ec::{AffineRepr, CurveGroup};
use ix_proof_compression::{
  aiur_backend::{
    chain::{
      Admission, Assets, Configuration, Envelope, Limits, Prover,
      StageConfiguration, Verifier,
    },
    compress_bn, compress_gl,
    kzg::VerifyingKey,
    kzg_advice as wire,
  },
  pipeline::SetupConfig,
};
use multi_stark::{
  batch::ShardInput,
  config::ProofConfig,
  expr::Expr,
  lookup::Lookup,
  p3_field::PrimeCharacteristicRing,
  p3_matrix::dense::RowMajorMatrix,
  system::{CircuitInputs, System, SystemWitness},
  types::{GoldilocksBlake3Config, Val},
};
use stark_verifier::compress_wrap::Input;
use std::{fs, num::NonZeroU32, path::PathBuf};

fn root_input() -> Input {
  let parameters = Parameters::DEFAULT;
  let cp = parameters.commitment();
  let fp = parameters.fri();
  let one = Expr::constant(Val::ONE);
  let mut message = vec![one.clone(), Expr::constant(Val::ZERO)];
  message.extend((0..16).map(Expr::main));
  let (system, key) = System::new(
    GoldilocksBlake3Config::new(cp, fp),
    vec![CircuitInputs {
      main_width: 16,
      constraints: vec![Expr::main(0) * Expr::main(0) - Expr::main(1)],
      lookups: vec![Lookup::pull(one, message)],
      ..Default::default()
    }],
  );
  let mut args = vec![Val::ZERO; 16];
  args[0] = Val::from_u64(3);
  args[1] = Val::from_u64(9);
  let mut claim = vec![Val::ONE, Val::ZERO];
  claim.extend_from_slice(&args);
  let claims = vec![claim];
  let witness =
    SystemWitness::from_stage_1(vec![RowMajorMatrix::new(args, 16)], &system);
  let proof = system.prove_batch(
    &key,
    vec![ShardInput { claims: claims.clone(), witness }],
    vec![],
  );
  let key = stark_key::to_bytes(&system, cp, fp);
  Input::new(
    &key,
    *blake3::hash(&key).as_bytes(),
    &claims,
    &proof.to_bytes().unwrap(),
  )
  .unwrap()
}

#[test]
#[ignore = "requires IX_COMPRESS_GL_TEST_ARTIFACT; profiles a real GL-to-BN chain and proves BN when IX_AIUR_CHAIN_PROVE_BN=1"]
fn authenticated_chain_proves_and_resumes_a_small_fri_root() {
  let gl_artifact =
    fs::read(std::env::var("IX_COMPRESS_GL_TEST_ARTIFACT").unwrap()).unwrap();
  let bn_path = std::env::var_os("IX_AIUR_CHAIN_BN_ARTIFACT").map_or_else(
    || {
      PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../aiur/tests/fixtures/kzg-source.ixa")
    },
    PathBuf::from,
  );
  let bn_artifact = fs::read(bn_path).unwrap();
  let output = std::env::var_os("IX_AIUR_CHAIN_TEST_DIR").map(PathBuf::from);
  if let Some(output) = &output {
    fs::create_dir_all(output).unwrap();
  }
  let setup = SetupConfig::from_env(true).unwrap();
  let gl_capacity =
    compress_gl::Capacity { max_log_height: 24, quotient_degree: 2 };
  let bn_capacity =
    compress_gl::Capacity { max_log_height: 24, quotient_degree: 8 };
  let gl = compress_gl::Wrapper::from_bytes(
    &gl_artifact,
    blake3::hash(&gl_artifact).as_bytes(),
  )
  .unwrap();
  let bn = compress_bn::Wrapper::from_bytes(
    &bn_artifact,
    blake3::hash(&bn_artifact).as_bytes(),
  )
  .unwrap();
  let gl_key = gl.verifying_key(&setup, gl_capacity).unwrap();
  let bn_key = bn
    .verifying_key(bn_capacity.config(&setup, 1 << 16).unwrap())
    .unwrap()
    .portable;
  let stage = |artifact: &[u8], key: &[u8], capacity: compress_gl::Capacity| {
    StageConfiguration {
      artifact_blake3: *blake3::hash(artifact).as_bytes(),
      key_blake3: *blake3::hash(key).as_bytes(),
      max_log_height: capacity.max_log_height,
      quotient_degree: capacity.quotient_degree,
    }
  };
  let configuration = Configuration {
    gl: stage(&gl_artifact, &gl_key, gl_capacity),
    bn: stage(&bn_artifact, &bn_key, bn_capacity),
    bn_stages: NonZeroU32::MIN,
  };
  let assets = || Assets {
    gl_artifact: &gl_artifact,
    gl_key: &gl_key,
    bn_artifact: &bn_artifact,
    bn_key: &bn_key,
  };
  for index in 0..4 {
    let mut invalid = configuration.clone();
    match index {
      0 => invalid.gl.artifact_blake3[0] ^= 1,
      1 => invalid.gl.key_blake3[0] ^= 1,
      2 => invalid.bn.artifact_blake3[0] ^= 1,
      _ => invalid.bn.key_blake3[0] ^= 1,
    }
    assert!(Verifier::from_bytes(invalid, assets()).is_err());
  }
  let mut wrong_capacity = configuration.clone();
  wrong_capacity.bn.quotient_degree = 4;
  assert!(Verifier::from_bytes(wrong_capacity, assets()).is_err());
  let mut mismatched = configuration.clone();
  mismatched.bn.key_blake3 = mismatched.gl.key_blake3;
  mismatched.bn.quotient_degree = 2;
  let error =
    Verifier::from_bytes(mismatched, Assets { bn_key: &gl_key, ..assets() })
      .err()
      .unwrap();
  assert!(error.contains("compiler artifact"), "{error}");

  let admission = Admission {
    gl: Limits {
      max_record_bytes: 16 << 30,
      max_trace_bytes: 64 << 30,
      max_total_rows: 1 << 32,
    },
    bn: Limits {
      max_record_bytes: 64 << 30,
      max_trace_bytes: 96 << 30,
      max_total_rows: 1 << 32,
    },
  };
  let verifier = Verifier::from_bytes(configuration.clone(), assets()).unwrap();
  let prover = Prover::new(verifier, setup, admission).unwrap();
  let root = root_input();
  let expected = root.statement();
  let mut changed = expected.clone();
  changed.key_digest[0] ^= 1;
  assert!(
    prover
      .prove_gl(&root, &changed)
      .err()
      .unwrap()
      .contains("expected statement")
  );
  assert!(gl.execute_with_record_limit(&root, 0).is_err());
  assert!(gl.execute_with_record_limit(&root, 1).is_err());
  let execution =
    gl.execute_with_record_limit(&root, admission.gl.max_record_bytes).unwrap();
  let gl_profile = gl.profile(&execution).unwrap();
  let mut limited = admission;
  limited.gl.max_trace_bytes = gl_profile.main_fixed_lookup_bytes - 1;
  let limited = Prover::new(
    Verifier::from_bytes(configuration.clone(), assets()).unwrap(),
    SetupConfig::from_env(true).unwrap(),
    limited,
  )
  .unwrap();
  let error = limited.prove_gl(&root, expected).err().unwrap();
  assert!(error.contains("GL trace exceeds chain admission"), "{error}");
  let error = gl
    .prove_with_expected_key(
      &execution,
      &SetupConfig::from_env(true).unwrap(),
      gl_capacity,
      &[0; 32],
    )
    .err()
    .unwrap();
  assert!(error.contains("trusted pin"), "{error}");
  drop(execution);
  if let Some(output) = &output {
    let bytes = serde_json::to_vec_pretty(&configuration).unwrap();
    let path = output.join("configuration.json");
    if path.exists() {
      assert_eq!(
        fs::read(path).unwrap(),
        bytes,
        "cached chain configuration changed"
      );
    } else {
      fs::write(path, bytes).unwrap();
    }
    fs::write(output.join("gl-key.bin"), &gl_key).unwrap();
    fs::write(output.join("bn-key.bin"), &bn_key).unwrap();
    fs::write(
      output.join("statement.json"),
      serde_json::to_vec_pretty(expected).unwrap(),
    )
    .unwrap();
  }
  let proof_path = output.as_ref().map(|out| out.join("gl-proof.bin"));
  let gl_proof =
    if let Some(path) = proof_path.as_ref().filter(|path| path.exists()) {
      fs::read(path).unwrap()
    } else {
      let gl_proven = prover.prove_gl(&root, expected).unwrap();
      if let Some(output) = &output {
        fs::write(output.join("gl-proof.bin"), &gl_proven.proof).unwrap();
        fs::write(
          output.join("gl-report.json"),
          serde_json::to_vec_pretty(&gl_proven.report).unwrap(),
        )
        .unwrap();
      }
      gl_proven.proof
    };
  prover.verifier().first_bn_input(expected, &gl_proof).unwrap();
  assert!(prover.verifier().first_bn_input(&changed, &gl_proof).is_err());
  let mut changed_claims = expected.clone();
  changed_claims.claims_digest[0] ^= 1;
  assert!(
    prover.verifier().first_bn_input(&changed_claims, &gl_proof).is_err()
  );
  let mut trailing = gl_proof.clone();
  trailing.push(0);
  assert!(prover.verifier().first_bn_input(expected, &trailing).is_err());
  if std::env::var("IX_AIUR_CHAIN_FORGED_OPENING").as_deref() == Ok("1") {
    let gl_verifier =
      VerifyingKey::from_bytes(&gl_key, &configuration.gl.key_blake3).unwrap();
    let claim = gl.claim(expected).unwrap();
    let mut forged = gl_verifier.decode_proof(&gl_proof).unwrap();
    forged.opening_proof.0[0] = (forged.opening_proof.0[0]
      + ark_bn254::G1Affine::generator())
    .into_affine();
    let forged_bytes = gl_verifier.encode_proof(&forged).unwrap();
    assert!(prover.verifier().first_bn_input(expected, &forged_bytes).is_err());
    let public = compress_bn::PublicInputs {
      policy: compress_bn::PolicyDigest::from_trusted(
        prover.verifier().policy().digest(),
      ),
      stage: compress_bn::Stage::FIRST,
      statement: compress_bn::StatementDigest::from_root(expected),
    };
    let input = compress_bn::Input::from_source(
      public,
      wire::key_bytes(&gl_verifier).unwrap(),
      wire::claims_bytes(&[claim]).unwrap(),
      wire::proof_bytes(&forged).unwrap(),
      prover.verifier().policy().to_bytes(),
    )
    .unwrap();
    let execution = bn.execute(&input, admission.bn.max_record_bytes).unwrap();
    assert!(
      execution
        .accumulator()
        .check_pairing(prover.verifier().parameters())
        .is_err()
    );
    let setup = SetupConfig::from_env(true).unwrap();
    let limits = compress_bn::TraceLimits {
      max_height: 1 << 24,
      max_total_rows: admission.bn.max_total_rows,
      max_trace_bytes: admission.bn.max_trace_bytes,
    };
    let profile = bn
      .preflight(&execution, &bn_capacity.config(&setup, 2).unwrap(), limits)
      .unwrap();
    if let Some(output) = &output {
      fs::write(
        output.join("forged-profile.json"),
        serde_json::to_vec_pretty(&profile).unwrap(),
      )
      .unwrap();
    }
    let proven = bn
      .prove(
        &execution,
        bn_capacity.config(&setup, profile.max_height).unwrap(),
        limits,
      )
      .unwrap();
    let native =
      VerifyingKey::from_bytes(&bn_key, &configuration.bn.key_blake3).unwrap();
    native.verify_bytes(&proven.claim, &proven.proof).unwrap();
    assert!(
      proven
        .accumulator
        .check_pairing(native.system().config.pcs().verifier_params())
        .is_err()
    );
    let envelope = Envelope {
      stage: 1,
      accumulator: *proven.accumulator.words(),
      proof: proven.proof,
    };
    let error = prover
      .verifier()
      .verify_bytes(expected, &envelope.to_bytes().unwrap())
      .unwrap_err();
    assert!(error.contains("deferred pairing equation failed"), "{error}");
    let preparation_error =
      prover.verifier().prepare_terminal(expected, &envelope).err().unwrap();
    assert!(
      preparation_error.contains("deferred pairing equation failed"),
      "{preparation_error}"
    );
    let mut stage_two_config = configuration.clone();
    stage_two_config.bn_stages = NonZeroU32::new(2).unwrap();
    let stage_two = Verifier::from_bytes(stage_two_config, assets()).unwrap();
    let mut changed_stage = envelope.clone();
    changed_stage.stage = 2;
    let stage_error = stage_two.verify(expected, &changed_stage).unwrap_err();
    assert!(
      stage_error.contains("Aiur KZG verification failed"),
      "{stage_error}"
    );
    let mut swapped = envelope.clone();
    let mut points = compress_bn::Accumulator::from_words(&swapped.accumulator)
      .unwrap()
      .points();
    points.swap(0, 1);
    swapped.accumulator =
      *compress_bn::Accumulator::from_points(&points).unwrap().words();
    compress_bn::Accumulator::from_words(&swapped.accumulator).unwrap();
    assert_ne!(swapped.accumulator, envelope.accumulator);
    let swap_error = prover.verifier().verify(expected, &swapped).unwrap_err();
    assert!(
      swap_error.contains("Aiur KZG verification failed"),
      "{swap_error}"
    );
    if let Some(output) = &output {
      fs::write(
        output.join("forged-outer-proof.bin"),
        envelope.to_bytes().unwrap(),
      )
      .unwrap();
      fs::write(output.join("forged-result.json"), serde_json::to_vec_pretty(&serde_json::json!({
        "native_gl_rejected":true,"outer_proof_verified":true,"accumulator_rejected":true,"chain_rejected":true,
          "stage_proof_binding_rejected":true,"canonical_point_swap_proof_binding_rejected":true,
          "real_gl_trace_budget_rejected":true,
        "chain_error":error,"profile":profile,
      })).unwrap()).unwrap();
    }
    return;
  }
  if std::env::var("IX_AIUR_CHAIN_PROVE_BN").as_deref() != Ok("1") {
    let profile = prover.profile_from_gl(expected, &gl_proof).unwrap();
    eprintln!(
      "BN preflight: height {}, rows {}, trace bytes {}",
      profile.max_height, profile.total_rows, profile.main_fixed_lookup_bytes
    );
    if let Some(output) = &output {
      fs::write(
        output.join("bn-profile.json"),
        serde_json::to_vec_pretty(&profile).unwrap(),
      )
      .unwrap();
    }
    return;
  }
  let proven = prover.prove_from_gl(expected, &gl_proof).unwrap();
  let independent =
    Verifier::from_bytes(configuration.clone(), assets()).unwrap();
  let bytes = proven.envelope.to_bytes().unwrap();
  independent.verify_bytes(expected, &bytes).unwrap();
  let terminal =
    independent.prepare_terminal(expected, &proven.envelope).unwrap();
  assert_eq!(terminal.stage, 2);
  assert_eq!(
    terminal.statement,
    *compress_bn::StatementDigest::from_root(expected).as_bytes()
  );
  terminal.advice().unwrap();
  let terminal_configuration: serde_json::Value =
    serde_json::from_slice(&terminal.configuration.to_json().unwrap()).unwrap();
  assert_eq!(terminal_configuration["min_stage"], 2);
  assert_eq!(terminal_configuration["max_stage"], 2);
  assert!(independent.prepare_terminal(&changed, &proven.envelope).is_err());
  assert!(independent.verify(&changed, &proven.envelope).is_err());
  assert!(independent.verify(&changed_claims, &proven.envelope).is_err());
  let mut wrong_stage = proven.envelope.clone();
  wrong_stage.stage += 1;
  assert!(independent.verify(expected, &wrong_stage).is_err());
  let mut stage_two = configuration;
  stage_two.bn_stages = NonZeroU32::new(2).unwrap();
  let stage_two = Verifier::from_bytes(stage_two, assets()).unwrap();
  let error = stage_two.verify(expected, &wrong_stage).unwrap_err();
  assert!(error.contains("Aiur KZG verification failed"), "{error}");
  let mut wrong_accumulator = proven.envelope.clone();
  let mut points =
    compress_bn::Accumulator::from_words(&wrong_accumulator.accumulator)
      .unwrap()
      .points();
  points.swap(0, 1);
  wrong_accumulator.accumulator =
    *compress_bn::Accumulator::from_points(&points).unwrap().words();
  compress_bn::Accumulator::from_words(&wrong_accumulator.accumulator).unwrap();
  assert_ne!(wrong_accumulator.accumulator, proven.envelope.accumulator);
  let error = independent.verify(expected, &wrong_accumulator).unwrap_err();
  assert!(error.contains("Aiur KZG verification failed"), "{error}");
  let mut trailing = bytes.clone();
  trailing.push(0);
  assert!(Envelope::from_bytes(&trailing).is_err());
  if let Some(output) = &output {
    fs::write(output.join("chain-proof.bin"), bytes).unwrap();
    fs::write(
      output.join("bn-reports.json"),
      serde_json::to_vec_pretty(&proven.stages).unwrap(),
    )
    .unwrap();
  }
}
