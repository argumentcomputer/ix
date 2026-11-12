use aiur::{artifact::WidePackage, trace::stark::Parameters};
use ix_proof_compression::{
  aiur_backend::{
    compress_gl::{Capacity, Wrapper},
    kzg::VerifyingKey,
  },
  pipeline::SetupConfig,
};
use multi_stark::{
  batch::ShardInput,
  expr::Expr,
  lookup::Lookup,
  p3_field::PrimeCharacteristicRing,
  p3_matrix::dense::RowMajorMatrix,
  system::{CircuitInputs, System, SystemWitness},
  types::{GoldilocksBlake3Config, Val},
};
use stark_verifier::compress_wrap::Input;

fn input() -> Input {
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
#[ignore = "requires IX_COMPRESS_GL_TEST_ARTIFACT naming trusted compiler output; proves a small FRI root over BN254"]
fn compiled_root_binds_statement_artifact_and_capacity() {
  let bytes =
    std::fs::read(std::env::var("IX_COMPRESS_GL_TEST_ARTIFACT").unwrap())
      .unwrap();
  assert!(Wrapper::from_bytes(&bytes, &[0; 32]).is_err());
  let wrapper =
    Wrapper::from_bytes(&bytes, blake3::hash(&bytes).as_bytes()).unwrap();
  let input = input();
  let execution = wrapper.execute(&input).unwrap();
  let mut variant = WidePackage::decode(&bytes).unwrap();
  variant.program.tables[0].name.push_str("_metadata_variant");
  let variant = variant.encode().unwrap();
  let other =
    Wrapper::from_bytes(&variant, blake3::hash(&variant).as_bytes()).unwrap();
  assert_ne!(wrapper.artifact_digest(), other.artifact_digest());
  assert!(other.profile(&execution).is_err());
  let setup = SetupConfig::from_env(true).unwrap();
  assert!(
    wrapper
      .prove(
        &execution,
        &setup,
        Capacity { max_log_height: 1, quotient_degree: 2 }
      )
      .is_err()
  );
  let proven = wrapper
    .prove(
      &execution,
      &setup,
      Capacity { max_log_height: 24, quotient_degree: 2 },
    )
    .unwrap();
  let key =
    VerifyingKey::from_bytes(&proven.key, blake3::hash(&proven.key).as_bytes())
      .unwrap();
  key
    .verify_bytes(&wrapper.claim(input.statement()).unwrap(), &proven.proof)
    .unwrap();
  for index in 0..2 {
    let mut statement = input.statement().clone();
    if index == 0 {
      statement.key_digest[0] ^= 1;
    } else {
      statement.claims_digest[0] ^= 1;
    }
    assert!(
      key
        .verify_bytes(&wrapper.claim(&statement).unwrap(), &proven.proof)
        .is_err()
    );
  }
  let mut trailing = proven.proof;
  trailing.push(0);
  assert!(key.verify_bytes(&proven.claim, &trailing).is_err());
}
