use std::sync::Arc;

use aiur::{artifact::WidePackage, field::FieldBackend, trace::TracePlan};
use ix_proof_compression::{
  aiur_backend::{
    Bn254,
    kzg::{Backend, VerifyingKey},
  },
  kzg::{KzgConfig, Srs},
};

#[test]
fn portable_key_verifies_distinct_trace_shapes_without_proving_powers() {
  let package = WidePackage::decode(include_bytes!(
    "../../aiur/tests/fixtures/bn254-trace.ixa"
  ))
  .unwrap();
  let artifact = package.trace.unwrap();
  let mut program = package.program.check_with(Bn254).unwrap();
  program.track_depth(&artifact).unwrap();
  let plan = TracePlan::new(&program, artifact).unwrap();
  let backend = Backend::new(
    &plan,
    KzgConfig::new(
      Arc::new(Srs::unsafe_dev_setup(64, b"aiur-portable-key")),
      8,
    ),
  )
  .unwrap();
  let encoded = backend.verifying_key().unwrap().to_bytes().unwrap();
  let key =
    VerifyingKey::from_bytes(&encoded, blake3::hash(&encoded).as_bytes())
      .unwrap();
  assert_eq!(key.to_bytes().unwrap(), encoded);
  assert!(
    key.system().circuits.iter().all(|circuit| circuit.preprocessed.is_none())
  );
  assert!(key.system().preprocessed_indices.iter().any(Option::is_none));
  assert!(key.system().preprocessed_indices.iter().any(Option::is_some));
  let mut shapes = vec![];
  for n in [0, 3, 9] {
    let args = [Bn254.from_u64(n), Bn254.neg(Bn254.one())];
    let expected = [Bn254.from_u64(n + 6)];
    let record = program.execute("BN254Trace::run", args.to_vec()).unwrap();
    let public = plan.public_args(&record, "BN254Trace::run", &args).unwrap();
    let proof = backend
      .prove(
        "BN254Trace::run",
        &public,
        &expected,
        backend.generate(&record, "BN254Trace::run", &args).unwrap(),
      )
      .unwrap();
    shapes.push(proof.log_degrees.clone());
    let claim = backend.claim("BN254Trace::run", &public, &expected).unwrap();
    let bytes = key.encode_proof(&proof).unwrap();
    key.verify_bytes(&claim, &bytes).unwrap();
    for i in 0..claim.len() {
      let mut wrong = claim.clone();
      wrong[i] = Bn254.add(wrong[i], Bn254.one());
      assert!(key.verify_bytes(&wrong, &bytes).is_err());
    }
    let mut trailing = bytes.clone();
    trailing.push(0);
    assert!(key.verify_bytes(&claim, &trailing).is_err());
    assert!(key.verify_bytes(&claim, &bytes[..bytes.len() - 1]).is_err());
  }
  assert_ne!(shapes[0], shapes[1]);
  assert_ne!(shapes[1], shapes[2]);
  assert!(VerifyingKey::from_bytes(&encoded, &[0; 32]).is_err());
  let mut trailing = encoded;
  trailing.push(0);
  assert!(
    VerifyingKey::from_bytes(&trailing, blake3::hash(&trailing).as_bytes())
      .is_err()
  );
}

#[test]
fn portable_proof_preserves_inactive_compiler_circuits() {
  let package = WidePackage::decode(include_bytes!(
    "../../aiur/tests/fixtures/bn254-inactive.ixa"
  ))
  .unwrap();
  let artifact = package.trace.unwrap();
  let mut program = package.program.check_with(Bn254).unwrap();
  program.track_depth(&artifact).unwrap();
  let plan = TracePlan::new(&program, artifact).unwrap();
  let backend = Backend::new(
    &plan,
    KzgConfig::new(
      Arc::new(Srs::unsafe_dev_setup(32, b"aiur-inactive-proof")),
      8,
    ),
  )
  .unwrap();
  let record = program.execute("Inactive::run", vec![Bn254.zero()]).unwrap();
  let public =
    plan.public_args(&record, "Inactive::run", &[Bn254.zero()]).unwrap();
  let expected = [Bn254.from_u64(8)];
  let proof = backend
    .prove(
      "Inactive::run",
      &public,
      &expected,
      backend.generate(&record, "Inactive::run", &[Bn254.zero()]).unwrap(),
    )
    .unwrap();
  assert!(proof.active.iter().any(|&on| !on));
  backend.verify("Inactive::run", &public, &expected, &proof).unwrap();
  let claim = backend.claim("Inactive::run", &public, &expected).unwrap();
  let key = backend.verifying_key().unwrap();
  let bytes = key.encode_proof(&proof).unwrap();
  key.verify_bytes(&claim, &bytes).unwrap();
}
