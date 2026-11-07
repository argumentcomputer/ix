use super::*;
use multi_stark::batch::Retention;

/// Main's parameters are the default, and they are exactly at the floor.
#[test]
fn default_parameters_are_mains() {
  let p = Parameters::default();
  assert_eq!(p, Parameters::DEFAULT);
  assert_eq!(
    (
      p.log_blowup,
      p.num_queries,
      p.commit_proof_of_work_bits,
      p.query_proof_of_work_bits
    ),
    (2, 100, 0, 20)
  );
  assert_eq!(p.conjectured_bits(), 220);
  assert_eq!(p.conjectured_bits(), stark_key::security::MIN_CONJECTURED_BITS);
  p.check().unwrap();
}

/// The default and the floor are mirrored in `Ix/Aiur/Protocol.lean`.
#[test]
fn lean_mirror_matches() {
  let path =
    concat!(env!("CARGO_MANIFEST_DIR"), "/../../Ix/Aiur/Protocol.lean");
  let source = std::fs::read_to_string(path).unwrap();
  let field = |name: &str| -> usize {
    let mut values = source.lines().filter_map(|line| {
      let rest = line
        .split(&format!("{name} := "))
        .nth(1)
        .or_else(|| line.split(&format!("def {name} : Nat := ")).nth(1))?;
      rest
        .trim_end_matches(|c: char| !c.is_ascii_digit())
        .split(|c: char| !c.is_ascii_digit())
        .next()?
        .parse()
        .ok()
    });
    let value = values.next().unwrap_or_else(|| panic!("{name} not in {path}"));
    assert!(values.next().is_none(), "{name} is set twice in {path}");
    value
  };
  let p = Parameters::DEFAULT;
  assert_eq!(field("logBlowup"), p.log_blowup);
  assert_eq!(field("capHeight"), p.commitment().cap_height);
  assert_eq!(field("logFinalPolyLen"), p.fri().log_final_poly_len);
  assert_eq!(field("maxLogArity"), p.fri().max_log_arity);
  assert_eq!(field("numQueries"), p.num_queries);
  assert_eq!(field("commitProofOfWorkBits"), p.commit_proof_of_work_bits);
  assert_eq!(field("queryProofOfWorkBits"), p.query_proof_of_work_bits);
  assert_eq!(
    field("minConjecturedSecurityBits"),
    stark_key::security::MIN_CONJECTURED_BITS
  );
  assert_eq!(
    field("maxProofOfWorkBits"),
    stark_key::security::MAX_PROOF_OF_WORK_BITS
  );
}

#[test]
fn backends_reject_parameters_below_the_floor() {
  let (program, artifact) = identity(false);
  let plan = TracePlan::new(&program, activate(artifact)).unwrap();
  let weak = [
    // #678's original default, 64 conjectured bits.
    Parameters { log_blowup: 1, num_queries: 64, ..parameters() },
    Parameters { num_queries: 219, ..parameters() },
    Parameters {
      num_queries: 100,
      query_proof_of_work_bits: 19,
      ..Parameters::DEFAULT
    },
    Parameters { commit_proof_of_work_bits: 33, ..parameters() },
  ];
  for p in weak {
    let error = Backend::new(&plan, p).err().expect("accepted weak parameters");
    assert!(error.contains("floor") || error.contains("exceeds"), "{error}");
    assert!(Backend::for_batch(&plan, p).is_err());
    assert!(Backend::for_batch_verification(&plan, p).is_err());
    assert!(Backend::for_batch_on_device(&plan, p, None).is_err());
  }
  // Only the test waiver builds a toy backend.
  let toy = Parameters { num_queries: 2, ..parameters() };
  let backend = Backend::for_batch_below_floor(&plan, toy).unwrap();
  let bytes = backend.verifying_key_bytes().unwrap();
  assert!(VerifyingKey::from_bytes(&bytes).is_err());
  VerifyingKey::from_bytes_below_floor(&bytes).unwrap();
}

/// Every parameter is in the key, and a proof made under other parameters,
/// even stronger ones, verifies against neither that key nor its backend.
#[test]
fn proofs_are_bound_to_their_parameters() {
  let (program, artifact) = fixture();
  let plan = TracePlan::new(&program, activate(artifact)).unwrap();
  let record = program.execute("root", vec![3]).unwrap();
  let base = parameters();
  let variants = [
    base,
    Parameters { log_blowup: 2, num_queries: 110, ..base },
    Parameters { num_queries: 221, ..base },
    Parameters { commit_proof_of_work_bits: 1, ..base },
    Parameters { query_proof_of_work_bits: 1, ..base },
  ];
  let mut keys = vec![];
  let mut proofs = vec![];
  let mut backends = vec![];
  for p in variants {
    let backend = Backend::for_batch(&plan, p).unwrap();
    let witness = backend.generate(&record, "root", &[3]).unwrap();
    let proof = backend
      .prove_batch("root", &[3], &[9], witness, 1, Retention::Regenerate)
      .unwrap();
    let bytes = backend.verifying_key_bytes().unwrap();
    let key = VerifyingKey::from_bytes(&bytes).unwrap();
    assert_eq!(key.commitment_parameters().log_blowup, p.log_blowup);
    let fri = key.fri_parameters();
    assert_eq!(
      (
        fri.num_queries,
        fri.commit_proof_of_work_bits,
        fri.query_proof_of_work_bits
      ),
      (p.num_queries, p.commit_proof_of_work_bits, p.query_proof_of_work_bits)
    );
    assert!(!keys.contains(&bytes), "parameters missing from the key");
    keys.push(bytes);
    proofs.push(proof);
    backends.push(backend);
  }
  let claim = backends[0].claim("root", &[3], &[9]).unwrap();
  for (i, bytes) in keys.iter().enumerate() {
    let key = VerifyingKey::from_bytes(bytes).unwrap();
    for (j, proof) in proofs.iter().enumerate() {
      // A mismatch is an error, not a panic.
      let by_key = key.verify(std::slice::from_ref(&claim), proof);
      let by_backend = backends[i].verify_batch("root", &[3], &[9], proof);
      assert_eq!(by_key.is_ok(), i == j, "key {i}, proof {j}: {by_key:?}");
      assert_eq!(by_backend.is_ok(), i == j, "backend {i}, proof {j}");
    }
  }
}

/// A proof made under weaker parameters, such as #678's original default,
/// verifies against neither a default key nor a default backend.
#[test]
fn weaker_proofs_do_not_verify_against_default_keys() {
  let (program, artifact) = fixture();
  let plan = TracePlan::new(&program, activate(artifact)).unwrap();
  let record = program.execute("root", vec![3]).unwrap();
  let default =
    Backend::for_batch_verification(&plan, Parameters::DEFAULT).unwrap();
  let key =
    VerifyingKey::from_bytes(&default.verifying_key_bytes().unwrap()).unwrap();
  let claim = default.claim("root", &[3], &[9]).unwrap();
  for weak in [
    Parameters {
      log_blowup: 1,
      num_queries: 64,
      commit_proof_of_work_bits: 0,
      query_proof_of_work_bits: 0,
    },
    Parameters { query_proof_of_work_bits: 0, ..Parameters::DEFAULT },
    Parameters { num_queries: 99, ..Parameters::DEFAULT },
  ] {
    let backend = Backend::for_batch_below_floor(&plan, weak).unwrap();
    let witness = backend.generate(&record, "root", &[3]).unwrap();
    let proof = backend
      .prove_batch("root", &[3], &[9], witness, 1, Retention::Regenerate)
      .unwrap();
    backend.verify_batch("root", &[3], &[9], &proof).unwrap();
    assert!(key.verify(std::slice::from_ref(&claim), &proof).is_err());
    assert!(default.verify_batch("root", &[3], &[9], &proof).is_err());
  }
}
