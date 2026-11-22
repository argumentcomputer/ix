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

/// The default and the floor are mirrored in `Ix/Aiur/Parameters.lean`.
#[test]
fn lean_mirror_matches() {
  let path =
    concat!(env!("CARGO_MANIFEST_DIR"), "/../../Ix/Aiur/Parameters.lean");
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
    field("minProvableUdBits"),
    stark_key::security::MIN_PROVABLE_UD_BITS
  );
  assert_eq!(field("minJohnsonBits"), stark_key::security::MIN_JOHNSON_BITS);
  assert_eq!(
    field("johnsonSlackMillibitsPerQuery"),
    stark_key::security::JOHNSON_SLACK_MILLIBITS_PER_QUERY
  );
  assert_eq!(
    field("maxProofOfWorkBits"),
    stark_key::security::MAX_PROOF_OF_WORK_BITS
  );

  // Extract `| k => some v` tables from `def <fn_name>` in `Parameters.lean`.
  let table_entry = |fn_name: &str, key: usize| -> usize {
    let mut in_fn = false;
    let mut found = None;
    let prefix = format!("| {key} => some ");
    for line in source.lines() {
      let trimmed = line.trim();
      if trimmed.starts_with(&format!("def {fn_name} ")) {
        in_fn = true;
        continue;
      }
      if in_fn {
        if trimmed.is_empty()
          || trimmed.starts_with("def ")
          || trimmed.starts_with("theorem ")
        {
          break;
        }
        if let Some(rest) = trimmed.strip_prefix(&prefix) {
          let val: usize = rest
            .split(|c: char| !c.is_ascii_digit())
            .next()
            .unwrap()
            .parse()
            .unwrap();
          assert!(found.replace(val).is_none(), "{fn_name}({key}) set twice");
        }
      }
    }
    found.unwrap_or_else(|| panic!("{fn_name}({key}) not found in {path}"))
  };

  for lb in *stark_key::security::LOG_BLOWUP_RANGE.start()
    ..=*stark_key::security::LOG_BLOWUP_RANGE.end()
  {
    assert_eq!(
      table_entry("udMillibitsPerQuery", lb),
      stark_key::security::ud_millibits_per_query(lb).unwrap(),
      "udMillibitsPerQuery mismatch at log_blowup={lb}"
    );
    assert_eq!(
      table_entry("minQueriesForLogBlowup", lb),
      stark_key::security::min_queries_for_log_blowup(lb).unwrap(),
      "minQueriesForLogBlowup mismatch at log_blowup={lb}"
    );
  }

  // Verify `meetsSecurityFloor` wires all mirrored floors and agrees with
  // `stark_key::security::check` on boundary cases including `(4, 55, 0)` and `(4, 52, 32)`.
  let floor_section = source
    .split("def meetsSecurityFloor")
    .nth(1)
    .expect("meetsSecurityFloor missing");
  let floor_body = floor_section.split("theorem ").next().unwrap();
  for required in [
    "commitment.capHeight == 0",
    "fri.logFinalPolyLen == 0",
    "fri.maxLogArity == 1",
    "minQueriesForLogBlowup",
    "conjecturedSecurityBits",
    "provableUdMillibits",
    "minProvableUdBits",
    "johnsonMillibits",
    "minJohnsonBits",
  ] {
    assert!(
      floor_body.contains(required),
      "meetsSecurityFloor in {path} is missing {required}"
    );
  }

  let min_conj = field("minConjecturedSecurityBits");
  let min_ud = field("minProvableUdBits");
  let min_johnson = field("minJohnsonBits");
  let max_pow = field("maxProofOfWorkBits");
  let johnson_slack = field("johnsonSlackMillibitsPerQuery");
  let lean_meets_floor =
    |lb: usize, q: usize, cpow: usize, qpow: usize| -> bool {
      if !(1..=4).contains(&lb) || q == 0 || cpow > max_pow || qpow > max_pow {
        return false;
      }
      let min_q = table_entry("minQueriesForLogBlowup", lb);
      let ud_rate = table_entry("udMillibitsPerQuery", lb);
      let conj = lb * q + qpow;
      let ud_mb = q * ud_rate + qpow * 1000;
      let johnson_mb = (lb * 500 - johnson_slack) * q + qpow * 1000;
      q >= min_q
        && conj >= min_conj
        && ud_mb >= min_ud * 1000
        && johnson_mb >= min_johnson * 1000
    };

  for (lb, q, cpow, qpow, expected) in [
    (2, 100, 0, 20, true),   // default
    (1, 220, 0, 0, true),    // blowup 1 floor
    (2, 118, 0, 0, true),    // blowup 2 floor
    (3, 73, 0, 20, true),    // blowup 3 floor
    (4, 66, 0, 20, true),    // blowup 4 floor with PoW
    (4, 88, 0, 0, true),     // blowup 4 floor without PoW
    (4, 55, 0, 0, false),    // 220 conjectured, 50.2 UD (rejected)
    (4, 52, 0, 32, false),   // below query floor 53 (rejected)
    (2, 110, 0, 0, false),   // 220 conjectured, 74.6 UD (rejected)
    (3, 67, 0, 20, false),   // 221 conjectured, 75.6 UD (rejected)
    (4, 87, 0, 0, false),    // 79.3 UD (rejected)
    (2, 99, 0, 20, false),   // 218 conjectured (rejected)
    (2, 100, 0, 19, false),  // 219 conjectured (rejected)
    (2, 100, 33, 20, false), // commit PoW > 32 (rejected)
  ] {
    let rust_ok = Parameters {
      log_blowup: lb,
      num_queries: q,
      commit_proof_of_work_bits: cpow,
      query_proof_of_work_bits: qpow,
    }
    .check()
    .is_ok();
    let lean_ok = lean_meets_floor(lb, q, cpow, qpow);
    assert_eq!(
      rust_ok, expected,
      "Rust floor mismatch for ({lb}, {q}, {cpow}, {qpow})"
    );
    assert_eq!(
      lean_ok, expected,
      "Lean floor mismatch for ({lb}, {q}, {cpow}, {qpow})"
    );
    assert_eq!(
      lean_ok, rust_ok,
      "Lean/Rust parity mismatch for ({lb}, {q}, {cpow}, {qpow})"
    );
  }
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
    // 220 conjectured bits, but only 50.2 provable UD bits (HIGH-8).
    Parameters {
      log_blowup: 4,
      num_queries: 55,
      commit_proof_of_work_bits: 0,
      query_proof_of_work_bits: 0,
    },
    // 220 conjectured bits, but only 74.6 provable UD bits.
    Parameters {
      log_blowup: 2,
      num_queries: 110,
      commit_proof_of_work_bits: 0,
      query_proof_of_work_bits: 0,
    },
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
    Parameters { log_blowup: 2, num_queries: 118, ..base },
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
