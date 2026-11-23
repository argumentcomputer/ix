use super::*;
use multi_stark::batch::Retention;

/// Protocol v6 (Fp^3) default parameters clear the 128-bit floor with headroom.
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
    (2, 128, 0, 20)
  );
  assert_eq!(p.conjectured_bits(), 276);
  assert!(p.conjectured_bits() >= stark_key::security::MIN_CONJECTURED_BITS);
  assert_eq!(
    stark_key::security::johnson_millibits(&p.commitment(), &p.fri()),
    142_240
  );
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
    (2, 128, 0, 20, true), // Protocol v6 default (142.2b Johnson, 106.8b UD)
    (1, 282, 0, 0, true),  // blowup 1 floor (128.3b Johnson, 117.0b UD)
    (2, 135, 0, 0, true),  // blowup 2 floor without PoW (128.9b Johnson)
    (2, 114, 0, 20, true), // blowup 2 floor with PoW (128.9b Johnson)
    (3, 78, 0, 20, true), // blowup 3 shrinker --stark-128 (133.5b Johnson, 84.7b UD)
    (4, 66, 0, 20, true), // blowup 4 floor with PoW (149.0b Johnson, 80.2b UD)
    (4, 88, 0, 0, true),  // blowup 4 floor without PoW
    (2, 100, 0, 20, false), // retired v5 default: 115.5b Johnson (< 128b, rejected)
    (2, 113, 0, 20, false), // 127.9b Johnson (< 128b, rejected)
    (3, 74, 0, 20, false),  // 127.7b Johnson (< 128b, rejected)
    (4, 58, 0, 20, false),  // 133.4b Johnson, but 72.9b UD (< 80b, rejected)
    (4, 55, 0, 0, false),   // 220 conjectured, 50.2 UD (rejected)
    (4, 52, 0, 32, false),  // below query floor 53 (rejected)
    (2, 110, 0, 0, false),  // 220 conjectured, 74.6 UD (rejected)
    (4, 87, 0, 0, false),   // 79.3 UD (rejected)
    (2, 128, 33, 20, false), // commit PoW > 32 (rejected)
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

  // Mirror checks for the `v6` 128-bit security profile constants and tables.
  assert_eq!(
    field("extensionDegreeV6"),
    stark_key::security::EXTENSION_DEGREE_V6
  );
  assert_eq!(
    field("protocolVersionV6"),
    stark_key::security::PROTOCOL_VERSION_V6
  );
  assert_eq!(
    field("minProvableSecurityBits128"),
    stark_key::security::MIN_PROVABLE_SECURITY_BITS_128
  );
  assert_eq!(
    field("digestBytesXof48"),
    stark_key::security::DIGEST_BYTES_XOF48
  );
  for lb in *stark_key::security::LOG_BLOWUP_RANGE.start()
    ..=*stark_key::security::LOG_BLOWUP_RANGE.end()
  {
    assert_eq!(
      table_entry("minQueriesForLogBlowup128Ud", lb),
      stark_key::security::min_queries_for_log_blowup_128_ud(lb).unwrap(),
      "minQueriesForLogBlowup128Ud mismatch at log_blowup={lb}"
    );
    assert_eq!(
      table_entry("minQueriesForLogBlowup128Johnson", lb),
      stark_key::security::min_queries_for_log_blowup_128_johnson(lb).unwrap(),
      "minQueriesForLogBlowup128Johnson mismatch at log_blowup={lb}"
    );
  }

  let ext_v6 = field("extensionDegreeV6");
  let ver_v6 = field("protocolVersionV6");
  let min_128 = field("minProvableSecurityBits128");
  let lean_meets_128_ud =
    |ext: usize, ver: usize, lb: usize, q: usize, cpow: usize, qpow: usize| {
      if ext < ext_v6 || ver < ver_v6 || !lean_meets_floor(lb, q, cpow, qpow) {
        return false;
      }
      let min_q = table_entry("minQueriesForLogBlowup128Ud", lb);
      let ud_rate = table_entry("udMillibitsPerQuery", lb);
      q >= min_q && q * ud_rate + qpow * 1000 >= min_128 * 1000
    };
  let lean_meets_128_johnson =
    |ext: usize, ver: usize, lb: usize, q: usize, cpow: usize, qpow: usize| {
      if ext < ext_v6 || ver < ver_v6 || !lean_meets_floor(lb, q, cpow, qpow) {
        return false;
      }
      let min_q = table_entry("minQueriesForLogBlowup128Johnson", lb);
      let johnson_mb = (lb * 500 - johnson_slack) * q + qpow * 1000;
      q >= min_q && johnson_mb >= min_128 * 1000
    };

  for (ext, ver, lb, q, cpow, qpow, want_ud, want_j) in [
    (3, 6, 2, 160, 0, 20, true, true), // v6 UD 128b
    (3, 6, 2, 118, 0, 20, false, true), // v6 Johnson 128b lower edge
    (3, 6, 2, 128, 0, 20, false, true), // v6 Johnson 128b recommended
    (3, 6, 3, 78, 0, 20, false, true), // v6 Johnson lb=3
    (3, 6, 4, 66, 0, 20, false, true), // v6 Johnson lb=4
    (2, 6, 2, 160, 0, 20, false, false), // Fp2 rejected
    (3, 5, 2, 160, 0, 20, false, false), // v5 protocol rejected
    (3, 6, 2, 100, 0, 20, false, false), // v5 default rejected
    (3, 6, 4, 55, 0, 0, false, false), // deceptive (4,55,0) rejected
    (3, 6, 2, 159, 0, 20, false, true), // 127.802 UD, 171.845 Johnson
    (3, 6, 2, 113, 0, 20, false, false), // 127.915 Johnson (< 128)
  ] {
    let p = Parameters {
      log_blowup: lb,
      num_queries: q,
      commit_proof_of_work_bits: cpow,
      query_proof_of_work_bits: qpow,
    };
    let rust_ud =
      stark_key::security::check_128_ud(ext, ver, &p.commitment(), &p.fri())
        .is_ok();
    let rust_j = stark_key::security::check_128_johnson(
      ext,
      ver,
      &p.commitment(),
      &p.fri(),
    )
    .is_ok();
    let lean_ud = lean_meets_128_ud(ext, ver, lb, q, cpow, qpow);
    let lean_j = lean_meets_128_johnson(ext, ver, lb, q, cpow, qpow);
    assert_eq!(rust_ud, want_ud, "Rust 128 UD mismatch");
    assert_eq!(lean_ud, want_ud, "Lean 128 UD mismatch");
    assert_eq!(rust_j, want_j, "Rust 128 Johnson mismatch");
    assert_eq!(lean_j, want_j, "Lean 128 Johnson mismatch");
  }
}

#[test]
fn backends_reject_parameters_below_the_floor() {
  let (program, artifact) = identity(false);
  let plan = TracePlan::new(&program, activate(artifact)).unwrap();
  let weak = [
    // #678's original default, 64 conjectured bits.
    Parameters { log_blowup: 1, num_queries: 64, ..parameters() },
    Parameters { num_queries: 281, ..parameters() },
    // Retired v5 default (115.5b Johnson < 128b).
    Parameters {
      num_queries: 100,
      query_proof_of_work_bits: 20,
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
    Parameters { log_blowup: 2, num_queries: 135, ..base },
    Parameters { num_queries: 283, ..base },
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
