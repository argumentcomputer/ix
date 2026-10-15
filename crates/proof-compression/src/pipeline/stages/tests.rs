use super::*;
use multi_stark::plonkish::CircuitBuilder;
use multi_stark::types::{CommitmentParameters, FriParameters};

#[test]
fn unsupported_fri_profiles_fail_before_proving() {
  for (cap, arity, final_log, queries) in
    [(1, 1, 0, 2), (0, 2, 0, 2), (0, 1, 1, 2), (0, 1, 0, 0)]
  {
    let config = || {
      GoldilocksBlake3Config::new(
        CommitmentParameters { log_blowup: 2, cap_height: cap },
        FriParameters {
          log_final_poly_len: final_log,
          max_log_arity: arity,
          num_queries: queries,
          commit_proof_of_work_bits: 0,
          query_proof_of_work_bits: 0,
        },
      )
    };
    if cfg!(feature = "cuda") && (cap != 0 || arity > 1) {
      assert!(std::panic::catch_unwind(config).is_err());
    } else {
      assert!(arithmetic(Val::ONE, 2).prove_fri(config(), 32).is_err());
    }
  }
}

fn arithmetic<F: Field>(value: F, repetitions: usize) -> Prepared<F> {
  let mut b = CircuitBuilder::new();
  let table = b.fixed_table("small", vec![vec![F::ONE], vec![F::TWO]]);
  let x = b.public_input("x");
  for _ in 0..repetitions {
    b.lookup(table, &[x]);
  }
  let square = b.mul(x, x);
  b.expose_public(square);
  let circuit = b.finish();
  let mut witness = circuit.witness();
  witness.set(x, value).unwrap();
  let assignment = witness.generate().unwrap();
  Prepared { circuit, assignment }
}

#[test]
fn fri_stage_preserves_publics_through_foreign_translation() -> Result<()> {
  for value in [Val::ONE, Val::TWO] {
    let expected = [value, value * value];
    let prepared = arithmetic(value, 2);
    let config = || {
      GoldilocksBlake3Config::new(
        CommitmentParameters { log_blowup: 2, cap_height: 0 },
        FriParameters {
          log_final_poly_len: 0,
          max_log_arity: 1,
          num_queries: 2,
          commit_proof_of_work_bits: 0,
          query_proof_of_work_bits: 0,
        },
      )
    };
    let local = setup::fri(arithmetic(value, 2).circuit, config(), 32)?;
    let (verifier, proof) = prepared.prove_fri(config(), 32)?;
    assert_eq!(local.to_bytes()?, verifier.to_bytes()?);
    let key_bytes = verifier.to_bytes()?;
    let verifier = FriVerifier::from_bytes(&key_bytes)?;
    assert_eq!(verifier.to_bytes()?, key_bytes);
    assert!(
      FriVerifier::from_bytes(&key_bytes[..key_bytes.len() - 1]).is_err()
    );
    let mut extra_key = key_bytes;
    extra_key.push(0);
    assert!(FriVerifier::from_bytes(&extra_key).is_err());
    let mut bad = FriVerifier::from_bytes(&verifier.to_bytes()?)?;
    bad.statement.locations[0] = (usize::MAX, 3);
    assert!(FriVerifier::from_bytes(&bad.to_bytes()?).is_err());
    assert!(KzgVerifier::from_bytes(&verifier.to_bytes()?).is_err());
    verifier.verify(&proof, &expected)?;
    assert!(
      verifier.verify(&proof, &[value, value * value + Val::ONE]).is_err()
    );
    assert!(verifier.verify(&proof, &expected[..1]).is_err());
    let translated =
      prepare_kzg(&verifier, &proof, &expected, Default::default())?;
    assert_eq!(translated.public_values(), scalar_statement(&expected));
    assert!(
      prepare_kzg(
        &verifier,
        &proof,
        &[value + Val::ONE, value * value],
        Default::default()
      )
      .is_err()
    );
  }
  Ok(())
}

#[test]
fn kzg_stages_derive_claims_for_different_layouts_and_parameters() -> Result<()>
{
  for (height, value) in [(32, Scalar::ONE), (128, Scalar::TWO)] {
    let stage = arithmetic(value, 50);
    let expected = [value, value * value];
    let srs = Arc::new(Srs::unsafe_dev_setup(height, &height.to_le_bytes()));
    srs.validate()?;
    let local = setup::kzg(arithmetic(value, 50).circuit, srs.clone(), height)?;
    let (verifier, proof) = stage.prove_kzg(srs.clone(), height)?;
    assert_eq!(local.to_bytes()?, verifier.to_bytes()?);
    drop(local);
    let key_bytes = verifier.to_bytes()?;
    let verifier = KzgVerifier::from_bytes(&key_bytes)?;
    assert_eq!(verifier.to_bytes()?, key_bytes);
    assert!(
      KzgVerifier::from_bytes(&key_bytes[..key_bytes.len() - 1]).is_err()
    );
    let mut extra_key = key_bytes;
    extra_key.push(0);
    assert!(KzgVerifier::from_bytes(&extra_key).is_err());
    let mut bad = KzgVerifier::from_bytes(&verifier.to_bytes()?)?;
    bad.system.circuits[0].graph.max_constraint_degree += 1;
    assert!(KzgVerifier::from_bytes(&bad.to_bytes()?).is_err());
    let mut bad = KzgVerifier::from_bytes(&verifier.to_bytes()?)?;
    bad.system.circuits[0].preprocessed_height = 0;
    assert!(KzgVerifier::from_bytes(&bad.to_bytes()?).is_err());
    let mut other = KzgVerifier::from_bytes(&verifier.to_bytes()?)?;
    other.params = VerifierParams::from_srs(&Srs::unsafe_dev_setup(
      height,
      b"other-parameters",
    ));
    let other = KzgVerifier::from_bytes(&other.to_bytes()?)?;
    assert!(other.verify(&proof, &expected).is_err());
    verifier.verify(&proof, &expected)?;
    assert!(
      verifier.verify(&proof, &[value, value * value + Scalar::ONE]).is_err()
    );
    assert!(verifier.verify(&proof, &expected[..1]).is_err());
    assert!(verifier.system.circuits.iter().all(|c| c.preprocessed.is_none()));
    // The verifier does not retain the proving powers.
    assert_eq!(Arc::strong_count(&srs), 1);
    if height == 128 {
      let claim: Vec<_> = expected
        .iter()
        .map(|v| Val::from_u64(v.canonical_limbs_le()[0]))
        .collect();
      let recursive = prepare_recursive(&verifier, &proof, &claim)?;
      assert!(recursive.circuit().stats().publics > claim.len());
      let mut wrong = claim;
      wrong[0] += Val::ONE;
      assert!(prepare_recursive(&verifier, &proof, &wrong).is_err());
    }
  }
  let srs = Arc::new(Srs::unsafe_dev_setup(8, b"too-small"));
  assert!(arithmetic(Scalar::ONE, 2).prove_kzg(srs, 16).is_err());
  Ok(())
}

#[test]
fn kzg_table_merging_respects_the_callers_height_bound() -> Result<()> {
  fn tables() -> Prepared<Scalar> {
    let mut builder = CircuitBuilder::new();
    let x = builder.public_input("x");
    for name in ["first", "second"] {
      let table = builder.fixed_table(
        name,
        (0..64).map(|i| vec![Scalar::from_u64(i)]).collect(),
      );
      builder.lookup(table, &[x]);
    }
    let circuit = builder.finish();
    let mut witness = circuit.witness();
    witness.set(x, Scalar::from_u8(7)).unwrap();
    let assignment = witness.generate().unwrap();
    Prepared { circuit, assignment }
  }

  let srs = Arc::new(Srs::unsafe_dev_setup(256, b"bounded-table-merge"));
  assert!(tables().prove_kzg(srs.clone(), 64).is_err());
  assert!(setup::kzg(tables().circuit, srs.clone(), 64).is_err());
  let local = setup::kzg(tables().circuit, srs.clone(), 128)?;
  let (verifier, proof) = tables().prove_kzg(srs, 128)?;
  assert_eq!(local.to_bytes()?, verifier.to_bytes()?);
  assert!(
    verifier.system.circuits.iter().all(|c| c.preprocessed_height <= 128)
  );
  verifier.verify(&proof, &[Scalar::from_u8(7)])?;
  Ok(())
}
