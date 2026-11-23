//! The saved intermediate Protocol v6 (`F_p^3`) FRI proof and the statement it
//! exposes.
use super::claims::{ClaimTemplate, decode_claims};
use crate::fri::*;
use multi_stark::prover::Proof;
use multi_stark::types::GoldilocksBlake3V6Config;
use multi_stark::types::Val;
use p3_field::PrimeCharacteristicRing;
use std::{fs, path::Path};

/// Independently expected public values of the Init proof fixture.
#[cfg(test)]
pub(crate) const INIT_PUBLIC_WORDS: [u64; 18] = [
  0, 293, 3008464260, 3936129970, 1088962797, 1141056675, 2347219926,
  1176003176, 683533119, 3085659920, 1422858688, 3165160492, 1899567894,
  784981652, 376864732, 1915641123, 2034217541, 2163067803,
];

pub(crate) struct Fixture {
  pub key: VerifierKey,
  pub proof: Proof<GoldilocksBlake3V6Config>,
  pub public: [Val; 18],
  pub claims: Vec<Vec<Val>>,
  pub profile: ProofProfile,
  pub schema: Statement<StatementSlot>,
}

#[tracing::instrument(
  level = "info",
  skip_all,
  name = "compression/load_input"
)]
pub(crate) fn load(dir: &Path) -> Result<Fixture, Box<dyn std::error::Error>> {
  let key = VerifierKey::from_bytes(&fs::read(dir.join("outer-vk.bin"))?)?;
  let bytes = fs::read(dir.join("outer-proof.bin"))?;
  let proof = Proof::<GoldilocksBlake3V6Config>::from_bytes(&bytes)?;
  if proof.to_bytes()? != bytes {
    return Err("noncanonical proof".into());
  }
  let claims = decode_claims(&fs::read(dir.join("outer-claims.bin"))?)?;
  let statement = ClaimTemplate::from_claims(&claims, 18)?;
  let public: [Val; 18] = statement
    .public_values(&claims)?
    .try_into()
    .map_err(|_words| "compressed proof does not expose 18 statement words")?;
  if statement.template[0][0] != Val::from_u8(super::lowering::FRI_NAMESPACE) {
    return Err("compressed proof does not expose the statement rows".into());
  }
  let refs: Vec<_> = claims.iter().map(Vec::as_slice).collect();
  key
    .system()
    .verify_multiple_claims(&refs, &proof)
    .map_err(|e| format!("saved recursive proof: {e:?}"))?;
  eprintln!("Saved {}-byte recursive FRI proof verified", bytes.len());
  let profile = super::lowering::fri_profile(&key, &claims)?;
  if proof.active != profile.active || proof.log_degrees != profile.log_degrees
  {
    return Err("compressed proof profile differs from the key".into());
  }
  let schema = statement.schema();
  Ok(Fixture { key, proof, public, claims, profile, schema })
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::kzg::curve::{Bls12381, Bn254};
  use crate::pipeline::claims::encode_claims;
  use crate::pipeline::stage::{Prepared, prepare_kzg_for, scalar_statement};
  use crate::test_support::TempDir;
  use multi_stark::plonkish::CircuitBuilder;
  use multi_stark::types::{CommitmentParameters, FriParameters};

  #[test]
  fn legacy_v5_init_fri_fixture_is_rejected_fail_closed() {
    let dir =
      Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/init-fri");
    let legacy_vk = fs::read(dir.join("outer-vk.bin")).unwrap();
    assert!(
      VerifierKey::from_bytes(&legacy_vk).is_err(),
      "legacy v5 (Fp^2) outer-vk.bin must be rejected fail-closed"
    );
    assert!(
      load(&dir).is_err(),
      "legacy v5 (Fp^2) init-fri fixture must be rejected fail-closed"
    );
  }

  #[test]
  fn v6_init_fri_proof_and_public_statement_verify_and_translate_both_curves() {
    let expected = INIT_PUBLIC_WORDS.map(Val::from_u64);
    let mut b = CircuitBuilder::<Val>::new();
    let table =
      b.fixed_table("pair", vec![vec![expected[0]], vec![expected[1]]]);
    let mut wires = Vec::with_capacity(expected.len());
    for i in 0..expected.len() {
      wires.push(b.public_input(format!("w[{i}]")));
    }
    b.lookup(table, &[wires[0]]);
    b.lookup(table, &[wires[1]]);
    let circuit = b.finish();
    let mut witness = circuit.witness();
    for (&wire, &val) in wires.iter().zip(&expected) {
      witness.set(wire, val).unwrap();
    }
    let assignment = witness.generate().unwrap();
    let config = GoldilocksBlake3V6Config::new(
      CommitmentParameters { log_blowup: 2, cap_height: 0 },
      FriParameters {
        log_final_poly_len: 0,
        max_log_arity: 1,
        num_queries: 135,
        commit_proof_of_work_bits: 0,
        query_proof_of_work_bits: 0,
      },
    );
    let (verifier, proof) =
      Prepared { circuit, assignment }.prove_fri(config, 64).unwrap();
    let claims = verifier.statement.claims(&expected).unwrap();
    let dir = TempDir::new("v6-init-fri-roundtrip");
    fs::write(dir.join("outer-vk.bin"), verifier.key.to_bytes().unwrap())
      .unwrap();
    fs::write(dir.join("outer-proof.bin"), proof.to_bytes().unwrap()).unwrap();
    fs::write(dir.join("outer-claims.bin"), encode_claims(&claims)).unwrap();

    let fixture = load(&dir).unwrap();
    assert_eq!(fixture.public, expected);
    for i in 0..fixture.public.len() {
      let mut wrong = fixture.claims.clone();
      wrong[i + 1][3] += Val::ONE;
      assert!(
        fixture
          .key
          .system()
          .verify_multiple_claims(
            &wrong.iter().map(Vec::as_slice).collect::<Vec<_>>(),
            &fixture.proof,
          )
          .is_err(),
        "altered public word {i} was accepted",
      );
    }
    let plan =
      VerifierPlan::validate(&fixture.key, fixture.profile, Default::default())
        .unwrap();
    plan.identity(&fixture.schema).unwrap();

    // Verify translation of the Protocol v6 outer FRI proof into BOTH BN254
    // and BLS12-381 scalar-field KZG stage-1 circuits.
    let bn254 = prepare_kzg_for::<Bn254>(
      &verifier,
      &proof,
      &expected,
      Default::default(),
    )
    .unwrap();
    assert_eq!(bn254.public_values(), scalar_statement::<Bn254>(&expected));
    let bls = prepare_kzg_for::<Bls12381>(
      &verifier,
      &proof,
      &expected,
      Default::default(),
    )
    .unwrap();
    assert_eq!(bls.public_values(), scalar_statement::<Bls12381>(&expected));
  }
}
