//! The saved intermediate FRI proof and the statement it exposes.
use super::claims::{ClaimTemplate, decode_claims};
use crate::fri::*;
use multi_stark::prover::Proof;
use multi_stark::types::GoldilocksBlake3Config;
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
  pub proof: Proof<GoldilocksBlake3Config>,
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
  let proof = Proof::<GoldilocksBlake3Config>::from_bytes(&bytes)?;
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

  #[test]
  fn saved_init_fri_proof_and_public_statement_verify() {
    let fixture = load(
      &Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/init-fri"),
    )
    .unwrap();
    assert_eq!(fixture.public, INIT_PUBLIC_WORDS.map(Val::from_u64));
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
  }
}
