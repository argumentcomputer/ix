//! Fixed saved intermediate proof and independently expected Init claim.
#[path = "init_claim.rs"]
mod init_claim;
pub(crate) use init_claim::INIT_PUBLIC_WORDS;
use ix_proof_compression::fri::*;
use multi_stark::prover::Proof;
use multi_stark::types::GoldilocksBlake3Config;
use multi_stark::types::Val;
use p3_field::{PrimeCharacteristicRing, PrimeField64};
use std::{fs, path::Path};

pub(crate) struct Fixture {
  pub key: VerifierKey,
  pub proof: Proof<GoldilocksBlake3Config>,
  pub public: [Val; 18],
  pub claims: Vec<Vec<Val>>,
  pub profile: ProofProfile,
  pub schema: Statement<StatementSlot>,
}

pub(crate) fn load(dir: &Path) -> Result<Fixture, Box<dyn std::error::Error>> {
  let key = VerifierKey::from_bytes(&fs::read(dir.join("outer-vk.bin"))?)?;
  let bytes = fs::read(dir.join("outer-proof.bin"))?;
  let proof = Proof::<GoldilocksBlake3Config>::from_bytes(&bytes)?;
  if proof.to_bytes()? != bytes {
    return Err("noncanonical proof".into());
  }
  // Independently expected Init public values.
  let public = INIT_PUBLIC_WORDS.map(Val::from_u64);
  let claims = claims_from_bytes(&fs::read(dir.join("outer-claims.bin"))?)?;
  let expected: Vec<_> = std::iter::once(Val::ZERO)
    .chain(public)
    .enumerate()
    .map(|(i, v)| vec![Val::from_u8(107), Val::ONE, Val::from_usize(i), v])
    .collect();
  if !claims.starts_with(&expected) {
    return Err(
      "compressed proof does not expose the expected Init claim".into(),
    );
  }
  let refs: Vec<_> = claims.iter().map(Vec::as_slice).collect();
  key
    .system()
    .verify_multiple_claims(&refs, &proof)
    .map_err(|e| format!("saved recursive proof: {e:?}"))?;
  for i in 0..18 {
    let mut wrong = claims.clone();
    wrong[i + 1][3] += Val::ONE;
    assert!(
      key
        .system()
        .verify_multiple_claims(
          &wrong.iter().map(Vec::as_slice).collect::<Vec<_>>(),
          &proof
        )
        .is_err()
    );
  }
  println!(
    "Saved {}-byte recursive FRI proof verified; all 18 altered Init claim words rejected",
    bytes.len()
  );
  let active = vec![true; key.system().circuits.len()];
  let logs: Vec<_> = key
    .system()
    .circuits
    .iter()
    .map(|c| {
      u8::try_from(
        c.preprocessed_height.checked_ilog2().ok_or("missing trace height")?,
      )
      .map_err(|error| format!("invalid trace height: {error}"))
    })
    .collect::<Result<_, _>>()?;
  if proof.active != active || proof.log_degrees != logs {
    return Err("compressed proof profile differs from the key".into());
  }
  let profile = ProofProfile {
    envelope: Envelope::Ordinary,
    active,
    log_degrees: logs,
    claim_lengths: claims.iter().map(Vec::len).collect(),
    message_lengths: vec![],
    max_field_retries: 2,
  };
  let mut schema = Statement {
    claims: claims
      .iter()
      .map(|c| {
        c.iter().copied().map(StatementSlot::Constant).collect::<Vec<_>>()
      })
      .collect::<Vec<_>>(),
    messages: vec![],
  };
  for c in &mut schema.claims[1..19] {
    c[3] = StatementSlot::Public;
  }
  Ok(Fixture { key, proof, public, claims, profile, schema })
}

fn claims_from_bytes(bytes: &[u8]) -> Result<Vec<Vec<Val>>, String> {
  let (words, remainder) = bytes.as_chunks::<8>();
  if !remainder.is_empty() {
    return Err("unaligned claims".into());
  }
  let mut words = words.iter();
  let n = u64::from_le_bytes(*words.next().ok_or("missing claims count")?);
  let mut claims = Vec::new();
  for _ in 0..n {
    let len = u64::from_le_bytes(*words.next().ok_or("missing claim length")?);
    let mut claim = Vec::new();
    for _ in 0..len {
      let v = u64::from_le_bytes(*words.next().ok_or("missing claim value")?);
      if v >= Val::ORDER_U64 {
        return Err("noncanonical claim".into());
      }
      claim.push(Val::from_u64(v));
    }
    claims.push(claim);
  }
  if words.next().is_some() {
    return Err("trailing claims".into());
  }
  Ok(claims)
}
