//! Export an existing aggregate root without executing or normalizing it.
//! Artifact pins authorize the proving systems; an independently reconstructed
//! Ix claim determines the expected public statement of the raw batch proof.
use aggregate_controller::{
  Identity,
  protocol::{ChildKind, WordIdentity},
  store::{decode_wrapper, read_store},
};
use aiur::trace::stark::fri_parameter_bytes;
use ix_common::address::Address;
use ix_prover::{
  aggregate::{AGGR_ENTRY, AGGR_MAGIC},
  request::Environment,
  system::{ProtocolParameters, System},
};
use ixon::{Claim, shard::ShardManifest};
use serde_json::json;
use std::{error::Error, fs, path::Path, time::Instant};

const USAGE: &str = "usage:\n  export_root expected ENV MANIFEST OUTPUT [STRUCTURAL_ABOVE]\n  export_root extract IXVM_PACKAGE IXVM_ARTIFACT_BLAKE3 AGGR_PACKAGE AGGR_ARTIFACT_BLAKE3 PROOF EXPECTED_IX_CLAIM OUTPUT [STORE_DIR]\nPROOF is an Ixon proof file, or its content address when STORE_DIR is supplied.";

fn new_directory(path: &Path) -> Result<(), Box<dyn Error>> {
  fs::create_dir_all(path)?;
  if fs::read_dir(path)?.next().transpose()?.is_some() {
    return Err(
      format!("output directory is not empty: {}", path.display()).into(),
    );
  }
  Ok(())
}

fn pinned_system(path: &str, expected: &str) -> Result<System, Box<dyn Error>> {
  let pin = blake3::Hash::from_hex(expected)?;
  let (bytes, digest) = aiur::artifact::read(path.as_ref())?;
  if &digest.0 != pin.as_bytes() {
    return Err(
      format!("artifact differs from the independently expected pin: {path}")
        .into(),
    );
  }
  let package = aiur::artifact::Package::decode(&bytes)?;
  let (program, trace) = package.traced()?;
  let program = ix_prover::system::Program::new(program, trace, digest)?;
  Ok(System::prepare(&program, ProtocolParameters::default())?)
}

fn expected(args: &[String]) -> Result<(), Box<dyn Error>> {
  if !(3..=4).contains(&args.len()) {
    return Err(USAGE.into());
  }
  let environment = Environment::open(args[0].as_ref())?;
  let manifest_bytes = fs::read(&args[1])?;
  let manifest = ShardManifest::from_bytes(&manifest_bytes)?;
  let structural_above =
    args.get(3).map(|v| v.parse()).transpose()?.unwrap_or(0);
  let context = aggregate_controller::claim_context(environment.env(), false)?;
  let (statement, constants) = aggregate_controller::expected_from_manifest(
    &context,
    environment.env(),
    &manifest,
    structural_above,
  )?;
  let out = Path::new(&args[2]);
  new_directory(out)?;
  fs::write(out.join("ix-claim.bin"), &statement.claim_bytes)?;
  let report = json!({
    "format": "ix-expected-root-v1",
    "claim_blake3": blake3::hash(&statement.claim_bytes).to_hex().to_string(),
    "manifest_blake3": blake3::hash(&manifest_bytes).to_hex().to_string(),
    "constants": constants,
    "shards": manifest.shards.len(),
    "structural_above": structural_above,
    "assume_binding": false,
  });
  fs::write(out.join("identity.json"), serde_json::to_vec_pretty(&report)?)?;
  println!("{report}");
  Ok(())
}

fn proof_bytes(
  source: &str,
  store: Option<&String>,
) -> Result<Vec<u8>, Box<dyn Error>> {
  if let Some(store) = store {
    let address = Address::from_blake3_hash(blake3::Hash::from_hex(source)?);
    let bytes = read_store(store.as_ref(), &address)?;
    if Address::hash(&bytes) != address {
      return Err("proof store object differs from its content address".into());
    }
    Ok(bytes)
  } else {
    Ok(fs::read(source)?)
  }
}

fn decode_expected_root(
  encoded: &[u8],
  expected_claim: &[u8],
) -> Result<ixon::Proof, Box<dyn Error>> {
  let expected = Claim::from_bytes(expected_claim)?;
  if expected.commit().1 != expected_claim {
    return Err("expected Ix claim is not canonically encoded".into());
  }
  let wrapper = decode_wrapper(encoded)?;
  if wrapper.commit().1 != encoded {
    return Err("Ixon proof wrapper is not canonically encoded".into());
  }
  if wrapper.claim.commit().1 != expected_claim {
    return Err(
      "aggregate root differs from the independently expected Ix claim".into(),
    );
  }
  if !wrapper.proof.starts_with(AGGR_MAGIC) {
    return Err("proof is not an IXAGGR2 aggregate root".into());
  }
  Ok(wrapper)
}

fn extract(args: &[String]) -> Result<(), Box<dyn Error>> {
  if !(7..=8).contains(&args.len()) {
    return Err(USAGE.into());
  }
  let start = Instant::now();
  let ixvm = pinned_system(&args[0], &args[1])?;
  let aggr = pinned_system(&args[2], &args[3])?;
  let expected_claim = fs::read(&args[5])?;
  let encoded = proof_bytes(&args[4], args.get(7))?;
  let wrapper = decode_expected_root(&encoded, &expected_claim)?;
  let raw = wrapper
    .proof
    .strip_prefix(AGGR_MAGIC)
    .ok_or("proof is not an IXAGGR2 aggregate root")?;
  let ixvm_identity = ixvm.identity("IxVM::verify_claim", 8)?;
  let aggr_identity = aggr.identity(AGGR_ENTRY, 16)?;
  if ixvm_identity.call_channel != aggr_identity.call_channel {
    return Err(
      "IxVM and aggregation artifacts use different claim channels".into(),
    );
  }
  let identity = WordIdentity::new(
    aggr_identity.call_channel,
    &ixvm_identity.key,
    ixvm_identity.function_index,
    &aggr_identity.key,
    aggr_identity.function_index,
    fri_parameter_bytes(aggr.parameters().into()),
  );
  let outer = identity.outer_claim(ChildKind::Aggr, &expected_claim);
  let shards = aggr.verify(AGGR_ENTRY, &outer[2..], raw)?;
  let claims = identity.claims_bytes(&outer);
  let out = Path::new(&args[6]);
  new_directory(out)?;
  fs::write(out.join("root-vk.bin"), aggr.key())?;
  fs::write(out.join("root-claims.bin"), &claims)?;
  fs::write(out.join("root-proof.bin"), raw)?;
  fs::write(out.join("ix-claim.bin"), &expected_claim)?;
  fs::write(out.join("backend-allowed.bin"), &identity.allowed)?;
  fs::write(out.join("ixon-proof.bin"), &encoded)?;
  let report = json!({
    "format": "ix-raw-root-export-v1",
    "ixvm_artifact_blake3": blake3::Hash::from(*ixvm.program().identity()).to_hex().to_string(),
    "aggr_artifact_blake3": blake3::Hash::from(*aggr.program().identity()).to_hex().to_string(),
    "ixon_proof_blake3": blake3::hash(&encoded).to_hex().to_string(),
    "ix_claim_blake3": blake3::hash(&expected_claim).to_hex().to_string(),
    "key_blake3": blake3::hash(aggr.key()).to_hex().to_string(),
    "claims_blake3": blake3::hash(&claims).to_hex().to_string(),
    "proof_blake3": blake3::hash(raw).to_hex().to_string(),
    "claim_words": outer,
    "parameters": aiur::trace::stark::Parameters::from(aggr.parameters()),
    "shards": shards,
    "proof_bytes": raw.len(),
    "normalization_performed": false,
    "verified": true,
    "elapsed_seconds": start.elapsed().as_secs_f64(),
  });
  fs::write(out.join("identity.json"), serde_json::to_vec_pretty(&report)?)?;
  println!("{report}");
  Ok(())
}

fn main() -> Result<(), Box<dyn Error>> {
  let args = std::env::args().skip(1).collect::<Vec<_>>();
  match args.first().map(String::as_str) {
    Some("expected") => expected(&args[1..]),
    Some("extract") => extract(&args[1..]),
    _ => Err(USAGE.into()),
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  fn claim(name: &[u8]) -> Claim {
    Claim::Catalog { members: Address::hash(name) }
  }

  #[test]
  fn root_extraction_keeps_the_original_payload_and_claim() {
    let claim = claim(b"members");
    let expected = claim.commit().1;
    let raw = [1, 2, 3, 4];
    let mut payload = AGGR_MAGIC.to_vec();
    payload.extend_from_slice(&raw);
    let encoded = ixon::Proof::new(claim, payload.clone()).commit().1;
    let decoded = decode_expected_root(&encoded, &expected).unwrap();
    assert_eq!(decoded.proof, payload);
    assert_eq!(decoded.claim.commit().1, expected);
    assert_eq!(decoded.proof.strip_prefix(AGGR_MAGIC).unwrap(), raw);
  }

  #[test]
  fn root_extraction_rejects_a_different_expected_claim_and_proof_kind() {
    let expected = claim(b"members").commit().1;
    let encoded =
      ixon::Proof::new(claim(b"other"), AGGR_MAGIC.to_vec()).commit().1;
    assert!(decode_expected_root(&encoded, &expected).is_err());
    let encoded =
      ixon::Proof::new(claim(b"members"), b"IXAIUR2\0".to_vec()).commit().1;
    assert!(decode_expected_root(&encoded, &expected).is_err());
  }

  #[test]
  fn root_extraction_rejects_trailing_envelope_or_expected_claim_bytes() {
    let expected = claim(b"members").commit().1;
    let encoded =
      ixon::Proof::new(claim(b"members"), AGGR_MAGIC.to_vec()).commit().1;
    let mut trailing_proof = encoded.clone();
    trailing_proof.push(0);
    assert!(decode_expected_root(&trailing_proof, &expected).is_err());
    let mut trailing_claim = expected;
    trailing_claim.push(0);
    assert!(decode_expected_root(&encoded, &trailing_claim).is_err());
  }
}
