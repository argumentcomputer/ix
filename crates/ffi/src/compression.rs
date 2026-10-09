//! Locally generated fixed compression configurations. No verifier import.
mod local;
use crate::aiur::aggregate::protocol::{
  aggregate_outer_claim, serialize_claims,
};
use aiur::{
  synthesis::{AiurProof, AiurSystem},
  vk_codec::{AiurVerifyingKey, aiur_system_to_bytes},
};
use ix_proof_compression::{
  kzg::{Srs, VerifierParams},
  pipeline::{self, FixedRoot, RecursiveVerifier},
};
use ixvm_codegen::aiur_ix_aggr_runner::{
  AggrAdvice, aggr_io_buffer, execute_ix_aggr,
};
use lean_ffi::object::{
  LeanArray, LeanBorrowed, LeanByteArray, LeanExternal, LeanIOResult, LeanNat,
  LeanOwned, LeanString,
};
use multi_stark::types::{CommitmentParameters, GoldilocksBlake3Config};
use std::{fs::File, io::BufReader, path::Path, sync::Arc};

const MAGIC: &[u8; 8] = b"IXCMP002";
const FRI_HEIGHT: usize = 1 << 20;

fn configuration(
  system: &AiurSystem,
  root_log: u32,
  claim_len: usize,
) -> pipeline::Result<FixedRoot> {
  let mut widths = system.toplevel().memory_sizes.clone();
  widths.sort_unstable();
  FixedRoot::new(root_log, widths, claim_len)
}

fn fri_config(key: &AiurVerifyingKey) -> GoldilocksBlake3Config {
  GoldilocksBlake3Config::new(
    CommitmentParameters { log_blowup: 2, cap_height: 0 },
    key.fri_parameters(),
  )
}

fn load_srs(path: &Path) -> pipeline::Result<Arc<Srs>> {
  Ok(Arc::new(Srs::from_reader(BufReader::new(File::open(path)?))?))
}

fn setup(
  system: &AiurSystem,
  dir: &Path,
  srs_path: &Path,
  dev: bool,
  root_log: u32,
  kzg_log: u32,
  claim_len: usize,
) -> pipeline::Result<String> {
  if !(1..=26).contains(&root_log) || !(16..=26).contains(&kzg_log) {
    return Err(
      "root log-height must be 1–26; KZG log-height must be 16–26".into(),
    );
  }
  if dev == !srs_path.as_os_str().is_empty() {
    return Err("specify exactly one of --srs FILE or --dev-srs".into());
  }
  let vk = aiur_system_to_bytes(system)?;
  let key = AiurVerifyingKey::from_bytes(&vk)?;
  let root = configuration(system, root_log, claim_len)?;
  eprintln!("[compression setup] loading KZG parameters");
  let srs = if dev {
    let srs =
      Srs::unsafe_dev_setup(1usize << kzg_log, b"ix-compression-cli-dev-v1");
    srs.validate()?;
    Arc::new(srs)
  } else {
    load_srs(srs_path)?
  };
  if srs.max_len() < 1usize << kzg_log {
    return Err("SRS is smaller than the KZG partition height".into());
  }
  let params = VerifierParams::from_srs(&srs).to_bytes()?;
  let settings =
    local::Settings::new(&vk, &params, root_log, kzg_log, claim_len);
  let id = settings.id();
  if dir.join(&id).exists() {
    let entry = local::load(dir, &id, &vk)?;
    RecursiveVerifier::from_bytes(&entry.key_bytes)?;
    local::reuse(dir, &id, srs_path, dev.then_some(srs.as_ref()))?;
    return Ok(id);
  }
  eprintln!(
    "[compression setup] deriving fixed verifier (no certificate or proof input)"
  );
  let verifier = pipeline::setup(
    &key,
    &root,
    srs.clone(),
    fri_config(&key),
    FRI_HEIGHT,
    1usize << kzg_log,
  )?;
  let bytes = verifier.to_bytes()?;
  RecursiveVerifier::from_bytes(&bytes)?;
  local::publish(
    dir,
    &settings,
    &bytes,
    srs_path,
    dev.then_some(srs.as_ref()),
  )?;
  Ok(id)
}

fn compress(
  system: &AiurSystem,
  allowed: &[u8],
  aggr_idx: usize,
  certificate: &[u8],
  bytes: &[u8],
  dir: &Path,
) -> pipeline::Result<Vec<u8>> {
  let vk = aiur_system_to_bytes(system)?;
  let entry = local::load(dir, &local::active(dir)?, &vk)?;
  let expected = aggregate_outer_claim(aggr_idx, allowed, certificate);
  if expected.len() != entry.settings.claim_len {
    return Err("compression claim shape changed; run setup again".into());
  }
  let key = AiurVerifyingKey::from_bytes(&vk)?;
  let fixed = configuration(system, entry.settings.root_log, expected.len())?;
  let proof = AiurProof::from_bytes(bytes)?;
  let advice = system.proof_to_advice_bytes(&expected, &proof)?;
  let srs = load_srs(&entry.srs_path)?;
  if blake3::hash(&VerifierParams::from_srs(&srs).to_bytes()?).to_hex().as_str()
    != entry.settings.params_hash
  {
    return Err(
      "SRS no longer matches the local compression configuration".into(),
    );
  }
  drop(proof);
  let claims = serialize_claims(&[&expected]);
  let mut io = aggr_io_buffer(&AggrAdvice {
    shape: 1,
    proof_advice: [&advice, &[]],
    ixvm_vk: &[],
    self_vk: &vk,
    child_claims: [&claims, &[]],
    output_claim: certificate,
    allowed,
    preimages: &[],
    trees: &[],
    paths: &[],
  });
  eprintln!(
    "[compress] normalizing the aggregate root to the configured trace bounds"
  );
  // The aggregate call is [channel, entrypoint, inputs…], with no outputs.
  let input = &expected[2..];
  let (record, output) =
    execute_ix_aggr(system.toplevel(), aggr_idx, input.to_vec(), &mut io)?;
  if !output.is_empty() {
    return Err("aggregate normalizer returned unexpected outputs".into());
  }
  drop(advice);
  let (claim, proof) = system.prove_from_execution_normalized(
    aggr_idx,
    input,
    &io,
    record,
    &output,
    entry.settings.root_log,
  )?;
  if claim != expected {
    return Err("normalizer changed the certificate claim".into());
  }
  drop(io);
  eprintln!("[compress] normalized root → FRI");
  let prepared = fixed.prepare(&key, &proof, &expected, Default::default())?;
  drop(proof);
  let (fri, proof) = prepared.prove_fri(fri_config(&key), FRI_HEIGHT)?;
  eprintln!("[compress] FRI → KZG");
  let prepared =
    pipeline::prepare_kzg(&fri, &proof, &expected, Default::default())?;
  let height = 1usize << entry.settings.kzg_log;
  let (kzg, proof) = prepared.prove_kzg(srs.clone(), height)?;
  eprintln!("[compress] KZG → recursive KZG");
  let prepared = pipeline::prepare_recursive(&kzg, &proof, &expected)?;
  let (verifier, proof) = prepared.prove(srs, height)?;
  if verifier.to_bytes()? != entry.key_bytes {
    return Err(
      "prover circuit differs from the locally configured verifier".into(),
    );
  }
  let bytes = verifier.encode_proof(&proof)?;
  RecursiveVerifier::from_bytes(&entry.key_bytes)?
    .verify_bytes(&bytes, &expected)?;
  let mut result = MAGIC.to_vec();
  result.extend(local::decode_id(&entry.settings.id())?);
  result.extend(bytes);
  Ok(result)
}

#[unsafe(no_mangle)]
extern "C" fn rs_compression_setup(
  system: LeanExternal<AiurSystem, LeanBorrowed<'_>>,
  dir: LeanString<LeanBorrowed<'_>>,
  srs: LeanString<LeanBorrowed<'_>>,
  dev: bool,
  root_log: u32,
  kzg_log: u32,
  claim_len: u32,
) -> LeanIOResult<LeanOwned> {
  match setup(
    system.get(),
    Path::new(dir.as_str()),
    Path::new(srs.as_str()),
    dev,
    root_log,
    kzg_log,
    claim_len as usize,
  ) {
    Ok(id) => LeanIOResult::ok(LeanString::new(&id)),
    Err(e) => LeanIOResult::error_string(&e.to_string()),
  }
}

#[unsafe(no_mangle)]
extern "C" fn rs_compression_run(
  system: LeanExternal<AiurSystem, LeanBorrowed<'_>>,
  allowed: LeanByteArray<LeanBorrowed<'_>>,
  idx: LeanNat<LeanBorrowed<'_>>,
  certificate: LeanByteArray<LeanBorrowed<'_>>,
  proof: LeanByteArray<LeanBorrowed<'_>>,
  dir: LeanString<LeanBorrowed<'_>>,
) -> LeanIOResult<LeanOwned> {
  match compress(
    system.get(),
    allowed.as_bytes(),
    crate::aiur::lean_unbox_nat_as_usize(idx.inner()),
    certificate.as_bytes(),
    proof.as_bytes(),
    Path::new(dir.as_str()),
  ) {
    Ok(bytes) => LeanIOResult::ok(LeanByteArray::from_bytes(&bytes)),
    Err(e) => LeanIOResult::error_string(&e.to_string()),
  }
}

#[unsafe(no_mangle)]
extern "C" fn rs_compression_verify(
  vk: LeanByteArray<LeanBorrowed<'_>>,
  proof: LeanByteArray<LeanBorrowed<'_>>,
  claim: LeanArray<LeanBorrowed<'_>>,
  dir: LeanString<LeanBorrowed<'_>>,
) -> LeanIOResult<LeanOwned> {
  let result = (|| -> pipeline::Result<()> {
    let (id, body) = envelope(proof.as_bytes())?;
    let entry = local::load(Path::new(dir.as_str()), &id, vk.as_bytes())?;
    let expected = claim.map(|x| crate::aiur::lean_unbox_g(&x));
    RecursiveVerifier::from_bytes(&entry.key_bytes)?
      .verify_bytes(body, &expected)
  })();
  match result {
    Ok(()) => LeanIOResult::ok(LeanOwned::box_usize(0)),
    Err(e) => LeanIOResult::error_string(&e.to_string()),
  }
}

fn envelope(bytes: &[u8]) -> pipeline::Result<(String, &[u8])> {
  if bytes.len() <= 40 || !bytes.starts_with(MAGIC) {
    return Err("invalid compressed certificate envelope".into());
  }
  let id: [u8; 32] = bytes[8..40].try_into()?;
  Ok((blake3::Hash::from(id).to_hex().to_string(), &bytes[40..]))
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn envelope_has_only_version_configuration_and_proof() {
    let mut bytes = MAGIC.to_vec();
    bytes.extend([7; 32]);
    bytes.push(42);
    let (id, proof) = envelope(&bytes).unwrap();
    assert_eq!(local::decode_id(&id).unwrap(), [7; 32]);
    assert_eq!(proof, &[42]);
    for len in 0..=40 {
      assert!(envelope(&bytes[..len]).is_err());
    }
    bytes[7] = b'1';
    assert!(envelope(&bytes).is_err());
  }
}
