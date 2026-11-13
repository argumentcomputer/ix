//! Statement-bound Aiur Goldilocks compression for the CLI.
use ix_proof_compression::{
  aiur_backend::{
    compress_gl::{Capacity, Wrapper},
    kzg::VerifyingKey,
  },
  pipeline::{self, SetupClass, SetupConfig},
};
use lean_ffi::object::{
  LeanBorrowed, LeanByteArray, LeanIOResult, LeanOwned, LeanString,
};
use multi_stark::config::ProofConfig;
use stark_verifier::compress_wrap::{Input, Statement, decode_claims};
use std::{fs, io::Write, path::Path};

const MAGIC: &[u8; 8] = b"IXACGL1\0";

pub(super) fn reset_output(out: &Path) -> Result<(), String> {
  for name in [
    "aiur-gl-proof.bin",
    "aiur-gl-report.json",
    "aiur-bn-proof.bin",
    "aiur-bn-report.json",
  ] {
    match fs::remove_file(out.join(name)) {
      Ok(()) => {},
      Err(error) if error.kind() == std::io::ErrorKind::NotFound => {},
      Err(error) => return Err(error.to_string()),
    }
  }
  Ok(())
}

#[unsafe(no_mangle)]
extern "C" fn rs_aiur_compression_reset_output(
  out: LeanString<LeanBorrowed<'_>>,
) -> LeanIOResult<LeanOwned> {
  match reset_output(Path::new(&out.to_string())) {
    Ok(()) => LeanIOResult::ok(LeanOwned::box_usize(0)),
    Err(error) => LeanIOResult::error_string(&error),
  }
}

#[cfg_attr(not(feature = "cuda"), allow(clippy::unnecessary_wraps))]
pub(super) fn configure_prover(development: bool) -> Result<(), String> {
  let _ = tracing_subscriber::fmt()
    .with_env_filter(
      tracing_subscriber::EnvFilter::try_from_default_env()
        .unwrap_or_else(|_error| "info".into()),
    )
    .with_writer(std::io::stderr)
    .try_init();
  #[cfg(feature = "cuda")]
  {
    let config = pipeline::CompressConfig::from_env(
      Path::new("."),
      development,
      pipeline::FinalOptions::default(),
    )
    .map_err(|e| e.to_string())?;
    let settings = config.cuda;
    if !ix_proof_compression::kzg::cuda::configure(settings.clone())
      && ix_proof_compression::kzg::cuda::settings() != &settings
    {
      return Err(
        "KZG CUDA settings were fixed by an earlier incompatible operation"
          .into(),
      );
    }
    eprintln!("[compress] Aiur KZG CUDA settings: {settings:?}");
  }
  #[cfg(not(feature = "cuda"))]
  let _ = development;
  Ok(())
}

#[unsafe(no_mangle)]
extern "C" fn rs_aiur_compression_preflight(
  artifact_path: LeanString<LeanBorrowed<'_>>,
  artifact_pin: LeanString<LeanBorrowed<'_>>,
  key_path: LeanString<LeanBorrowed<'_>>,
  key_pin: LeanString<LeanBorrowed<'_>>,
  max_log: u8,
  quotient: u32,
  development: bool,
) -> LeanIOResult<LeanOwned> {
  let result = (|| -> Result<&'static str, String> {
    configure_prover(development)?;
    let wrapper =
      artifact(&artifact_path.to_string(), &artifact_pin.to_string())?;
    let (key, _, class) =
      trusted_key(&key_path.to_string(), &key_pin.to_string(), development)?;
    let setup =
      SetupConfig::from_env(development).map_err(|e| e.to_string())?;
    if wrapper.verifying_key(
      &setup,
      Capacity { max_log_height: max_log, quotient_degree: quotient as usize },
    )? != key
    {
      return Err("Aiur artifact/setup/capacity differs from the independently trusted key".into());
    }
    Ok(class.label())
  })();
  match result {
    Ok(class) => LeanIOResult::ok(LeanString::new(class)),
    Err(e) => LeanIOResult::error_string(&e),
  }
}

fn pin(text: &str) -> Result<[u8; 32], String> {
  blake3::Hash::from_hex(text)
    .map(|hash| *hash.as_bytes())
    .map_err(|e| e.to_string())
}
fn artifact(path: &str, digest: &str) -> Result<Wrapper, String> {
  Wrapper::from_bytes(
    &fs::read(path).map_err(|e| e.to_string())?,
    &pin(digest)?,
  )
}
fn trusted_key(
  path: &str,
  digest: &str,
  development: bool,
) -> Result<(Vec<u8>, VerifyingKey, SetupClass), String> {
  let bytes = fs::read(path).map_err(|e| e.to_string())?;
  let key = VerifyingKey::from_bytes(&bytes, &pin(digest)?)?;
  if !key.is_key_bound() {
    return Err("Aiur compression requires a key-bound KZG transcript".into());
  }
  let class = SetupClass::of(key.system().config.pcs().verifier_params());
  if class != SetupClass::Ignition && !development {
    return Err(
      "Aiur KZG verifier does not use the released Ignition parameters".into(),
    );
  }
  Ok((bytes, key, class))
}
pub(super) fn expected(
  vk: &[u8],
  claim: &[u8],
  rows: &[u8],
) -> Result<Statement, String> {
  pipeline::check_claim(claim, rows).map_err(|e| e.to_string())?;
  let rows = decode_claims(rows)?;
  if rows.len() != 1 {
    return Err("expected exactly one aggregate root claim".into());
  }
  Ok(Statement::new(*blake3::hash(vk).as_bytes(), &rows))
}
fn bytes_result(result: Result<Vec<u8>, String>) -> LeanIOResult<LeanOwned> {
  match result {
    Ok(bytes) => LeanIOResult::ok(LeanByteArray::from_bytes(&bytes)),
    Err(e) => LeanIOResult::error_string(&e),
  }
}

#[unsafe(no_mangle)]
extern "C" fn rs_aiur_compression_prepare_key(
  artifact_path: LeanString<LeanBorrowed<'_>>,
  artifact_pin: LeanString<LeanBorrowed<'_>>,
  out: LeanString<LeanBorrowed<'_>>,
  max_log: u8,
  quotient: u32,
  development: bool,
) -> LeanIOResult<LeanOwned> {
  let result = (|| -> Result<String, String> {
    configure_prover(development)?;
    let wrapper =
      artifact(&artifact_path.to_string(), &artifact_pin.to_string())?;
    let setup =
      SetupConfig::from_env(development).map_err(|e| e.to_string())?;
    let key = wrapper.verifying_key(
      &setup,
      Capacity { max_log_height: max_log, quotient_degree: quotient as usize },
    )?;
    let out = out.to_string();
    fs::OpenOptions::new()
      .write(true)
      .create_new(true)
      .open(&out)
      .and_then(|mut file| file.write_all(&key))
      .map_err(|e| e.to_string())?;
    Ok(blake3::hash(&key).to_hex().to_string())
  })();
  match result {
    Ok(digest) => LeanIOResult::ok(LeanString::new(&digest)),
    Err(e) => LeanIOResult::error_string(&e),
  }
}

#[unsafe(no_mangle)]
extern "C" fn rs_aiur_compression_run(
  vk: LeanByteArray<LeanBorrowed<'_>>,
  raw: LeanByteArray<LeanBorrowed<'_>>,
  claim: LeanByteArray<LeanBorrowed<'_>>,
  rows: LeanByteArray<LeanBorrowed<'_>>,
  artifact_path: LeanString<LeanBorrowed<'_>>,
  artifact_pin: LeanString<LeanBorrowed<'_>>,
  key_path: LeanString<LeanBorrowed<'_>>,
  key_pin: LeanString<LeanBorrowed<'_>>,
  out: LeanString<LeanBorrowed<'_>>,
  max_log: u8,
  quotient: u32,
  development: bool,
  fresh: bool,
) -> LeanIOResult<LeanOwned> {
  bytes_result((|| {
    let out = out.to_string();
    let out = Path::new(&out);
    if fresh {
      reset_output(out)?;
    }
    configure_prover(development)?;
    let expected = expected(vk.as_bytes(), claim.as_bytes(), rows.as_bytes())?;
    let wrapper =
      artifact(&artifact_path.to_string(), &artifact_pin.to_string())?;
    let (key, verifier, class) =
      trusted_key(&key_path.to_string(), &key_pin.to_string(), development)?;
    let setup =
      SetupConfig::from_env(development).map_err(|e| e.to_string())?;
    let capacity =
      Capacity { max_log_height: max_log, quotient_degree: quotient as usize };
    if wrapper.verifying_key(&setup, capacity)? != key {
      return Err("Aiur artifact/setup/capacity differs from the independently trusted key".into());
    }
    let input = Input::from_bytes(
      vk.as_bytes(),
      expected.key_digest,
      rows.as_bytes(),
      raw.as_bytes(),
    )?;
    fs::create_dir_all(out).map_err(|e| e.to_string())?;
    if !fresh && fs::read_dir(out).map_err(|e| e.to_string())?.next().is_some()
    {
      return Err("Aiur output directory is nonempty; use --fresh to replace its stage artifacts".into());
    }
    let report = out.join("aiur-gl-report.json");
    fs::write(&report, b"{\"proof_verified\":false}\n")
      .map_err(|e| e.to_string())?;
    eprintln!("[compress] executing the raw aggregate verifier over BN254");
    let execution = wrapper.execute(&input)?;
    let profile = wrapper.profile(&execution)?;
    fs::write(
      &report,
      serde_json::to_vec_pretty(
        &serde_json::json!({"proof_verified":false,"profile":profile}),
      )
      .map_err(|e| e.to_string())?,
    )
    .map_err(|e| e.to_string())?;
    eprintln!(
      "[compress] Aiur trace: {} main cells, {} bytes before proving workspaces",
      profile.main_cells, profile.main_fixed_lookup_bytes
    );
    let proven = wrapper.prove(&execution, &setup, capacity)?;
    if proven.key != key {
      return Err("Aiur proving key changed with the execution".into());
    }
    verifier.verify_bytes(&wrapper.claim(&expected)?, &proven.proof)?;
    fs::write(out.join("aiur-gl-proof.bin"), &proven.proof)
      .map_err(|e| e.to_string())?;
    let report_value = serde_json::json!({"format":"ix-aiur-compress-gl-v1", "proof_verified":true,
      "setup":class.label(), "profile":proven.profile, "capacity":proven.capacity,
      "setup_seconds":proven.setup_seconds, "trace_seconds":proven.trace_seconds,
      "proving_seconds":proven.proving_seconds, "verification_seconds":proven.verification_seconds,
      "proof_bytes":proven.proof.len(), "trusted_key_blake3":blake3::hash(&key).to_hex().as_str(),
      "peak_resident_bytes":aiur::trace::stark::planning::peak_resident_memory()});
    fs::write(
      report,
      serde_json::to_vec_pretty(&report_value).map_err(|e| e.to_string())?,
    )
    .map_err(|e| e.to_string())?;
    let mut envelope = MAGIC.to_vec();
    envelope.extend_from_slice(&proven.proof);
    Ok(envelope)
  })())
}

#[unsafe(no_mangle)]
extern "C" fn rs_aiur_compression_verify(
  proof: LeanByteArray<LeanBorrowed<'_>>,
  vk: LeanByteArray<LeanBorrowed<'_>>,
  claim: LeanByteArray<LeanBorrowed<'_>>,
  rows: LeanByteArray<LeanBorrowed<'_>>,
  artifact_path: LeanString<LeanBorrowed<'_>>,
  artifact_pin: LeanString<LeanBorrowed<'_>>,
  key_path: LeanString<LeanBorrowed<'_>>,
  key_pin: LeanString<LeanBorrowed<'_>>,
  max_log: u8,
  quotient: u32,
  development: bool,
) -> LeanIOResult<LeanOwned> {
  let result = (|| -> Result<&'static str, String> {
    let proof = proof
      .as_bytes()
      .strip_prefix(MAGIC)
      .ok_or("unsupported Aiur compression envelope")?;
    let statement = expected(vk.as_bytes(), claim.as_bytes(), rows.as_bytes())?;
    let wrapper =
      artifact(&artifact_path.to_string(), &artifact_pin.to_string())?;
    let (_, key, class) =
      trusted_key(&key_path.to_string(), &key_pin.to_string(), development)?;
    if key.system().config.max_log_degree() != usize::from(max_log)
      || key.system().config.max_quotient_degree() != quotient as usize
    {
      return Err(
        "requested Aiur capacity differs from the trusted verifier key".into(),
      );
    }
    let claim = wrapper.claim(&statement)?;
    key.verify_bytes(&claim, proof)?;
    Ok(class.label())
  })();
  match result {
    Ok(class) => LeanIOResult::ok(LeanString::new(class)),
    Err(e) => LeanIOResult::error_string(&e),
  }
}
