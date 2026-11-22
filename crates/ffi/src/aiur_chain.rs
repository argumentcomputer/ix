//! Trusted-file configuration and CLI transport for the Aiur GL-to-BN chain.
use ix_proof_compression::{
  aiur_backend::{
    chain::{
      Admission, Assets, Configuration, Prover, StageConfiguration, Verifier,
    },
    compress_bn, compress_gl,
    kzg::Compiler,
  },
  pipeline::{SetupClass, SetupConfig},
};
use lean_ffi::object::{
  LeanBorrowed, LeanByteArray, LeanIOResult, LeanOwned, LeanString,
};
use serde::{Deserialize, Serialize};
use stark_verifier::compress_wrap::Input;
use std::{
  fs,
  num::NonZeroU32,
  path::{Path, PathBuf},
  time::Instant,
};

const FORMAT: &str = "ix-aiur-chain-v1";

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct StageFiles {
  artifact: PathBuf,
  artifact_blake3: String,
  #[serde(skip_serializing_if = "Option::is_none")]
  key: Option<PathBuf>,
  #[serde(skip_serializing_if = "Option::is_none")]
  key_blake3: Option<String>,
  max_log_height: u8,
  quotient_degree: usize,
}

impl StageFiles {
  fn capacity(&self) -> compress_gl::Capacity {
    compress_gl::Capacity {
      max_log_height: self.max_log_height,
      quotient_degree: self.quotient_degree,
    }
  }

  fn configuration(&self) -> Result<StageConfiguration, String> {
    self.capacity().height()?;
    self.key.as_ref().ok_or("chain stage is missing its trusted key path")?;
    Ok(StageConfiguration {
      artifact_blake3: pin(&self.artifact_blake3)?,
      key_blake3: pin(
        self
          .key_blake3
          .as_deref()
          .ok_or("chain stage is missing its independent key pin")?,
      )?,
      max_log_height: self.max_log_height,
      quotient_degree: self.quotient_degree,
    })
  }

  fn resolve(&mut self, directory: &Path) {
    self.artifact = resolve(directory, &self.artifact);
    self.key = self.key.as_ref().map(|path| resolve(directory, path));
  }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Manifest {
  format: String,
  gl: StageFiles,
  bn: StageFiles,
  bn_stages: NonZeroU32,
  admission: Admission,
}

impl Manifest {
  fn read(path: &Path, expected: &str) -> Result<Self, String> {
    let expected = pin(expected)?;
    let bytes = read(path)?;
    if blake3::hash(&bytes).as_bytes() != &expected {
      return Err(
        "Aiur chain manifest differs from the independently trusted pin".into(),
      );
    }
    Self::decode(path, &bytes)
  }

  fn decode(path: &Path, bytes: &[u8]) -> Result<Self, String> {
    let mut value: Self = serde_json::from_slice(bytes)
      .map_err(|error| format!("invalid Aiur chain manifest: {error}"))?;
    if value.format != FORMAT {
      return Err("unsupported Aiur chain manifest format".into());
    }
    let directory = path.parent().unwrap_or_else(|| Path::new("."));
    value.gl.resolve(directory);
    value.bn.resolve(directory);
    Ok(value)
  }

  fn configuration(&self) -> Result<Configuration, String> {
    Ok(Configuration {
      gl: self.gl.configuration()?,
      bn: self.bn.configuration()?,
      bn_stages: self.bn_stages,
    })
  }

  fn verifier(
    &self,
    development: bool,
  ) -> Result<(Verifier, SetupClass), String> {
    let configuration = self.configuration()?;
    let gl_artifact = read(&self.gl.artifact)?;
    let bn_artifact = read(&self.bn.artifact)?;
    let gl_key = read(self.gl.key.as_ref().ok_or("missing GL key path")?)?;
    let bn_key = read(self.bn.key.as_ref().ok_or("missing BN key path")?)?;
    let verifier = Verifier::from_bytes(
      configuration,
      Assets {
        gl_artifact: &gl_artifact,
        gl_key: &gl_key,
        bn_artifact: &bn_artifact,
        bn_key: &bn_key,
      },
    )?;
    let class = SetupClass::of(verifier.parameters());
    admit_setup(class, development)?;
    Ok((verifier, class))
  }

  fn prover(&self, development: bool) -> Result<(Prover, SetupClass), String> {
    let (verifier, class) = self.verifier(development)?;
    let setup =
      SetupConfig::from_env(development).map_err(|error| error.to_string())?;
    Ok((Prover::new(verifier, setup, self.admission)?, class))
  }
}

fn read(path: &Path) -> Result<Vec<u8>, String> {
  fs::read(path).map_err(|error| format!("{}: {error}", path.display()))
}

fn resolve(directory: &Path, path: &Path) -> PathBuf {
  if path.is_absolute() { path.to_owned() } else { directory.join(path) }
}

fn pin(text: &str) -> Result<[u8; 32], String> {
  blake3::Hash::from_hex(text)
    .map(|hash| *hash.as_bytes())
    .map_err(|error| error.to_string())
}

fn admit_setup(class: SetupClass, development: bool) -> Result<(), String> {
  match class {
    SetupClass::Ignition => Ok(()),
    SetupClass::Development if development => Ok(()),
    _ => Err("Aiur chain verifier does not use the released Ignition parameters; development parameters require explicit development mode".into()),
  }
}

fn report(path: &Path, value: &serde_json::Value) -> Result<(), String> {
  fs::write(
    path,
    serde_json::to_vec_pretty(value).map_err(|error| error.to_string())?,
  )
  .map_err(|error| error.to_string())
}

fn string_result(result: Result<String, String>) -> LeanIOResult<LeanOwned> {
  match result {
    Ok(value) => LeanIOResult::ok(LeanString::new(&value)),
    Err(error) => LeanIOResult::error_string(&error),
  }
}

#[unsafe(no_mangle)]
extern "C" fn rs_aiur_chain_preflight(
  manifest: LeanString<LeanBorrowed<'_>>,
  manifest_pin: LeanString<LeanBorrowed<'_>>,
  development: bool,
) -> LeanIOResult<LeanOwned> {
  string_result((|| {
    super::aiur_compression::configure_prover(development)?;
    let (_, class) = Manifest::read(
      Path::new(&manifest.to_string()),
      &manifest_pin.to_string(),
    )?
    .prover(development)?;
    Ok(class.label().into())
  })())
}

#[unsafe(no_mangle)]
extern "C" fn rs_aiur_chain_run(
  vk: LeanByteArray<LeanBorrowed<'_>>,
  raw: LeanByteArray<LeanBorrowed<'_>>,
  claim: LeanByteArray<LeanBorrowed<'_>>,
  rows: LeanByteArray<LeanBorrowed<'_>>,
  manifest: LeanString<LeanBorrowed<'_>>,
  manifest_pin: LeanString<LeanBorrowed<'_>>,
  out: LeanString<LeanBorrowed<'_>>,
  development: bool,
  fresh: bool,
) -> LeanIOResult<LeanOwned> {
  let result = (|| -> Result<Vec<u8>, String> {
    let started = Instant::now();
    let out = PathBuf::from(out.to_string());
    if fresh {
      super::aiur_compression::reset_output(&out)?;
    }
    super::aiur_compression::configure_prover(development)?;
    let expected = super::aiur_compression::expected(
      vk.as_bytes(),
      claim.as_bytes(),
      rows.as_bytes(),
    )?;
    let manifest = Manifest::read(
      Path::new(&manifest.to_string()),
      &manifest_pin.to_string(),
    )?;
    let (prover, class) = manifest.prover(development)?;
    let input = Input::from_bytes(
      vk.as_bytes(),
      expected.key_digest,
      rows.as_bytes(),
      raw.as_bytes(),
    )?;
    fs::create_dir_all(&out).map_err(|error| error.to_string())?;
    if !fresh
      && fs::read_dir(&out).map_err(|error| error.to_string())?.next().is_some()
    {
      return Err("Aiur output directory is nonempty; use --fresh to replace its stage artifacts".into());
    }
    let report_path = out.join("aiur-bn-report.json");
    let mut value = serde_json::json!({
      "format":FORMAT, "proof_verified":false, "setup":class.label(),
      "manifest_blake3":manifest_pin.to_string(),
      "configuration":manifest.configuration()?, "admission":manifest.admission,
      "root_key_blake3":blake3::Hash::from_bytes(expected.key_digest).to_hex().as_str(),
      "root_claims_blake3":blake3::Hash::from_bytes(expected.claims_digest).to_hex().as_str(),
      "policy_blake3":blake3::Hash::from_bytes(prover.verifier().policy().digest()).to_hex().as_str(),
    });
    report(&report_path, &value)?;
    eprintln!("[compress] proving the aggregate verifier with Aiur CompressGL");
    let gl = prover.prove_gl(&input, &expected)?;
    fs::write(out.join("aiur-gl-proof.bin"), &gl.proof)
      .map_err(|error| error.to_string())?;
    value["stages"] =
      serde_json::to_value([&gl.report]).map_err(|error| error.to_string())?;
    report(&report_path, &value)?;
    eprintln!(
      "[compress] proving {} Aiur CompressBN stage(s)",
      manifest.bn_stages
    );
    let mut proven = prover.prove_from_gl(&expected, &gl.proof)?;
    proven.stages.insert(0, gl.report);
    let proof = proven.envelope.to_bytes()?;
    prover.verifier().verify_bytes(&expected, &proof)?;
    fs::write(out.join("aiur-bn-proof.bin"), &proof)
      .map_err(|error| error.to_string())?;
    value["proof_verified"] = true.into();
    value["native_accumulator_verified"] = true.into();
    value["proof_bytes"] = proof.len().into();
    value["stages"] = serde_json::to_value(&proven.stages)
      .map_err(|error| error.to_string())?;
    value["total_seconds"] = started.elapsed().as_secs_f64().into();
    value["peak_resident_bytes"] =
      aiur::trace::stark::planning::peak_resident_memory().into();
    report(&report_path, &value)?;
    Ok(proof)
  })();
  match result {
    Ok(bytes) => LeanIOResult::ok(LeanByteArray::from_bytes(&bytes)),
    Err(error) => LeanIOResult::error_string(&error),
  }
}

#[unsafe(no_mangle)]
extern "C" fn rs_aiur_chain_verify(
  proof: LeanByteArray<LeanBorrowed<'_>>,
  vk: LeanByteArray<LeanBorrowed<'_>>,
  claim: LeanByteArray<LeanBorrowed<'_>>,
  rows: LeanByteArray<LeanBorrowed<'_>>,
  manifest: LeanString<LeanBorrowed<'_>>,
  manifest_pin: LeanString<LeanBorrowed<'_>>,
  development: bool,
) -> LeanIOResult<LeanOwned> {
  string_result((|| {
    let expected = super::aiur_compression::expected(
      vk.as_bytes(),
      claim.as_bytes(),
      rows.as_bytes(),
    )?;
    let (verifier, class) = Manifest::read(
      Path::new(&manifest.to_string()),
      &manifest_pin.to_string(),
    )?
    .verifier(development)?;
    verifier.verify_bytes(&expected, proof.as_bytes())?;
    Ok(class.label().into())
  })())
}

fn prepare(
  template: &Path,
  output: &Path,
  development: bool,
) -> Result<String, String> {
  let mut manifest = Manifest::decode(template, &read(template)?)?;
  if [&manifest.gl, &manifest.bn]
    .iter()
    .any(|stage| stage.key.is_some() || stage.key_blake3.is_some())
  {
    return Err("key preparation template must omit key paths and pins".into());
  }
  let gl_bytes = read(&manifest.gl.artifact)?;
  let bn_bytes = read(&manifest.bn.artifact)?;
  let gl = compress_gl::Wrapper::from_bytes(
    &gl_bytes,
    &pin(&manifest.gl.artifact_blake3)?,
  )?;
  let bn = compress_bn::Wrapper::from_bytes(
    &bn_bytes,
    &pin(&manifest.bn.artifact_blake3)?,
  )?;
  let setup =
    SetupConfig::from_env(development).map_err(|error| error.to_string())?;
  let gl_key = gl.verifying_key(&setup, manifest.gl.capacity())?;
  let fixed_height = Compiler::new(bn.plan())?
    .inputs()
    .iter()
    .filter_map(|input| input.preprocessed.as_ref())
    .map(|matrix| matrix.values.len() / matrix.width)
    .max()
    .unwrap_or(2)
    .max(2);
  let bn_key = bn
    .verifying_key(manifest.bn.capacity().config(&setup, fixed_height)?)?
    .portable;
  manifest.gl.key = Some("gl-key.bin".into());
  manifest.bn.key = Some("bn-key.bin".into());
  manifest.gl.key_blake3 = Some(blake3::hash(&gl_key).to_hex().to_string());
  manifest.bn.key_blake3 = Some(blake3::hash(&bn_key).to_hex().to_string());
  manifest.gl.artifact = "gl-program.ixa".into();
  manifest.bn.artifact = "bn-program.ixa".into();
  let verifier = Verifier::from_bytes(
    manifest.configuration()?,
    Assets {
      gl_artifact: &gl_bytes,
      gl_key: &gl_key,
      bn_artifact: &bn_bytes,
      bn_key: &bn_key,
    },
  )?;
  admit_setup(SetupClass::of(verifier.parameters()), development)?;
  Prover::new(verifier, setup, manifest.admission)?;
  let bytes =
    serde_json::to_vec_pretty(&manifest).map_err(|error| error.to_string())?;
  fs::create_dir(output).map_err(|error| error.to_string())?;
  for (name, bytes) in [
    ("gl-program.ixa", &gl_bytes),
    ("bn-program.ixa", &bn_bytes),
    ("gl-key.bin", &gl_key),
    ("bn-key.bin", &bn_key),
    ("manifest.json", &bytes),
  ] {
    fs::write(output.join(name), bytes).map_err(|error| error.to_string())?;
  }
  Ok(blake3::hash(&bytes).to_hex().to_string())
}

#[unsafe(no_mangle)]
extern "C" fn rs_aiur_chain_prepare(
  template: LeanString<LeanBorrowed<'_>>,
  output: LeanString<LeanBorrowed<'_>>,
  development: bool,
) -> LeanIOResult<LeanOwned> {
  string_result((|| {
    super::aiur_compression::configure_prover(development)?;
    prepare(
      Path::new(&template.to_string()),
      Path::new(&output.to_string()),
      development,
    )
  })())
}

#[cfg(test)]
mod tests {
  use super::*;

  fn stage() -> StageFiles {
    StageFiles {
      artifact: "program.ixa".into(),
      artifact_blake3: "00".repeat(32),
      key: Some("key.bin".into()),
      key_blake3: Some("11".repeat(32)),
      max_log_height: 24,
      quotient_degree: 2,
    }
  }

  #[test]
  fn manifest_requires_independent_key_pins_and_valid_capacity() {
    let valid = stage();
    valid.configuration().unwrap();
    for invalid in [
      StageFiles { key: None, ..valid.clone() },
      StageFiles { key_blake3: None, ..valid.clone() },
      StageFiles { artifact_blake3: "bad".into(), ..valid.clone() },
      StageFiles { quotient_degree: 3, ..valid },
    ] {
      assert!(invalid.configuration().is_err());
    }
    let mut unknown = serde_json::to_value(stage()).unwrap();
    unknown["proof_supplied_pin"] = true.into();
    assert!(serde_json::from_value::<StageFiles>(unknown).is_err());
  }

  #[test]
  fn manifest_paths_resolve_from_its_directory_and_setup_requires_opt_in() {
    let mut stage = stage();
    stage.resolve(Path::new("/trusted/config"));
    assert_eq!(stage.artifact, PathBuf::from("/trusted/config/program.ixa"));
    assert_eq!(stage.key.unwrap(), PathBuf::from("/trusted/config/key.bin"));
    assert_eq!(
      resolve(Path::new("/ignored"), Path::new("/absolute")),
      PathBuf::from("/absolute")
    );
    assert!(admit_setup(SetupClass::Ignition, false).is_ok());
    assert!(admit_setup(SetupClass::Development, false).is_err());
    assert!(admit_setup(SetupClass::Development, true).is_ok());
    assert!(admit_setup(SetupClass::Groth16, true).is_err());
  }

  #[test]
  fn manifest_pin_covers_exact_bytes_before_parsing_and_fresh_preserves_other_files()
   {
    let directory = std::env::temp_dir().join(format!(
      "ix-chain-manifest-{}-{}",
      std::process::id(),
      std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos()
    ));
    fs::create_dir(&directory).unwrap();
    let limit = ix_proof_compression::aiur_backend::chain::Limits {
      max_record_bytes: 1,
      max_trace_bytes: 1,
      max_total_rows: 1,
    };
    let manifest = Manifest {
      format: FORMAT.into(),
      gl: stage(),
      bn: stage(),
      bn_stages: NonZeroU32::MIN,
      admission: Admission { gl: limit, bn: limit },
    };
    let bytes = serde_json::to_vec_pretty(&manifest).unwrap();
    let digest = blake3::hash(&bytes).to_hex().to_string();
    let path = directory.join("manifest.json");
    fs::write(&path, &bytes).unwrap();
    Manifest::read(&path, &digest).unwrap();
    let mut changed = bytes.clone();
    changed.push(b'\n');
    Manifest::decode(&path, &changed).unwrap().configuration().unwrap();
    fs::write(&path, changed).unwrap();
    assert!(
      Manifest::read(&path, &digest)
        .unwrap_err()
        .contains("independently trusted pin")
    );
    fs::write(&path, b"invalid JSON").unwrap();
    assert!(
      Manifest::read(&path, &digest)
        .unwrap_err()
        .contains("independently trusted pin")
    );
    for name in [
      "aiur-gl-proof.bin",
      "aiur-gl-report.json",
      "aiur-bn-proof.bin",
      "aiur-bn-report.json",
    ] {
      fs::write(directory.join(name), b"stale").unwrap();
    }
    fs::write(directory.join("unrelated.txt"), b"keep").unwrap();
    super::super::aiur_compression::reset_output(&directory).unwrap();
    assert!(Manifest::read(&path, &digest).is_err());
    for name in [
      "aiur-gl-proof.bin",
      "aiur-gl-report.json",
      "aiur-bn-proof.bin",
      "aiur-bn-report.json",
    ] {
      assert!(!directory.join(name).exists());
    }
    assert_eq!(fs::read(directory.join("unrelated.txt")).unwrap(), b"keep");
    fs::remove_dir_all(directory).unwrap();
  }

  #[test]
  #[ignore = "requires IX_AIUR_CHAIN_TEST_MANIFEST pointing to prepared Ignition assets; run with IX_KZG_SRS set to a missing path"]
  fn prepared_manifest_verifier_does_not_need_proving_powers() {
    let path = std::env::var("IX_AIUR_CHAIN_TEST_MANIFEST").unwrap();
    let expected = std::env::var("IX_AIUR_CHAIN_TEST_MANIFEST_BLAKE3").unwrap();
    let manifest = Manifest::read(Path::new(&path), &expected).unwrap();
    let (verifier, class) = manifest.verifier(false).unwrap();
    assert_eq!(class, SetupClass::Ignition);
    let expected = stark_verifier::compress_wrap::Statement {
      key_digest: [0; 32],
      claims_digest: [0; 32],
    };
    let error = verifier.verify_bytes(&expected, b"IXAUCH02").unwrap_err();
    assert!(error.contains("envelope tag"), "{error}");
  }
}
