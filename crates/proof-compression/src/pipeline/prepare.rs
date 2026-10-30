//! `ix compress setup`: everything a fresh machine computes once before its
//! first compression of the bundled version. The Ignition SRS is checked
//! against its pin, and the fixed preprocessing of the first KZG stage and
//! the recursive stage is published to the fixed cache under the identity
//! those stages look it up by.
//!
//! Under Ignition each stage's cache identity follows from bundled pins and
//! the setup alone, so a stage whose entry is present and checks costs only
//! that check. A missing stage is derived without a proof, its key checked
//! against its pin, and its fixed columns committed and published.
//! Development setups have no pins: the first stage is still found by its
//! pinned plan, but the recursive stage is rebuilt to find its identity,
//! and only missing entries are committed.
use super::{
  CompressConfig, FixedRoot, Result, SetupClass, SetupConfig,
  claims::first_claims,
  first,
  fixed_cache::{FixedCache, Prepared},
  prover::FixedSetup,
  root,
  setup::IGNITION_SRS_VAR,
  storage::Manifest,
  verifying_keys, wrap,
};
use sha2::{Digest, Sha256};
use std::{fs, io::Read, path::Path};

/// SHA-256 of the released gnark-format Ignition SRS file.
pub(super) const IGNITION_SRS_SHA256: &str =
  "06db33d8aa83291237aec6b8fa74752d3d4a516db0bb1221f4a554e8f8510a93";

fn sha256_file(path: &Path) -> Result<[u8; 32]> {
  let mut file = fs::File::open(path)?;
  let mut hasher = Sha256::new();
  let mut buffer = vec![0; 1 << 24];
  loop {
    let read = file.read(&mut buffer)?;
    if read == 0 {
      break;
    }
    hasher.update(&buffer[..read]);
  }
  Ok(hasher.finalize().into())
}

fn hex(bytes: &[u8]) -> String {
  bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

fn gigabytes(bytes: u64) -> String {
  format!(
    "{}.{} GB",
    bytes / 1_000_000_000,
    bytes % 1_000_000_000 / 100_000_000
  )
}

fn report(stage: &str, prepared: Prepared) {
  match prepared {
    Prepared::Present { bytes } => {
      eprintln!("{stage}: present ({}), skipped", gigabytes(bytes));
    },
    Prepared::Published { bytes } => {
      eprintln!("{stage}: published ({})", gigabytes(bytes));
    },
  }
}

/// Check the Ignition SRS file `config` loads against its pin. A file named
/// by `IX_KZG_SRS` replaces the release file and is only checked against
/// the released anchors when it is loaded.
fn check_srs(config: &SetupConfig) -> Result<()> {
  let SetupConfig::Ignition { srs, .. } = config else {
    eprintln!("parameters: development setup, no Ignition SRS needed");
    return Ok(());
  };
  if std::env::var_os(IGNITION_SRS_VAR).is_some() {
    eprintln!(
      "parameters: {} from {IGNITION_SRS_VAR}, not pin-checked",
      srs.display()
    );
    return Ok(());
  }
  if sha256_file(srs)? != verifying_keys::decode(IGNITION_SRS_SHA256)? {
    return Err(
      format!(
        "{} differs from the released Ignition SRS; delete it and rerun",
        srs.display()
      )
      .into(),
    );
  }
  eprintln!("parameters: {} verified", srs.display());
  Ok(())
}

/// The first stage's manifest for its fixed setup `parts`, with the claims
/// of a zero statement, as `first::setup` derives it.
fn first_manifest(parts: &[FixedSetup]) -> Manifest {
  Manifest {
    widths: parts.iter().map(|(circuit, _)| circuit.main_width).collect(),
    heights: parts
      .iter()
      .map(|(circuit, _)| circuit.preprocessed_height)
      .collect(),
    claims: first_claims(parts.len(), &[0; 18]),
  }
}

/// The first stage's manifest and fixed setup, from its cache entry or
/// derived and published, and the entry's status.
fn prepare_first(
  root_vk: &[u8],
  config: &SetupConfig,
  cache_root: &Path,
) -> Result<(Option<(Manifest, Vec<FixedSetup>)>, Prepared, FixedCache)> {
  let plan_id = verifying_keys::decode(verifying_keys::FIRST_PLAN_ID)?;
  let cache = first::fixed_cache(
    &plan_id,
    verifying_keys::FIRST_LOG_HEIGHT,
    config,
    cache_root,
  )?;
  if let Some(bytes) = cache.check()? {
    return Ok((None, Prepared::Present { bytes }, cache));
  }
  let fri = {
    let key = aiur::vk_codec::AiurVerifyingKey::from_bytes(root_vk)?;
    let layout = verifying_keys::release_root_layout(root_vk)?;
    root::verifier(&key, &FixedRoot::from_json(layout)?)?
  };
  let (manifest, parts, prepared) = first::setup(
    &fri,
    verifying_keys::FIRST_LOG_HEIGHT,
    config,
    Some(cache_root),
  )?;
  let (derived, prepared) = prepared.ok_or("first stage was not cached")?;
  if derived != plan_id {
    return Err(
      format!(
        "derived first-stage plan {} differs from its pin",
        hex(&derived)
      )
      .into(),
    );
  }
  Ok((Some((manifest, parts)), prepared, cache))
}

/// Publish the fixed preprocessing of the bundled version's stages for the
/// aggregation backend `root_vk` under `config`, and check the Ignition SRS.
pub fn prepare(root_vk: &[u8], config: &CompressConfig) -> Result<()> {
  let setup = &config.setup;
  let cache_root = config.fixed_cache.as_path();
  check_srs(setup)?;
  verifying_keys::release_root_layout(root_vk)?;
  fs::create_dir_all(cache_root)?;
  eprintln!("fixed cache: {}", cache_root.display());
  let (mut first_setup, prepared, first_cache) =
    prepare_first(root_vk, setup, cache_root)?;
  report("first KZG", prepared);
  let mut first_setup = || -> Result<(Manifest, Vec<FixedSetup>)> {
    if let Some(derived) = first_setup.take() {
      return Ok(derived);
    }
    let parts = first_cache.setup_parts()?;
    Ok((first_manifest(&parts), parts))
  };

  if setup.class() == SetupClass::Ignition {
    let recursive =
      wrap::VerifyingKey::from_bytes(verifying_keys::RECURSIVE_VK)?;
    let height = recursive.system()?.circuits[0].preprocessed_height;
    let identity =
      verifying_keys::decode(verifying_keys::RECURSIVE_FRONTEND_ID)?;
    let cache = wrap::fixed_cache(&identity, height, setup, cache_root)?;
    let prepared = match cache.check()? {
      Some(bytes) => Prepared::Present { bytes },
      None => {
        let (manifest, parts) = first_setup()?;
        let frontend = wrap::frontend(&manifest, parts, setup)?;
        if frontend.identity() != identity {
          return Err(
            format!(
              "derived recursive frontend {} differs from its pin",
              hex(frontend.identity())
            )
            .into(),
          );
        }
        let (vk, prepared) = frontend.prepared_key(setup, cache_root)?;
        if vk.to_bytes()? != verifying_keys::RECURSIVE_VK {
          return Err("derived recursive key differs from its pin".into());
        }
        prepared
      },
    };
    report("recursive KZG", prepared);
  } else {
    let (manifest, parts) = first_setup()?;
    let (_, prepared) = wrap::frontend(&manifest, parts, setup)?
      .prepared_key(setup, cache_root)?;
    report("recursive KZG", prepared);
  }
  Ok(())
}

/// Build the PLONK circuit, keys and parameter exports for the bundled
/// recursive key into the PLONK cache, and check the key against its pin.
#[cfg(feature = "plonk")]
pub fn prepare_plonk(config: &CompressConfig) -> Result<()> {
  let key = super::plonk::derive_verifying_key(
    verifying_keys::RECURSIVE_VK,
    &verifying_keys::STATEMENT_PREFIX,
    &config.setup,
    &config.plonk_cache,
  )?;
  if Sha256::digest(&key).as_slice()
    != verifying_keys::decode(verifying_keys::PLONK_VK_SHA256)?
  {
    return Err(
      "the PLONK key derived for the bundled recursive key differs from the \
       bundled PLONK key"
        .into(),
    );
  }
  eprintln!("PLONK: {} verified", config.plonk_cache.display());
  Ok(())
}

#[cfg(not(feature = "plonk"))]
pub fn prepare_plonk(_config: &CompressConfig) -> Result<()> {
  Err("this ix was built without PLONK; rebuild with IX_PLONK=1".into())
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::kzg::Scalar;
  use multi_stark::{
    plonkish::CircuitBuilder,
    traits::{Algebra, Field},
  };

  fn compiled() -> multi_stark::plonkish::MultiStarkCircuit<Scalar> {
    let mut b = CircuitBuilder::new();
    let table =
      b.fixed_table("small", vec![vec![Scalar::ONE], vec![Scalar::TWO]]);
    let x = b.input("x");
    b.lookup(table, &[x]);
    let y = b.mul(x, x);
    b.expose_public(y);
    b.finish()
      .lower_to_multi_stark_sharded(Scalar::from_u8(94), 16)
      .unwrap()
      .merge_table_traces(16)
      .unwrap()
  }

  #[test]
  fn prepared_preprocessing_is_published_once_in_the_prover_format()
  -> Result<()> {
    let scratch = crate::test_support::TempDir::new("setup-publish");
    let root = scratch.join("cache");
    let compiled = compiled();
    let setup = crate::pipeline::setup::SetupSource::development(b"setup", 63)?;
    let config = setup.config(16, 2, false)?;
    let cache = FixedCache::from_identity(&root, b"setup-fixture");
    assert_eq!(cache.check()?, None);
    let (parts, first) = cache.prepare(&config, &compiled)?;
    let Prepared::Published { bytes } = first else {
      panic!("expected a new entry, found {first:?}");
    };
    assert_eq!(cache.check()?, Some(bytes));
    let (again, second) = cache.prepare(&config, &compiled)?;
    assert_eq!(second, Prepared::Present { bytes });
    let encode = |parts: &[FixedSetup]| {
      bincode::serde::encode_to_vec(parts, bincode::config::standard()).unwrap()
    };
    assert_eq!(encode(&parts), encode(&again));
    assert_eq!(
      encode(&parts),
      encode(&super::super::prover::fixed_setup(&config, &compiled,)?)
    );
    // A stage restores the entry and reads its fixed columns in place.
    let staged = root.join("stage");
    let shape = cache.restore(&staged)?.ok_or("entry was not restored")?;
    assert_eq!(shape.heights.len(), compiled.num_circuits());
    let fixed = cache.fixed_directory(&staged)?;
    assert!(fixed.starts_with(cache.directory()));
    let read =
      super::super::prover::fixed_setup_in(&config, &compiled, &fixed)?;
    assert_eq!(encode(&parts), encode(&read));
    // Only the entry is left beside the staged stage: no partial directories.
    let names: Vec<_> = fs::read_dir(&root)?
      .map(|entry| Ok(entry?.file_name()))
      .collect::<Result<_>>()?;
    assert_eq!(names.len(), 2);
    // A damaged entry fails the check instead of being skipped.
    let checkpoint = cache.directory().join("kzg/fixed-0.bin");
    let mut bytes = fs::read(&checkpoint)?;
    *bytes.last_mut().unwrap() ^= 1;
    fs::remove_file(&checkpoint)?;
    fs::write(&checkpoint, bytes)?;
    assert!(cache.check().is_err());
    Ok(())
  }
}
