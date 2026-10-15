//! KZG compression of the saved recursive FRI proof.
//!
//! `run` stages, proves and verifies in one process: the translated traces
//! feed commitment directly, and the loaded SRS, fixed preprocessing and
//! device residency are shared between the two halves. The stage writes its
//! proof and the metadata the recursive stage verifies it with, plus the
//! fixed-preprocessing checkpoints that populate the cross-run disk cache.
use crate::fri::{VerifierLimits, VerifierPlan};
#[cfg(test)]
use crate::kzg::Scalar;
use multi_stark::config::ProofConfig;
#[cfg(test)]
use multi_stark::plonkish::{Assignment, MultiStarkCircuit};
#[cfg(test)]
use multi_stark::traits::Field;
use std::{fs, path::Path, time::Instant};

use super::stages::construct::{self, FriConstruction, Lowered, max_height};
use super::{
  fixed_cache::FixedCache,
  setup::{FIRST_SEED, SetupClass},
  storage,
};
#[cfg(test)]
use super::{init_claim, setup::SetupSource};
use super::{init_fri, prover};

/// Partitions of the supported Init profile: ten carry the public words and
/// the rest are tables, which only exist above eleven partitions.
pub(super) const MIN_PARTITIONS: usize = 11;
pub(super) use super::stages::statement::first_claims as expected_claims;

fn log_height_arg(arg: Option<&String>) -> storage::Result<usize> {
  let log_height = arg.map(|s| s.parse::<usize>()).transpose()?.unwrap_or(24);
  if !(24..=28).contains(&log_height) {
    return Err("log-height must be 24..28".into());
  }
  Ok(log_height)
}

pub(super) fn run(
  args: &[String],
  config: &super::WorkerConfig,
) -> storage::Result<()> {
  const USAGE: &str = "usage: ix-compression-worker kzg run <saved-fri-dir> <output-dir> [log-height: 24..28]";
  let Some(command) = args.first() else {
    return Err(USAGE.into());
  };
  let rest = &args[1..];
  match command.as_str() {
    "run" if (2..=3).contains(&rest.len()) => {
      let log_height = log_height_arg(rest.get(2))?;
      stage_and_prove(
        Path::new(&rest[0]),
        Path::new(&rest[1]),
        log_height,
        config,
      )
    },
    _ => Err(USAGE.into()),
  }
}

fn stage_and_prove(
  fri: &Path,
  out: &Path,
  log_height: usize,
  config: &super::WorkerConfig,
) -> storage::Result<()> {
  let trace_height = 1usize << log_height;
  fs::create_dir_all(out)?;
  let fixture = init_fri::load(fri)?;
  let plan = VerifierPlan::validate(
    &fixture.key,
    fixture.profile,
    VerifierLimits::default(),
  )?;
  let plan_id = plan.identity(&fixture.schema)?;
  fs::write(out.join("plan-id.bin"), plan_id)?;
  fs::write(out.join("inner-vk.bin"), fixture.key.to_bytes()?)?;
  let start = Instant::now();
  let prepared = FriConstruction::build(&plan, fixture.schema)?.assign(
    &plan,
    &fixture.proof,
    fixture.claims,
  )?;
  assert_eq!(prepared.public_values(), fixture.public);
  let public = super::stages::scalar_statement(&fixture.public);
  let lowered =
    construct::prepare_first(prepared, trace_height, construct::TABLE_HEIGHT)?;
  assert_eq!(lowered.assignment.public_values(), public);
  println!(
    "Scalar translation and lowering of {} circuits: {:?}; {:?}",
    lowered.compiled.num_circuits(),
    start.elapsed(),
    lowered.compiled.circuit().stats()
  );
  let height = max_height(&lowered.compiled)?;
  let setup = config.setup.for_stage(FIRST_SEED, height)?;
  setup.bind_stage(out, height, 2)?;
  let setup_id = setup.identity(height, 2)?;
  let cache = config.fixed_cache(out, &[plan_id, setup_id].concat())?;
  let cached = cache.restore(out)?;
  let manifest = storage::Manifest::for_compiled(
    &lowered.compiled,
    lowered.compiled.claims(&public)?,
    cached.as_ref(),
  )?;
  storage::save(&out.join("manifest.bin"), &manifest)?;
  println!("Generating fixed and witness traces directly into commitment");
  prove(out, lowered, &cache, config)?;
  println!("RUN COMPLETE: {:?}", start.elapsed());
  Ok(())
}

/// Commit the fixed and witness traces of every partition, prove them
/// together, verify the proof and write it with its packet. Fixed
/// preprocessing comes from the cache when it holds this profile and is
/// published to it after the proof verifies.
fn prove(
  dir: &Path,
  lowered: Lowered,
  cache: &FixedCache,
  config: &super::WorkerConfig,
) -> storage::Result<()> {
  let manifest: storage::Manifest = storage::load(&dir.join("manifest.bin"))?;
  let count = manifest.heights.len();
  if count < MIN_PARTITIONS
    || manifest.widths.len() != count
    || manifest.widths.contains(&0)
  {
    return Err("unexpected trace layout".into());
  }
  let height = *manifest.heights.iter().max().ok_or("empty manifest")?;
  if height > 1 << 28
    || manifest.heights.iter().any(|h| *h < 2 || !h.is_power_of_two())
  {
    return Err("unsupported trace height".into());
  }
  let compiled = &lowered.compiled;
  if compiled.num_circuits() != count
    || (0..count).any(|i| {
      compiled.trace_dimensions(i)
        != Some((manifest.heights[i], manifest.widths[i]))
    })
  {
    return Err(
      "generated trace dimensions differ from the staged manifest".into(),
    );
  }
  let statement = super::statement::from_rows(&manifest.claims)?;
  if manifest.claims != expected_claims(count, &statement) {
    return Err(
      "staged claims differ from the statement and activation anchors".into(),
    );
  }
  let setup = config.setup.for_stage(FIRST_SEED, height)?;
  setup.check_binding(dir, height, 2)?;
  let setup_id = setup.identity(height, 2)?;
  let plan_id: [u8; 32] = fs::read(dir.join("plan-id.bin"))?
    .try_into()
    .map_err(|bytes: Vec<u8>| {
      format!("invalid verifier plan identity: {} bytes", bytes.len())
    })?;
  let out = dir.join("kzg");
  fs::create_dir_all(&out)?;
  fs::write(out.join("SECURITY.txt"), setup.security_description())?;
  let start = Instant::now();
  let prefetch_bytes = config.prefetch_bytes;
  let config = setup
    .config(height, 2, false)?
    .with_streaming_lookups()
    .with_streaming_quotient();
  println!("KZG parameters ready: {:?}", start.elapsed());
  println!("Partition prefetch budget: {} GiB", prefetch_bytes >> 30);
  let prover::Proved { system, bytes, verify_seconds, .. } = lowered
    .commit(config, Some(&out), prefetch_bytes)?
    .prove(&manifest.claims)?;
  let output_span = tracing::info_span!("compression/write_output").entered();
  // The label is part of every published profile id and predates the
  // Filecoin setup; the setup class is bound through the transcript seed.
  let mut profile = blake3::Hasher::new();
  profile.update(b"init-fri-kzg-ordinary-v1/development-srs/quotient2");
  profile.update(system.config.transcript_seed());
  profile.update(&plan_id);
  profile.update(&fs::read(dir.join("manifest.bin"))?);
  for i in 0..count {
    profile.update(&fs::read(out.join(format!("setup-{i}.bin")))?);
  }
  let profile = *profile.finalize().as_bytes();
  let mut packet = profile.to_vec();
  for claim in &manifest.claims[1..19] {
    packet.extend_from_slice(&claim[3].canonical_limbs_le()[0].to_le_bytes());
  }
  packet.extend_from_slice(&bytes);
  storage::write_atomic(&out.join("proof.compact.bin"), &bytes)?;
  storage::write_atomic(&out.join("profile-id.bin"), &profile)?;
  storage::write_atomic(&out.join("packet.bin"), &packet)?;
  let development = setup.class() == SetupClass::Development;
  let public_setup = system.config.pcs().public_setup();
  let evidence = serde_json::json!({
    "proof_bytes": bytes.len(),
    "packet_bytes": packet.len(),
    "trace_heights": manifest.heights,
    "verify_seconds": verify_seconds,
    "total_seconds": start.elapsed().as_secs_f64(),
    "native_verification_passed": true,
    "development_srs": development,
    "known_trapdoor": development,
    "setup": setup.class().label(),
    "setup_id": blake3::Hash::from_bytes(setup_id).to_string(),
    "public_setup_id": blake3::Hash::from_bytes(public_setup.id).to_string(),
    "public_max_degree": public_setup.max_degree,
  });
  fs::write(out.join("prove-report.json"), format!("{evidence}\n"))?;
  drop(output_span);
  cache.publish(dir)?;
  println!(
    "VERIFIED: proof_bytes={} packet_bytes={} verify_seconds={verify_seconds} total_seconds={} development_srs={development}",
    bytes.len(),
    packet.len(),
    start.elapsed().as_secs_f64()
  );
  Ok(())
}

#[cfg(test)]
mod tests {
  use super::*;
  use multi_stark::plonkish::gadgets::ByteGadgets;
  use multi_stark::plonkish::gadgets::blake3;
  use multi_stark::plonkish::{CircuitBuilder, Value};

  const OPTIONS: super::super::WorkerConfig = super::super::WorkerConfig {
    prefetch_bytes: 1 << 20,
    setup: super::super::setup::SetupConfig::Development {
      cache_directory: None,
    },
    fixed_cache_root: None,
  };

  fn artifacts(directory: &Path) -> storage::Result<Vec<Vec<u8>>> {
    Ok(
      ["proof.compact.bin", "packet.bin", "profile-id.bin"]
        .into_iter()
        .map(|name| fs::read(directory.join("kzg").join(name)))
        .collect::<Result<_, _>>()?,
    )
  }

  struct Fixture {
    compiled: MultiStarkCircuit<Scalar>,
    public: Vec<Scalar>,
    input: Value,
    private: Value,
  }

  impl Fixture {
    fn assign(&self, private_byte: u8) -> storage::Result<Assignment<Scalar>> {
      let mut witness = self.compiled.witness();
      witness.set(self.input, Scalar::from_u8(7))?;
      witness.set(self.private, Scalar::from_u8(private_byte))?;
      Ok(witness.generate()?)
    }
  }

  /// A small circuit whose lowering has the Init stage's partition layout.
  fn fixture(log_height: usize) -> storage::Result<Fixture> {
    let mut builder = CircuitBuilder::<Scalar>::new();
    builder.enable_compact_blake3();
    let bytes = ByteGadgets::new(&mut builder);
    let input = bytes.input(&mut builder, "byte");
    let private = bytes.input(&mut builder, "private byte");
    let _digest = blake3(&mut builder, &bytes, &[input, private]);
    let seven = builder.constant(Scalar::from_u8(7));
    for _ in 0..65540 {
      builder.assert_equal(input.value(), seven);
    }
    let public: Vec<_> =
      init_claim::INIT_PUBLIC_WORDS.into_iter().map(Scalar::from_u64).collect();
    for &word in &public {
      let value = builder.constant(word);
      builder.expose_public(value);
    }
    let compiled = builder
      .finish()
      .lower_to_multi_stark_sharded(Scalar::from_u8(93), 1 << log_height)?
      .merge_table_traces(1 << 22)?;
    Ok(Fixture {
      compiled,
      public,
      input: input.value(),
      private: private.value(),
    })
  }

  /// Write the metadata `stage_and_prove` produces before proving.
  fn stage(
    dir: &Path,
    compiled: &MultiStarkCircuit<Scalar>,
    public: &[Scalar],
    cache_root: &Path,
  ) -> storage::Result<FixedCache> {
    fs::create_dir_all(dir)?;
    let height = max_height(compiled)?;
    SetupSource::development(FIRST_SEED, height - 1)?
      .bind_stage(dir, height, 2)?;
    fs::write(dir.join("plan-id.bin"), [0u8; 32])?;
    let cache = FixedCache::from_profile(cache_root, b"fixture-v1")?;
    let cached = cache.restore(dir)?;
    let manifest = storage::Manifest::for_compiled(
      compiled,
      compiled.claims(public)?,
      cached.as_ref(),
    )?;
    storage::save(&dir.join("manifest.bin"), &manifest)?;
    Ok(cache)
  }

  #[test]
  fn fused_fixture_proves_and_reuses_fixed_preprocessing() -> storage::Result<()>
  {
    let partitioned = prove_fixture(16)?;
    let single = prove_fixture(17)?;
    assert!(single < partitioned, "fewer partitions should reduce this proof");
    Ok(())
  }

  fn prove_fixture(log_height: usize) -> storage::Result<usize> {
    let root = std::env::temp_dir().join(format!(
      "init-fri-kzg-fixture-{}-{log_height}",
      std::process::id()
    ));
    fs::create_dir(&root)?;
    let fixture = fixture(log_height)?;
    let (compiled, public) = (&fixture.compiled, &fixture.public);
    assert_eq!(compiled.num_circuits(), if log_height == 16 { 12 } else { 11 });
    let prove =
      |dir: &Path, cache: &FixedCache, private: u8| -> storage::Result<()> {
        let fixture = self::fixture(log_height)?;
        let assignment = fixture.assign(private)?;
        prove(
          dir,
          Lowered { compiled: fixture.compiled, assignment },
          cache,
          &OPTIONS,
        )
      };
    let cache_root = root.join("cache");

    // A cold run commits the fixed traces, proves and publishes the cache.
    let dir = root.join("cold");
    let cache = stage(&dir, compiled, public, &cache_root)?;
    prove(&dir, &cache, 9)?;
    let first = artifacts(&dir)?;
    let manifest: storage::Manifest = storage::load(&dir.join("manifest.bin"))?;
    for i in 0..manifest.heights.len() {
      assert!(dir.join(format!("kzg/fixed-{i}.bin")).exists());
      assert!(dir.join(format!("kzg/setup-{i}.bin")).exists());
      assert!(!dir.join(format!("kzg/main-{i}.bin")).exists());
    }
    let report: serde_json::Value =
      serde_json::from_slice(&fs::read(dir.join("kzg/prove-report.json"))?)?;
    assert_eq!(report["setup"], "development");
    assert_eq!(report["development_srs"], true);

    // A warm run restores the fixed preprocessing from the cache and
    // produces identical artifacts.
    let warm = root.join("warm");
    let cache = stage(&warm, compiled, public, &cache_root)?;
    for i in 0..manifest.heights.len() {
      assert!(warm.join(format!("kzg/fixed-{i}.bin")).exists());
    }
    prove(&warm, &cache, 9)?;
    assert_eq!(first, artifacts(&warm)?);
    let different =
      FixedCache::from_profile(&cache_root, b"different-profile")?;
    assert!(different.restore(&root.join("miss"))?.is_none());

    // A different witness changes the proof but not the profile.
    let changed = root.join("changed");
    let cache = stage(&changed, compiled, public, &cache_root)?;
    prove(&changed, &cache, 231)?;
    let second = artifacts(&changed)?;
    assert_ne!(first[0], second[0]);
    assert_eq!(first[2], second[2]);

    // Manifests that disagree with the generated traces are rejected
    // before any parameters load.
    for case in 0..3 {
      let mut shape = storage::Manifest {
        widths: manifest.widths.clone(),
        heights: manifest.heights.clone(),
        claims: manifest.claims.clone(),
      };
      match case {
        0 => shape.widths[0] += 1,
        1 => shape.heights[0] *= 2,
        _ => {
          shape.widths.push(1);
          shape.heights.push(2);
        },
      }
      let malformed = root.join(format!("invalid-shape-{case}"));
      let cache = stage(&malformed, compiled, public, &cache_root)?;
      storage::save(&malformed.join("manifest.bin"), &shape)?;
      let error = prove(&malformed, &cache, 9).unwrap_err();
      assert!(error.to_string().contains("trace dimensions differ"));
      assert!(!malformed.join("kzg/proof.compact.bin").exists());
    }
    let malformed = root.join("invalid-height");
    let cache = stage(&malformed, compiled, public, &cache_root)?;
    let mut shape = storage::Manifest {
      widths: manifest.widths.clone(),
      heights: manifest.heights.clone(),
      claims: manifest.claims.clone(),
    };
    shape.heights[1] = 3;
    storage::save(&malformed.join("manifest.bin"), &shape)?;
    let error = prove(&malformed, &cache, 9).unwrap_err();
    assert!(error.to_string().contains("trace height"));
    shape.heights[1] = manifest.heights[1];
    shape.widths[1] = 0;
    storage::save(&malformed.join("manifest.bin"), &shape)?;
    let error = prove(&malformed, &cache, 9).unwrap_err();
    assert!(error.to_string().contains("unexpected trace layout"));

    // Removing a claim invalidates the staged claims.
    let mut fewer = storage::Manifest {
      widths: manifest.widths.clone(),
      heights: manifest.heights.clone(),
      claims: manifest.claims.clone(),
    };
    fewer.claims.pop();
    storage::save(&malformed.join("manifest.bin"), &fewer)?;
    let error = prove(&malformed, &cache, 9).unwrap_err();
    assert!(error.to_string().contains("staged claims differ"));

    // A damaged cache entry is rejected before anything is linked into a
    // stage, whether it is metadata or a fixed checkpoint whose interior
    // bytes still decode. Files are replaced rather than edited so the
    // hard links into the proved stages keep their contents.
    let entries = fs::read_dir(&cache_root)?
      .map(|entry| Ok(entry?.path()))
      .collect::<storage::Result<Vec<_>>>()?;
    let [entry] = entries.as_slice() else {
      panic!("expected one published entry, found {entries:?}");
    };
    let cache = FixedCache::from_profile(&cache_root, b"fixture-v1")?;
    let damaged = root.join("damaged");
    for name in ["kzg/fixed-0.bin", "kzg/setup-0.bin"] {
      let published = entry.join(name);
      let original = fs::read(&published)?;
      let mut bytes = original.clone();
      let middle = bytes.len() / 2;
      bytes[middle] ^= 1;
      fs::remove_file(&published)?;
      fs::write(&published, bytes)?;
      fs::create_dir(&damaged)?;
      let error =
        cache.restore(&damaged).err().ok_or("damaged cache was restored")?;
      assert!(error.to_string().contains("incomplete or damaged"));
      assert!(!damaged.join("kzg").exists());
      fs::remove_dir_all(&damaged)?;
      fs::remove_file(&published)?;
      fs::write(&published, original)?;
    }
    fs::create_dir(&damaged)?;
    assert!(cache.restore(&damaged)?.is_some());
    fs::remove_dir_all(root)?;
    Ok(first[0].len())
  }
}
