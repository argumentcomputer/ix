//! Recursive KZG wrapper: fused or checkpointed staging, proving and the
//! portable development verifier.
use super::{
  super::Result as PipelineResult,
  super::{
    init_claim,
    setup::{SetupClass, SetupSource},
    storage,
    support::kzg_fixed_cache as fixed_cache,
  },
};
use crate::{
  foreign::KzgCircuitExt,
  kzg::{
    KzgCommitment, KzgConfig, Scalar, TranscriptKind, compact::FixedProofCodec,
  },
  recursive::native_verifier::Built,
};
use multi_stark::{
  plonkish::{Assignment, MultiStarkCircuit, TraceShards},
  traits::Field,
};
use p3_matrix::Matrix;
use std::{fs, path::Path};

pub(super) const OUTER_SEED: &[u8] = b"init-kzg-recursive-v1";
const OUTER_PROFILE_VERSION: u32 = 5;
/// Largest admitted recursive computation trace. The development public
/// degree of a staged profile covers exactly its own height.
pub(super) const MAX_TRACE_LEN: usize = 1 << 27;

#[derive(serde::Serialize, serde::Deserialize)]
struct Pairings {
  keys: Vec<u8>,
}

pub(crate) fn stage(
  built: Built,
  assignment: &Assignment<Scalar>,
  dir: &Path,
  profile: &[u8],
  fused: bool,
) -> storage::Result<()> {
  Frontend::new(built.circuit, &built.pairing_keys, profile, MAX_TRACE_LEN)?
    .stage(assignment, dir, fused)
}

/// A recursive circuit lowered into one computation trace and one merged
/// table, ready to stage any number of requests of its profile.
pub(crate) struct Frontend {
  compiled: MultiStarkCircuit<Scalar>,
  pairings: Pairings,
  profile: Vec<u8>,
}

impl Frontend {
  pub(crate) fn new(
    circuit: multi_stark::plonkish::Circuit<Scalar>,
    keys: &[ark_bls12_381::G2Affine],
    profile: &[u8],
    max_height: usize,
  ) -> storage::Result<Self> {
    use ark_serialize::CanonicalSerialize;
    if keys.len() != 2 {
      return Err("invalid recursive pairing profile".into());
    }
    let height = circuit.multi_stark_layout()?.main_height;
    if height > max_height {
      return Err(
        "recursive computation exceeds its single-trace height cap".into(),
      );
    }
    let mut encoded = vec![];
    keys.serialize_compressed(&mut encoded)?;
    eprintln!(
      "Lowering recursive circuit into one {height}-row computation trace"
    );
    let compiled = circuit
      .lower_to_multi_stark_sharded(Scalar::from_u8(94), height)?
      .merge_table_traces(height)?;
    if compiled.num_circuits() != 2 || compiled.main_heights() != [height] {
      return Err("expected one computation trace and one merged table".into());
    }
    Ok(Self {
      compiled,
      pairings: Pairings { keys: encoded },
      profile: profile.to_vec(),
    })
  }

  /// Stage one request. Fused staging keeps the witness traces in memory
  /// and proves immediately; otherwise the traces are checkpointed for a
  /// later `prove`. Fixed preprocessing comes from the trusted cache when
  /// one is configured and already holds this profile.
  pub(crate) fn stage(
    &self,
    assignment: &Assignment<Scalar>,
    dir: &Path,
    fused: bool,
  ) -> storage::Result<()> {
    if dir.join("manifest.bin").exists() {
      // A fused run writes its manifest before proving and keeps no witness
      // files; a directory with a manifest but no traces is an interrupted
      // fused run and is staged again.
      if !fused || super::super::first::has_restartable_traces(dir)? {
        return Err("already staged".into());
      }
      fs::remove_file(dir.join("manifest.bin"))?;
    }
    super::super::first::clear_partition_artifacts(dir)?;
    if assignment.public_values().len() != 18 + 2 * 2
      || assignment.public_values()[..18]
        .iter()
        .zip(init_claim::INIT_PUBLIC_WORDS)
        .any(|(&value, word)| value != Scalar::from_u64(word))
    {
      return Err(
        "recursive assignment differs from the independently expected statement"
          .into(),
      );
    }
    let start = std::time::Instant::now();
    let height = self.compiled.main_height();
    let setup = SetupSource::for_stage(OUTER_SEED, height, None)?
      .with_transcript(TranscriptKind::Keccak256);
    let setup_id = setup.identity(height, 2)?;
    let traces = self.compiled.trace_shards(assignment)?;
    fs::create_dir_all(dir)?;
    setup.bind_stage(dir, height, 2)?;
    fs::write(
      dir.join("frontend-id.bin"),
      blake3::hash(&self.profile).as_bytes(),
    )?;
    storage::save(&dir.join("pairings.bin"), &self.pairings)?;
    let mut manifest = storage::Manifest {
      widths: vec![],
      heights: vec![],
      claims: self.compiled.claims(assignment.public_values())?,
    };
    let cache_profile = [self.profile.as_slice(), &setup_id].concat();
    let cache = Some(fixed_cache::FixedCache::for_stage(dir, &cache_profile)?);
    let cached =
      cache.as_ref().map(|cache| cache.restore(dir)).transpose()?.flatten();
    if cached.as_ref().is_some_and(|shape| {
      shape.widths.len() != self.compiled.num_circuits()
        || shape.heights.len() != self.compiled.num_circuits()
    }) {
      return Err(
        "cached trace count differs from the compiled circuit".into(),
      );
    }
    for i in 0..self.compiled.num_circuits() {
      let (expected_height, expected_width) =
        self.compiled.trace_dimensions(i).ok_or("missing compiled trace")?;
      if let Some(shape) = &cached {
        if shape.widths[i] != expected_width
          || shape.heights[i] != expected_height
        {
          return Err(
            "cached fixed trace dimensions differ from the compiled circuit"
              .into(),
          );
        }
        manifest.widths.push(shape.widths[i]);
        manifest.heights.push(shape.heights[i]);
      } else if fused {
        manifest.widths.push(expected_width);
        manifest.heights.push(expected_height);
      } else {
        let mut definition = self
          .compiled
          .kzg_circuit_input(i, height, 2)?
          .ok_or("missing circuit")?;
        let fixed =
          definition.preprocessed.take().ok_or("missing preprocessing")?;
        manifest.widths.push(definition.main_width);
        manifest.heights.push(fixed.height());
        storage::save(&dir.join(format!("{i}.meta")), &definition)?;
        storage::write_matrix(&dir.join(format!("{i}.fixed.zst")), &fixed)?;
      }
      if !fused {
        let trace = traces.trace(i)?;
        if trace.width() != manifest.widths[i]
          || trace.height() != manifest.heights[i]
        {
          return Err(
            "cached fixed trace and witness have different shapes".into(),
          );
        }
        storage::write_matrix(&dir.join(format!("{i}.witness.zst")), &trace)?;
      }
      eprintln!("Staged recursive trace {i}: {:?}", start.elapsed());
    }
    storage::save(&dir.join("manifest.bin"), &manifest)?;
    fs::write(dir.join("SECURITY.txt"), setup.security_description())?;
    eprintln!("Recursive staging complete: {:?}", start.elapsed());
    if fused {
      prove_with_traces(dir, false, true, Some(&traces))?;
      eprintln!("Recursive stage-and-prove complete: {:?}", start.elapsed());
    }
    Ok(())
  }
}

fn pairing_keys(dir: &Path) -> storage::Result<Vec<ark_bls12_381::G2Affine>> {
  let profile: Pairings = storage::load(&dir.join("pairings.bin"))?;
  decode_pairing_keys(&profile)
}

fn decode_pairing_keys(
  profile: &Pairings,
) -> storage::Result<Vec<ark_bls12_381::G2Affine>> {
  use ark_ec::AffineRepr;
  use ark_serialize::CanonicalDeserialize;
  if profile.keys.len() != 8 + 2 * 96
    || profile.keys.get(..8) != Some(&2u64.to_le_bytes())
  {
    return Err("invalid pairing profile".into());
  }
  let mut input = profile.keys.as_slice();
  let keys =
    Vec::<ark_bls12_381::G2Affine>::deserialize_compressed(&mut input)?;
  if !input.is_empty()
    || keys.len() != 2
    || keys.iter().any(AffineRepr::is_zero)
  {
    return Err("invalid pairing profile".into());
  }
  Ok(keys)
}

fn pairing_bytes(publics: &[Scalar]) -> storage::Result<Vec<u8>> {
  let mut bytes = vec![];
  for value in publics {
    let full: Vec<_> = value
      .canonical_limbs_le()
      .into_iter()
      .flat_map(u64::to_le_bytes)
      .collect();
    if full[24..].iter().any(|&v| v != 0) {
      return Err("noncanonical packed point".into());
    }
    bytes.extend_from_slice(&full[..24]);
  }
  Ok(bytes)
}
fn check_pairings(
  bytes: &[u8],
  keys: &[ark_bls12_381::G2Affine],
) -> storage::Result<()> {
  use ark_ec::pairing::Pairing;
  use ark_ff::Zero;
  use ark_serialize::CanonicalDeserialize;
  if bytes.len() != keys.len() * 48 || keys.len() != 2 {
    return Err("pairing point count".into());
  }
  let points = bytes
    .as_chunks::<48>()
    .0
    .iter()
    .map(|bytes| {
      ark_bls12_381::G1Affine::deserialize_compressed(bytes.as_slice())
    })
    .collect::<Result<Vec<_>, _>>()?;
  if !ark_bls12_381::Bls12_381::multi_pairing(points, keys.iter().copied())
    .is_zero()
  {
    return Err("external opening pairing equation failed".into());
  }
  Ok(())
}
fn packet_claims(
  packet: &[u8],
  profile: &[u8; 32],
  pairing_count: usize,
) -> storage::Result<(Vec<Vec<Scalar>>, usize)> {
  use multi_stark::traits::Algebra;
  let offset = 32 + 18 * 8 + pairing_count * 48;
  if packet.len() < offset || packet[..32] != *profile {
    return Err("packet profile mismatch".into());
  }
  let mut publics = vec![];
  for (bytes, expected) in packet[32..32 + 18 * 8]
    .as_chunks::<8>()
    .0
    .iter()
    .zip(init_claim::INIT_PUBLIC_WORDS)
  {
    let word = u64::from_le_bytes(*bytes);
    if word != expected {
      return Err("unexpected Init claim".into());
    }
    publics.push(Scalar::from_u64(word));
  }
  for bytes in packet[32 + 18 * 8..offset].as_chunks::<24>().0.iter() {
    let mut limbs = [0u64; 4];
    for (i, chunk) in bytes.as_chunks::<8>().0.iter().enumerate() {
      limbs[i] = u64::from_le_bytes(*chunk);
    }
    publics.push(Scalar::from_limbs_le(limbs));
  }
  let claims = std::iter::once(Scalar::ZERO)
    .chain(publics)
    .enumerate()
    .map(|(i, value)| {
      vec![Scalar::from_u8(94), Scalar::ONE, Scalar::from_usize(i), value]
    })
    .collect();
  Ok((claims, offset))
}
fn verify_packet(
  system: &multi_stark::system::System<KzgConfig>,
  codec: &FixedProofCodec,
  packet: &[u8],
  profile: &[u8; 32],
  keys: &[ark_bls12_381::G2Affine],
) -> storage::Result<()> {
  let (claims, offset) = packet_claims(packet, profile, keys.len())?;
  let proof = codec.decode(&packet[offset..])?;
  system
    .verify_multiple_claims(
      &claims.iter().map(Vec::as_slice).collect::<Vec<_>>(),
      &proof,
    )
    .map_err(|e| format!("outer KZG proof: {e:?}"))?;
  check_pairings(&packet[32 + 18 * 8..offset], keys)
}

fn staged_publics(
  claims: &[Vec<Scalar>],
  pairing_count: usize,
) -> storage::Result<Vec<Scalar>> {
  use multi_stark::traits::Algebra;
  let expected = pairing_count
    .checked_mul(2)
    .and_then(|n| n.checked_add(19))
    .ok_or("public count overflow")?;
  if claims.len() != expected
    || claims.iter().enumerate().any(|(i, row)| {
      row.len() != 4
        || row[0] != Scalar::from_u8(94)
        || row[1] != Scalar::ONE
        || row[2] != Scalar::from_usize(i)
    })
    || claims[0][3] != Scalar::ZERO
  {
    return Err("wrong recursive public profile".into());
  }
  Ok(claims[1..].iter().map(|row| row[3]).collect())
}

pub(crate) fn prove(
  dir: &Path,
  verify_only: bool,
  resident: bool,
) -> storage::Result<()> {
  prove_with_traces(dir, verify_only, resident, None)
}

/// Prove or verify a staged request. With `traces`, the fused witness is
/// committed from memory and never checkpointed; otherwise the staged
/// witness files are read. Fixed columns are always checkpointed because
/// every proof of the profile shares them. Without `resident`, committed
/// columns are served from their checkpoints instead of host memory.
fn prove_with_traces(
  dir: &Path,
  verify_only: bool,
  resident: bool,
  traces: Option<&TraceShards<'_, Scalar>>,
) -> storage::Result<()> {
  use crate::kzg::pcs::KzgProverData;
  use multi_stark::{
    config::ProofConfig,
    lookup::LookupValues,
    prover::Stage1,
    system::{Circuit, CircuitInputs, ProverKey, System},
    traits::{Algebra, Pcs},
  };
  use std::{fs::File, time::Instant};
  let _ = tracing_subscriber::fmt()
    .with_ansi(false)
    .with_max_level(tracing_subscriber::filter::LevelFilter::INFO)
    .try_init();
  let start = Instant::now();
  let manifest: storage::Manifest = storage::load(&dir.join("manifest.bin"))?;
  if manifest.heights.len() != 2
    || manifest.widths.len() != 2
    || manifest.widths[0] != 3
    || manifest.widths[1] != 1
    || manifest
      .heights
      .iter()
      .any(|h| *h < 2 || !h.is_power_of_two() || *h > 1 << 28)
    || manifest.heights[1] > manifest.heights[0]
  {
    return Err("expected one computation trace and one merged table".into());
  }
  let count = manifest.heights.len();
  let height = manifest.heights[0];
  if let Some(traces) = traces {
    let compiled = traces.compiled();
    if compiled.num_circuits() != count
      || compiled.main_heights() != [height]
      || (0..count).any(|i| {
        compiled.trace_dimensions(i)
          != Some((manifest.heights[i], manifest.widths[i]))
      })
    {
      return Err(
        "compiled trace dimensions differ from the staged manifest".into(),
      );
    }
  }
  let keys = pairing_keys(dir)?;
  let publics = staged_publics(&manifest.claims, keys.len())?;
  let point_bytes = pairing_bytes(&publics[18..])?;
  check_pairings(&point_bytes, &keys)?;
  for (&value, expected) in
    publics[..18].iter().zip(init_claim::INIT_PUBLIC_WORDS)
  {
    if value != Scalar::from_u64(expected) {
      return Err("wrong Init claim".into());
    }
  }
  let out = dir.join("kzg");
  fs::create_dir_all(&out)?;
  eprintln!("Preparing KZG parameters for 2^{} rows", height.ilog2());
  let setup =
    SetupSource::for_stage(OUTER_SEED, height, Some(out.join("dev-srs.bin")))?
      .with_transcript(TranscriptKind::Keccak256);
  setup.check_binding(dir, height, 2)?;
  fs::write(out.join("SECURITY.txt"), setup.security_description())?;
  let setup_id = setup.identity(height, 2)?;
  let verifier_params = setup.verifier_params(height)?;
  let config_started = Instant::now();
  let config = setup
    .config(height, 2, verify_only)?
    .with_streaming_lookups()
    .with_streaming_quotient();
  let srs_config_load_seconds = config_started.elapsed().as_secs_f64();
  eprintln!("Outer KZG parameters ready: {:?}", start.elapsed());
  let checkpoint = super::super::first::write_checkpoint;
  let load = |path: &Path| -> storage::Result<KzgProverData> {
    Ok(if resident || cfg!(feature = "cuda") {
      KzgProverData::read_checkpoint(std::io::BufReader::with_capacity(
        1 << 20,
        File::open(path)?,
      ))?
    } else {
      KzgProverData::read_checkpoint_file(path)?
    })
  };
  let retain = |path: &Path,
                data: KzgProverData,
                persist: bool|
   -> storage::Result<KzgProverData> {
    if resident {
      if persist {
        checkpoint(path, &data)?;
      }
      return Ok(data);
    }
    checkpoint(path, &data)?;
    drop(data);
    load(path)
  };
  let mut circuits = vec![];
  let mut commits = vec![];
  let mut fixed_parts = vec![];
  let mut main_parts = vec![];
  for i in 0..count {
    let meta = out.join(format!("setup-{i}.bin"));
    let fixed_path = out.join(format!("fixed-{i}.bin"));
    let main_path = out.join(format!("main-{i}.bin"));
    let (circuit, commit): (Circuit<Scalar>, KzgCommitment) = if meta.exists()
      && (verify_only || fixed_path.exists())
    {
      if !verify_only {
        fixed_parts.push(load(&fixed_path)?);
      }
      storage::load(&meta)?
    } else {
      if verify_only {
        return Err("missing setup checkpoint".into());
      }
      let mut definition: CircuitInputs<Scalar> = match traces {
        Some(traces) => traces
          .compiled()
          .kzg_circuit_input(i, height, 2)?
          .ok_or("missing compiled circuit")?,
        None => storage::definition(dir, i, height)?,
      };
      if definition.main_width != manifest.widths[i]
        || definition.preprocessed.as_ref().is_none_or(|fixed| {
          fixed.width() == 0 || fixed.height() != manifest.heights[i]
        })
      {
        return Err(
          "fixed trace dimensions differ from the staged manifest".into(),
        );
      }
      if traces.is_some() {
        let fixed =
          definition.preprocessed.take().ok_or("missing preprocessing")?;
        storage::save(&dir.join(format!("{i}.meta")), &definition)?;
        definition.preprocessed = Some(fixed);
      }
      eprintln!("Committing recursive fixed trace {i}: {:?}", start.elapsed());
      let (mut local, key) =
        System::new_without_preprocessed(config.clone(), [definition]);
      let mut circuit = local.circuits.remove(0);
      circuit.preprocessed = None;
      let data = key.preprocessed_data.unwrap();
      fixed_parts.push(retain(&fixed_path, data, true)?);
      let pair = (circuit, local.preprocessed_commit.unwrap());
      storage::save(&meta, &pair)?;
      pair
    };
    if circuit.preprocessed_height != manifest.heights[i]
      || circuit.main_width != manifest.widths[i]
    {
      return Err("setup shape mismatch".into());
    }
    circuits.push(circuit);
    commits.push(commit);
    if !verify_only {
      let data = if traces.is_none() && main_path.exists() {
        load(&main_path)?
      } else {
        let main = match traces {
          Some(traces) => traces.trace(i)?,
          None => storage::read_matrix_with_shape(
            &dir.join(format!("{i}.witness.zst")),
            manifest.widths[i],
            manifest.heights[i],
          )?,
        };
        if main.width() != manifest.widths[i]
          || main.height() != manifest.heights[i]
        {
          return Err(
            "generated trace dimensions differ from the staged manifest".into(),
          );
        }
        eprintln!("Committing recursive main trace {i}: {:?}", start.elapsed());
        let (_, data) = config.pcs().commit(vec![(
          config.pcs().natural_domain_for_degree(manifest.heights[i]),
          main,
        )]);
        if traces.is_none() { retain(&main_path, data, false)? } else { data }
      };
      main_parts.push(data);
    }
    eprintln!("Prepared recursive trace {i}: {:?}", start.elapsed());
  }
  let mut fixed_commit = KzgCommitment(vec![]);
  for mut commit in commits {
    fixed_commit.0.append(&mut commit.0);
  }
  let system = System {
    config,
    circuits,
    preprocessed_commit: Some(fixed_commit),
    preprocessed_indices: (0..count).map(Some).collect(),
  };
  let logs: Vec<_> =
    manifest.heights.iter().map(|h| u8::try_from(h.ilog2()).unwrap()).collect();
  let codec = FixedProofCodec::new(&system, &logs)?;
  let refs: Vec<_> = manifest.claims.iter().map(Vec::as_slice).collect();
  let path = out.join("proof.compact.bin");
  let bytes = if verify_only {
    fs::read(&path)?
  } else {
    let (commit, fixed) = KzgProverData::concatenate(fixed_parts);
    assert_eq!(Some(commit), system.preprocessed_commit);
    let (commit, main) = KzgProverData::concatenate(main_parts);
    let lookups = system
      .circuits
      .iter()
      .zip(&manifest.heights)
      .map(|(c, &h)| {
        LookupValues::shape_only(
          h,
          &c.graph.lookups.iter().map(|l| l.args.len()).collect::<Vec<_>>(),
        )
      })
      .collect();
    let stage = Stage1 {
      active: vec![true; count],
      active_indices: (0..count).collect(),
      log_degrees: logs.iter().map(|&v| usize::from(v)).collect(),
      stage_1_trace_commit: commit,
      stage_1_trace_data: main,
      lookups,
    };
    eprintln!("Proving recursive KZG wrapper: {:?}", start.elapsed());
    let proof = system.prove_committed(
      &ProverKey { preprocessed_data: Some(fixed) },
      &refs,
      stage,
    );
    system
      .verify_multiple_claims(&refs, &proof)
      .map_err(|e| format!("new outer proof: {e:?}"))?;
    let bytes = codec.encode(&proof)?;
    fs::write(&path, &bytes)?;
    bytes
  };
  let verifier = VerifierProfile {
    version: OUTER_PROFILE_VERSION,
    heights: [manifest.heights[0], manifest.heights[1]],
    setup: [
      fs::read(out.join("setup-0.bin"))?,
      fs::read(out.join("setup-1.bin"))?,
    ],
    pairings: fs::read(dir.join("pairings.bin"))?,
    parameters: verifier_params.to_bytes()?,
  };
  let profile = verifier.id();
  let mut packet = profile.to_vec();
  for word in init_claim::INIT_PUBLIC_WORDS {
    packet.extend(word.to_le_bytes());
  }
  packet.extend(point_bytes);
  packet.extend(&bytes);
  if packet.len() >= 3_000 {
    return Err(
      "final public-degree proof packet must be smaller than 3000 bytes".into(),
    );
  }
  if verify_only
    && (fs::read(out.join("packet.bin"))? != packet
      || fs::read(out.join("profile-id.bin"))? != profile)
  {
    return Err("saved packet or profile differs".into());
  }
  let verify_start = Instant::now();
  verify_packet(&system, &codec, &packet, &profile, &keys)?;
  let verify_seconds = verify_start.elapsed().as_secs_f64();
  let decoded = codec.decode(&bytes)?;
  for i in 0..18 {
    let mut wrong = manifest.claims.clone();
    wrong[i + 1][3] += Scalar::ONE;
    assert!(
      system
        .verify_multiple_claims(
          &wrong.iter().map(Vec::as_slice).collect::<Vec<_>>(),
          &decoded
        )
        .is_err()
    );
  }
  for offset in [0, 32, 32 + 18 * 8, packet.len() - 1] {
    let mut wrong = packet.clone();
    wrong[offset] ^= 1;
    assert!(verify_packet(&system, &codec, &wrong, &profile, &keys).is_err());
  }
  assert!(
    verify_packet(
      &system,
      &codec,
      &packet[..packet.len() - 1],
      &profile,
      &keys
    )
    .is_err()
  );
  let mut extra = packet.clone();
  extra.push(0);
  assert!(verify_packet(&system, &codec, &extra, &profile, &keys).is_err());
  if !verify_only {
    // The packet is published last, so its presence means the portable
    // verifier and profile it depends on are complete; a stage without a
    // packet is proved again.
    let encoded =
      bincode::serde::encode_to_vec(&verifier, bincode::config::standard())?;
    storage::write_atomic(&dir.join("verifier.bin"), &encoded)?;
    storage::write_atomic(&out.join("profile-id.bin"), &profile)?;
    storage::write_atomic(&out.join("packet.bin"), &packet)?;
  }
  let public_setup = system.config.pcs().verifier_params().public_setup();
  let development = setup.class() == SetupClass::Development;
  let report = serde_json::json!({
    "proof_bytes": bytes.len(),
    "packet_bytes": packet.len(),
    "claim_bytes": 144,
    "pairing_bytes": keys.len() * 48,
    "profile_bytes": 32,
    "profile_version": OUTER_PROFILE_VERSION,
    "transcript": "keccak256",
    "total_seconds": start.elapsed().as_secs_f64(),
    "verify_seconds": verify_seconds,
    "srs_config_load_seconds": srs_config_load_seconds,
    "native_verification_passed": true,
    "external_pairings_pass": true,
    "negative_tests_pass": true,
    "development_srs": development,
    "known_trapdoor": development,
    "setup": setup.class().label(),
    "fused_witness": traces.is_some(),
    "resident_columns": resident,
    "public_setup_id": blake3::Hash::from_bytes(public_setup.id).to_hex().to_string(),
    "public_max_degree": public_setup.max_degree,
    "setup_id": blake3::Hash::from_bytes(setup_id).to_hex().to_string(),
    "profile_id": blake3::Hash::from_bytes(profile).to_hex().to_string(),
    "trace_heights": manifest.heights,
  });
  fs::write(
    out.join(if verify_only {
      "verify-report.json"
    } else {
      "prove-report.json"
    }),
    serde_json::to_vec_pretty(&report)?,
  )?;
  println!("{}", serde_json::to_string_pretty(&report)?);
  if !verify_only && let Some(cache) = fixed_cache::FixedCache::for_prove(dir)?
  {
    cache.publish(dir)?;
  }
  Ok(())
}

/// Portable recursive verifier. Authentication is handled by the registry.
#[derive(serde::Serialize, serde::Deserialize)]
pub(crate) struct VerifierProfile {
  version: u32,
  heights: [usize; 2],
  setup: [Vec<u8>; 2],
  pairings: Vec<u8>,
  parameters: Vec<u8>,
}

fn decode<T: serde::de::DeserializeOwned>(bytes: &[u8]) -> storage::Result<T> {
  if bytes.len() > 1 << 20 {
    return Err("verifier profile too large".into());
  }
  let (value, consumed) = bincode::serde::decode_from_slice(
    bytes,
    bincode::config::standard().with_limit::<{ 1 << 20 }>(),
  )?;
  if consumed != bytes.len() {
    return Err("trailing verifier profile bytes".into());
  }
  Ok(value)
}

impl VerifierProfile {
  pub(crate) fn from_bytes(bytes: &[u8]) -> PipelineResult<Self> {
    let profile: Self = decode(bytes)?;
    profile.system()?;
    profile.keys()?;
    Ok(profile)
  }

  pub(crate) fn id(&self) -> [u8; 32] {
    let mut hash = blake3::Hasher::new();
    hash.update(
      format!("init-kzg-recursive-profile/v{}", self.version).as_bytes(),
    );
    hash.update(OUTER_SEED);
    hash.update(&self.parameters);
    hash.update(&(self.heights[0] as u64).to_le_bytes());
    for setup in &self.setup {
      hash.update(setup);
    }
    hash.update(&self.pairings);
    *hash.finalize().as_bytes()
  }

  fn keys(&self) -> storage::Result<Vec<ark_bls12_381::G2Affine>> {
    decode_pairing_keys(&decode(&self.pairings)?)
  }

  /// The verifier parameters the profile carries.
  pub(crate) fn verifier_params(
    &self,
  ) -> storage::Result<crate::kzg::VerifierParams> {
    Ok(crate::kzg::VerifierParams::from_bytes(&self.parameters)?)
  }

  fn transcript_kind(&self) -> storage::Result<TranscriptKind> {
    match self.version {
      4 => Ok(TranscriptKind::Blake3),
      5 => Ok(TranscriptKind::Keccak256),
      _ => Err("unsupported recursive verifier profile".into()),
    }
  }

  fn system(&self) -> storage::Result<multi_stark::system::System<KzgConfig>> {
    use crate::kzg::VerifierParams;
    use multi_stark::system::{Circuit, System};
    let kind = self.transcript_kind()?;
    if self
      .heights
      .iter()
      .any(|h| *h < 2 || !h.is_power_of_two() || *h > 1 << 28)
      || self.heights[1] > self.heights[0]
    {
      return Err("unsupported recursive verifier profile".into());
    }
    let params = VerifierParams::from_bytes(&self.parameters)?;
    if params.max_trace_len() != self.heights[0] {
      return Err("verifier SRS range mismatch".into());
    }
    let mut circuits = vec![];
    let mut fixed = KzgCommitment(vec![]);
    for (i, bytes) in self.setup.iter().enumerate() {
      let (circuit, mut commit): (Circuit<Scalar>, KzgCommitment) =
        decode(bytes)?;
      if circuit.main_width != [3, 1][i]
        || circuit.preprocessed_height != self.heights[i]
      {
        return Err("setup shape mismatch".into());
      }
      circuits.push(circuit);
      fixed.0.append(&mut commit.0);
    }
    Ok(System {
      config: KzgConfig::verifier_only(params, 2).with_transcript(kind),
      circuits,
      preprocessed_commit: Some(fixed),
      preprocessed_indices: vec![Some(0), Some(1)],
    })
  }

  pub(crate) fn verify(&self, packet: &[u8]) -> PipelineResult<()> {
    let keys = self.keys()?;
    packet_claims(packet, &self.id(), keys.len())?;
    let system = self.system()?;
    let logs: Vec<_> =
      self.heights.iter().map(|h| u8::try_from(h.ilog2()).unwrap()).collect();
    let codec = FixedProofCodec::new(&system, &logs)?;
    verify_packet(&system, &codec, packet, &self.id(), &keys)
  }
}

pub(crate) fn verify_saved(dir: &Path, packet: &[u8]) -> PipelineResult<()> {
  VerifierProfile::from_bytes(&fs::read(dir.join("verifier.bin"))?)?
    .verify(packet)
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::kzg::Srs;
  use ark_ec::CurveGroup;
  use ark_serialize::CanonicalSerialize;
  use multi_stark::{
    plonkish::CircuitBuilder,
    system::{System, SystemWitness},
    traits::Algebra,
  };
  use std::sync::Arc;

  #[test]
  fn packet_requires_outer_proof_claim_and_external_pairings() {
    let inner = Srs::unsafe_dev_setup(8, b"packet-inner");
    let keys = vec![inner.g2, inner.tau_g2];
    let profile = [17u8; 32];
    let packet_prefix = |wrong: bool| {
      let mut packet = profile.to_vec();
      for v in init_claim::INIT_PUBLIC_WORDS {
        packet.extend(v.to_le_bytes());
      }
      let lhs = if wrong {
        (inner.g1[1] * ark_bls12_381::Fr::from(2u8)).into_affine()
      } else {
        inner.g1[1]
      };
      lhs.serialize_compressed(&mut packet).unwrap();
      (-inner.g1[0]).serialize_compressed(&mut packet).unwrap();
      packet
    };
    let (claims, _) =
      packet_claims(&packet_prefix(false), &profile, 2).unwrap();
    let mut b = CircuitBuilder::new();
    let inputs: Vec<_> = (1..claims.len())
      .map(|i| {
        let v = b.input(format!("public{i}"));
        b.expose_public(v);
        v
      })
      .collect();
    let circuit = b.finish();
    let lowered = circuit.lower_to_multi_stark(Scalar::from_u8(94)).unwrap();
    let config =
      KzgConfig::new(Arc::new(Srs::unsafe_dev_setup(64, b"packet-outer")), 2)
        .with_transcript(TranscriptKind::Keccak256);
    let (system, key) =
      System::new(config, lowered.kzg_circuit_inputs(64, 2).unwrap());
    let codec = FixedProofCodec::new(
      &system,
      &[u8::try_from(system.circuits[0].preprocessed_height.ilog2()).unwrap()],
    )
    .unwrap();
    for wrong in [false, true] {
      let mut packet = packet_prefix(wrong);
      let (claims, _) = packet_claims(&packet, &profile, 2).unwrap();
      let mut w = lowered.witness();
      for (&input, claim) in inputs.iter().zip(&claims[1..]) {
        w.set(input, claim[3]).unwrap();
      }
      let a = w.generate().unwrap();
      let proof = system.prove_multiple_claims(
        &key,
        &claims.iter().map(Vec::as_slice).collect::<Vec<_>>(),
        SystemWitness::from_stage_1(lowered.traces(&a).unwrap(), &system),
      );
      packet.extend(codec.encode(&proof).unwrap());
      assert_eq!(
        verify_packet(&system, &codec, &packet, &profile, &keys).is_ok(),
        !wrong
      );
      if !wrong {
        let mut changed = packet.clone();
        changed[32 + 8] ^= 1;
        assert!(
          verify_packet(&system, &codec, &changed, &profile, &keys).is_err()
        );
        let mut changed_claims = claims.clone();
        changed_claims[2][3] += Scalar::ONE;
        assert!(
          system
            .verify_multiple_claims(
              &changed_claims.iter().map(Vec::as_slice).collect::<Vec<_>>(),
              &proof
            )
            .is_err()
        );
        assert!(
          verify_packet(
            &system,
            &codec,
            &packet[..packet.len() - 1],
            &profile,
            &keys
          )
          .is_err()
        );
        packet.push(0);
        assert!(
          verify_packet(&system, &codec, &packet, &profile, &keys).is_err()
        );
      }
    }
  }

  fn init_packet_claims(inner: &Srs) -> Vec<Vec<Scalar>> {
    let mut prefix = [0u8; 32].to_vec();
    for word in init_claim::INIT_PUBLIC_WORDS {
      prefix.extend(word.to_le_bytes());
    }
    inner.g1[1].serialize_compressed(&mut prefix).unwrap();
    (-inner.g1[0]).serialize_compressed(&mut prefix).unwrap();
    packet_claims(&prefix, &[0u8; 32], 2).unwrap().0
  }

  #[test]
  fn staged_profiles_prove_in_both_storage_modes() -> storage::Result<()> {
    let dir = std::env::temp_dir()
      .join(format!("outer-staged-{}-v5", std::process::id()));
    fs::create_dir(&dir)?;
    let inner = Srs::unsafe_dev_setup(8, b"staged-inner");
    let keys = vec![inner.g2, inner.tau_g2];
    let claims = init_packet_claims(&inner);
    let mut b = CircuitBuilder::new();
    let table =
      b.fixed_table("small", vec![vec![Scalar::ONE], vec![Scalar::TWO]]);
    let one = b.constant(Scalar::ONE);
    b.lookup(table, &[one]);
    for claim in &claims[1..] {
      let value = b.constant(claim[3]);
      b.expose_public(value);
    }
    let compiled = b
      .finish()
      .lower_to_multi_stark_sharded(Scalar::from_u8(94), 128)?
      .merge_table_traces(128)?;
    let assignment = compiled.witness().generate()?;
    let traces = compiled.trace_shards(&assignment)?;
    let height = compiled
      .circuit_inputs()
      .iter()
      .map(|c| c.preprocessed.as_ref().unwrap().height())
      .max()
      .unwrap();
    let mut manifest = storage::Manifest {
      widths: vec![],
      heights: vec![],
      claims: compiled.claims(assignment.public_values())?,
    };
    assert_eq!(manifest.claims, claims);
    for i in 0..compiled.num_circuits() {
      let mut definition = compiled.kzg_circuit_input(i, height, 2)?.unwrap();
      let fixed = definition.preprocessed.take().unwrap();
      manifest.widths.push(definition.main_width);
      manifest.heights.push(fixed.height());
      storage::save(&dir.join(format!("{i}.meta")), &definition)?;
      storage::write_matrix(&dir.join(format!("{i}.fixed.zst")), &fixed)?;
      storage::write_matrix(
        &dir.join(format!("{i}.witness.zst")),
        &traces.trace(i)?,
      )?;
    }
    SetupSource::development(OUTER_SEED, height - 1, None)?
      .with_transcript(TranscriptKind::Keccak256)
      .bind_stage(&dir, height, 2)?;
    storage::save(&dir.join("manifest.bin"), &manifest)?;
    let mut encoded = vec![];
    keys.serialize_compressed(&mut encoded)?;
    storage::save(&dir.join("pairings.bin"), &Pairings { keys: encoded })?;
    prove(&dir, false, true)?;
    assert!(dir.join("kzg/fixed-0.bin").exists());
    assert!(!dir.join("kzg/main-0.bin").exists());
    let resident = fs::read(dir.join("kzg/packet.bin"))?;
    verify_saved(&dir, &resident)?;
    for offset in [0, 32, resident.len() - 1] {
      let mut bad = resident.clone();
      bad[offset] ^= 1;
      assert!(verify_saved(&dir, &bad).is_err());
    }
    assert!(verify_saved(&dir, &resident[..resident.len() - 1]).is_err());
    let mut extra = resident.clone();
    extra.push(0);
    assert!(verify_saved(&dir, &extra).is_err());
    prove(&dir, true, false)?;
    prove(&dir, false, false)?;
    assert!(dir.join("kzg/main-0.bin").exists());
    assert_eq!(resident, fs::read(dir.join("kzg/packet.bin"))?);
    prove(&dir, true, false)?;
    for (row, col) in [(0, 3), (1, 0), (1, 1), (1, 2)] {
      let mut bad = claims.clone();
      bad[row][col] += Scalar::ONE;
      assert!(staged_publics(&bad, keys.len()).is_err());
    }
    let mut bad = claims.clone();
    bad[1].pop();
    assert!(staged_publics(&bad, keys.len()).is_err());
    assert!(staged_publics(&claims[..claims.len() - 1], keys.len()).is_err());
    let portable = fs::read(dir.join("verifier.bin"))?;
    let profile = VerifierProfile::from_bytes(&portable)?;
    assert_eq!(profile.version, OUTER_PROFILE_VERSION);
    assert_eq!(
      profile.system()?.config.transcript_kind(),
      TranscriptKind::Keccak256
    );

    let mut legacy: VerifierProfile = decode(&portable)?;
    legacy.version = 4;
    assert_eq!(
      legacy.system()?.config.transcript_kind(),
      TranscriptKind::Blake3
    );
    assert_ne!(legacy.id(), profile.id());
    let legacy_config = SetupSource::development(OUTER_SEED, height - 1, None)?
      .config(height, 2, false)?;
    let (legacy_system, legacy_key) =
      System::new(legacy_config, compiled.kzg_circuit_inputs(height, 2)?);
    let refs: Vec<_> = claims.iter().map(Vec::as_slice).collect();
    let legacy_proof = legacy_system.prove_multiple_claims(
      &legacy_key,
      &refs,
      SystemWitness::from_stage_1(
        compiled.traces(&assignment)?,
        &legacy_system,
      ),
    );
    let logs: Vec<_> = manifest
      .heights
      .iter()
      .map(|h| u8::try_from(h.ilog2()).unwrap())
      .collect();
    let legacy_proof =
      FixedProofCodec::new(&legacy_system, &logs)?.encode(&legacy_proof)?;
    let offset = 32 + 18 * 8 + 2 * 48;
    let mut legacy_packet = legacy.id().to_vec();
    legacy_packet.extend_from_slice(&resident[32..offset]);
    legacy_packet.extend_from_slice(&legacy_proof);
    assert_eq!(legacy_packet.len(), resident.len());
    let legacy_bytes =
      bincode::serde::encode_to_vec(&legacy, bincode::config::standard())?;
    VerifierProfile::from_bytes(&legacy_bytes)?.verify(&legacy_packet)?;

    let mut downgraded = resident.clone();
    downgraded[..32].copy_from_slice(&legacy.id());
    assert!(legacy.verify(&downgraded).is_err());
    let mut upgraded = legacy_packet.clone();
    upgraded[..32].copy_from_slice(&profile.id());
    assert!(profile.verify(&upgraded).is_err());

    let mut unsupported: VerifierProfile = decode(&portable)?;
    unsupported.version = 6;
    let unsupported =
      bincode::serde::encode_to_vec(&unsupported, bincode::config::standard())?;
    assert!(VerifierProfile::from_bytes(&unsupported).is_err());

    let digest = blake3::hash(&portable).to_hex().to_string();
    let registry = dir.join("registry");
    let file = dir.join("verifier.bin");
    assert!(
      super::super::super::registry::register(
        &file,
        &registry,
        Some(&"00".repeat(32)),
        true,
      )
      .is_err()
    );
    assert!(!registry.exists());
    super::super::super::registry::register(
      &file,
      &registry,
      Some(&digest),
      true,
    )?;
    // Verify using only the portable object after deleting the SRS and all checkpoints.
    fs::remove_dir_all(&dir)?;
    profile.verify(&resident)?;
    legacy.verify(&legacy_packet)?;
    let mut wrong_range: VerifierProfile = decode(&portable)?;
    wrong_range.heights[0] *= 2;
    assert!(wrong_range.system().is_err());
    Ok(())
  }

  #[test]
  fn fused_recursive_traces_preserve_proof_bytes_and_resume_verification()
  -> storage::Result<()> {
    let inner = Srs::unsafe_dev_setup(8, b"fused-recursive-inner");
    let claims = init_packet_claims(&inner);
    let make = |private| -> storage::Result<(Built, Assignment<Scalar>)> {
      let mut builder = CircuitBuilder::new();
      let input = builder.input("private");
      let table = builder.fixed_table(
        "small",
        (0..16).map(|v| vec![Scalar::from_u8(v)]).collect(),
      );
      builder.lookup(table, &[input]);
      for _ in 0..8 {
        builder.mul(input, input);
      }
      for claim in &claims[1..] {
        let wire = builder.constant(claim[3]);
        builder.expose_public(wire);
      }
      let circuit = builder.finish();
      let mut witness = circuit.witness();
      witness.set(input, Scalar::from_u8(private))?;
      let assignment = witness.generate()?;
      Ok((
        Built {
          circuit,
          inputs: vec![],
          points: vec![],
          pairing_outputs: vec![],
          pairing_keys: vec![inner.g2, inner.tau_g2],
          terms: vec![],
        },
        assignment,
      ))
    };
    let root = std::env::temp_dir()
      .join(format!("kzg-recursive-fused-{}", std::process::id()));
    fs::create_dir(&root)?;
    let mut outputs = vec![];
    for (name, fused, private) in
      [("checkpointed", false, 7), ("fused", true, 7), ("fresh", true, 9)]
    {
      let dir = root.join(name);
      fs::create_dir(&dir)?;
      let (built, assignment) = make(private)?;
      stage(built, &assignment, &dir, b"recursive-fixture", fused)?;
      if !fused {
        prove(&dir, false, false)?;
      }
      prove(&dir, true, false)?;
      for name in ["prove-report.json", "verify-report.json"] {
        let report: serde_json::Value =
          serde_json::from_slice(&fs::read(dir.join("kzg").join(name))?)?;
        assert_eq!(report["setup"], "development");
        assert_eq!(report["development_srs"], true);
        assert_eq!(report["native_verification_passed"], true);
        assert!(report["public_max_degree"].is_u64());
        assert_eq!(report["trace_heights"].as_array().unwrap().len(), 2);
      }
      let manifest: storage::Manifest =
        storage::load(&dir.join("manifest.bin"))?;
      assert_eq!(
        fs::read(dir.join("frontend-id.bin"))?,
        blake3::hash(b"recursive-fixture").as_bytes()
      );
      for i in 0..manifest.heights.len() {
        assert_eq!(dir.join(format!("{i}.witness.zst")).exists(), !fused);
        assert_eq!(dir.join(format!("kzg/main-{i}.bin")).exists(), !fused);
        assert!(dir.join(format!("kzg/fixed-{i}.bin")).exists());
      }
      outputs.push(
        ["proof.compact.bin", "packet.bin", "profile-id.bin"]
          .map(|name| fs::read(dir.join("kzg").join(name)).unwrap()),
      );
    }
    assert_eq!(outputs[0], outputs[1]);
    assert_ne!(outputs[1][0], outputs[2][0]);
    assert_eq!(outputs[1][2], outputs[2][2]);
    let resumed = root.join("checkpointed");
    let old_checkpoint = fs::read(resumed.join("kzg/main-0.bin"))?;
    let (built, assignment) = make(9)?;
    let height = built.circuit.multi_stark_layout()?.main_height;
    let compiled = built
      .circuit
      .lower_to_multi_stark_sharded(Scalar::from_u8(94), height)?
      .merge_table_traces(height)?;
    let traces = compiled.trace_shards(&assignment)?;
    prove_with_traces(&resumed, false, true, Some(&traces))?;
    prove(&resumed, true, false)?;
    assert_eq!(fs::read(resumed.join("kzg/proof.compact.bin"))?, outputs[2][0]);
    assert_eq!(fs::read(resumed.join("kzg/main-0.bin"))?, old_checkpoint);
    for name in ["packet.bin", "profile-id.bin"] {
      let path = resumed.join("kzg").join(name);
      let original = fs::read(&path)?;
      let mut altered = original.clone();
      altered[0] ^= 1;
      fs::write(&path, &altered)?;
      let error = prove(&resumed, true, false).unwrap_err();
      assert!(error.to_string().contains("saved packet or profile differs"));
      assert_eq!(fs::read(&path)?, altered);
      fs::write(path, original)?;
    }
    fs::remove_dir_all(root)?;
    Ok(())
  }

  #[test]
  #[ignore = "eight-minute CPU outer proof over an identity-commitment wrapper"]
  fn constant_column_first_stage_proof_wraps_proves_and_verifies()
  -> storage::Result<()> {
    use crate::recursive::native_verifier::Plan;
    use multi_stark::{expr::Expr, lookup::Lookup, system::CircuitInputs};
    use p3_matrix::dense::RowMajorMatrix;
    let words = init_claim::INIT_PUBLIC_WORDS;
    let srs = Arc::new(Srs::unsafe_dev_setup(8, b"constant-column-inner"));
    let (system, key) = System::new(
      KzgConfig::new(srs.clone(), 2),
      [CircuitInputs {
        main_width: 18,
        preprocessed: Some(RowMajorMatrix::new_col(vec![
          Scalar::ONE,
          Scalar::ZERO,
          Scalar::ZERO,
          Scalar::ZERO,
        ])),
        constraints: (0..18)
          .map(|i| Expr::main_next(i) - Expr::main(i))
          .collect(),
        lookups: (0..19)
          .map(|index| {
            Lookup::pull(
              Expr::preprocessed(0),
              vec![
                Expr::constant(Scalar::from_u8(93)),
                Expr::constant(Scalar::ONE),
                Expr::constant(Scalar::from_usize(index)),
                if index == 0 {
                  Expr::constant(Scalar::ZERO)
                } else {
                  Expr::main(u32::try_from(index - 1).unwrap())
                },
              ],
            )
          })
          .collect(),
        ..Default::default()
      }],
    );
    let claims: Vec<_> = std::iter::once(0)
      .chain(words)
      .enumerate()
      .map(|(index, value)| {
        vec![
          Scalar::from_u8(93),
          Scalar::ONE,
          Scalar::from_usize(index),
          Scalar::from_u64(value),
        ]
      })
      .collect();
    // Every main column is constant and the first is zero, so the proof
    // carries an identity commitment and generator multiples the affine
    // wrapper arithmetic must handle without exceptional additions.
    let main = RowMajorMatrix::new(
      words.into_iter().map(Scalar::from_u64).collect::<Vec<_>>().repeat(4),
      18,
    );
    let refs: Vec<_> = claims.iter().map(Vec::as_slice).collect();
    let proof = system.prove_multiple_claims(
      &key,
      &refs,
      SystemWitness::from_stage_1(vec![main], &system),
    );
    system
      .verify_multiple_claims(&refs, &proof)
      .map_err(|e| format!("inner proof: {e:?}"))?;
    assert!(
      proof.commitments.stage_1_trace.0.iter().flatten().any(|p| p.infinity)
    );
    let plan = Plan::new(
      &system,
      &[2],
      super::super::saved::claim_schema(&claims)?,
      super::super::saved::layout(),
    )?;
    let built = plan.build(&proof, &claims)?;
    let (_, assignment) = built.check_and_assign()?;
    let dir = std::env::temp_dir()
      .join(format!("kzg-recursive-constant-{}", std::process::id()));
    fs::create_dir(&dir)?;
    stage(built, &assignment, &dir, &plan.identity(), true)?;
    prove(&dir, true, false)?;
    let packet = fs::read(dir.join("kzg/packet.bin"))?;
    verify_saved(&dir, &packet)?;
    let mut bad = packet.clone();
    bad[32 + 18 * 8 + 1] ^= 1;
    assert!(verify_saved(&dir, &bad).is_err());
    fs::remove_dir_all(dir)?;
    Ok(())
  }
}
