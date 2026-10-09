use crate::native_verifier::Built;
use ix_proof_compression::foreign::KzgCircuitExt;

use ix_proof_compression::kzg::Scalar;
use multi_stark::plonkish::Assignment;
use multi_stark::traits::Field;
use p3_matrix::Matrix;
use std::{fs, path::Path};
#[allow(dead_code)]
#[path = "../support/kzg_storage.rs"]
mod storage;
#[derive(serde::Serialize, serde::Deserialize)]
struct Pairings {
  degree_count: usize,
  keys: Vec<u8>,
}

pub(crate) fn stage(
  built: Built,
  assignment: &Assignment<Scalar>,
  dir: &Path,
) -> storage::Result<()> {
  use ark_serialize::CanonicalSerialize;
  if dir.join("manifest.bin").exists() {
    return Err("already staged".into());
  }
  let start = std::time::Instant::now();
  let mut keys = vec![];
  built.pairing_keys.serialize_compressed(&mut keys)?;
  storage::save(
    &dir.join("pairings.bin"),
    &Pairings { degree_count: built.degree_output_count, keys },
  )?;
  let height = built.circuit.multi_stark_layout()?.main_height;
  eprintln!(
    "Lowering recursive circuit into one {height}-row computation trace"
  );
  let compiled = built
    .circuit
    .lower_to_multi_stark_sharded(Scalar::from_u8(94), height)?
    .merge_table_traces(height)?;
  let claims = compiled.claims(assignment.public_values())?;
  let mut manifest =
    storage::Manifest { widths: vec![], heights: vec![], claims };
  let traces = compiled.trace_shards(assignment)?;
  for i in 0..compiled.num_circuits() {
    eprintln!("Preparing recursive trace {i}/{}", compiled.num_circuits());
    let mut definition =
      compiled.kzg_circuit_input(i, height, 2)?.ok_or("missing circuit")?;
    let fixed =
      definition.preprocessed.take().ok_or("missing preprocessing")?;
    manifest.widths.push(definition.main_width);
    manifest.heights.push(fixed.height());
    storage::save(&dir.join(format!("{i}.meta")), &definition)?;
    storage::write_matrix(&dir.join(format!("{i}.fixed.zst")), &fixed)?;
    drop(fixed);
    let trace = traces.trace(i)?;
    storage::write_matrix(&dir.join(format!("{i}.witness.zst")), &trace)?;
    eprintln!("Staged recursive trace {i}: {:?}", start.elapsed());
  }
  storage::save(&dir.join("manifest.bin"), &manifest)?;
  fs::write(
    dir.join("SECURITY.txt"),
    "Development SRS with known trapdoor; not production-secure. The final verifier must check the 18-word Init claim and both external pairing equations.\n",
  )?;
  eprintln!("Recursive staging complete: {:?}", start.elapsed());
  Ok(())
}

const OUTER_SEED: &[u8] = b"init-kzg-recursive-v1";
use crate::init_claim;

fn pairing_keys(
  dir: &Path,
) -> storage::Result<(usize, Vec<ark_bls12_381::G2Affine>)> {
  use ark_serialize::CanonicalDeserialize;
  let profile: Pairings = storage::load(&dir.join("pairings.bin"))?;
  let mut input = profile.keys.as_slice();
  let keys =
    Vec::<ark_bls12_381::G2Affine>::deserialize_compressed(&mut input)?;
  if !input.is_empty() || keys.len() != profile.degree_count + 2 {
    return Err("invalid pairing profile".into());
  }
  Ok((profile.degree_count, keys))
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
  degree_count: usize,
  keys: &[ark_bls12_381::G2Affine],
) -> storage::Result<()> {
  use ark_ec::pairing::Pairing;
  use ark_ff::Zero;
  use ark_serialize::CanonicalDeserialize;
  if bytes.len() != keys.len() * 48 || keys.len() != degree_count + 2 {
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
  for range in [0..degree_count, degree_count..keys.len()] {
    if !ark_bls12_381::Bls12_381::multi_pairing(
      points[range.clone()].to_vec(),
      keys[range].to_vec(),
    )
    .is_zero()
    {
      return Err("external pairing equation failed".into());
    }
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
  system: &multi_stark::system::System<ix_proof_compression::kzg::KzgConfig>,
  codec: &ix_proof_compression::kzg::compact::FixedProofCodec,
  packet: &[u8],
  profile: &[u8; 32],
  degree_count: usize,
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
  check_pairings(&packet[32 + 18 * 8..offset], degree_count, keys)
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
  use ix_proof_compression::kzg::KzgCommitment;
  use ix_proof_compression::kzg::KzgConfig;
  use ix_proof_compression::kzg::Srs;
  use ix_proof_compression::kzg::compact::FixedProofCodec;
  use ix_proof_compression::kzg::pcs::KzgProverData;
  use multi_stark::config::ProofConfig;
  use multi_stark::lookup::LookupValues;
  use multi_stark::prover::Stage1;
  use multi_stark::system::Circuit;
  use multi_stark::system::CircuitInputs;
  use multi_stark::system::ProverKey;
  use multi_stark::system::System;
  use multi_stark::traits::Algebra;
  use multi_stark::traits::Pcs;
  use std::{
    fs::File,
    io::{BufWriter, Write},
    sync::Arc,
    time::Instant,
  };
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
  let (degree_count, keys) = pairing_keys(dir)?;
  let publics = staged_publics(&manifest.claims, keys.len())?;
  let point_bytes = pairing_bytes(&publics[18..])?;
  check_pairings(&point_bytes, degree_count, &keys)?;
  for (&value, expected) in
    publics[..18].iter().zip(init_claim::INIT_PUBLIC_WORDS)
  {
    if value != Scalar::from_u64(expected) {
      return Err("wrong Init claim".into());
    }
  }
  let out = dir.join("kzg");
  fs::create_dir_all(&out)?;
  fs::write(
    out.join("SECURITY.txt"),
    "Known-trapdoor development SRS. Not production-secure.\n",
  )?;
  eprintln!("Generating development SRS for 2^{} rows", height.ilog2());
  let config = KzgConfig::new(
    Arc::new(Srs::unsafe_dev_setup_cached(
      height,
      OUTER_SEED,
      out.join("dev-srs.bin"),
    )?),
    2,
  )
  .with_streaming_lookups()
  .with_streaming_quotient();
  eprintln!("Outer development SRS ready: {:?}", start.elapsed());
  let checkpoint = |path: &Path, data: &KzgProverData| -> storage::Result<()> {
    let temp = path.with_extension("partial");
    let mut writer = BufWriter::with_capacity(1 << 20, File::create(&temp)?);
    data.write_checkpoint(&mut writer)?;
    writer.flush()?;
    drop(writer);
    fs::rename(temp, path)?;
    Ok(())
  };
  let mut circuits = vec![];
  let mut commits = vec![];
  let mut fixed_parts = vec![];
  let mut main_parts = vec![];
  let load = |path: &Path| -> storage::Result<KzgProverData> {
    Ok(if resident {
      KzgProverData::read_checkpoint(std::io::BufReader::with_capacity(
        1 << 20,
        File::open(path)?,
      ))?
    } else {
      KzgProverData::read_checkpoint_file(path)?
    })
  };
  let retain =
    |path: &Path, data: KzgProverData| -> storage::Result<KzgProverData> {
      if resident {
        return Ok(data);
      }
      checkpoint(path, &data)?;
      drop(data);
      load(path)
    };
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
      let mut definition: CircuitInputs<Scalar> =
        storage::load(&dir.join(format!("{i}.meta")))?;
      definition.preprocessed = Some(storage::read_matrix_bounded(
        &dir.join(format!("{i}.fixed.zst")),
        height,
      )?);
      eprintln!("Committing recursive fixed trace {i}: {:?}", start.elapsed());
      let (mut local, key) =
        System::new_without_preprocessed(config.clone(), [definition]);
      let mut circuit = local.circuits.remove(0);
      circuit.preprocessed = None;
      let data = key.preprocessed_data.unwrap();
      fixed_parts.push(retain(&fixed_path, data)?);
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
      let data = if main_path.exists() {
        load(&main_path)?
      } else {
        let main = storage::read_matrix_bounded(
          &dir.join(format!("{i}.witness.zst")),
          height,
        )?;
        eprintln!("Committing recursive main trace {i}: {:?}", start.elapsed());
        let (_, data) = config.pcs().commit(vec![(
          config.pcs().natural_domain_for_degree(manifest.heights[i]),
          main,
        )]);
        retain(&main_path, data)?
      };
      main_parts.push(data);
    }
    eprintln!("Prepared recursive trace {i}: {:?}", start.elapsed());
  }
  let mut fixed_commit = KzgCommitment(vec![], vec![]);
  for mut commit in commits {
    fixed_commit.0.append(&mut commit.0);
    fixed_commit.1.append(&mut commit.1);
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
  let mut hash = blake3::Hasher::new();
  hash.update(b"init-kzg-recursive-profile/v1");
  hash.update(OUTER_SEED);
  hash.update(&(height as u64).to_le_bytes());
  for i in 0..count {
    hash.update(&fs::read(out.join(format!("setup-{i}.bin")))?);
  }
  hash.update(&fs::read(dir.join("pairings.bin"))?);
  let profile = *hash.finalize().as_bytes();
  let mut packet = profile.to_vec();
  for word in init_claim::INIT_PUBLIC_WORDS {
    packet.extend(word.to_le_bytes());
  }
  packet.extend(point_bytes);
  packet.extend(&bytes);
  if verify_only && fs::read(out.join("packet.bin"))? != packet {
    return Err("saved packet differs".into());
  }
  let verify_start = Instant::now();
  verify_packet(&system, &codec, &packet, &profile, degree_count, &keys)?;
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
    assert!(
      verify_packet(&system, &codec, &wrong, &profile, degree_count, &keys)
        .is_err()
    );
  }
  assert!(
    verify_packet(
      &system,
      &codec,
      &packet[..packet.len() - 1],
      &profile,
      degree_count,
      &keys
    )
    .is_err()
  );
  let mut extra = packet.clone();
  extra.push(0);
  assert!(
    verify_packet(&system, &codec, &extra, &profile, degree_count, &keys)
      .is_err()
  );
  fs::write(out.join("packet.bin"), &packet)?;
  fs::write(out.join("profile-id.bin"), profile)?;
  let report = serde_json::json!({"proof_bytes":bytes.len(),"packet_bytes":packet.len(),"claim_bytes":144,"pairing_bytes":keys.len()*48,"profile_bytes":32,"total_seconds":start.elapsed().as_secs_f64(),"verify_seconds":verify_seconds,"external_pairings_pass":true,"negative_tests_pass":true,"development_srs":true});
  fs::write(
    out.join(if verify_only {
      "verify-report.json"
    } else {
      "prove-report.json"
    }),
    serde_json::to_vec_pretty(&report)?,
  )?;
  println!("{}", serde_json::to_string_pretty(&report)?);
  Ok(())
}

#[cfg(test)]
mod tests {
  use super::*;
  use ark_ec::CurveGroup;
  use ark_serialize::CanonicalSerialize;
  use ix_proof_compression::kzg::KzgConfig;
  use ix_proof_compression::kzg::Srs;
  use ix_proof_compression::kzg::compact::FixedProofCodec;
  use multi_stark::plonkish::CircuitBuilder;
  use multi_stark::system::System;
  use multi_stark::system::SystemWitness;
  use multi_stark::traits::Algebra;
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
      KzgConfig::new(Arc::new(Srs::unsafe_dev_setup(64, b"packet-outer")), 2);
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
        verify_packet(&system, &codec, &packet, &profile, 0, &keys).is_ok(),
        !wrong
      );
      if !wrong {
        let mut changed = packet.clone();
        changed[32 + 8] ^= 1;
        assert!(
          verify_packet(&system, &codec, &changed, &profile, 0, &keys).is_err()
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
            0,
            &keys
          )
          .is_err()
        );
        packet.push(0);
        assert!(
          verify_packet(&system, &codec, &packet, &profile, 0, &keys).is_err()
        );
      }
    }
  }

  #[test]
  fn staged_profiles_prove_in_both_storage_modes() -> storage::Result<()> {
    for degree_count in [0, 2] {
      let dir = std::env::temp_dir()
        .join(format!("outer-staged-{}-{degree_count}", std::process::id()));
      fs::create_dir(&dir)?;
      let inner = Srs::unsafe_dev_setup(8, b"staged-inner");
      let mut keys = vec![inner.g2; degree_count];
      keys.extend([inner.g2, inner.tau_g2]);
      let mut prefix = [17u8; 32].to_vec();
      for word in init_claim::INIT_PUBLIC_WORDS {
        prefix.extend(word.to_le_bytes());
      }
      if degree_count != 0 {
        inner.g1[0].serialize_compressed(&mut prefix)?;
        (-inner.g1[0]).serialize_compressed(&mut prefix)?;
      }
      inner.g1[1].serialize_compressed(&mut prefix)?;
      (-inner.g1[0]).serialize_compressed(&mut prefix)?;
      let (claims, _) = packet_claims(&prefix, &[17u8; 32], keys.len())?;
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
      storage::save(&dir.join("manifest.bin"), &manifest)?;
      let mut encoded = vec![];
      keys.serialize_compressed(&mut encoded)?;
      storage::save(
        &dir.join("pairings.bin"),
        &Pairings { degree_count, keys: encoded },
      )?;
      prove(&dir, false, true)?;
      assert!(!dir.join("kzg/fixed-0.bin").exists());
      assert!(!dir.join("kzg/main-0.bin").exists());
      let resident = fs::read(dir.join("kzg/packet.bin"))?;
      prove(&dir, true, false)?;
      prove(&dir, false, false)?;
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
      fs::remove_dir_all(dir)?;
    }
    Ok(())
  }
}
