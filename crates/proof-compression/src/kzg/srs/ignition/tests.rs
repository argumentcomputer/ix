use super::*;
use ark_bn254::{Fq, Fq2, G2Projective};
use ark_ec::PrimeGroup;
use std::{
  fs,
  path::PathBuf,
  sync::{
    Arc,
    atomic::{AtomicU64, Ordering},
  },
};

use crate::kzg::{KzgPcs, KzgTranscript, Scalar, VerifierParams};
use multi_stark::traits::{EvaluationDomain, Pcs};
use p3_matrix::dense::RowMajorMatrix;

static NEXT_FIXTURE: AtomicU64 = AtomicU64::new(0);
const TOTAL_POINTS: u32 = 12;
const POINTS_PER_TRANSCRIPT: u32 = 5;

fn source_field(value: Fq) -> Vec<u8> {
  value.into_bigint().0.into_iter().flat_map(u64::to_be_bytes).collect()
}

fn source_g1(point: G1Affine) -> Vec<u8> {
  [source_field(point.x), source_field(point.y)].concat()
}

fn source_g2(point: G2Affine) -> Vec<u8> {
  [point.x.c0, point.x.c1, point.y.c0, point.y.c1]
    .into_iter()
    .flat_map(source_field)
    .collect()
}

fn digest_text(bytes: &[u8]) -> String {
  blake2b_simd::blake2b(bytes).to_hex().to_string()
}

fn transcript_path(
  root: &Path,
  contribution: &Contribution,
  index: u32,
) -> PathBuf {
  root
    .join(format!("{:03}_{}", contribution.position, contribution.address))
    .join(format!("transcript{index:02}.dat"))
}

fn shifted_points(tau: Fr, count: usize) -> Vec<G1Affine> {
  (1..=count)
    .map(|exponent| {
      (G1Projective::generator() * tau.pow([exponent as u64])).into_affine()
    })
    .collect()
}

fn write_contribution(
  root: &Path,
  position: u32,
  address: &str,
  tau: Fr,
  update: Fr,
) -> Contribution {
  let mut contribution = Contribution {
    position,
    address: address.to_owned(),
    transcripts: Vec::new(),
  };
  let points = shifted_points(tau, TOTAL_POINTS as usize);
  let count = TOTAL_POINTS.div_ceil(POINTS_PER_TRANSCRIPT);
  for index in 0..count {
    let start = index * POINTS_PER_TRANSCRIPT;
    let length = POINTS_PER_TRANSCRIPT.min(TOTAL_POINTS - start);
    let mut bytes: Vec<u8> = [
      index,
      count,
      TOTAL_POINTS,
      1,
      length,
      if index == 0 { 2 } else { 0 },
      start,
    ]
    .into_iter()
    .flat_map(u32::to_be_bytes)
    .collect();
    for point in &points[start as usize..(start + length) as usize] {
      bytes.extend(source_g1(*point));
    }
    if index == 0 {
      for scalar in [tau, update] {
        bytes.extend(source_g2(
          (G2Projective::generator() * scalar).into_affine(),
        ));
      }
    }
    bytes.extend_from_slice(blake2b_simd::blake2b(&bytes).as_bytes());
    let path = transcript_path(root, &contribution, index);
    fs::create_dir_all(path.parent().unwrap()).unwrap();
    fs::write(path, &bytes).unwrap();
    contribution
      .transcripts
      .push(Transcript { index, blake2b512: digest_text(&bytes) });
  }
  contribution
}

struct Fixture {
  directory: PathBuf,
  root: PathBuf,
  manifest_path: PathBuf,
  cache: PathBuf,
  manifest: SourceManifest,
  pin: [u8; 32],
  points: Vec<G1Affine>,
}

impl Fixture {
  fn new(with_predecessor: bool) -> Self {
    let directory = std::env::temp_dir().join(format!(
      "ix-ignition-import-{}-{}",
      std::process::id(),
      NEXT_FIXTURE.fetch_add(1, Ordering::Relaxed),
    ));
    fs::create_dir(&directory).unwrap();
    let root = directory.join("source");
    let previous_tau = Fr::from(7u64);
    let update = Fr::from(11u64);
    let tau = previous_tau * update;
    let contribution =
      write_contribution(&root, FINAL_POSITION, FINAL_ADDRESS, tau, update);
    let predecessor = with_predecessor.then(|| {
      write_contribution(
        &root,
        PREDECESSOR_POSITION,
        PREDECESSOR_ADDRESS,
        previous_tau,
        previous_tau,
      )
    });
    let manifest = SourceManifest {
      format: SOURCE_FORMAT.to_owned(),
      ceremony: "MAIN IGNITION".to_owned(),
      basis: SHIFTED_TAU_BASIS.to_owned(),
      num_g1_points: TOTAL_POINTS,
      points_per_transcript: POINTS_PER_TRANSCRIPT,
      contribution,
      predecessor,
    };
    let mut fixture = Self {
      manifest_path: directory.join("source.json"),
      cache: directory.join("cache.bin"),
      directory,
      root,
      manifest,
      pin: [0; 32],
      points: shifted_points(tau, TOTAL_POINTS as usize),
    };
    fixture.save_manifest();
    fixture
  }

  fn save_manifest(&mut self) {
    let bytes = serde_json::to_vec_pretty(&self.manifest).unwrap();
    self.pin = *blake3::hash(&bytes).as_bytes();
    fs::write(&self.manifest_path, bytes).unwrap();
  }

  fn mutate_source(
    &mut self,
    predecessor: bool,
    index: u32,
    repair_checksum: bool,
    mutate: impl FnOnce(&mut Vec<u8>),
  ) {
    let contribution = if predecessor {
      self.manifest.predecessor.as_mut().unwrap()
    } else {
      &mut self.manifest.contribution
    };
    let path = transcript_path(&self.root, contribution, index);
    let mut bytes = fs::read(&path).unwrap();
    mutate(&mut bytes);
    if repair_checksum {
      let end = bytes.len() - 64;
      let checksum = blake2b_simd::blake2b(&bytes[..end]);
      bytes[end..].copy_from_slice(checksum.as_bytes());
    }
    fs::write(path, &bytes).unwrap();
    contribution.transcripts[index as usize].blake2b512 = digest_text(&bytes);
    self.save_manifest();
  }

  fn import(&self, prefix_len: usize) -> io::Result<IgnitionCacheIdentity> {
    import_ignition_transcripts(
      &self.root,
      &self.manifest_path,
      self.pin,
      &self.cache,
      prefix_len,
    )
  }

  fn assert_rejected(&self, prefix_len: usize, reason: &str) {
    let error = self.import(prefix_len).unwrap_err();
    assert!(error.to_string().contains(reason), "unexpected error: {error}");
    assert!(!self.cache.exists());
    assert!(fs::read_dir(&self.directory).unwrap().all(|entry| {
      !entry.unwrap().file_name().to_string_lossy().ends_with(".partial")
    }));
  }
}

impl Drop for Fixture {
  fn drop(&mut self) {
    let _ = fs::remove_dir_all(&self.directory);
  }
}

#[test]
fn authenticated_shifted_prefixes_preserve_public_identity_and_degree() {
  let fixture = Fixture::new(true);
  let receipt = fixture.import(8).unwrap();
  assert_eq!(receipt.source_manifest_digest, fixture.pin);
  assert_eq!(receipt.public_setup, fixture.manifest.public_setup().unwrap());
  assert_eq!(receipt.public_setup.max_degree, TOTAL_POINTS as usize - 1);
  for prefix_len in [2, 4, 8] {
    let srs =
      load_ignition_cache(&fixture.cache, receipt.digest, prefix_len).unwrap();
    assert_eq!(srs.g1, fixture.points[..prefix_len]);
    assert_ne!(srs.g1[0], G1Affine::generator());
    assert_eq!(srs.g2, G2Affine::generator());
    assert_eq!(srs.public_setup, receipt.public_setup);
    srs.validate().unwrap();
  }
  let smaller_cache = fixture.directory.join("smaller.bin");
  let smaller = import_ignition_transcripts(
    &fixture.root,
    &fixture.manifest_path,
    fixture.pin,
    &smaller_cache,
    4,
  )
  .unwrap();
  assert_eq!(smaller.public_setup, receipt.public_setup);
  assert_ne!(smaller.digest, receipt.digest);
}

#[test]
fn shifted_import_supports_native_kzg_openings_with_anchor_only_verifier() {
  let fixture = Fixture::new(false);
  let receipt = fixture.import(8).unwrap();
  let srs = load_ignition_cache(&fixture.cache, receipt.digest, 8).unwrap();
  let anchors = load_ignition_cache(&fixture.cache, receipt.digest, 2).unwrap();
  let verifier =
    KzgPcs::verifier_only(VerifierParams::with_max_trace_len(&anchors, 8), 2);
  let pcs = KzgPcs::new(Arc::new(srs), 2);
  let domain = pcs.natural_domain_for_degree(8);
  let matrix = RowMajorMatrix::new(
    (0..domain.size())
      .flat_map(|i| {
        [Scalar(Fr::from(7u64)), Scalar(Fr::from((i * i + 3) as u64))]
      })
      .collect(),
    2,
  );
  let (commitment, data) = pcs.commit(vec![(domain, matrix)]);
  let point = Scalar(Fr::from(19u64));
  let (values, proof) =
    pcs.open(vec![(&data, vec![vec![point]])], &mut KzgTranscript::default());
  let mut rounds =
    vec![(commitment, vec![(domain, vec![(point, values[0][0][0].clone())])])];
  verifier
    .verify(rounds.clone(), &proof, &mut KzgTranscript::default())
    .unwrap();
  rounds[0].1[0].1[0].1[0] += Scalar(Fr::ONE);
  assert!(
    verifier.verify(rounds, &proof, &mut KzgTranscript::default()).is_err()
  );
}

#[test]
fn inventory_hashes_complete_files_and_does_not_change_setup_identity() {
  let fixture = Fixture::new(true);
  let inventory = inspect_ignition_source(
    &fixture.root,
    FINAL_POSITION,
    FINAL_ADDRESS,
    Some((PREDECESSOR_POSITION, PREDECESSOR_ADDRESS)),
  )
  .unwrap();
  assert_eq!(inventory, fixture.manifest);
  let mut without_previous = inventory.clone();
  without_previous.predecessor = None;
  assert_eq!(
    inventory.public_setup().unwrap(),
    without_previous.public_setup().unwrap()
  );
  let first =
    fs::read(transcript_path(&fixture.root, &inventory.contribution, 0))
      .unwrap();
  assert_ne!(
    inventory.contribution.transcripts[0].blake2b512,
    digest_text(&first[..first.len() - 64]),
  );
}

#[test]
fn source_manifest_requires_an_external_exact_byte_pin() {
  let fixture = Fixture::new(false);
  assert!(read_source_manifest(&fixture.manifest_path, [0; 32]).is_err());
  let mut bytes = fs::read(&fixture.manifest_path).unwrap();
  bytes.push(b'\n');
  fs::write(&fixture.manifest_path, bytes).unwrap();
  fixture.assert_rejected(8, "manifest digest mismatch");
}

#[test]
fn source_manifest_rejects_oversize_and_unknown_fields() {
  let fixture = Fixture::new(false);
  let oversized = vec![b' '; (1 << 20) + 1];
  fs::write(&fixture.manifest_path, &oversized).unwrap();
  assert!(
    read_source_manifest(
      &fixture.manifest_path,
      *blake3::hash(&oversized).as_bytes()
    )
    .is_err()
  );
  let mut value = serde_json::to_value(&fixture.manifest).unwrap();
  value["unrecognized"] = serde_json::Value::Bool(true);
  let bytes = serde_json::to_vec(&value).unwrap();
  fs::write(&fixture.manifest_path, &bytes).unwrap();
  assert!(
    read_source_manifest(
      &fixture.manifest_path,
      *blake3::hash(&bytes).as_bytes()
    )
    .is_err()
  );
}

#[test]
fn descriptor_rejects_bad_geometry_paths_and_transcript_order() {
  let fixture = Fixture::new(true);
  let original = fixture.manifest.clone();
  let mutations: [fn(&mut SourceManifest); 8] = [
    |m| m.basis = "unshifted".to_owned(),
    |m| m.num_g1_points = u32::MAX,
    |m| m.points_per_transcript = 0,
    |m| m.contribution.address = "../outside".to_owned(),
    |m| m.contribution.position = u32::MAX,
    |m| m.contribution.transcripts.swap(0, 1),
    |m| m.contribution.transcripts[0].blake2b512 = "ff".to_owned(),
    |m| m.predecessor.as_mut().unwrap().position = m.contribution.position,
  ];
  for mutate in mutations {
    let mut manifest = original.clone();
    mutate(&mut manifest);
    assert!(manifest.validate().is_err());
  }
}

#[test]
fn wrong_source_pin_in_unretained_transcript_never_publishes_cache() {
  let mut fixture = Fixture::new(false);
  fixture.manifest.contribution.transcripts[2].blake2b512 = "00".repeat(64);
  fixture.save_manifest();
  fixture.assert_rejected(8, "source digest mismatch");
}

#[test]
fn embedded_checksum_is_checked_even_with_a_matching_external_file_pin() {
  let mut fixture = Fixture::new(false);
  fixture
    .mutate_source(false, 2, false, |bytes| *bytes.last_mut().unwrap() ^= 1);
  fixture.assert_rejected(8, "internal checksum mismatch");
}

#[test]
fn malformed_header_and_file_lengths_never_publish_cache() {
  let mut fixture = Fixture::new(false);
  fixture.mutate_source(false, 1, true, |bytes| bytes[27] ^= 1);
  fixture.assert_rejected(8, "header mismatch");
  for extra_byte in [false, true] {
    let mut fixture = Fixture::new(false);
    fixture.mutate_source(false, 2, false, |bytes| {
      if extra_byte {
        bytes.push(0);
      } else {
        bytes.pop();
      }
    });
    fixture.assert_rejected(8, "file length mismatch");
  }
}

#[test]
fn wrong_successive_power_with_repaired_hashes_is_rejected() {
  let mut fixture = Fixture::new(false);
  let wrong = source_g1(fixture.points[6]);
  fixture.mutate_source(false, 1, true, |bytes| {
    bytes[28..92].copy_from_slice(&wrong)
  });
  fixture.assert_rejected(8, "not one tau progression");
}

#[test]
fn rescaled_valid_progression_is_not_the_ignition_shifted_basis() {
  let mut fixture = Fixture::new(false);
  let rescaled: Vec<_> = fixture
    .points
    .iter()
    .map(|p| (*p * Fr::from(13u64)).into_affine())
    .collect();
  for index in 0..TOTAL_POINTS.div_ceil(POINTS_PER_TRANSCRIPT) {
    fixture.mutate_source(false, index, true, |bytes| {
      let start = (index * POINTS_PER_TRANSCRIPT) as usize;
      let count =
        (TOTAL_POINTS as usize - start).min(POINTS_PER_TRANSCRIPT as usize);
      for (i, point) in rescaled[start..start + count].iter().enumerate() {
        bytes[28 + i * 64..28 + (i + 1) * 64]
          .copy_from_slice(&source_g1(*point));
      }
    });
  }
  fixture.assert_rejected(8, "does not match its shifted basis");
}

#[test]
fn incorrect_contribution_link_is_rejected() {
  let mut fixture = Fixture::new(true);
  fixture.mutate_source(false, 0, true, |bytes| {
    let start = 28 + POINTS_PER_TRANSCRIPT as usize * 64 + 128;
    let wrong =
      source_g2((G2Projective::generator() * Fr::from(13u64)).into_affine());
    bytes[start..start + 128].copy_from_slice(&wrong);
  });
  fixture.assert_rejected(8, "does not follow its predecessor");
}

#[test]
fn predecessor_prefix_and_unused_files_are_authenticated() {
  let mut fixture = Fixture::new(true);
  let wrong = source_g1(G1Affine::generator());
  fixture.mutate_source(true, 1, true, |bytes| {
    bytes[28..92].copy_from_slice(&wrong)
  });
  fixture.assert_rejected(8, "not one tau progression");
  let mut fixture = Fixture::new(true);
  fixture.manifest.predecessor.as_mut().unwrap().transcripts[2].blake2b512 =
    "00".repeat(64);
  fixture.save_manifest();
  fixture.assert_rejected(8, "source digest mismatch");
}

#[test]
fn invalid_prefixes_are_rejected_before_publication() {
  let fixture = Fixture::new(false);
  for prefix_len in [0, 1, 3, 16, usize::MAX] {
    fixture.assert_rejected(prefix_len, "prefix length");
  }
}

#[test]
fn destination_is_never_overwritten() {
  let fixture = Fixture::new(false);
  fs::write(&fixture.cache, b"existing cache").unwrap();
  assert_eq!(
    fixture.import(8).unwrap_err().kind(),
    io::ErrorKind::AlreadyExists
  );
  assert_eq!(fs::read(&fixture.cache).unwrap(), b"existing cache");
}

#[test]
fn cache_pin_header_and_requested_data_are_authenticated() {
  let fixture = Fixture::new(false);
  let receipt = fixture.import(8).unwrap();
  assert!(load_ignition_cache(&fixture.cache, [0; 32], 8).is_err());
  assert!(load_ignition_cache(&fixture.cache, receipt.digest, 16).is_err());
  let original = fs::read(&fixture.cache).unwrap();
  let payload_offset = original.len() - 8 * 64 - 32 - 32;
  let mut corrupt = original.clone();
  corrupt[payload_offset + 6 * 64] ^= 1;
  fs::write(&fixture.cache, &corrupt).unwrap();
  assert!(load_ignition_cache(&fixture.cache, receipt.digest, 8).is_err());
  assert!(load_ignition_cache(&fixture.cache, receipt.digest, 4).is_err());
  let anchors = load_ignition_cache(&fixture.cache, receipt.digest, 2).unwrap();
  assert_eq!(anchors.g1, fixture.points[..2]);
  for offset in [0, payload_offset - 1, original.len() - 33, original.len() - 1]
  {
    let mut corrupt = original.clone();
    corrupt[offset] ^= 1;
    fs::write(&fixture.cache, &corrupt).unwrap();
    assert!(load_ignition_cache(&fixture.cache, receipt.digest, 2).is_err());
  }
  fs::write(&fixture.cache, &original[..original.len() - 1]).unwrap();
  assert!(load_ignition_cache(&fixture.cache, receipt.digest, 2).is_err());
}

#[test]
fn cache_prefix_loads_skip_unrequested_chunks() {
  let fixture = Fixture::new(false);
  let block_points = 1 << 16;
  let prefix_len = 2 * block_points;
  let setup =
    crate::kzg::PublicSetup { max_degree: prefix_len - 1, id: [29; 32] };
  let anchors = Anchors {
    g1: [G1Affine::generator(); 2],
    tau_g2: G2Affine::generator(),
    contribution_g2: G2Affine::generator(),
  };
  let mut writer =
    cache::CacheWriter::create(&fixture.cache, prefix_len, setup, [31; 32])
      .unwrap();
  let block = vec![G1Affine::generator(); block_points];
  writer.push(&block).unwrap();
  writer.push(&block).unwrap();
  let receipt = writer.finish(&anchors).unwrap();
  let mut bytes = fs::read(&fixture.cache).unwrap();
  let payload_offset = bytes.len() - prefix_len * 64 - 2 * 32 - 32;
  bytes[payload_offset + block_points * 64] ^= 1;
  fs::write(&fixture.cache, bytes).unwrap();
  let loaded = load_ignition_cache(&fixture.cache, receipt.digest, 4).unwrap();
  assert_eq!(loaded.g1, vec![G1Affine::generator(); 4]);
  assert_eq!(loaded.public_setup, setup);
  assert!(
    load_ignition_cache(&fixture.cache, receipt.digest, prefix_len).is_err()
  );
}

#[test]
fn coordinate_decoders_match_canonical_generators_and_reject_aliases() {
  let g1 = G1Affine::generator();
  let g2 = G2Affine::generator();
  let mut source_generator = [0; 64];
  source_generator[7] = 1;
  source_generator[39] = 2;
  assert_eq!(points::decode_source_g1(&source_generator).unwrap(), g1);
  let mut cache_generator = [0; 64];
  cache_generator[0] = 1;
  cache_generator[32] = 2;
  assert_eq!(points::encode_g1(&g1), cache_generator);
  assert_eq!(points::decode_source_g1(&source_g1(g1)).unwrap(), g1);
  assert_eq!(points::decode_source_g2(&source_g2(g2)).unwrap(), g2);
  assert_eq!(points::decode_g1(&points::encode_g1(&g1)).unwrap(), g1);
  assert_eq!(points::decode_g2(&points::encode_g2(&g2)).unwrap(), g2);
  let mut noncanonical = source_g1(g1);
  let modulus: Vec<_> =
    Fq::MODULUS.0.into_iter().flat_map(u64::to_be_bytes).collect();
  noncanonical[..32].copy_from_slice(&modulus);
  assert!(points::decode_source_g1(&noncanonical).is_err());
  assert!(points::decode_source_g1(&[0; 64]).is_err());
  assert!(points::decode_source_g2(&[0; 128]).is_err());
  assert!(points::decode_source_g1(&[0; 63]).is_err());
  assert!(points::decode_source_g2(&[0; 129]).is_err());
  let mut swapped = source_g2(g2);
  for coordinate in swapped.as_chunks_mut::<64>().0 {
    coordinate.rotate_left(32);
  }
  assert!(points::decode_source_g2(&swapped).is_err());
}

#[test]
fn g2_decoder_rejects_on_curve_points_outside_the_prime_order_subgroup() {
  let point = (0..100u64).find_map(|value| {
    let x = Fq2::new(Fq::from(value), Fq::ONE);
    let rhs = x.square() * x + <ark_bn254::g2::Config as ark_ec::short_weierstrass::SWCurveConfig>::COEFF_B;
    let point = G2Affine::new_unchecked(x, rhs.sqrt()?);
    (!point.is_in_correct_subgroup_assuming_on_curve()).then_some(point)
  }).expect("small deterministic G2 point outside the subgroup");
  assert!(point.is_on_curve());
  assert!(points::decode_source_g2(&source_g2(point)).is_err());
}

#[test]
fn progression_checks_include_chunk_boundaries() {
  let tau = Fr::from(7u64);
  let points = shifted_points(tau, 8);
  let anchors = Anchors {
    g1: [points[0], points[1]],
    tau_g2: (G2Projective::generator() * tau).into_affine(),
    contribution_g2: G2Affine::generator(),
  };
  for chunk_size in [1, 2, 3, 8] {
    let mut check = ProgressionCheck::new([17; 32], points.len(), 197);
    check.absorb(&[]).unwrap();
    for chunk in points.chunks(chunk_size) {
      check.absorb(chunk).unwrap();
    }
    check.verify(&anchors).unwrap();
  }
  let mut corrupt = points;
  for point in &mut corrupt[4..] {
    *point = (*point * Fr::from(13u64)).into_affine();
  }
  let mut check = ProgressionCheck::new([17; 32], corrupt.len(), 197);
  for chunk in corrupt.chunks(4) {
    check.absorb(chunk).unwrap();
  }
  assert!(check.verify(&anchors).is_err());
  let mut check = ProgressionCheck::new([17; 32], 8, 197);
  check.absorb(&corrupt[..2]).unwrap();
  assert!(check.verify(&anchors).is_err());
  let mut check = ProgressionCheck::new([17; 32], 2, 197);
  assert!(check.absorb(&corrupt).is_err());
}
