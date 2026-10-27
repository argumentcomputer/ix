//! Canonical verifier programs and witnesses for the terminal BLS PLONK circuit.
use super::*;
mod ir;

fn point(point: G1Affine) -> Json {
  if point.is_zero() {
    json!({"x": "0x0", "y": "0x0"})
  } else {
    json!({"x": hex_json(&fq(point.x)), "y": hex_json(&fq(point.y))})
  }
}

fn key(point: &G2Affine) -> String {
  let mut bytes = vec![];
  point.serialize_compressed(&mut bytes).unwrap();
  hex_json(&bytes)
}

pub(in crate::pipeline) fn export(
  verifier: &Path,
  packet: &Path,
  trusted_digest: &str,
  expected: &Statement,
  directory: &Path,
) -> Result<()> {
  let bytes = fs::read(verifier)?;
  if blake3::hash(&bytes).to_hex().as_str() != trusted_digest {
    return Err("trusted verifier digest differs".into());
  }
  let profile = VerifierProfile::from_bytes(&bytes)?;
  profile.check_setup_class(SetupClass::Filecoin)?;
  write_export(
    &profile,
    &fs::read(packet)?,
    expected,
    directory,
    "witness",
    true,
  )
}

pub(super) fn write_export(
  profile: &VerifierProfile,
  packet: &[u8],
  expected: &Statement,
  directory: &Path,
  name: &str,
  valid_pairing: bool,
) -> Result<()> {
  let system = profile.system()?;
  if system.config.transcript_kind() != TranscriptKind::Blake3 {
    return Err("PLONK wrapping requires a BLAKE3 final KZG profile".into());
  }
  profile.check_setup_class(SetupClass::Filecoin)?;
  let (claims, offset) = packet_claims(packet, &profile.id(), 2, expected)?;
  let logs = profile
    .heights
    .iter()
    .map(|h| u8::try_from(h.ilog2()))
    .collect::<std::result::Result<Vec<_>, _>>()?;
  let proof =
    FixedProofCodec::new(&system, &logs)?.decode(&packet[offset..])?;
  let diagnostic = diagnostics(&system, &proof, &claims)?;
  let deferred_bytes = &packet[32 + 18 * 8..offset];
  if check_pairings(deferred_bytes, &profile.keys()?).is_ok() != valid_pairing {
    return Err("unexpected deferred pairing result".into());
  }
  let layout = codegen::OpeningLayout::new(profile, &system)?;
  let program = ir::build(&system, &layout)?;
  let params = system.config.pcs().verifier_params();
  let fixed: Vec<_> = system
    .preprocessed_commit
    .as_ref()
    .unwrap()
    .0
    .iter()
    .flatten()
    .copied()
    .map(point)
    .collect();
  let circuits: Vec<_> = system.circuits.iter().enumerate().map(|(i, c)| {
    json!({
      "logDegree": logs[i],
      "shape": [c.constraint_count(), c.max_constraint_degree(), profile.heights[i],
        c.preprocessed_width, c.main_width, c.stage_2_width, c.lookup_group_size],
    })
  }).collect();
  let matrices: Vec<_> = layout
    .matrices
    .iter()
    .map(|m| {
      json!({
        "width": m.width, "rows": m.rows, "pointOffset": m.point_offset,
        "valueOffset": m.value_offset,
      })
    })
    .collect();
  let exported = json!({
    "format": "ix-bls-plonk-profile-v1",
    "profileId": hex_json(&profile.id()),
    "setupId": hex_json(&params.public_setup.id),
    "publicMaxDegree": params.public_setup.max_degree,
    "prefix": &expected[..10],
    "seed": hex_json(system.config.transcript_seed()),
    "circuits": circuits,
    "matrices": matrices,
    "pointCount": layout.point_count,
    "fieldCount": layout.field_count,
    "witnessOffset": layout.commitment_count,
    "openingCount": layout.factors.len(),
    "fixed": fixed,
    "generator": point(params.g1[0]),
    "outerKeys": [key(&params.g2), key(&params.tau_g2)],
    "deferredKeys": profile.keys()?.iter().map(key).collect::<Vec<_>>(),
    "program": program,
  });
  let mut values = vec![proof.intermediate_accumulators[0]];
  for round in [
    &proof.stage_1_opened_values,
    &proof.stage_2_opened_values,
    &proof.quotient_opened_values,
    proof.preprocessed_opened_values.as_ref().unwrap(),
  ] {
    values.extend(round.iter().flatten().flatten().copied());
  }
  if values.len() != layout.field_count {
    return Err("exported scalar count differs".into());
  }
  let deferred = deferred_bytes
    .as_chunks::<48>()
    .0
    .iter()
    .map(|bytes| G1Affine::deserialize_compressed(bytes.as_slice()).map(point))
    .collect::<std::result::Result<Vec<_>, _>>()?;
  let digest = expected[10..]
    .iter()
    .map(|word| u32::try_from(*word))
    .collect::<std::result::Result<Vec<_>, _>>()?
    .into_iter()
    .flat_map(u32::to_le_bytes)
    .collect::<Vec<_>>();
  let witness = json!({
    "claimDigest": hex_json(&digest),
    "points": proof_points(&proof).into_iter().map(point).collect::<Vec<_>>(),
    "deferred": deferred,
    "values": values.into_iter().map(scalar).collect::<Vec<_>>(),
  });
  fs::create_dir_all(directory)?;
  storage::write_atomic(
    &directory.join("profile.json"),
    &serde_json::to_vec_pretty(&exported)?,
  )?;
  storage::write_atomic(
    &directory.join(format!("{name}.json")),
    &serde_json::to_vec_pretty(&witness)?,
  )?;
  storage::write_atomic(
    &directory.join(format!("{name}-diagnostic.json")),
    &serde_json::to_vec_pretty(&diagnostic)?,
  )?;
  storage::write_atomic(&directory.join(format!("{name}.bin")), packet)?;
  storage::write_atomic(
    &directory.join(format!("{name}-statement.json")),
    &serde_json::to_vec_pretty(expected)?,
  )?;
  Ok(())
}
