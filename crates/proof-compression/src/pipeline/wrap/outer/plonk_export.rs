//! Canonical verifier programs and witnesses for terminal circuits.
use super::relation::{codegen, *};
use super::*;
use crate::kzg::curve::G1Affine;
use ark_ec::AffineRepr;
use ark_ff::{BigInteger, PrimeField};
use ark_serialize::CanonicalDeserialize;
use multi_stark::{
  config::ProofConfig,
  prover::Proof,
  system::System,
  traits::{Algebra, Pcs},
};
use serde_json::{Value as Json, json};
type Result<T> = std::result::Result<T, Box<dyn std::error::Error>>;
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
  for value in [point.x.c0, point.x.c1, point.y.c0, point.y.c1] {
    bytes.extend(value.into_bigint().to_bytes_be());
  }
  hex_json(&bytes)
}

pub(in crate::pipeline) fn export(
  verifier: &Path,
  packet: &Path,
  trusted_digest: &str,
  expected: &Statement,
  directory: &Path,
  setup: &super::super::super::setup::SetupConfig,
) -> Result<()> {
  let bytes = fs::read(verifier)?;
  if blake3::hash(&bytes).to_hex().as_str() != trusted_digest {
    return Err("trusted verifier digest differs".into());
  }
  let vk = VerifyingKey::from_bytes(&bytes)?;
  let admission = setup
    .ignition_admission()
    .ok_or("terminal export requires admitted Ignition parameters")?;
  vk.check_ignition_admission(admission)?;
  write_export(&vk, &fs::read(packet)?, expected, directory, "witness", true)
}

/// How the verifier supplies each public scalar referenced by the claim rows.
#[derive(Clone, Copy)]
enum PublicSource {
  Constant(Scalar),
  Prefix(usize),
  DigestWord(usize),
  DeferredHalf(usize),
}

impl PublicSource {
  fn json(self) -> Json {
    match self {
      Self::Constant(value) => json!({"constant": scalar(value)}),
      Self::Prefix(index) => json!({"prefix": index}),
      Self::DigestWord(index) => json!({"digestWord": index}),
      Self::DeferredHalf(index) => json!({"deferredHalf": index}),
    }
  }
}

fn slot_json(slot: ir::ClaimSlot) -> Json {
  match slot {
    ir::ClaimSlot::Constant(value) => json!({"constant": scalar(value)}),
    ir::ClaimSlot::Public(index) => json!({"public": index}),
  }
}

struct Export<'a> {
  system: &'a System<KzgConfig>,
  proof: &'a Proof<KzgConfig>,
  logs: &'a [u8],
  slots: Vec<Vec<ir::ClaimSlot>>,
  publics: Vec<PublicSource>,
  vk_id: [u8; 32],
  deferred_keys: Vec<G2Affine>,
  deferred_bytes: &'a [u8],
  packet: &'a [u8],
  diagnostic: Json,
}

pub(super) fn write_export(
  vk: &VerifyingKey,
  packet: &[u8],
  expected: &Statement,
  directory: &Path,
  name: &str,
  valid_pairing: bool,
) -> Result<()> {
  let system = vk.system()?;
  if system.config.transcript_kind() != TranscriptKind::Blake3 {
    return Err(
      "PLONK wrapping requires a BLAKE3 final KZG verifying key".into(),
    );
  }
  let (claims, offset) = packet_claims(packet, &vk.id(), 2, expected)?;
  let logs = vk
    .heights
    .iter()
    .map(|h| u8::try_from(h.ilog2()))
    .collect::<std::result::Result<Vec<_>, _>>()?;
  let proof =
    FixedProofCodec::new(&system, &logs)?.decode(&packet[offset..])?;
  let diagnostic = diagnostics(&system, &proof, &claims)?;
  let deferred_bytes = &packet[32 + 18 * 8..offset];
  if check_pairings(deferred_bytes, &vk.keys()?).is_ok() != valid_pairing {
    return Err("unexpected deferred pairing result".into());
  }
  // The zero-anchor row precedes the public prefix, claim digest and
  // deferred pairing operands in the recursive statement.
  let claim_count = RECURSIVE_PUBLIC_VALUES + 1;
  if claims.len() != claim_count {
    return Err("recursive packet claim count".into());
  }
  let slots = (0..claim_count)
    .map(|i| {
      vec![
        ir::ClaimSlot::Constant(Scalar::from_u8(94)),
        ir::ClaimSlot::Constant(Scalar::ONE),
        ir::ClaimSlot::Constant(Scalar::from_usize(i)),
        ir::ClaimSlot::Public(i),
      ]
    })
    .collect();
  let publics = std::iter::once(PublicSource::Constant(Scalar::ZERO))
    .chain((0..10).map(PublicSource::Prefix))
    .chain((0..8).map(PublicSource::DigestWord))
    .chain((0..PUBLIC_VALUES).map(PublicSource::DeferredHalf))
    .collect();
  write_vk(
    &Export {
      system: &system,
      proof: &proof,
      logs: &logs,
      slots,
      publics,
      vk_id: vk.id(),
      deferred_keys: vk.keys()?,
      deferred_bytes,
      packet,
      diagnostic,
    },
    expected,
    directory,
    name,
  )
}

fn write_vk(
  export: &Export<'_>,
  expected: &Statement,
  directory: &Path,
  name: &str,
) -> Result<()> {
  let Export { system, proof, logs, .. } = export;
  let diagnostic = {
    let mut diagnostic = export.diagnostic.clone();
    let encodings = proof_points(proof)
      .into_iter()
      .map(|point| {
        let mut bytes = Vec::new();
        ark_serialize::CanonicalSerialize::serialize_compressed(
          &point, &mut bytes,
        )
        .expect("Vec serialization");
        hex_json(&bytes)
      })
      .collect::<Vec<_>>();
    diagnostic["pointEncodings"] = json!(encodings);
    diagnostic
  };
  let layout = codegen::OpeningLayout::new_for_system(system, logs)?;
  let program = ir::build(system, &layout, &export.slots)?;
  let params = system.config.pcs().verifier_params();
  let fixed: Vec<_> = system
    .preprocessed_commit
    .as_ref()
    .ok_or("missing fixed commitment")?
    .0
    .iter()
    .flatten()
    .copied()
    .map(point)
    .collect();
  if fixed.len() != layout.fixed_count {
    return Err("fixed commitment count differs from layout".into());
  }
  let circuits: Vec<_> = system.circuits.iter().enumerate().map(|(i, c)| {
    json!({
      "logDegree": logs[i],
      "shape": [c.constraint_count(), c.max_constraint_degree(), 1usize << logs[i],
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
    "format": "ix-bn254-plonk-vk-v1",
    "vkId": hex_json(&export.vk_id),
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
    "accumulatorCount": layout.accumulator_count,
    "claims": export.slots.iter().map(|row| row.iter().copied().map(slot_json).collect::<Vec<_>>()).collect::<Vec<_>>(),
    "publics": export.publics.iter().copied().map(PublicSource::json).collect::<Vec<_>>(),
    "fixed": fixed,
    "generator": point(params.g1[0]),
    "outerKeys": [key(&params.g2), key(&params.tau_g2)],
    "deferredKeys": export.deferred_keys.iter().map(key).collect::<Vec<_>>(),
    "program": program,
  });
  let mut values: Vec<Scalar> =
    proof.intermediate_accumulators[..layout.accumulator_count].to_vec();
  for round in [
    &proof.stage_1_opened_values,
    &proof.stage_2_opened_values,
    &proof.quotient_opened_values,
    proof
      .preprocessed_opened_values
      .as_ref()
      .ok_or("missing fixed openings")?,
  ] {
    values.extend(round.iter().flatten().flatten().copied());
  }
  if values.len() != layout.field_count {
    return Err("exported scalar count differs".into());
  }
  let deferred = export
    .deferred_bytes
    .as_chunks::<{ G1_COMPRESSED_BYTES }>()
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
    "points": proof_points(proof).into_iter().map(point).collect::<Vec<_>>(),
    "deferred": deferred,
    "values": values.into_iter().map(scalar).collect::<Vec<_>>(),
  });
  fs::create_dir_all(directory)?;
  storage::write_atomic(
    &directory.join("vk.json"),
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
  storage::write_atomic(&directory.join(format!("{name}.bin")), export.packet)?;
  storage::write_atomic(
    &directory.join(format!("{name}-statement.json")),
    &serde_json::to_vec_pretty(expected)?,
  )?;
  Ok(())
}
