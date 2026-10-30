//! Canonical verifier programs and witnesses for final circuits.
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
  vk.check_setup_class(setup.class())?;
  vk.verify(&fs::read(packet)?, expected)?;
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

/// The recursive verifier system of `vk` and its partitions' log heights.
fn verifier_system(vk: &VerifyingKey) -> Result<(System<KzgConfig>, Vec<u8>)> {
  let system = vk.system()?;
  if system.config.transcript_kind() != TranscriptKind::Blake3 {
    return Err(
      "PLONK wrapping requires a BLAKE3 final KZG verifying key".into(),
    );
  }
  let logs = vk
    .heights
    .iter()
    .map(|h| u8::try_from(h.ilog2()))
    .collect::<std::result::Result<Vec<_>, _>>()?;
  Ok((system, logs))
}

/// The claim slots of the recursive statement and the source of each public.
/// The zero-anchor row precedes the public prefix, claim digest and deferred
/// pairing operands.
fn recursive_statement() -> (Vec<Vec<ir::ClaimSlot>>, Vec<PublicSource>) {
  let slots = (0..=RECURSIVE_PUBLIC_VALUES)
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
  (slots, publics)
}

/// The verifier description (`vk.json`) final circuits are compiled from:
/// it depends on the recursive key `vk` and the statement prefix `prefix`
/// its claims carry, never on a proof.
pub(in crate::pipeline) fn describe(
  vk: &VerifyingKey,
  prefix: &[u64],
) -> Result<Vec<u8>> {
  let (system, logs) = verifier_system(vk)?;
  let (slots, publics) = recursive_statement();
  let (description, _layout) = description(
    &system,
    &logs,
    &slots,
    &publics,
    vk.id(),
    &vk.keys()?,
    prefix,
  )?;
  Ok(serde_json::to_vec_pretty(&description)?)
}

pub(super) fn write_export(
  vk: &VerifyingKey,
  packet: &[u8],
  expected: &Statement,
  directory: &Path,
  name: &str,
  valid_pairing: bool,
) -> Result<()> {
  let (system, logs) = verifier_system(vk)?;
  let (claims, offset) = packet_claims(packet, &vk.id(), 2, expected)?;
  let proof =
    FixedProofCodec::new(&system, &logs)?.decode(&packet[offset..])?;
  let diagnostic = diagnostics(&system, &proof, &claims)?;
  let deferred_bytes = &packet[32 + 18 * 8..offset];
  if check_pairings(deferred_bytes, &vk.keys()?).is_ok() != valid_pairing {
    return Err("unexpected deferred pairing result".into());
  }
  if claims.len() != RECURSIVE_PUBLIC_VALUES + 1 {
    return Err("recursive packet claim count".into());
  }
  let (slots, publics) = recursive_statement();
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
  let (exported, layout) = description(
    system,
    logs,
    &export.slots,
    &export.publics,
    export.vk_id,
    &export.deferred_keys,
    &expected[..10],
  )?;
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

/// The verifier description of `system` and the opening layout it follows.
fn description(
  system: &System<KzgConfig>,
  logs: &[u8],
  slots: &[Vec<ir::ClaimSlot>],
  publics: &[PublicSource],
  vk_id: [u8; 32],
  deferred_keys: &[G2Affine],
  prefix: &[u64],
) -> Result<(Json, codegen::OpeningLayout)> {
  let layout = codegen::OpeningLayout::new_for_system(system, logs)?;
  let program = ir::build(system, &layout, slots)?;
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
    "vkId": hex_json(&vk_id),
    "setupId": hex_json(&params.public_setup.id),
    "publicMaxDegree": params.public_setup.max_degree,
    "prefix": prefix,
    "seed": hex_json(system.config.transcript_seed()),
    "circuits": circuits,
    "matrices": matrices,
    "pointCount": layout.point_count,
    "fieldCount": layout.field_count,
    "witnessOffset": layout.commitment_count,
    "openingCount": layout.factors.len(),
    "accumulatorCount": layout.accumulator_count,
    "claims": slots.iter().map(|row| row.iter().copied().map(slot_json).collect::<Vec<_>>()).collect::<Vec<_>>(),
    "publics": publics.iter().copied().map(PublicSource::json).collect::<Vec<_>>(),
    "fixed": fixed,
    "generator": point(params.g1[0]),
    "outerKeys": [key(&params.g2), key(&params.tau_g2)],
    "deferredKeys": deferred_keys.iter().map(key).collect::<Vec<_>>(),
    "program": program,
  });
  Ok((exported, layout))
}
