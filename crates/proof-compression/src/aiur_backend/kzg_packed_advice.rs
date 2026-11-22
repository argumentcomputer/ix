//! Canonical wire projection of packed-SHPLONK multi-stark keys and proofs
//! for the Aiur packed verifier (`KzgPackedVerifier::verify_deferred`).
//!
//! Circuits, scalars, openings and claims use the column projection's
//! encoding ([`super::kzg_advice`]). Packed commitments travel as their exact
//! native bytes ([`packed_shplonk::Commitment::to_bytes`]) inside a
//! length-prefixed blob, so the Aiur transcript absorbs the same bytes as the
//! native one; the Aiur program parses those bytes and checks every matrix
//! shape against the key and the proof's heights. Channels and digests are
//! those of [`super::kzg_advice::Inputs`].

use crate::kzg::{
  Scalar, TranscriptKind,
  curve::G1Affine,
  packed_shplonk::{Commitment, PackedShplonkConfig},
};
use ark_serialize::CanonicalSerialize;
use multi_stark::{
  config::ProofConfig,
  expr::{RowOffset, Source},
  graph::Node,
  system::System,
};

pub const KEY_MAGIC: &[u8; 8] = b"IXAUSK02";
pub const PROOF_MAGIC: &[u8; 8] = b"IXAUSP01";
pub const MAX_BYTES: usize = super::kzg_advice::MAX_BYTES;

pub type Proof = multi_stark::prover::Proof<PackedShplonkConfig>;

#[derive(Default)]
struct Writer(Vec<u8>);

impl Writer {
  fn count(&mut self, value: usize) -> Result<(), String> {
    self.0.extend(
      u32::try_from(value)
        .map_err(|error| format!("packed wire count: {error}"))?
        .to_le_bytes(),
    );
    Ok(())
  }
  fn scalar(&mut self, value: Scalar) -> Result<(), String> {
    value.0.serialize_compressed(&mut self.0).map_err(|error| error.to_string())
  }
  fn point(&mut self, value: &G1Affine) -> Result<(), String> {
    if !value.is_on_curve() || !value.is_in_correct_subgroup_assuming_on_curve()
    {
      return Err("invalid G1 point in packed wire data".into());
    }
    value.serialize_compressed(&mut self.0).map_err(|error| error.to_string())
  }
  fn bytes(&mut self, bytes: &[u8]) -> Result<(), String> {
    self.count(bytes.len())?;
    self.0.extend_from_slice(bytes);
    Ok(())
  }
  fn ids(
    &mut self,
    values: impl ExactSizeIterator<Item = u32>,
  ) -> Result<(), String> {
    self.count(values.len())?;
    for value in values {
      self.0.extend(value.to_le_bytes());
    }
    Ok(())
  }
  fn scalars(&mut self, values: &[Scalar]) -> Result<(), String> {
    self.count(values.len())?;
    for &value in values {
      self.scalar(value)?;
    }
    Ok(())
  }
  fn commitment(&mut self, value: &Commitment) -> Result<(), String> {
    self.bytes(&value.to_bytes()?)
  }
  fn openings(&mut self, values: &[Vec<Vec<Scalar>>]) -> Result<(), String> {
    self.count(values.len())?;
    for matrix in values {
      self.count(matrix.len())?;
      for row in matrix {
        self.scalars(row)?;
      }
    }
    Ok(())
  }
  fn finish(self) -> Result<Vec<u8>, String> {
    if self.0.len() > MAX_BYTES {
      Err("packed wire data exceeds 64 MiB".into())
    } else {
      Ok(self.0)
    }
  }
}

/// [`key_bytes_with_copies`] with one copy of every circuit.
pub fn key_bytes(
  system: &System<PackedShplonkConfig>,
) -> Result<Vec<u8>, String> {
  key_bytes_with_copies(system, &vec![1; system.circuits.len()])
}

/// Seed bytes; trace cap (log) and quotient budget; G1 generator; G2 and
/// tau-G2 anchors; distinct circuits, each as its copy count followed by the
/// column projection's encoding; then the fixed section: tag 0 without fixed
/// matrices, tag 1 and the packed commitment bytes when each circuit with
/// fixed columns commits its own matrix, or tag 2, the commitment bytes and
/// every system circuit's fixed slot plus one (zero without fixed columns)
/// when circuits share committed matrices (`System::new_shared`).
///
/// `copies[i]` consecutive system circuits are copies of one circuit (a
/// sharded function circuit). The caller builds them from one
/// `CircuitInputs`; only the first copy is encoded and the verifier repeats
/// it.
pub fn key_bytes_with_copies(
  system: &System<PackedShplonkConfig>,
  copies: &[usize],
) -> Result<Vec<u8>, String> {
  if copies.contains(&0)
    || copies.iter().sum::<usize>() != system.circuits.len()
  {
    return Err("packed circuit copies do not cover the system".into());
  }
  if system.config.initialise_challenger().0.kind() != TranscriptKind::Blake3 {
    return Err("Aiur packed verifier requires BLAKE3".into());
  }
  let parameters = system.config.pcs().parameters();
  let mut writer = Writer(KEY_MAGIC.to_vec());
  writer.bytes(system.config.transcript_seed())?;
  writer.count(system.config.max_log_degree())?;
  writer.count(system.config.max_quotient_degree())?;
  writer.point(&parameters.g1[0])?;
  let mut anchors = vec![];
  parameters
    .g2
    .serialize_compressed(&mut anchors)
    .map_err(|error| error.to_string())?;
  parameters
    .tau_g2
    .serialize_compressed(&mut anchors)
    .map_err(|error| error.to_string())?;
  if anchors.len() != 128 {
    return Err("unexpected BN254 G2 encoding size".into());
  }
  writer.0.extend(anchors);
  writer.count(copies.len())?;
  let mut first = 0;
  for &count in copies {
    let circuit = &system.circuits[first];
    first += count;
    writer.count(count)?;
    for value in [
      circuit.constraint_count(),
      circuit.max_constraint_degree(),
      circuit.preprocessed_height,
      circuit.preprocessed_width,
      circuit.main_width,
      circuit.stage_2_width,
      circuit.lookup_group_size,
      circuit.quotient_degree(),
    ] {
      writer.count(value)?;
    }
    writer.count(circuit.graph.nodes.len())?;
    for node in &circuit.graph.nodes {
      match *node {
        Node::Const(value) => {
          writer.0.push(0);
          writer.scalar(value)?;
        },
        Node::Var(column) => {
          writer.0.extend([
            1,
            match column.source {
              Source::Preprocessed => 0,
              Source::Main => 1,
              Source::Stage2 => 2,
            },
            u8::from(column.offset == RowOffset::Next),
          ]);
          writer.0.extend(column.index.to_le_bytes());
        },
        Node::Public(index) => {
          writer.0.push(2);
          writer.0.extend(index.to_le_bytes());
        },
        Node::IsFirstRow => writer.0.push(3),
        Node::IsLastRow => writer.0.push(4),
        Node::IsTransition => writer.0.push(5),
        Node::Add(a, b) | Node::Sub(a, b) | Node::Mul(a, b) => {
          writer.0.push(match node {
            Node::Add(..) => 6,
            Node::Sub(..) => 7,
            _ => 8,
          });
          writer.0.extend(a.0.to_le_bytes());
          writer.0.extend(b.0.to_le_bytes());
        },
        Node::Neg(value) => {
          writer.0.push(9);
          writer.0.extend(value.0.to_le_bytes());
        },
      }
    }
    writer.ids(circuit.graph.zeros.iter().map(|id| id.0))?;
    writer.count(circuit.graph.lookups.len())?;
    for lookup in &circuit.graph.lookups {
      writer.0.extend(lookup.multiplicity.0.to_le_bytes());
      writer.ids(lookup.args.iter().map(|id| id.0))?;
    }
  }
  let slots: Vec<usize> = system
    .preprocessed_indices
    .iter()
    .map(|slot| slot.map_or(0, |s| s + 1))
    .collect();
  let committed = slots.iter().copied().max().unwrap_or(0);
  let shared = committed < slots.iter().filter(|&&slot| slot != 0).count();
  match &system.preprocessed_commit {
    None => writer.0.push(0),
    Some(commitment) => {
      writer.0.push(if shared { 2 } else { 1 });
      writer.commitment(commitment)?;
      if shared {
        writer.count(slots.len())?;
        for slot in slots {
          writer.count(slot)?;
        }
      }
    },
  }
  writer.finish()
}

/// Activation bytes, log-degree bytes, main/stage-2/quotient commitment
/// blobs, accumulators, main/stage-2/quotient openings, optional fixed
/// openings, extra pack evaluations, then `[W₁]` and `[W₂]`.
pub fn proof_bytes(proof: &Proof) -> Result<Vec<u8>, String> {
  let mut writer = Writer(PROOF_MAGIC.to_vec());
  writer.count(proof.active.len())?;
  writer.0.extend(proof.active.iter().copied().map(u8::from));
  writer.bytes(&proof.log_degrees)?;
  for commitment in [
    &proof.commitments.stage_1_trace,
    &proof.commitments.stage_2_trace,
    &proof.commitments.quotient_chunks,
  ] {
    writer.commitment(commitment)?;
  }
  writer.scalars(&proof.intermediate_accumulators)?;
  for openings in [
    &proof.stage_1_opened_values,
    &proof.stage_2_opened_values,
    &proof.quotient_opened_values,
  ] {
    writer.openings(openings)?;
  }
  writer.0.push(u8::from(proof.preprocessed_opened_values.is_some()));
  if let Some(openings) = &proof.preprocessed_opened_values {
    writer.openings(openings)?;
  }
  writer.scalars(&proof.opening_proof.extra_values)?;
  writer.point(&proof.opening_proof.opening.w1)?;
  writer.point(&proof.opening_proof.opening.w2)?;
  writer.finish()
}
