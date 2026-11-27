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

use super::{AiurCurve, kzg_advice};
use crate::kzg::{
  CurveScalar, KzgCurve, TranscriptKind,
  curve::{Bn254 as Bn254Curve, G1AffineOf},
  packed_shplonk::{Commitment, PackedShplonkConfig},
};
use ark_serialize::CanonicalSerialize;
use multi_stark::{
  config::ProofConfig,
  expr::{RowOffset, Source},
  graph::Node,
  system::System,
};
use std::marker::PhantomData;

pub const KEY_MAGIC: &[u8; 8] = b"IXAUSK02";
pub const PROOF_MAGIC: &[u8; 8] = b"IXAUSP01";
pub const MAX_BYTES: usize = kzg_advice::MAX_BYTES;

pub type Proof<C = Bn254Curve> =
  multi_stark::prover::Proof<PackedShplonkConfig<C>>;

struct Writer<C: KzgCurve> {
  buf: Vec<u8>,
  _curve: PhantomData<C>,
}

impl<C: KzgCurve> Writer<C> {
  fn new(buf: Vec<u8>) -> Self {
    Self { buf, _curve: PhantomData }
  }
  fn count(&mut self, value: usize) -> Result<(), String> {
    self.buf.extend(
      u32::try_from(value)
        .map_err(|error| format!("packed wire count: {error}"))?
        .to_le_bytes(),
    );
    Ok(())
  }
  fn scalar(&mut self, value: CurveScalar<C>) -> Result<(), String> {
    value
      .0
      .serialize_compressed(&mut self.buf)
      .map_err(|error| error.to_string())
  }
  fn point(&mut self, value: &G1AffineOf<C>) -> Result<(), String> {
    if !value.is_on_curve() || !value.is_in_correct_subgroup_assuming_on_curve()
    {
      return Err("invalid G1 point in packed wire data".into());
    }
    value.serialize_compressed(&mut self.buf).map_err(|error| error.to_string())
  }
  fn bytes(&mut self, bytes: &[u8]) -> Result<(), String> {
    self.count(bytes.len())?;
    self.buf.extend_from_slice(bytes);
    Ok(())
  }
  fn ids(
    &mut self,
    values: impl ExactSizeIterator<Item = u32>,
  ) -> Result<(), String> {
    self.count(values.len())?;
    for value in values {
      self.buf.extend(value.to_le_bytes());
    }
    Ok(())
  }
  fn scalars(&mut self, values: &[CurveScalar<C>]) -> Result<(), String> {
    self.count(values.len())?;
    for &value in values {
      self.scalar(value)?;
    }
    Ok(())
  }
  fn commitment(&mut self, value: &Commitment<C>) -> Result<(), String> {
    self.bytes(&value.to_bytes()?)
  }
  fn openings(
    &mut self,
    values: &[Vec<Vec<CurveScalar<C>>>],
  ) -> Result<(), String> {
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
    if self.buf.len() > MAX_BYTES {
      Err("packed wire data exceeds 64 MiB".into())
    } else {
      Ok(self.buf)
    }
  }
}

/// [`key_bytes_with_copies_for`] with one copy of every circuit.
pub fn key_bytes_for<C: AiurCurve>(
  system: &System<PackedShplonkConfig<C>>,
) -> Result<Vec<u8>, String> {
  key_bytes_with_copies_for::<C>(system, &vec![1; system.circuits.len()])
}

/// [`key_bytes_with_copies`] with one copy of every circuit.
pub fn key_bytes(
  system: &System<PackedShplonkConfig>,
) -> Result<Vec<u8>, String> {
  key_bytes_for::<Bn254Curve>(system)
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
pub fn key_bytes_with_copies_for<C: AiurCurve>(
  system: &System<PackedShplonkConfig<C>>,
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
  let mut writer = Writer::<C>::new(KEY_MAGIC.to_vec());
  writer.bytes(system.config.transcript_seed())?;
  writer.count(system.config.max_log_degree())?;
  writer.count(system.config.max_quotient_degree())?;
  writer.point(&parameters.g1[0])?;
  writer.buf.extend(kzg_advice::anchors_for::<C>(parameters)?);
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
          writer.buf.push(0);
          writer.scalar(value)?;
        },
        Node::Var(column) => {
          writer.buf.extend([
            1,
            match column.source {
              Source::Preprocessed => 0,
              Source::Main => 1,
              Source::Stage2 => 2,
            },
            u8::from(column.offset == RowOffset::Next),
          ]);
          writer.buf.extend(column.index.to_le_bytes());
        },
        Node::Public(index) => {
          writer.buf.push(2);
          writer.buf.extend(index.to_le_bytes());
        },
        Node::IsFirstRow => writer.buf.push(3),
        Node::IsLastRow => writer.buf.push(4),
        Node::IsTransition => writer.buf.push(5),
        Node::Add(a, b) | Node::Sub(a, b) | Node::Mul(a, b) => {
          writer.buf.push(match node {
            Node::Add(..) => 6,
            Node::Sub(..) => 7,
            _ => 8,
          });
          writer.buf.extend(a.0.to_le_bytes());
          writer.buf.extend(b.0.to_le_bytes());
        },
        Node::Neg(value) => {
          writer.buf.push(9);
          writer.buf.extend(value.0.to_le_bytes());
        },
      }
    }
    writer.ids(circuit.graph.zeros.iter().map(|id| id.0))?;
    writer.count(circuit.graph.lookups.len())?;
    for lookup in &circuit.graph.lookups {
      writer.buf.extend(lookup.multiplicity.0.to_le_bytes());
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
    None => writer.buf.push(0),
    Some(commitment) => {
      writer.buf.push(if shared { 2 } else { 1 });
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

pub fn key_bytes_with_copies(
  system: &System<PackedShplonkConfig>,
  copies: &[usize],
) -> Result<Vec<u8>, String> {
  key_bytes_with_copies_for::<Bn254Curve>(system, copies)
}

/// Activation bytes, log-degree bytes, main/stage-2/quotient commitment
/// blobs, accumulators, main/stage-2/quotient openings, optional fixed
/// openings, extra pack evaluations, then `[W₁]` and `[W₂]`.
pub fn proof_bytes_for<C: AiurCurve>(
  proof: &Proof<C>,
) -> Result<Vec<u8>, String> {
  let mut writer = Writer::<C>::new(PROOF_MAGIC.to_vec());
  writer.count(proof.active.len())?;
  writer.buf.extend(proof.active.iter().copied().map(u8::from));
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
  writer.buf.push(u8::from(proof.preprocessed_opened_values.is_some()));
  if let Some(openings) = &proof.preprocessed_opened_values {
    writer.openings(openings)?;
  }
  writer.scalars(&proof.opening_proof.extra_values)?;
  writer.point(&proof.opening_proof.opening.w1)?;
  writer.point(&proof.opening_proof.opening.w2)?;
  writer.finish()
}

pub fn proof_bytes(proof: &Proof) -> Result<Vec<u8>, String> {
  proof_bytes_for::<Bn254Curve>(proof)
}
