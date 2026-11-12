//! Canonical wire projection and byte transport for the Aiur KZG verifier.
//! Counts and indices are fixed little-endian u32 integers. Scalars use 32
//! canonical little-endian bytes; G1 uses strict arkworks compressed bytes.
//! This encoding changes transport only, never the native Fiat-Shamir bytes.
//!
//! Expected key and policy digests come from trusted compilation/configuration.
//! Supplying bytes through these advice channels does not authenticate them;
//! the Aiur program hashes, parses and verifies their contents.

use super::{
  Bn254,
  kzg::{Proof, VerifyingKey},
};
use crate::kzg::{
  KzgCommitment, Scalar, TranscriptKind, VerifierParams, curve::G1Affine,
};
use aiur::{bytecode::Type, field::FieldBackend, hints::HintChannels};
use ark_ff::{BigInteger, PrimeField};
use ark_serialize::CanonicalSerialize;
use multi_stark::{
  config::ProofConfig,
  expr::{RowOffset, Source},
  graph::Node,
};
use num_bigint::BigUint;
use std::sync::Arc;

pub const KEY_MAGIC: &[u8; 8] = b"IXAUKY01";
pub const PROOF_MAGIC: &[u8; 8] = b"IXAUPF01";
pub const CLAIMS_MAGIC: &[u8; 8] = b"IXAUCL01";
pub const POLICY_MAGIC: &[u8; 8] = b"IXAUKL01";
pub const MAX_BYTES: usize = 64 << 20;
pub const FOLD_DOMAIN: &[u8] = b"ix/aiur/kzg/fold/v1\0";

pub fn digest_words(digest: &[u8; 32]) -> [Scalar; 8] {
  std::array::from_fn(|i| {
    Bn254.from_u64(u64::from(u32::from_le_bytes(
      digest[4 * i..4 * i + 4].try_into().unwrap(),
    )))
  })
}

/// Two canonical compressed points packed into four little-endian u128 words.
pub fn accumulator_words(
  points: &[G1Affine; 2],
) -> Result<[Scalar; 4], String> {
  super::g1::encode_chunks(*points)
}

pub fn decode_accumulator(words: &[Scalar]) -> Result<[G1Affine; 2], String> {
  super::g1::decode_chunks(words)
}

/// Native reference for the source fold's domain-separated challenge. This
/// derives a scalar from public data and does not verify either operand.
pub fn fold_challenge(
  policy: &[u8; 32],
  statement: &[u8; 32],
  stage: u32,
  key: &[u8; 32],
  proof: &[u8; 32],
  previous: &[G1Affine; 2],
  current: &[G1Affine; 2],
) -> Result<Scalar, String> {
  let mut writer = Writer(FOLD_DOMAIN.to_vec());
  writer.0.extend(policy);
  writer.0.extend(statement);
  writer.0.extend(stage.to_le_bytes());
  writer.0.extend(key);
  writer.0.extend(proof);
  for point in previous.iter().chain(current) {
    writer.point(point)?;
  }
  let mut wide = [0u8; 64];
  blake3::Hasher::new().update(&writer.0).finalize_xof().fill(&mut wide);
  let scalar = Scalar(crate::kzg::curve::Fr::from_le_bytes_mod_order(&wide));
  if scalar == Bn254.zero() {
    Err("zero compression fold challenge".into())
  } else {
    Ok(scalar)
  }
}

/// Candidate canonical scalar bytes and subtraction limbs. The source parser
/// checks their ranges, recomposition and final borrow independently.
pub fn register(hints: &mut HintChannels<Scalar>) -> Result<(), String> {
  hints.insert_fixed::<1, 2>(
    "kzg.msm.window4",
    Type::Field,
    Type::Tuple { items: vec![Type::Field; 2] },
    |[value]| {
      use crate::recursive::native_field::{integer, scalar};
      let value = integer(value);
      if value.bits() > 80 {
        return Err("KZG MSM limb exceeds 80 bits".into());
      }
      Ok([scalar(&(&value >> 4usize)), scalar(&(value & BigUint::from(15u8)))])
    },
  )?;
  hints.insert_fixed::<1, 32>(
    "kzg.scalar_bytes",
    Type::Field,
    Type::Tuple { items: vec![Type::Field; 32] },
    |[value]| {
      let bytes = value.0.into_bigint().to_bytes_le();
      Ok(std::array::from_fn(|i| Bn254.from_u64(u64::from(bytes[i]))))
    },
  )?;
  let fields4 = Type::Tuple { items: vec![Type::Field; 4] };
  hints.insert_fixed::<4, 8>(
    "kzg.fr.canonical",
    fields4.clone(),
    Type::Tuple { items: vec![fields4; 2] },
    |input| {
      use crate::recursive::native_field::{integer, scalar};
      let radix = BigUint::from(1u8) << 80usize;
      let mask = &radix - 1u8;
      let maximum =
        BigUint::from_bytes_le(&crate::kzg::curve::Fr::MODULUS.to_bytes_le())
          - 1u8;
      let mut borrow = 0u8;
      let mut output = [Bn254.zero(); 8];
      for i in 0..4 {
        let value = integer(input[i]);
        if value >= radix {
          return Err("Fr canonical advice limb exceeds 80 bits".into());
        }
        let limit = (&maximum >> (80 * i)) & &mask;
        let subtract = value + borrow;
        let difference = if limit >= subtract {
          borrow = 0;
          limit - subtract
        } else {
          borrow = 1;
          &radix + limit - subtract
        };
        output[i] = scalar(&difference);
        output[4 + i] = Bn254.from_u64(u64::from(borrow));
      }
      Ok(output)
    },
  )
}

#[derive(Default)]
struct Writer(Vec<u8>);
impl Writer {
  fn count(&mut self, value: usize) -> Result<(), String> {
    self.0.extend(
      u32::try_from(value)
        .map_err(|error| format!("KZG wire count: {error}"))?
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
      return Err("invalid G1 point in KZG wire data".into());
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
  fn points(&mut self, values: &[G1Affine]) -> Result<(), String> {
    self.count(values.len())?;
    for value in values {
      self.point(value)?;
    }
    Ok(())
  }
  fn commitment(&mut self, value: &KzgCommitment) -> Result<(), String> {
    self.count(value.0.len())?;
    for row in &value.0 {
      self.points(row)?;
    }
    Ok(())
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
      Err("KZG source wire data exceeds 64 MiB".into())
    } else {
      Ok(self.0)
    }
  }
}

fn anchors(parameters: &VerifierParams) -> Result<[u8; 128], String> {
  let mut bytes = vec![];
  parameters
    .g2
    .serialize_compressed(&mut bytes)
    .map_err(|error| error.to_string())?;
  parameters
    .tau_g2
    .serialize_compressed(&mut bytes)
    .map_err(|error| error.to_string())?;
  bytes.try_into().map_err(|_error| "unexpected BN254 G2 encoding size".into())
}

/// Semantic key projection: seed bytes; trace/quotient caps; G1 generator;
/// G2 and tau-G2 anchors; circuits; optional fixed commitment. Each circuit
/// contains the seven native transcript shape fields, quotient degree, graph
/// nodes, zero roots, then lookups (multiplicity node and argument nodes).
/// Preprocessed slots follow the canonical order of circuits with fixed data.
pub fn key_bytes(key: &VerifyingKey) -> Result<Vec<u8>, String> {
  let system = key.system();
  if system.config.transcript_kind() != TranscriptKind::Blake3 {
    return Err("Aiur KZG source verifier requires BLAKE3".into());
  }
  let parameters = system.config.pcs().verifier_params();
  let mut writer = Writer(KEY_MAGIC.to_vec());
  writer.bytes(system.config.transcript_seed())?;
  writer.count(system.config.max_log_degree())?;
  writer.count(system.config.max_quotient_degree())?;
  writer.point(&parameters.g1[0])?;
  writer.0.extend(anchors(parameters)?);
  writer.count(system.circuits.len())?;
  for circuit in &system.circuits {
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
  writer.0.push(u8::from(system.preprocessed_commit.is_some()));
  if let Some(commitment) = &system.preprocessed_commit {
    writer.commitment(commitment)?;
  }
  writer.finish()
}

/// Proof order: activation bytes, log-degree bytes, main/stage2/quotient
/// commitments, accumulators, opening witnesses, then main/stage2/quotient
/// openings and optional fixed openings. Every vector has a u32 length.
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
  writer.points(&proof.opening_proof.0)?;
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
  writer.finish()
}

pub fn claims_bytes(claims: &[Vec<Scalar>]) -> Result<Vec<u8>, String> {
  let mut writer = Writer(CLAIMS_MAGIC.to_vec());
  writer.count(claims.len())?;
  for row in claims {
    writer.scalars(row)?;
  }
  writer.finish()
}

/// Authorized predecessor keys and entry callables for one compression chain.
/// The final verifier must pin this policy's digest. Making the policy data
/// public avoids embedding a verifier's own key digest into its circuit.
pub struct Policy {
  anchors: [u8; 128],
  gl_key: [u8; 32],
  gl_entry: u32,
  bn_key: [u8; 32],
  bn_entry: u32,
}
impl Policy {
  pub fn anchor_bytes(&self) -> &[u8; 128] {
    &self.anchors
  }

  /// Entry IDs are the physical callable IDs in `TracePlan::public_claim`'s
  /// second word, after deduplication; bytecode entry function indices are
  /// not necessarily the public call IDs.
  pub fn new(
    parameters: &VerifierParams,
    gl_key: [u8; 32],
    gl_entry: u32,
    bn_key: [u8; 32],
    bn_entry: u32,
  ) -> Result<Self, String> {
    Ok(Self {
      anchors: anchors(parameters)?,
      gl_key,
      gl_entry,
      bn_key,
      bn_entry,
    })
  }
  pub fn to_bytes(&self) -> Vec<u8> {
    let mut bytes = POLICY_MAGIC.to_vec();
    bytes.extend(self.anchors);
    bytes.extend(self.gl_key);
    bytes.extend(self.gl_entry.to_le_bytes());
    bytes.extend(self.bn_key);
    bytes.extend(self.bn_entry.to_le_bytes());
    bytes
  }
  pub fn digest(&self) -> [u8; 32] {
    *blake3::hash(&self.to_bytes()).as_bytes()
  }
}

/// Immutable candidate byte streams: channel1 key,2 claims,3 proof,4 policy.
/// Expected digests are separate public inputs to the Aiur entrypoint.
pub struct Inputs {
  channels: [Arc<[u8]>; 4],
}
impl Inputs {
  pub fn new(
    key: Vec<u8>,
    claims: Vec<u8>,
    proof: Vec<u8>,
    policy: Vec<u8>,
  ) -> Result<Self, String> {
    if [&key, &claims, &proof, &policy]
      .iter()
      .any(|bytes| bytes.len() > MAX_BYTES)
    {
      return Err("KZG source input exceeds 64 MiB".into());
    }
    Ok(Self {
      channels: [key.into(), claims.into(), proof.into(), policy.into()],
    })
  }
  pub fn register(
    &self,
    hints: &mut HintChannels<Scalar>,
  ) -> Result<(), String> {
    let channels = self.channels.clone();
    hints.insert_fixed::<1, 1>(
      "kzg.io.length",
      Type::Field,
      Type::Field,
      move |[channel]| {
        let channel = usize::try_from(Bn254.try_to_u64(channel)?)
          .map_err(|error| error.to_string())?;
        let bytes = channel
          .checked_sub(1)
          .and_then(|i| channels.get(i))
          .ok_or("unknown KZG byte channel")?;
        Ok([Bn254.from_u64(
          u64::try_from(bytes.len()).map_err(|error| error.to_string())?,
        )])
      },
    )?;
    let channels = self.channels.clone();
    hints.insert_fixed::<2, 1>(
      "kzg.io.read1",
      Type::Tuple { items: vec![Type::Field; 2] },
      Type::Field,
      move |[channel, offset]| {
        let channel = usize::try_from(Bn254.try_to_u64(channel)?)
          .map_err(|error| error.to_string())?;
        let offset = usize::try_from(Bn254.try_to_u64(offset)?)
          .map_err(|error| error.to_string())?;
        let byte = channel
          .checked_sub(1)
          .and_then(|i| channels.get(i))
          .and_then(|bytes| bytes.get(offset))
          .ok_or("KZG byte read out of bounds")?;
        Ok([Bn254.from_u64(u64::from(*byte))])
      },
    )
  }
}
