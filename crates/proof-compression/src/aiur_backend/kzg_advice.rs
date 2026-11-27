//! Canonical wire projection and byte transport for the Aiur KZG verifier.
//! Counts and indices are fixed little-endian u32 integers. Scalars use 32
//! canonical little-endian bytes; G1 uses strict arkworks compressed bytes.
//! This encoding changes transport only, never the native Fiat-Shamir bytes.
//!
//! Expected key and policy digests come from trusted compilation/configuration.
//! Supplying bytes through these advice channels does not authenticate them;
//! the Aiur program hashes, parses and verifies their contents.

use super::{
  AiurCurve,
  kzg::{Proof, VerifyingKey},
};
use crate::kzg::{
  CurveScalar, KzgCommitment, KzgCurve, KzgTranscript, Scalar, TranscriptKind,
  VerifierParams,
  curve::{Bn254 as Bn254Curve, G1Affine, G1AffineOf},
};
use aiur::{bytecode::Type, field::FieldBackend, hints::HintChannels};
use ark_ec::AffineRepr;
use ark_ff::{BigInteger, PrimeField};
use ark_serialize::CanonicalSerialize;
use multi_stark::{
  config::ProofConfig,
  expr::{RowOffset, Source},
  graph::Node,
};
use num_bigint::BigUint;
use std::{marker::PhantomData, sync::Arc};

pub const KEY_MAGIC: &[u8; 8] = b"IXAUKY01";
pub const PROOF_MAGIC: &[u8; 8] = b"IXAUPF01";
pub const CLAIMS_MAGIC: &[u8; 8] = b"IXAUCL01";
pub const POLICY_MAGIC: &[u8; 8] = b"IXAUKL01";
pub const MAX_BYTES: usize = 64 << 20;
pub const FOLD_DOMAIN: &[u8] = b"ix/aiur/kzg/fold/v1\0";
pub const TRANSCRIPT_FOLD_DOMAIN: &[u8] = b"ix/aiur/kzg/fold-transcript/v1\0";

pub fn digest_words_for<C: AiurCurve>(
  digest: &[u8; 32],
) -> [CurveScalar<C>; 8] {
  std::array::from_fn(|i| {
    C::FIELD.from_u64(u64::from(u32::from_le_bytes(
      digest[4 * i..4 * i + 4].try_into().unwrap(),
    )))
  })
}

pub fn digest_words(digest: &[u8; 32]) -> [Scalar; 8] {
  digest_words_for::<Bn254Curve>(digest)
}

/// Two canonical compressed points packed into `C::ACCUMULATOR_CHUNKS`
/// little-endian u128 words (`4` for BN254, `6` for BLS12-381).
pub fn accumulator_words_for<C: AiurCurve>(
  points: &[G1AffineOf<C>; 2],
) -> Result<Vec<CurveScalar<C>>, String> {
  super::g1::encode_chunks_for::<C>(*points)
}

/// Two canonical compressed BN254 points packed into four little-endian u128 words.
pub fn accumulator_words(
  points: &[G1Affine; 2],
) -> Result<[Scalar; 4], String> {
  super::g1::encode_chunks(*points)
}

pub fn decode_accumulator_for<C: AiurCurve>(
  words: &[CurveScalar<C>],
) -> Result<[G1AffineOf<C>; 2], String> {
  super::g1::decode_chunks_for::<C>(words)
}

pub fn decode_accumulator(words: &[Scalar]) -> Result<[G1Affine; 2], String> {
  super::g1::decode_chunks(words)
}

/// Native reference for the source fold's domain-separated challenge. This
/// derives a scalar from public data and does not verify either operand.
pub fn fold_challenge_for<C: AiurCurve>(
  policy: &[u8; 32],
  statement: &[u8; 32],
  stage: u32,
  key: &[u8; 32],
  proof: &[u8; 32],
  previous: &[G1AffineOf<C>; 2],
  current: &[G1AffineOf<C>; 2],
) -> Result<CurveScalar<C>, String> {
  let mut writer = Writer::<C>::new(FOLD_DOMAIN.to_vec());
  writer.bytes_raw(policy);
  writer.bytes_raw(statement);
  writer.bytes_raw(&stage.to_le_bytes());
  writer.bytes_raw(key);
  writer.bytes_raw(proof);
  for point in previous.iter().chain(current) {
    writer.point(point)?;
  }
  let mut wide = [0u8; 64];
  blake3::Hasher::new().update(&writer.buf).finalize_xof().fill(&mut wide);
  let scalar = CurveScalar::<C>::new(C::Fr::from_le_bytes_mod_order(&wide));
  if scalar == C::FIELD.zero() {
    Err("zero compression fold challenge".into())
  } else {
    Ok(scalar)
  }
}

/// Native reference for the BN254 source fold's domain-separated challenge.
pub fn fold_challenge(
  policy: &[u8; 32],
  statement: &[u8; 32],
  stage: u32,
  key: &[u8; 32],
  proof: &[u8; 32],
  previous: &[G1Affine; 2],
  current: &[G1Affine; 2],
) -> Result<Scalar, String> {
  fold_challenge_for::<Bn254Curve>(
    policy, statement, stage, key, proof, previous, current,
  )
}

/// Native reference for `CompressBNPacked::fold`'s weight. `transcript` must
/// be the predecessor verifier's final transcript (after `[W₂]`); the weight is
/// its next challenge after the domain tag, policy, statement, little-endian
/// stage, predecessor key digest and the four points. Deriving it does not
/// verify either operand.
pub fn transcript_fold_challenge_for<C: AiurCurve>(
  transcript: &KzgTranscript<C>,
  policy: &[u8; 32],
  statement: &[u8; 32],
  stage: u32,
  key: &[u8; 32],
  previous: &[G1AffineOf<C>; 2],
  current: &[G1AffineOf<C>; 2],
) -> Result<CurveScalar<C>, String> {
  use multi_stark::traits::Transcript;
  let mut writer = Writer::<C>::new(TRANSCRIPT_FOLD_DOMAIN.to_vec());
  writer.bytes_raw(policy);
  writer.bytes_raw(statement);
  writer.bytes_raw(&stage.to_le_bytes());
  writer.bytes_raw(key);
  for point in previous.iter().chain(current) {
    writer.point(point)?;
  }
  let mut transcript = transcript.clone();
  transcript.observe_bytes(&writer.buf);
  let scalar = transcript.sample_challenge();
  if scalar == C::FIELD.zero() {
    Err("zero compression fold challenge".into())
  } else {
    Ok(scalar)
  }
}

pub fn transcript_fold_challenge(
  transcript: &KzgTranscript,
  policy: &[u8; 32],
  statement: &[u8; 32],
  stage: u32,
  key: &[u8; 32],
  previous: &[G1Affine; 2],
  current: &[G1Affine; 2],
) -> Result<Scalar, String> {
  transcript_fold_challenge_for::<Bn254Curve>(
    transcript, policy, statement, stage, key, previous, current,
  )
}

/// Candidate canonical scalar bytes and subtraction limbs for curve `C`.
/// The source parser checks their ranges, recomposition and final borrow
/// independently.
pub fn register_for<C: AiurCurve>(
  hints: &mut HintChannels<CurveScalar<C>>,
) -> Result<(), String> {
  hints.insert_fixed::<1, 2>(
    "kzg.msm.window4",
    Type::Field,
    Type::Tuple { items: vec![Type::Field; 2] },
    |[value]| {
      use crate::recursive::native_field::{integer, scalar};
      let value = integer::<C>(value);
      if value.bits() > 80 {
        return Err("KZG MSM limb exceeds 80 bits".into());
      }
      Ok([
        scalar::<C>(&(&value >> 4usize)),
        scalar::<C>(&(value & BigUint::from(15u8))),
      ])
    },
  )?;
  hints.insert_fixed::<1, 32>(
    "kzg.scalar_bytes",
    Type::Field,
    Type::Tuple { items: vec![Type::Field; 32] },
    |[value]| {
      let bytes = value.0.into_bigint().to_bytes_le();
      Ok(std::array::from_fn(|i| C::FIELD.from_u64(u64::from(bytes[i]))))
    },
  )?;
  hints.insert_fixed::<2, 1>(
    "kzg.io.div",
    Type::Tuple { items: vec![Type::Field; 2] },
    Type::Field,
    |[value, divisor]| {
      let value = C::FIELD.try_to_u64(value)?;
      let divisor = C::FIELD.try_to_u64(divisor)?;
      if divisor == 0 {
        return Err("KZG division by zero".into());
      }
      Ok([C::FIELD.from_u64(value / divisor)])
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
      let maximum = BigUint::from_bytes_le(&C::Fr::MODULUS.to_bytes_le()) - 1u8;
      let mut borrow = 0u8;
      let mut output = [C::FIELD.zero(); 8];
      for i in 0..4 {
        let value = integer::<C>(input[i]);
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
        output[i] = scalar::<C>(&difference);
        output[4 + i] = C::FIELD.from_u64(u64::from(borrow));
      }
      Ok(output)
    },
  )
}

/// Candidate canonical scalar bytes and subtraction limbs for BN254.
pub fn register(hints: &mut HintChannels<Scalar>) -> Result<(), String> {
  register_for::<Bn254Curve>(hints)
}

struct Writer<C: KzgCurve> {
  buf: Vec<u8>,
  _curve: PhantomData<C>,
}

impl<C: KzgCurve> Writer<C> {
  fn new(buf: Vec<u8>) -> Self {
    Self { buf, _curve: PhantomData }
  }
  fn bytes_raw(&mut self, raw: &[u8]) {
    self.buf.extend_from_slice(raw);
  }
  fn count(&mut self, value: usize) -> Result<(), String> {
    self.buf.extend(
      u32::try_from(value)
        .map_err(|error| format!("KZG wire count: {error}"))?
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
      return Err("invalid G1 point in KZG wire data".into());
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
  fn points(&mut self, values: &[G1AffineOf<C>]) -> Result<(), String> {
    self.count(values.len())?;
    for value in values {
      self.point(value)?;
    }
    Ok(())
  }
  fn commitment(&mut self, value: &KzgCommitment<C>) -> Result<(), String> {
    self.count(value.0.len())?;
    for row in &value.0 {
      self.points(row)?;
    }
    Ok(())
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
      Err("KZG source wire data exceeds 64 MiB".into())
    } else {
      Ok(self.buf)
    }
  }
}

pub(crate) fn anchors_for<C: AiurCurve>(
  parameters: &VerifierParams<C>,
) -> Result<Vec<u8>, String> {
  if parameters.g2.is_zero()
    || !parameters.g2.is_on_curve()
    || !parameters.g2.is_in_correct_subgroup_assuming_on_curve()
    || parameters.tau_g2.is_zero()
    || !parameters.tau_g2.is_on_curve()
    || !parameters.tau_g2.is_in_correct_subgroup_assuming_on_curve()
  {
    return Err(format!("invalid {} G2 anchor point", C::NAME));
  }
  let mut bytes = Vec::with_capacity(C::G2_PAIR_COMPRESSED_BYTES);
  parameters
    .g2
    .serialize_compressed(&mut bytes)
    .map_err(|error| error.to_string())?;
  parameters
    .tau_g2
    .serialize_compressed(&mut bytes)
    .map_err(|error| error.to_string())?;
  if bytes.len() != C::G2_PAIR_COMPRESSED_BYTES {
    return Err(format!("unexpected {} G2 encoding size", C::NAME));
  }
  Ok(bytes)
}

/// Semantic key projection for curve `C`: seed bytes; trace/quotient caps; G1
/// generator; G2 and tau-G2 anchors; circuits; optional fixed commitment. Each
/// circuit contains the seven native transcript shape fields, quotient degree,
/// graph nodes, zero roots, then lookups (multiplicity node and argument
/// nodes). Preprocessed slots follow the canonical order of circuits with fixed
/// data.
pub fn key_bytes_for<C: AiurCurve>(
  key: &VerifyingKey<C>,
) -> Result<Vec<u8>, String> {
  let system = key.system();
  if system.config.transcript_kind() != TranscriptKind::Blake3 {
    return Err("Aiur KZG source verifier requires BLAKE3".into());
  }
  let parameters = system.config.pcs().verifier_params();
  let mut writer = Writer::<C>::new(KEY_MAGIC.to_vec());
  writer.bytes(system.config.transcript_seed())?;
  writer.count(system.config.max_log_degree())?;
  writer.count(system.config.max_quotient_degree())?;
  writer.point(&parameters.g1[0])?;
  writer.buf.extend(anchors_for::<C>(parameters)?);
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
  writer.buf.push(u8::from(system.preprocessed_commit.is_some()));
  if let Some(commitment) = &system.preprocessed_commit {
    writer.commitment(commitment)?;
  }
  writer.finish()
}

pub fn key_bytes(key: &VerifyingKey) -> Result<Vec<u8>, String> {
  key_bytes_for::<Bn254Curve>(key)
}

/// Proof order: activation bytes, log-degree bytes, main/stage2/quotient
/// commitments, accumulators, opening witnesses, then main/stage2/quotient
/// openings and optional fixed openings. Every vector has a u32 length.
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
  writer.points(&proof.opening_proof.0)?;
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
  writer.finish()
}

pub fn proof_bytes(proof: &Proof) -> Result<Vec<u8>, String> {
  proof_bytes_for::<Bn254Curve>(proof)
}

pub fn claims_bytes_for<C: AiurCurve>(
  claims: &[Vec<CurveScalar<C>>],
) -> Result<Vec<u8>, String> {
  let mut writer = Writer::<C>::new(CLAIMS_MAGIC.to_vec());
  writer.count(claims.len())?;
  for row in claims {
    writer.scalars(row)?;
  }
  writer.finish()
}

pub fn claims_bytes(claims: &[Vec<Scalar>]) -> Result<Vec<u8>, String> {
  claims_bytes_for::<Bn254Curve>(claims)
}

/// Authorized predecessor keys and entry callables for one compression chain.
/// The final verifier must pin this policy's digest. Making the policy data
/// public avoids embedding a verifier's own key digest into its circuit.
pub struct Policy<C: AiurCurve = Bn254Curve> {
  anchors: Vec<u8>,
  gl_key: [u8; 32],
  gl_entry: u32,
  bn_key: [u8; 32],
  bn_entry: u32,
  _curve: PhantomData<C>,
}

impl<C: AiurCurve> Policy<C> {
  pub fn anchor_bytes_slice(&self) -> &[u8] {
    &self.anchors
  }

  /// Entry IDs are the physical callable IDs in `TracePlan::public_claim`'s
  /// second word, after deduplication; bytecode entry function indices are
  /// not necessarily the public call IDs.
  pub fn new(
    parameters: &VerifierParams<C>,
    gl_key: [u8; 32],
    gl_entry: u32,
    bn_key: [u8; 32],
    bn_entry: u32,
  ) -> Result<Self, String> {
    Ok(Self {
      anchors: anchors_for::<C>(parameters)?,
      gl_key,
      gl_entry,
      bn_key,
      bn_entry,
      _curve: PhantomData,
    })
  }
  pub fn to_bytes(&self) -> Vec<u8> {
    let mut bytes = POLICY_MAGIC.to_vec();
    bytes.extend(&self.anchors);
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

impl Policy<Bn254Curve> {
  pub fn anchor_bytes(&self) -> &[u8; 128] {
    self
      .anchors
      .as_slice()
      .try_into()
      .expect("BN254 G2 anchor pair is 128 bytes")
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
  pub fn register_for<C: AiurCurve>(
    &self,
    hints: &mut HintChannels<CurveScalar<C>>,
  ) -> Result<(), String> {
    let channels = self.channels.clone();
    hints.insert_fixed::<1, 1>(
      "kzg.io.length",
      Type::Field,
      Type::Field,
      move |[channel]| {
        let channel = usize::try_from(C::FIELD.try_to_u64(channel)?)
          .map_err(|error| error.to_string())?;
        let bytes = channel
          .checked_sub(1)
          .and_then(|i| channels.get(i))
          .ok_or("unknown KZG byte channel")?;
        Ok([C::FIELD.from_u64(
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
        let channel = usize::try_from(C::FIELD.try_to_u64(channel)?)
          .map_err(|error| error.to_string())?;
        let offset = usize::try_from(C::FIELD.try_to_u64(offset)?)
          .map_err(|error| error.to_string())?;
        let byte = channel
          .checked_sub(1)
          .and_then(|i| channels.get(i))
          .and_then(|bytes| bytes.get(offset))
          .ok_or("KZG byte read out of bounds")?;
        Ok([C::FIELD.from_u64(u64::from(*byte))])
      },
    )?;
    let channels = self.channels.clone();
    hints.insert_fixed::<2, 4>(
      "kzg.io.read4",
      Type::Tuple { items: vec![Type::Field; 2] },
      Type::Tuple { items: vec![Type::Field; 4] },
      move |[channel, offset]| {
        let channel = usize::try_from(C::FIELD.try_to_u64(channel)?)
          .map_err(|error| error.to_string())?;
        let offset = usize::try_from(C::FIELD.try_to_u64(offset)?)
          .map_err(|error| error.to_string())?;
        let word = channel
          .checked_sub(1)
          .and_then(|i| channels.get(i))
          .and_then(|bytes| bytes.get(offset..offset.checked_add(4)?))
          .ok_or("KZG word read out of bounds")?;
        Ok(std::array::from_fn(|i| C::FIELD.from_u64(u64::from(word[i]))))
      },
    )
  }
  pub fn register(
    &self,
    hints: &mut HintChannels<Scalar>,
  ) -> Result<(), String> {
    self.register_for::<Bn254Curve>(hints)
  }
}
