//! First production-shaped Flock circuit slice: hash the canonical Stage 2
//! root statement and expose only its BLAKE3 digest. The 80-byte domain/vk/FRI
//! prefix and BLAKE3 padding are fixed by the circuit; the 144 claim bytes are
//! private inputs whose 18 u64 limbs are constrained to be canonical
//! Goldilocks representatives.
//!
//! This proves real Boolean R1CS plus inter-row wiring with statement-bound
//! public I/O. It is deliberately not called a Stage 3 proof: it does not yet
//! parse the statement or verify the Aiur proof whose root it commits to.

use anyhow::{Context, Result, bail};
use bincode::Options;
use flock_prover::{
  challenger::FsChallenger,
  circuit::builder::{
    CircuitShape, GateType, ShapeBuilder, SlotId, SlotWitness, Wire,
  },
  field::F128,
  pcs::{Commitment, PcsParams, ligerito::embedded_initial_k_or_default},
  proof::R1csProofCircuitMerged,
  prover::{self, UnionSlotProverInput},
  r1cs_hashes::blake3,
  schedule::TableType,
  union::UnionInstance,
  verifier,
};
use ix_terminal::{STAGE2_ROOT_STATEMENT_BYTES, Stage2RootStatementV1};
use serde::{Deserialize, Serialize};

use crate::{
  FlockConfigV1, STAGE3_TRANSCRIPT_DOMAIN,
  goldilocks::{
    CanonicalGoldilocksPairGate, build_canonical_pair_r1cs,
    generate_canonical_pair_witness,
  },
};

pub const STAGE3_BINDING_ARTIFACT_MAGIC: &[u8; 8] = b"IXFLK3B1";
const STAGE3_BINDING_ARTIFACT_VERSION: u16 = 1;
const STAGE2_FIXED_PREFIX_BYTES: usize = 80;
const CONFIG_OFFSET: usize = 10;
const PREFIX_OFFSET: usize = CONFIG_OFFSET + 32;
const CIRCUIT_DIGEST_OFFSET: usize = PREFIX_OFFSET + STAGE2_FIXED_PREFIX_BYTES;
const ROOT_DIGEST_OFFSET: usize = CIRCUIT_DIGEST_OFFSET + 32;
const BUNDLE_LENGTH_OFFSET: usize = ROOT_DIGEST_OFFSET + 32;
const ARTIFACT_HEADER_BYTES: usize = BUNDLE_LENGTH_OFFSET + 8;
const MAX_PROOF_BUNDLE_BYTES: usize = 64 * 1024 * 1024;

const BLAKE3_CAPACITY_LOG: usize = 8;
const BLOCK_BYTES: usize = 64;
const WORD_BYTES: usize = 16;
const MESSAGE_BLOCKS: usize = STAGE2_ROOT_STATEMENT_BYTES.div_ceil(BLOCK_BYTES);
const FIRST_CLAIM_WORD: usize = STAGE2_FIXED_PREFIX_BYTES / WORD_BYTES;
const CLAIM_WORDS: usize =
  (STAGE2_ROOT_STATEMENT_BYTES - STAGE2_FIXED_PREFIX_BYTES) / WORD_BYTES;
pub(crate) const CHUNK_START: u32 = 1 << 0;
pub(crate) const CHUNK_END: u32 = 1 << 1;
pub(crate) const ROOT: u32 = 1 << 3;
pub(crate) const IV: [u32; 8] = [
  0x6A09_E667,
  0xBB67_AE85,
  0x3C6E_F372,
  0xA54F_F53A,
  0x510E_527F,
  0x9B05_688C,
  0x1F83_D9AB,
  0x5BE0_CD19,
];

/// A genuine Flock circuit proof of the statement-hash subrelation.
///
/// This artifact must never be accepted as [`crate::Stage3ArtifactV1`]. It
/// establishes only
/// `BLAKE3(fixed_domain_vk_fri_prefix || private_claim) = stage2_root_digest`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Stage3BindingArtifactV1 {
  fixed_statement_prefix: [u8; STAGE2_FIXED_PREFIX_BYTES],
  circuit_digest: [u8; 32],
  stage2_root_digest: [u8; 32],
  proof_bundle_bytes: Vec<u8>,
}

impl Stage3BindingArtifactV1 {
  pub fn to_bytes(&self) -> Vec<u8> {
    let mut bytes =
      Vec::with_capacity(ARTIFACT_HEADER_BYTES + self.proof_bundle_bytes.len());
    bytes.extend_from_slice(STAGE3_BINDING_ARTIFACT_MAGIC);
    bytes.extend_from_slice(&STAGE3_BINDING_ARTIFACT_VERSION.to_le_bytes());
    bytes.extend_from_slice(&FlockConfigV1.digest());
    bytes.extend_from_slice(&self.fixed_statement_prefix);
    bytes.extend_from_slice(&self.circuit_digest);
    bytes.extend_from_slice(&self.stage2_root_digest);
    bytes.extend_from_slice(
      &u64::try_from(self.proof_bundle_bytes.len())
        .expect("proof bundle length")
        .to_le_bytes(),
    );
    bytes.extend_from_slice(&self.proof_bundle_bytes);
    bytes
  }

  pub fn from_bytes(bytes: &[u8]) -> Result<Self> {
    if bytes.len() < ARTIFACT_HEADER_BYTES {
      bail!("truncated Flock statement-binding artifact");
    }
    if &bytes[..8] != STAGE3_BINDING_ARTIFACT_MAGIC {
      bail!("invalid Flock statement-binding artifact magic");
    }
    let version = u16::from_le_bytes(bytes[8..10].try_into().unwrap());
    if version != STAGE3_BINDING_ARTIFACT_VERSION {
      bail!("unsupported Flock statement-binding artifact version {version}");
    }
    if bytes[CONFIG_OFFSET..PREFIX_OFFSET] != FlockConfigV1.digest() {
      bail!("Flock statement-binding artifact configuration mismatch");
    }
    let mut fixed_statement_prefix = [0u8; STAGE2_FIXED_PREFIX_BYTES];
    fixed_statement_prefix
      .copy_from_slice(&bytes[PREFIX_OFFSET..CIRCUIT_DIGEST_OFFSET]);
    let mut circuit_digest = [0u8; 32];
    circuit_digest
      .copy_from_slice(&bytes[CIRCUIT_DIGEST_OFFSET..ROOT_DIGEST_OFFSET]);
    let mut stage2_root_digest = [0u8; 32];
    stage2_root_digest
      .copy_from_slice(&bytes[ROOT_DIGEST_OFFSET..BUNDLE_LENGTH_OFFSET]);
    let bundle_len = usize::try_from(u64::from_le_bytes(
      bytes[BUNDLE_LENGTH_OFFSET..ARTIFACT_HEADER_BYTES].try_into().unwrap(),
    ))
    .map_err(|error| {
      anyhow::anyhow!("Flock proof bundle length does not fit usize: {error}")
    })?;
    if bundle_len == 0 || bundle_len > MAX_PROOF_BUNDLE_BYTES {
      bail!("invalid Flock proof bundle length {bundle_len}");
    }
    let expected_len =
      ARTIFACT_HEADER_BYTES.checked_add(bundle_len).ok_or_else(|| {
        anyhow::anyhow!("Flock binding artifact length overflow")
      })?;
    if bytes.len() != expected_len {
      bail!(
        "Flock statement-binding artifact is {} bytes; header declares {expected_len}",
        bytes.len()
      );
    }
    let proof_bundle_bytes = bytes[ARTIFACT_HEADER_BYTES..].to_vec();
    decode_proof_bundle(&proof_bundle_bytes)
      .context("decode Flock statement-binding proof bundle")?;
    Ok(Self {
      fixed_statement_prefix,
      circuit_digest,
      stage2_root_digest,
      proof_bundle_bytes,
    })
  }

  pub fn fixed_statement_prefix(&self) -> &[u8; STAGE2_FIXED_PREFIX_BYTES] {
    &self.fixed_statement_prefix
  }

  pub fn circuit_digest(&self) -> &[u8; 32] {
    &self.circuit_digest
  }

  pub fn stage2_root_digest(&self) -> &[u8; 32] {
    &self.stage2_root_digest
  }

  pub fn proof_bundle_bytes(&self) -> &[u8] {
    &self.proof_bundle_bytes
  }
}

#[derive(Serialize, Deserialize)]
struct CircuitProofBundle {
  commitment: Commitment,
  proof: R1csProofCircuitMerged,
}

/// Produce a real Flock circuit proof that checks the private claim's
/// Goldilocks encodings and hashes the canonical 224-byte Stage 2 statement
/// to its public root digest.
pub fn prove_stage3_statement_binding(
  statement: &Stage2RootStatementV1,
) -> Result<Stage3BindingArtifactV1> {
  let statement_bytes = statement.to_bytes();
  let fixed_statement_prefix = statement_prefix(&statement_bytes);
  let relation = StatementHashRelation::build(&fixed_statement_prefix)?;
  let inputs = relation_inputs(&statement_bytes);
  let witness = relation.shape.run(&inputs, &[]);
  let stage2_root_digest = statement.digest();
  let expected_public =
    relation_public(&fixed_statement_prefix, &stage2_root_digest);
  if witness.public != expected_public {
    bail!("Flock BLAKE3 gate output disagrees with native Stage 2 digest");
  }

  let rows = witness.rows::<Blake3Gate>(relation.blake3_slot);
  let canonical_rows = witness
    .rows::<CanonicalGoldilocksPairGate>(relation.canonical_goldilocks_slot);
  relation.ensure_registry_order()?;
  let blake3_r1cs = blake3::build_block_r1cs(BLAKE3_CAPACITY_LOG);
  let blake3_lincheck = blake3_r1cs.csc_lincheck_circuit();
  let canonical_r1cs = build_canonical_pair_r1cs(BLAKE3_CAPACITY_LOG);
  let canonical_lincheck = canonical_r1cs.csc_lincheck_circuit();
  let union =
    UnionInstance::new(&relation.shape.registry, relation.shape.counts.clone());
  let pcs_params = pcs_params(&union);
  let mut challenger =
    FsChallenger::with_chained_blake3(STAGE3_TRANSCRIPT_DOMAIN);
  let (proof, commitment, _) = prover::prove_fast_ligerito_union_circuit(
    &union,
    &relation.shape.circuit,
    &witness.public,
    &pcs_params,
    vec![
      UnionSlotProverInput::new(
        blake3::generate_witness_batch_major_partial(rows, BLAKE3_CAPACITY_LOG),
        blake3_lincheck,
      ),
      UnionSlotProverInput::new(
        generate_canonical_pair_witness(canonical_rows, BLAKE3_CAPACITY_LOG),
        canonical_lincheck,
      ),
    ],
    Vec::new(),
    &mut challenger,
  );
  let proof_bundle_bytes =
    encode_proof_bundle(&CircuitProofBundle { commitment, proof })?;
  if proof_bundle_bytes.len() > MAX_PROOF_BUNDLE_BYTES {
    bail!("Flock proof bundle exceeds {MAX_PROOF_BUNDLE_BYTES} bytes");
  }
  Ok(Stage3BindingArtifactV1 {
    fixed_statement_prefix,
    circuit_digest: relation.shape.circuit.digest(),
    stage2_root_digest,
    proof_bundle_bytes,
  })
}

/// Verify the statement-hash circuit proof against the digest carried by its
/// strict artifact. Callers that expect a particular Stage 2 root must also
/// use [`verify_stage3_statement_binding_for`].
pub fn verify_stage3_statement_binding(
  artifact: &Stage3BindingArtifactV1,
) -> Result<()> {
  let relation =
    StatementHashRelation::build(&artifact.fixed_statement_prefix)?;
  relation.ensure_registry_order()?;
  if artifact.circuit_digest != relation.shape.circuit.digest() {
    bail!("Flock statement-binding circuit digest mismatch");
  }
  let bundle = decode_proof_bundle(&artifact.proof_bundle_bytes)
    .context("decode Flock statement-binding proof bundle")?;
  let public = relation_public(
    &artifact.fixed_statement_prefix,
    &artifact.stage2_root_digest,
  );
  let union =
    UnionInstance::new(&relation.shape.registry, relation.shape.counts.clone());
  let pcs_params = pcs_params(&union);
  let blake3_r1cs = blake3::build_block_r1cs(BLAKE3_CAPACITY_LOG);
  let blake3_lincheck = blake3_r1cs.csc_lincheck_circuit();
  let canonical_r1cs = build_canonical_pair_r1cs(BLAKE3_CAPACITY_LOG);
  let canonical_lincheck = canonical_r1cs.csc_lincheck_circuit();
  let linchecks: [&dyn flock_prover::lincheck::LincheckCircuit; 2] =
    [blake3_lincheck, canonical_lincheck];
  let mut challenger =
    FsChallenger::with_chained_blake3(STAGE3_TRANSCRIPT_DOMAIN);
  verifier::verify_ligerito_union_circuit(
    &union,
    &relation.shape.circuit,
    &public,
    &linchecks,
    &bundle.commitment,
    &bundle.proof,
    &pcs_params,
    &mut challenger,
  )
  .map_err(|error| {
    anyhow::anyhow!("Flock statement-binding proof rejected: {error:?}")
  })?;
  Ok(())
}

/// Verify and bind the proof to an expected canonical Stage 2 statement.
pub fn verify_stage3_statement_binding_for(
  artifact: &Stage3BindingArtifactV1,
  expected: &Stage2RootStatementV1,
) -> Result<()> {
  if artifact.fixed_statement_prefix != statement_prefix(&expected.to_bytes()) {
    bail!("Flock binding proof uses a different Stage 2 vk or FRI prefix");
  }
  if artifact.stage2_root_digest != expected.digest() {
    bail!("Flock binding proof targets a different Stage 2 root");
  }
  verify_stage3_statement_binding(artifact)
}

/// Content digest of this partial circuit. It is useful for diagnostics and
/// reproducibility, but is not the complete Stage 3 relation digest.
pub fn stage3_statement_binding_circuit_digest(
  statement: &Stage2RootStatementV1,
) -> Result<[u8; 32]> {
  let prefix = statement_prefix(&statement.to_bytes());
  Ok(StatementHashRelation::build(&prefix)?.shape.circuit.digest())
}

struct StatementHashRelation {
  shape: CircuitShape,
  blake3_slot: SlotId,
  canonical_goldilocks_slot: SlotId,
}

impl StatementHashRelation {
  fn build(prefix: &[u8; STAGE2_FIXED_PREFIX_BYTES]) -> Result<Self> {
    let mut builder = ShapeBuilder::new(BLAKE3_CAPACITY_LOG);
    let blake3_slot = builder.slot(Blake3Gate { nu: BLAKE3_CAPACITY_LOG });
    let canonical_goldilocks_slot =
      builder.slot(CanonicalGoldilocksPairGate { nu: BLAKE3_CAPACITY_LOG });
    let packed_iv = pack8(&IV);
    let initial_cv = [
      builder.fixed_public_input(packed_iv[0]),
      builder.fixed_public_input(packed_iv[1]),
    ];
    let canonical_zero = builder.fixed_public_input(F128::ZERO);
    let mut messages = Vec::<[Wire; 4]>::with_capacity(MESSAGE_BLOCKS);
    let mut params = Vec::<Wire>::with_capacity(MESSAGE_BLOCKS);
    for block in 0..MESSAGE_BLOCKS {
      let message: [_; 4] = std::array::from_fn(|word| {
        let word = block * 4 + word;
        match fixed_statement_word(prefix, word) {
          Some(value) => builder.fixed_public_input(value),
          None => builder.input(),
        }
      });
      messages.push(message);
      params.push(builder.fixed_public_input(block_params(block)));
    }

    for word in FIRST_CLAIM_WORD..FIRST_CLAIM_WORD + CLAIM_WORDS {
      let message = messages[word / 4][word % 4];
      let violation = builder.gate(canonical_goldilocks_slot, &[message])[0];
      builder.connect(canonical_zero, violation);
    }

    let mut cv = initial_cv;
    for block in 0..MESSAGE_BLOCKS {
      let message = messages[block];
      let outputs = builder.gate(
        blake3_slot,
        &[
          cv[0],
          cv[1],
          message[0],
          message[1],
          message[2],
          message[3],
          params[block],
        ],
      );
      cv = [outputs[0], outputs[1]];
    }
    builder.publish(cv[0]);
    builder.publish(cv[1]);
    let shape = builder.finish().map_err(|error| {
      anyhow::anyhow!("build Flock binding circuit: {error:?}")
    })?;
    Ok(Self { shape, blake3_slot, canonical_goldilocks_slot })
  }

  fn ensure_registry_order(&self) -> Result<()> {
    if self.shape.registry_slot(self.blake3_slot) != 0
      || self.shape.registry_slot(self.canonical_goldilocks_slot) != 1
    {
      bail!("unexpected Flock Boolean table registry order");
    }
    Ok(())
  }
}

pub(crate) struct Blake3Gate {
  pub(crate) nu: usize,
}

impl GateType for Blake3Gate {
  type Row = blake3::Compression;
  type Hint = ();

  fn table(&self) -> TableType {
    crate::boolean::table_from_block_r1cs(blake3::build_block_r1cs(self.nu))
      .with_io_schema(blake3::io_schema())
  }

  fn eval(
    &self,
    inputs: &[F128],
    _hint: &(),
    outputs: &mut Vec<F128>,
  ) -> Self::Row {
    let cv = unpack8(inputs[0], inputs[1]);
    let mut message = [0u32; 16];
    for index in 0..4 {
      message[4 * index..4 * index + 4]
        .copy_from_slice(&unpack4(inputs[2 + index]));
    }
    let (counter, block_len, flags) = unpack_params(inputs[6]);
    let output =
      blake3::blake3_compress(&cv, &message, counter, block_len, flags);
    let output_lo: [u32; 8] = output[..8].try_into().unwrap();
    let output_hi: [u32; 8] = output[8..].try_into().unwrap();
    outputs.extend_from_slice(&[
      pack8(&output_lo)[0],
      pack8(&output_lo)[1],
      pack8(&output_hi)[0],
      pack8(&output_hi)[1],
    ]);
    (cv, message, counter, block_len, flags)
  }

  fn witness(&self, _rows: &[Self::Row], _nu: usize) -> SlotWitness {
    SlotWitness::DeferredToRows
  }
}

fn relation_inputs(statement: &[u8]) -> Vec<F128> {
  assert_eq!(statement.len(), STAGE2_ROOT_STATEMENT_BYTES);
  let mut padded = [0u8; MESSAGE_BLOCKS * BLOCK_BYTES];
  padded[..statement.len()].copy_from_slice(statement);
  let packed_iv = pack8(&IV);
  let mut inputs = Vec::with_capacity(3 + MESSAGE_BLOCKS * 5);
  inputs.extend_from_slice(&packed_iv);
  inputs.push(F128::ZERO);
  for block in 0..MESSAGE_BLOCKS {
    let start = block * BLOCK_BYTES;
    for word in 0..4 {
      let offset = start + word * WORD_BYTES;
      inputs.push(pack_bytes(&padded[offset..offset + WORD_BYTES]));
    }
    inputs.push(block_params(block));
  }
  inputs
}

fn relation_public(
  prefix: &[u8; STAGE2_FIXED_PREFIX_BYTES],
  digest: &[u8; 32],
) -> Vec<F128> {
  let packed_iv = pack8(&IV);
  let mut public = Vec::with_capacity(3 + 7 + MESSAGE_BLOCKS + 2);
  public.extend_from_slice(&packed_iv);
  public.push(F128::ZERO);
  for block in 0..MESSAGE_BLOCKS {
    for word in 0..4 {
      if let Some(value) = fixed_statement_word(prefix, block * 4 + word) {
        public.push(value);
      }
    }
    public.push(block_params(block));
  }
  public.push(pack_bytes(&digest[..16]));
  public.push(pack_bytes(&digest[16..]));
  public
}

fn statement_prefix(statement: &[u8]) -> [u8; STAGE2_FIXED_PREFIX_BYTES] {
  statement[..STAGE2_FIXED_PREFIX_BYTES].try_into().unwrap()
}

fn fixed_statement_word(
  prefix: &[u8; STAGE2_FIXED_PREFIX_BYTES],
  word: usize,
) -> Option<F128> {
  if word * WORD_BYTES < STAGE2_FIXED_PREFIX_BYTES {
    let offset = word * WORD_BYTES;
    Some(pack_bytes(&prefix[offset..offset + WORD_BYTES]))
  } else if word * WORD_BYTES >= STAGE2_ROOT_STATEMENT_BYTES {
    Some(F128::ZERO)
  } else {
    None
  }
}

fn block_params(block: usize) -> F128 {
  let is_first = block == 0;
  let is_last = block + 1 == MESSAGE_BLOCKS;
  let mut flags = 0;
  if is_first {
    flags |= CHUNK_START;
  }
  if is_last {
    flags |= CHUNK_END | ROOT;
  }
  let consumed = block * BLOCK_BYTES;
  let remaining = STAGE2_ROOT_STATEMENT_BYTES - consumed;
  let block_len = u32::try_from(remaining.min(BLOCK_BYTES)).unwrap();
  pack_params(0, block_len, flags)
}

pub(crate) fn pcs_params(union: &UnionInstance<'_>) -> PcsParams {
  let profile = FlockConfigV1.profile();
  let m = union.dense_m();
  let log_batch_size = embedded_initial_k_or_default(m, profile);
  PcsParams {
    m,
    log_inv_rate: profile.log_inv_rate(),
    log_batch_size,
    profile,
    num_lanes: union.commit_lanes(log_batch_size),
    merkle_hash: FlockConfigV1.merkle_hash(),
  }
}

pub(crate) fn pack_bytes(bytes: &[u8]) -> F128 {
  assert_eq!(bytes.len(), WORD_BYTES);
  F128::new(
    u64::from_le_bytes(bytes[..8].try_into().unwrap()),
    u64::from_le_bytes(bytes[8..].try_into().unwrap()),
  )
}

pub(crate) fn pack4(words: [u32; 4]) -> F128 {
  F128::new(
    words[0] as u64 | ((words[1] as u64) << 32),
    words[2] as u64 | ((words[3] as u64) << 32),
  )
}

pub(crate) fn unpack4(value: F128) -> [u32; 4] {
  [
    value.lo as u32,
    (value.lo >> 32) as u32,
    value.hi as u32,
    (value.hi >> 32) as u32,
  ]
}

pub(crate) fn pack8(words: &[u32; 8]) -> [F128; 2] {
  [
    pack4([words[0], words[1], words[2], words[3]]),
    pack4([words[4], words[5], words[6], words[7]]),
  ]
}

pub(crate) fn unpack8(first: F128, second: F128) -> [u32; 8] {
  let first = unpack4(first);
  let second = unpack4(second);
  [
    first[0], first[1], first[2], first[3], second[0], second[1], second[2],
    second[3],
  ]
}

pub(crate) fn pack_params(counter: u64, block_len: u32, flags: u32) -> F128 {
  F128::new(counter, block_len as u64 | ((flags as u64) << 32))
}

fn unpack_params(value: F128) -> (u64, u32, u32) {
  (value.lo, value.hi as u32, (value.hi >> 32) as u32)
}

fn encode_proof_bundle(bundle: &CircuitProofBundle) -> Result<Vec<u8>> {
  bincode::DefaultOptions::new()
    .with_fixint_encoding()
    .serialize(bundle)
    .context("encode Flock statement-binding proof bundle")
}

fn decode_proof_bundle(bytes: &[u8]) -> Result<CircuitProofBundle> {
  bincode::DefaultOptions::new()
    .with_fixint_encoding()
    .with_limit(MAX_PROOF_BUNDLE_BYTES as u64)
    .reject_trailing_bytes()
    .deserialize(bytes)
    .context("invalid Flock statement-binding proof bundle")
}

#[cfg(test)]
mod tests {
  use super::*;
  use ix_terminal::OUTER_CLAIM_ELEMENTS;
  use multi_stark::types::FriParameters;

  fn statement() -> Stage2RootStatementV1 {
    let claim: Vec<u8> =
      (0..OUTER_CLAIM_ELEMENTS as u64).flat_map(u64::to_le_bytes).collect();
    Stage2RootStatementV1::new(
      b"binding-test-vk",
      &claim,
      &FriParameters {
        log_final_poly_len: 0,
        max_log_arity: 1,
        num_queries: 100,
        commit_proof_of_work_bits: 0,
        query_proof_of_work_bits: 20,
      },
    )
    .unwrap()
  }

  #[test]
  fn circuit_hashes_the_exact_stage2_statement() {
    let statement = statement();
    let statement_bytes = statement.to_bytes();
    let prefix = statement_prefix(&statement_bytes);
    let relation = StatementHashRelation::build(&prefix).unwrap();
    let witness = relation.shape.run(&relation_inputs(&statement_bytes), &[]);
    assert_eq!(witness.public, relation_public(&prefix, &statement.digest()));
    assert_eq!(relation.shape.counts, vec![MESSAGE_BLOCKS, CLAIM_WORDS]);
    assert_eq!(witness.rows::<Blake3Gate>(relation.blake3_slot).len(), 4);
    assert_eq!(
      witness
        .rows::<CanonicalGoldilocksPairGate>(relation.canonical_goldilocks_slot)
        .len(),
      CLAIM_WORDS
    );

    let mut changed = statement.to_bytes();
    let last = changed.len() - 1;
    changed[last] ^= 1;
    let changed = relation.shape.run(&relation_inputs(&changed), &[]);
    assert_ne!(changed.public, witness.public);

    let mut other_prefix = prefix;
    other_prefix[8] ^= 1;
    let other = StatementHashRelation::build(&other_prefix).unwrap();
    assert_ne!(other.shape.circuit.digest(), relation.shape.circuit.digest());
  }

  #[test]
  fn artifact_parser_rejects_short_and_wrong_magic() {
    assert!(Stage3BindingArtifactV1::from_bytes(&[]).is_err());
    let mut header = vec![0u8; ARTIFACT_HEADER_BYTES];
    header[..8].copy_from_slice(b"NOTFLOCK");
    assert!(Stage3BindingArtifactV1::from_bytes(&header).is_err());
  }

  #[test]
  #[ignore = "large upstream Flock circuit proof; run explicitly"]
  fn real_statement_binding_proof_round_trip_and_mutations() {
    let statement = statement();
    let artifact =
      prove_stage3_statement_binding(&statement).expect("prove binding");
    eprintln!(
      "Flock statement-binding circuit proof bundle: {} bytes",
      artifact.proof_bundle_bytes().len()
    );
    verify_stage3_statement_binding_for(&artifact, &statement)
      .expect("verify binding");

    let encoded = artifact.to_bytes();
    let decoded = Stage3BindingArtifactV1::from_bytes(&encoded).unwrap();
    verify_stage3_statement_binding_for(&decoded, &statement)
      .expect("verify decoded binding");

    let mut wrong_prefix = decoded.clone();
    wrong_prefix.fixed_statement_prefix[8] ^= 1;
    assert!(
      verify_stage3_statement_binding_for(&wrong_prefix, &statement).is_err()
    );

    let mut wrong_root = decoded.clone();
    wrong_root.stage2_root_digest[0] ^= 1;
    assert!(verify_stage3_statement_binding(&wrong_root).is_err());

    let mut wrong_proof = decoded;
    let flip_at = wrong_proof.proof_bundle_bytes.len() / 2;
    wrong_proof.proof_bundle_bytes[flip_at] ^= 1;
    assert!(verify_stage3_statement_binding(&wrong_proof).is_err());
  }
}
