//! Circuit-bound BLAKE3 Merkle authentication paths.
//!
//! Plonky3's `CompressionFunctionFromHasher<Blake3, 2, 32>` hashes the
//! concatenation of two 32-byte digests. One constrained direction bit orders
//! the current and sibling digests at every level, then the existing Flock
//! BLAKE3 compression table computes the parent.

use ::blake3 as native_blake3;
use anyhow::{Context, Result, bail};
use bincode::Options;
use flock_prover::{
  challenger::FsChallenger,
  circuit::builder::{
    CircuitShape, GateType, ShapeBuilder, SlotId, SlotWitness,
  },
  field::F128,
  pcs::Commitment,
  proof::R1csProofCircuitMerged,
  prover::{self, UnionSlotProverInput},
  r1cs::BlockR1cs,
  r1cs_hashes::blake3 as flock_blake3,
  schedule::{IoWord, TableType},
  union::{SlotWitnessDest, UnionInstance},
  verifier,
};
use serde::{Deserialize, Serialize};

use crate::{
  FlockConfigV1, MERKLE_CONFORMANCE_TRANSCRIPT_DOMAIN,
  binding::{
    Blake3Gate, CHUNK_END, CHUNK_START, IV, ROOT, pack_bytes, pack_params,
    pack8, pcs_params,
  },
  boolean::{
    BooleanR1csBuilder, BooleanR1csPlan, generate_boolean_witness,
    generate_boolean_witness_into, write_f128,
  },
};

pub const MERKLE_CONFORMANCE_ARTIFACT_MAGIC: &[u8; 8] = b"IXFLKMP1";
const ARTIFACT_VERSION: u16 = 1;
const CONFIG_OFFSET: usize = 10;
const DEPTH_OFFSET: usize = CONFIG_OFFSET + 32;
const INDEX_OFFSET: usize = DEPTH_OFFSET + 1;
const LEAF_OFFSET: usize = INDEX_OFFSET + 4;
const PATH_OFFSET: usize = LEAF_OFFSET + 32;
const FIXED_SUFFIX_BYTES: usize = 32 + 32 + 8;
const MAX_DEPTH: usize = 32;
const MAX_BUNDLE_BYTES: usize = 64 * 1024 * 1024;

const NU: usize = 8;
const ORDER_K_LOG: usize = 11;
const BIT_BASE: usize = 0;
const CURRENT_BASE: usize = 128;
const SIBLING_BASE: usize = 384;
const LEFT_BASE: usize = 640;
const RIGHT_BASE: usize = 896;
const ORDER_RESERVED_COLUMNS: usize = 1152;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MerklePathV1 {
  pub leaf: [u8; 32],
  pub siblings: Vec<[u8; 32]>,
  /// Leaf index; level zero consumes its least-significant bit.
  pub index: u32,
}

impl MerklePathV1 {
  pub fn root(&self) -> Result<[u8; 32]> {
    validate_path(self)?;
    Ok(native_root(self))
  }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MerkleConformanceArtifactV1 {
  path: MerklePathV1,
  circuit_digest: [u8; 32],
  root: [u8; 32],
  proof_bundle_bytes: Vec<u8>,
}

impl MerkleConformanceArtifactV1 {
  pub fn to_bytes(&self) -> Vec<u8> {
    let mut bytes = Vec::with_capacity(
      PATH_OFFSET
        + 32 * self.path.siblings.len()
        + FIXED_SUFFIX_BYTES
        + self.proof_bundle_bytes.len(),
    );
    bytes.extend_from_slice(MERKLE_CONFORMANCE_ARTIFACT_MAGIC);
    bytes.extend_from_slice(&ARTIFACT_VERSION.to_le_bytes());
    bytes.extend_from_slice(&FlockConfigV1.digest());
    bytes.push(u8::try_from(self.path.siblings.len()).expect("Merkle depth"));
    bytes.extend_from_slice(&self.path.index.to_le_bytes());
    bytes.extend_from_slice(&self.path.leaf);
    for sibling in &self.path.siblings {
      bytes.extend_from_slice(sibling);
    }
    bytes.extend_from_slice(&self.circuit_digest);
    bytes.extend_from_slice(&self.root);
    bytes.extend_from_slice(
      &u64::try_from(self.proof_bundle_bytes.len())
        .expect("proof bundle length")
        .to_le_bytes(),
    );
    bytes.extend_from_slice(&self.proof_bundle_bytes);
    bytes
  }

  pub fn from_bytes(bytes: &[u8]) -> Result<Self> {
    if bytes.len() < PATH_OFFSET + FIXED_SUFFIX_BYTES {
      bail!("truncated Flock Merkle conformance artifact");
    }
    if &bytes[..8] != MERKLE_CONFORMANCE_ARTIFACT_MAGIC {
      bail!("invalid Flock Merkle conformance artifact magic");
    }
    let version = u16::from_le_bytes(bytes[8..10].try_into().unwrap());
    if version != ARTIFACT_VERSION {
      bail!("unsupported Flock Merkle artifact version {version}");
    }
    if bytes[CONFIG_OFFSET..DEPTH_OFFSET] != FlockConfigV1.digest() {
      bail!("Flock Merkle artifact configuration mismatch");
    }
    let depth = usize::from(bytes[DEPTH_OFFSET]);
    validate_depth(depth)?;
    let index =
      u32::from_le_bytes(bytes[INDEX_OFFSET..LEAF_OFFSET].try_into().unwrap());
    let path_end = PATH_OFFSET
      .checked_add(depth * 32)
      .ok_or_else(|| anyhow::anyhow!("Merkle path length overflow"))?;
    let suffix_end = path_end
      .checked_add(FIXED_SUFFIX_BYTES)
      .ok_or_else(|| anyhow::anyhow!("Merkle artifact length overflow"))?;
    if bytes.len() < suffix_end {
      bail!("truncated Flock Merkle path or proof header");
    }
    let mut leaf = [0u8; 32];
    leaf.copy_from_slice(&bytes[LEAF_OFFSET..PATH_OFFSET]);
    let siblings = bytes[PATH_OFFSET..path_end].as_chunks::<32>().0.to_vec();
    let path = MerklePathV1 { leaf, siblings, index };
    validate_path(&path)?;
    let mut circuit_digest = [0u8; 32];
    circuit_digest.copy_from_slice(&bytes[path_end..path_end + 32]);
    let mut root = [0u8; 32];
    root.copy_from_slice(&bytes[path_end + 32..path_end + 64]);
    let bundle_len = usize::try_from(u64::from_le_bytes(
      bytes[path_end + 64..suffix_end].try_into().unwrap(),
    ))
    .map_err(|error| {
      anyhow::anyhow!("Merkle proof bundle length does not fit usize: {error}")
    })?;
    if bundle_len == 0 || bundle_len > MAX_BUNDLE_BYTES {
      bail!("invalid Flock Merkle proof bundle length {bundle_len}");
    }
    let expected_len = suffix_end
      .checked_add(bundle_len)
      .ok_or_else(|| anyhow::anyhow!("Merkle proof length overflow"))?;
    if bytes.len() != expected_len {
      bail!(
        "Flock Merkle artifact is {} bytes; header declares {expected_len}",
        bytes.len()
      );
    }
    let proof_bundle_bytes = bytes[suffix_end..].to_vec();
    decode_bundle(&proof_bundle_bytes)
      .context("decode Flock Merkle conformance proof bundle")?;
    Ok(Self { path, circuit_digest, root, proof_bundle_bytes })
  }

  pub fn path(&self) -> &MerklePathV1 {
    &self.path
  }

  pub fn circuit_digest(&self) -> &[u8; 32] {
    &self.circuit_digest
  }

  pub fn root(&self) -> &[u8; 32] {
    &self.root
  }

  pub fn proof_bundle_bytes(&self) -> &[u8] {
    &self.proof_bundle_bytes
  }
}

#[derive(Serialize, Deserialize)]
struct MerkleProofBundle {
  commitment: Commitment,
  proof: R1csProofCircuitMerged,
}

pub fn prove_merkle_conformance(
  path: &MerklePathV1,
) -> Result<MerkleConformanceArtifactV1> {
  validate_path(path)?;
  let relation = MerkleRelation::build(path.siblings.len())?;
  relation.ensure_registry_order()?;
  let witness = relation.shape.run(&relation_inputs(path), &[]);
  let root = native_root(path);
  if witness.public != relation_public(path, &root) {
    bail!("Flock Merkle circuit output disagrees with native BLAKE3 root");
  }
  let blake3_rows = witness.rows::<Blake3Gate>(relation.blake3_slot);
  let order_rows = witness.rows::<DigestOrderGate>(relation.order_slot);
  let blake3_r1cs = flock_blake3::build_block_r1cs(NU);
  let blake3_lincheck = blake3_r1cs.csc_lincheck_circuit();
  let order_r1cs = build_digest_order_r1cs(NU);
  let order_lincheck = order_r1cs.csc_lincheck_circuit();
  let union =
    UnionInstance::new(&relation.shape.registry, relation.shape.counts.clone());
  let params = pcs_params(&union);
  let mut challenger =
    FsChallenger::with_chained_blake3(MERKLE_CONFORMANCE_TRANSCRIPT_DOMAIN);
  let (proof, commitment, _) = prover::prove_fast_ligerito_union_circuit(
    &union,
    &relation.shape.circuit,
    &witness.public,
    &params,
    vec![
      UnionSlotProverInput::new(
        flock_blake3::generate_witness_batch_major_partial(blake3_rows, NU),
        blake3_lincheck,
      ),
      UnionSlotProverInput::new(
        generate_digest_order_witness(order_rows, NU),
        order_lincheck,
      ),
    ],
    Vec::new(),
    &mut challenger,
  );
  let proof_bundle_bytes =
    encode_bundle(&MerkleProofBundle { commitment, proof })?;
  if proof_bundle_bytes.len() > MAX_BUNDLE_BYTES {
    bail!("Flock Merkle proof bundle exceeds {MAX_BUNDLE_BYTES} bytes");
  }
  Ok(MerkleConformanceArtifactV1 {
    path: path.clone(),
    circuit_digest: relation.shape.circuit.digest(),
    root,
    proof_bundle_bytes,
  })
}

pub fn verify_merkle_conformance(
  artifact: &MerkleConformanceArtifactV1,
) -> Result<()> {
  validate_path(&artifact.path)?;
  let relation = MerkleRelation::build(artifact.path.siblings.len())?;
  relation.ensure_registry_order()?;
  if artifact.circuit_digest != relation.shape.circuit.digest() {
    bail!("Flock Merkle conformance circuit digest mismatch");
  }
  let bundle = decode_bundle(&artifact.proof_bundle_bytes)
    .context("decode Flock Merkle conformance proof bundle")?;
  let public = relation_public(&artifact.path, &artifact.root);
  let blake3_r1cs = flock_blake3::build_block_r1cs(NU);
  let blake3_lincheck = blake3_r1cs.csc_lincheck_circuit();
  let order_r1cs = build_digest_order_r1cs(NU);
  let order_lincheck = order_r1cs.csc_lincheck_circuit();
  let linchecks: [&dyn flock_prover::lincheck::LincheckCircuit; 2] =
    [blake3_lincheck, order_lincheck];
  let union =
    UnionInstance::new(&relation.shape.registry, relation.shape.counts.clone());
  let params = pcs_params(&union);
  let mut challenger =
    FsChallenger::with_chained_blake3(MERKLE_CONFORMANCE_TRANSCRIPT_DOMAIN);
  verifier::verify_ligerito_union_circuit(
    &union,
    &relation.shape.circuit,
    &public,
    &linchecks,
    &bundle.commitment,
    &bundle.proof,
    &params,
    &mut challenger,
  )
  .map_err(|error| {
    anyhow::anyhow!("Flock Merkle conformance proof rejected: {error:?}")
  })?;
  Ok(())
}

struct MerkleRelation {
  shape: CircuitShape,
  blake3_slot: SlotId,
  order_slot: SlotId,
}

impl MerkleRelation {
  fn build(depth: usize) -> Result<Self> {
    validate_depth(depth)?;
    let mut builder = ShapeBuilder::new(NU);
    let blake3_slot = builder.slot(Blake3Gate { nu: NU });
    let order_slot = builder.slot(DigestOrderGate { nu: NU });
    let packed_iv = pack8(&IV);
    let iv = [
      builder.fixed_public_input(packed_iv[0]),
      builder.fixed_public_input(packed_iv[1]),
    ];
    let params = builder.fixed_public_input(pack_params(
      0,
      64,
      CHUNK_START | CHUNK_END | ROOT,
    ));
    let mut current = [builder.public_input(), builder.public_input()];
    for _ in 0..depth {
      let direction = builder.public_input();
      let sibling = [builder.public_input(), builder.public_input()];
      let ordered = builder.gate(
        order_slot,
        &[direction, current[0], current[1], sibling[0], sibling[1]],
      );
      let parent = builder.gate(
        blake3_slot,
        &[iv[0], iv[1], ordered[0], ordered[1], ordered[2], ordered[3], params],
      );
      current = [parent[0], parent[1]];
    }
    builder.publish(current[0]);
    builder.publish(current[1]);
    let shape = builder.finish().map_err(|error| {
      anyhow::anyhow!("build Flock Merkle conformance circuit: {error:?}")
    })?;
    Ok(Self { shape, blake3_slot, order_slot })
  }

  fn ensure_registry_order(&self) -> Result<()> {
    if self.shape.registry_slot(self.blake3_slot) != 0
      || self.shape.registry_slot(self.order_slot) != 1
    {
      bail!("unexpected Flock Merkle table registry order");
    }
    Ok(())
  }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct DigestOrderRow {
  direction: bool,
  current: [F128; 2],
  sibling: [F128; 2],
}

#[derive(Clone, Copy, Debug)]
pub(crate) struct DigestOrderGate {
  pub(crate) nu: usize,
}

impl GateType for DigestOrderGate {
  type Row = DigestOrderRow;
  type Hint = ();

  fn table(&self) -> TableType {
    crate::boolean::table_from_block_r1cs(build_digest_order_r1cs(self.nu))
      .with_io_schema(vec![
        IoWord::input(0),
        IoWord::input(1),
        IoWord::input(2),
        IoWord::input(3),
        IoWord::input(4),
        IoWord::output(5),
        IoWord::output(6),
        IoWord::output(7),
        IoWord::output(8),
      ])
  }

  fn eval(
    &self,
    inputs: &[F128],
    _hint: &(),
    outputs: &mut Vec<F128>,
  ) -> Self::Row {
    let direction_word = inputs[0];
    assert_eq!(direction_word.hi, 0);
    assert!(direction_word.lo <= 1);
    let direction = direction_word.lo == 1;
    let current = [inputs[1], inputs[2]];
    let sibling = [inputs[3], inputs[4]];
    if direction {
      outputs
        .extend_from_slice(&[sibling[0], sibling[1], current[0], current[1]]);
    } else {
      outputs
        .extend_from_slice(&[current[0], current[1], sibling[0], sibling[1]]);
    }
    DigestOrderRow { direction, current, sibling }
  }

  fn witness(&self, _rows: &[Self::Row], _nu: usize) -> SlotWitness {
    SlotWitness::DeferredToRows
  }
}

pub(crate) fn build_digest_order_r1cs(nu: usize) -> BlockR1cs {
  build_digest_order_plan().block_r1cs(nu)
}

pub(crate) fn generate_digest_order_witness(
  rows: &[DigestOrderRow],
  nu: usize,
) -> (Vec<F128>, Vec<F128>, Vec<F128>, Vec<u8>) {
  let plan = build_digest_order_plan();
  generate_boolean_witness(&plan, rows, nu, |row, bits| {
    bits[BIT_BASE] = row.direction;
    write_f128(bits, CURRENT_BASE, row.current[0]);
    write_f128(bits, CURRENT_BASE + 128, row.current[1]);
    write_f128(bits, SIBLING_BASE, row.sibling[0]);
    write_f128(bits, SIBLING_BASE + 128, row.sibling[1]);
  })
}

pub(crate) fn generate_digest_order_witness_into(
  rows: &[DigestOrderRow],
  nu: usize,
  dst: SlotWitnessDest<'_>,
) -> Vec<u8> {
  let plan = build_digest_order_plan();
  generate_boolean_witness_into(&plan, rows, nu, dst, |row, bits| {
    bits[BIT_BASE] = row.direction;
    write_f128(bits, CURRENT_BASE, row.current[0]);
    write_f128(bits, CURRENT_BASE + 128, row.current[1]);
    write_f128(bits, SIBLING_BASE, row.sibling[0]);
    write_f128(bits, SIBLING_BASE + 128, row.sibling[1]);
  })
}

fn build_digest_order_plan() -> BooleanR1csPlan {
  let mut builder =
    BooleanR1csBuilder::new(ORDER_K_LOG, ORDER_RESERVED_COLUMNS);
  builder.free_boolean_at(BIT_BASE);
  for column in CURRENT_BASE..SIBLING_BASE + 256 {
    builder.free_boolean_at(column);
  }
  let one = builder.alloc_constant_one();
  for bit in 0..256 {
    let current = CURRENT_BASE + bit;
    let sibling = SIBLING_BASE + bit;
    let selected =
      builder.product_of_parities(&[BIT_BASE], &[current, sibling]);
    builder.write_xor(LEFT_BASE + bit, &[current, selected], one);
    builder.write_xor(
      RIGHT_BASE + bit,
      &[current, sibling, LEFT_BASE + bit],
      one,
    );
  }
  builder.finish()
}

fn relation_inputs(path: &MerklePathV1) -> Vec<F128> {
  let packed_iv = pack8(&IV);
  let mut inputs = Vec::with_capacity(5 + 3 * path.siblings.len());
  inputs.extend_from_slice(&packed_iv);
  inputs.push(pack_params(0, 64, CHUNK_START | CHUNK_END | ROOT));
  inputs.extend_from_slice(&pack_digest(&path.leaf));
  for (level, sibling) in path.siblings.iter().enumerate() {
    inputs.push(F128::new(u64::from((path.index >> level) & 1), 0));
    inputs.extend_from_slice(&pack_digest(sibling));
  }
  inputs
}

fn relation_public(path: &MerklePathV1, root: &[u8; 32]) -> Vec<F128> {
  let mut public = relation_inputs(path);
  public.extend_from_slice(&pack_digest(root));
  public
}

fn pack_digest(digest: &[u8; 32]) -> [F128; 2] {
  [pack_bytes(&digest[..16]), pack_bytes(&digest[16..])]
}

fn native_root(path: &MerklePathV1) -> [u8; 32] {
  let mut current = path.leaf;
  for (level, sibling) in path.siblings.iter().enumerate() {
    let mut input = [0u8; 64];
    let (left, right) = if (path.index >> level) & 1 == 0 {
      (&current, sibling)
    } else {
      (sibling, &current)
    };
    input[..32].copy_from_slice(left);
    input[32..].copy_from_slice(right);
    current = *native_blake3::hash(&input).as_bytes();
  }
  current
}

fn validate_path(path: &MerklePathV1) -> Result<()> {
  validate_depth(path.siblings.len())?;
  if u64::from(path.index) >= 1u64 << path.siblings.len() {
    bail!(
      "Merkle index {} does not fit depth {}",
      path.index,
      path.siblings.len()
    );
  }
  Ok(())
}

fn validate_depth(depth: usize) -> Result<()> {
  if !(1..=MAX_DEPTH).contains(&depth) {
    bail!("Merkle depth {depth}; expected 1..={MAX_DEPTH}");
  }
  Ok(())
}

fn encode_bundle(bundle: &MerkleProofBundle) -> Result<Vec<u8>> {
  bincode::DefaultOptions::new()
    .with_fixint_encoding()
    .serialize(bundle)
    .context("encode Flock Merkle conformance proof bundle")
}

fn decode_bundle(bytes: &[u8]) -> Result<MerkleProofBundle> {
  bincode::DefaultOptions::new()
    .with_fixint_encoding()
    .with_limit(MAX_BUNDLE_BYTES as u64)
    .reject_trailing_bytes()
    .deserialize(bytes)
    .context("invalid Flock Merkle conformance proof bundle")
}

#[cfg(test)]
mod tests {
  use super::*;

  fn fixture() -> MerklePathV1 {
    MerklePathV1 {
      leaf: *native_blake3::hash(b"ix-stage3-merkle-leaf").as_bytes(),
      siblings: (0..4u8)
        .map(|level| *native_blake3::hash(&[0xa5, level]).as_bytes())
        .collect(),
      index: 0b1010,
    }
  }

  #[test]
  fn native_path_matches_manual_blake3_compression() {
    let path = fixture();
    let root = path.root().unwrap();
    assert_ne!(root, path.leaf);
    let mut changed = path;
    changed.index ^= 1;
    assert_ne!(changed.root().unwrap(), root);
  }

  #[test]
  fn digest_order_r1cs_rejects_direction_and_output_mutations() {
    let plan = build_digest_order_plan();
    let r1cs = plan.block_r1cs(3);
    let row = DigestOrderRow {
      direction: true,
      current: [F128::new(1, 2), F128::new(3, 4)],
      sibling: [F128::new(5, 6), F128::new(7, 8)],
    };
    let mut logical = vec![false; plan.k()];
    plan.fill_row(&mut logical, |bits| {
      bits[BIT_BASE] = row.direction;
      write_f128(bits, CURRENT_BASE, row.current[0]);
      write_f128(bits, CURRENT_BASE + 128, row.current[1]);
      write_f128(bits, SIBLING_BASE, row.sibling[0]);
      write_f128(bits, SIBLING_BASE + 128, row.sibling[1]);
    });
    let mut witness = vec![false; r1cs.n()];
    witness[..plan.k()].copy_from_slice(&logical);
    assert!(r1cs.satisfies(&witness));

    let mut wrong_direction = witness.clone();
    wrong_direction[BIT_BASE] ^= true;
    assert!(!r1cs.satisfies(&wrong_direction));
    let mut wrong_output = witness;
    wrong_output[LEFT_BASE + 17] ^= true;
    assert!(!r1cs.satisfies(&wrong_output));
  }

  #[test]
  fn artifact_parser_is_strict_before_crypto() {
    let path = fixture();
    let artifact = MerkleConformanceArtifactV1 {
      root: path.root().unwrap(),
      path,
      circuit_digest: [7; 32],
      proof_bundle_bytes: vec![1, 2, 3],
    };
    let mut bytes = artifact.to_bytes();
    assert!(MerkleConformanceArtifactV1::from_bytes(&bytes).is_err());
    bytes[0] ^= 1;
    assert!(MerkleConformanceArtifactV1::from_bytes(&bytes).is_err());
  }

  #[test]
  #[ignore = "real Flock BLAKE3 Merkle circuit proof; run explicitly"]
  fn real_merkle_path_round_trip_and_mutations() {
    let artifact = prove_merkle_conformance(&fixture()).expect("prove path");
    eprintln!(
      "Flock BLAKE3-Merkle conformance bundle: {} bytes",
      artifact.proof_bundle_bytes().len()
    );
    verify_merkle_conformance(&artifact).expect("verify path");
    let decoded =
      MerkleConformanceArtifactV1::from_bytes(&artifact.to_bytes()).unwrap();
    verify_merkle_conformance(&decoded).expect("verify decoded path");

    let mut wrong_sibling = decoded.clone();
    wrong_sibling.path.siblings[1][7] ^= 1;
    assert!(verify_merkle_conformance(&wrong_sibling).is_err());
    let mut wrong_index = decoded.clone();
    wrong_index.path.index ^= 1;
    assert!(verify_merkle_conformance(&wrong_index).is_err());
    let mut wrong_root = decoded.clone();
    wrong_root.root[0] ^= 1;
    assert!(verify_merkle_conformance(&wrong_root).is_err());
    let mut wrong_proof = decoded;
    let flip_at = wrong_proof.proof_bundle_bytes.len() / 2;
    wrong_proof.proof_bundle_bytes[flip_at] ^= 1;
    assert!(verify_merkle_conformance(&wrong_proof).is_err());
  }
}
