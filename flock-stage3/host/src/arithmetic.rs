//! Real Flock circuit proof for the custom Goldilocks arithmetic tables.
//!
//! This remains a labelled conformance artifact, not a Stage 3 proof. It
//! exists to ensure new non-native field tables survive the complete union,
//! wiring, PCS, Fiat-Shamir, serialization, and verifier path before verifier
//! phases depend on them.

use anyhow::{Context, Result, bail};
use bincode::Options;
use flock_prover::{
  challenger::FsChallenger,
  circuit::builder::{CircuitShape, ShapeBuilder, SlotId},
  field::F128,
  pcs::Commitment,
  proof::R1csProofCircuitMerged,
  prover::{self, UnionSlotProverInput},
  union::UnionInstance,
  verifier,
};
use serde::{Deserialize, Serialize};

use crate::{
  ARITHMETIC_CONFORMANCE_TRANSCRIPT_DOMAIN, FlockConfigV1,
  binding::pcs_params,
  extension::{
    GoldilocksCircuitSlots, GoldilocksLaneRepackGate, build_lane_repack_r1cs,
    generate_lane_repack_witness, goldilocks_ext2_mul,
  },
  goldilocks::{
    CanonicalGoldilocksPairGate, GOLDILOCKS_MODULUS, GoldilocksAddPairGate,
    build_canonical_pair_r1cs, build_goldilocks_add_r1cs,
    generate_canonical_pair_witness, generate_goldilocks_add_witness,
  },
  multiplication::{
    GoldilocksMulPairGate, build_goldilocks_mul_r1cs,
    generate_goldilocks_mul_witness,
  },
};

pub const ARITHMETIC_CONFORMANCE_ARTIFACT_MAGIC: &[u8; 8] = b"IXFLKGA1";
const ARTIFACT_VERSION: u16 = 1;
const FIXED_PREFIX_BYTES: usize = 8 + 2 + 32 + 2 + 2 + 2;
const FIXED_SUFFIX_BYTES: usize = 32 + 8;
const OPERAND_BYTES: usize = 4 * 8;
const MAX_ADDITIONS: usize = 64;
const MAX_MULTIPLICATIONS: usize = 64;
const MAX_EXTENSION_MULTIPLICATIONS: usize = 16;
const MAX_BUNDLE_BYTES: usize = 64 * 1024 * 1024;
// The shared row domain leaves ample virtual address space for the largest
// custom table and always reaches Flock's audited Fast128 geometries.
// Declared row counts remain exact; this only supplies zero padding.
const MIN_SECURE_NU: usize = 10;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct GoldilocksAddPairV1 {
  pub left: [u64; 2],
  pub right: [u64; 2],
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct GoldilocksMulPairV1 {
  pub left: [u64; 2],
  pub right: [u64; 2],
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct GoldilocksExt2MulV1 {
  pub left: [u64; 2],
  pub right: [u64; 2],
}

impl GoldilocksExt2MulV1 {
  pub fn result(self) -> [u64; 2] {
    let result = goldilocks_ext2_mul(
      F128::new(self.left[0], self.left[1]),
      F128::new(self.right[0], self.right[1]),
    );
    [result.lo, result.hi]
  }
}

/// A real Flock proof of public lane-wise Goldilocks arithmetic.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ArithmeticConformanceArtifactV1 {
  additions: Vec<GoldilocksAddPairV1>,
  multiplications: Vec<GoldilocksMulPairV1>,
  extension_multiplications: Vec<GoldilocksExt2MulV1>,
  circuit_digest: [u8; 32],
  proof_bundle_bytes: Vec<u8>,
}

impl ArithmeticConformanceArtifactV1 {
  pub fn to_bytes(&self) -> Vec<u8> {
    let mut bytes = Vec::with_capacity(
      FIXED_PREFIX_BYTES
        + (self.additions.len()
          + self.multiplications.len()
          + self.extension_multiplications.len())
          * OPERAND_BYTES
        + FIXED_SUFFIX_BYTES
        + self.proof_bundle_bytes.len(),
    );
    bytes.extend_from_slice(ARITHMETIC_CONFORMANCE_ARTIFACT_MAGIC);
    bytes.extend_from_slice(&ARTIFACT_VERSION.to_le_bytes());
    bytes.extend_from_slice(&FlockConfigV1.digest());
    bytes.extend_from_slice(
      &u16::try_from(self.additions.len())
        .expect("addition count")
        .to_le_bytes(),
    );
    bytes.extend_from_slice(
      &u16::try_from(self.multiplications.len())
        .expect("multiplication count")
        .to_le_bytes(),
    );
    bytes.extend_from_slice(
      &u16::try_from(self.extension_multiplications.len())
        .expect("extension multiplication count")
        .to_le_bytes(),
    );
    for addition in &self.additions {
      encode_operands(&mut bytes, addition.left, addition.right);
    }
    for multiplication in &self.multiplications {
      encode_operands(&mut bytes, multiplication.left, multiplication.right);
    }
    for multiplication in &self.extension_multiplications {
      encode_operands(&mut bytes, multiplication.left, multiplication.right);
    }
    bytes.extend_from_slice(&self.circuit_digest);
    bytes.extend_from_slice(
      &u64::try_from(self.proof_bundle_bytes.len())
        .expect("proof bundle length")
        .to_le_bytes(),
    );
    bytes.extend_from_slice(&self.proof_bundle_bytes);
    bytes
  }

  pub fn from_bytes(bytes: &[u8]) -> Result<Self> {
    if bytes.len() < FIXED_PREFIX_BYTES + FIXED_SUFFIX_BYTES {
      bail!("truncated Flock arithmetic conformance artifact");
    }
    if &bytes[..8] != ARITHMETIC_CONFORMANCE_ARTIFACT_MAGIC {
      bail!("invalid Flock arithmetic conformance artifact magic");
    }
    let version = u16::from_le_bytes(bytes[8..10].try_into().unwrap());
    if version != ARTIFACT_VERSION {
      bail!("unsupported Flock arithmetic artifact version {version}");
    }
    if bytes[10..42] != FlockConfigV1.digest() {
      bail!("Flock arithmetic artifact configuration mismatch");
    }
    let addition_count =
      usize::from(u16::from_le_bytes(bytes[42..44].try_into().unwrap()));
    let multiplication_count =
      usize::from(u16::from_le_bytes(bytes[44..46].try_into().unwrap()));
    let extension_multiplication_count =
      usize::from(u16::from_le_bytes(bytes[46..48].try_into().unwrap()));
    validate_counts(
      addition_count,
      multiplication_count,
      extension_multiplication_count,
    )?;
    let operation_count =
      addition_count + multiplication_count + extension_multiplication_count;
    let operands_end = FIXED_PREFIX_BYTES
      .checked_add(operation_count * OPERAND_BYTES)
      .ok_or_else(|| anyhow::anyhow!("arithmetic operand length overflow"))?;
    let suffix_end = operands_end
      .checked_add(FIXED_SUFFIX_BYTES)
      .ok_or_else(|| anyhow::anyhow!("arithmetic artifact length overflow"))?;
    if bytes.len() < suffix_end {
      bail!("truncated Flock arithmetic operands or proof header");
    }
    let mut additions = Vec::with_capacity(addition_count);
    let mut multiplications = Vec::with_capacity(multiplication_count);
    let mut extension_multiplications =
      Vec::with_capacity(extension_multiplication_count);
    let (encoded_operations, remainder) =
      bytes[FIXED_PREFIX_BYTES..operands_end].as_chunks::<OPERAND_BYTES>();
    debug_assert!(remainder.is_empty());
    for encoded in &encoded_operations[..addition_count] {
      let (left, right) = decode_operands(encoded);
      let addition = GoldilocksAddPairV1 { left, right };
      validate_operands(addition.left, addition.right)?;
      additions.push(addition);
    }
    let multiplication_end = addition_count + multiplication_count;
    for encoded in &encoded_operations[addition_count..multiplication_end] {
      let (left, right) = decode_operands(encoded);
      let multiplication = GoldilocksMulPairV1 { left, right };
      validate_operands(multiplication.left, multiplication.right)?;
      multiplications.push(multiplication);
    }
    for encoded in &encoded_operations[multiplication_end..] {
      let (left, right) = decode_operands(encoded);
      let multiplication = GoldilocksExt2MulV1 { left, right };
      validate_operands(multiplication.left, multiplication.right)?;
      extension_multiplications.push(multiplication);
    }
    let mut circuit_digest = [0u8; 32];
    circuit_digest.copy_from_slice(&bytes[operands_end..operands_end + 32]);
    let bundle_len = usize::try_from(u64::from_le_bytes(
      bytes[operands_end + 32..suffix_end].try_into().unwrap(),
    ))
    .map_err(|error| {
      anyhow::anyhow!("proof bundle length does not fit usize: {error}")
    })?;
    if bundle_len == 0 || bundle_len > MAX_BUNDLE_BYTES {
      bail!("invalid Flock arithmetic proof bundle length {bundle_len}");
    }
    let expected_len = suffix_end
      .checked_add(bundle_len)
      .ok_or_else(|| anyhow::anyhow!("arithmetic proof length overflow"))?;
    if bytes.len() != expected_len {
      bail!(
        "Flock arithmetic artifact is {} bytes; header declares {expected_len}",
        bytes.len()
      );
    }
    let proof_bundle_bytes = bytes[suffix_end..].to_vec();
    decode_bundle(&proof_bundle_bytes)
      .context("decode Flock arithmetic conformance proof bundle")?;
    Ok(Self {
      additions,
      multiplications,
      extension_multiplications,
      circuit_digest,
      proof_bundle_bytes,
    })
  }

  pub fn additions(&self) -> &[GoldilocksAddPairV1] {
    &self.additions
  }

  pub fn multiplications(&self) -> &[GoldilocksMulPairV1] {
    &self.multiplications
  }

  pub fn extension_multiplications(&self) -> &[GoldilocksExt2MulV1] {
    &self.extension_multiplications
  }

  pub fn circuit_digest(&self) -> &[u8; 32] {
    &self.circuit_digest
  }

  pub fn proof_bundle_bytes(&self) -> &[u8] {
    &self.proof_bundle_bytes
  }
}

#[derive(Serialize, Deserialize)]
struct ArithmeticProofBundle {
  commitment: Commitment,
  proof: R1csProofCircuitMerged,
}

pub fn prove_arithmetic_conformance(
  additions: &[GoldilocksAddPairV1],
  multiplications: &[GoldilocksMulPairV1],
  extension_multiplications: &[GoldilocksExt2MulV1],
) -> Result<ArithmeticConformanceArtifactV1> {
  validate_operations(additions, multiplications, extension_multiplications)?;
  let relation = ArithmeticRelation::build(
    additions.len(),
    multiplications.len(),
    extension_multiplications.len(),
  )?;
  let inputs =
    relation_inputs(additions, multiplications, extension_multiplications);
  let witness = relation.shape.run(&inputs, &[]);
  relation.ensure_registry_order()?;

  let add_rows = witness.rows::<GoldilocksAddPairGate>(relation.add_slot);
  let mul_rows = witness.rows::<GoldilocksMulPairGate>(relation.mul_slot);
  let repack_rows =
    witness.rows::<GoldilocksLaneRepackGate>(relation.repack_slot);
  let canonical_rows =
    witness.rows::<CanonicalGoldilocksPairGate>(relation.canonical_slot);
  let add_r1cs = build_goldilocks_add_r1cs(relation.nu);
  let add_lincheck = add_r1cs.csc_lincheck_circuit();
  let mul_r1cs = build_goldilocks_mul_r1cs(relation.nu);
  let mul_lincheck = mul_r1cs.csc_lincheck_circuit();
  let repack_r1cs = build_lane_repack_r1cs(relation.nu);
  let repack_lincheck = repack_r1cs.csc_lincheck_circuit();
  let canonical_r1cs = build_canonical_pair_r1cs(relation.nu);
  let canonical_lincheck = canonical_r1cs.csc_lincheck_circuit();
  let union =
    UnionInstance::new(&relation.shape.registry, relation.shape.counts.clone());
  let params = pcs_params(&union);
  let mut challenger =
    FsChallenger::with_chained_blake3(ARITHMETIC_CONFORMANCE_TRANSCRIPT_DOMAIN);
  let (proof, commitment, _) = prover::prove_fast_ligerito_union_circuit(
    &union,
    &relation.shape.circuit,
    &witness.public,
    &params,
    vec![
      UnionSlotProverInput::new(
        generate_goldilocks_mul_witness(mul_rows, relation.nu),
        mul_lincheck,
      ),
      UnionSlotProverInput::new(
        generate_goldilocks_add_witness(add_rows, relation.nu),
        add_lincheck,
      ),
      UnionSlotProverInput::new(
        generate_lane_repack_witness(repack_rows, relation.nu),
        repack_lincheck,
      ),
      UnionSlotProverInput::new(
        generate_canonical_pair_witness(canonical_rows, relation.nu),
        canonical_lincheck,
      ),
    ],
    Vec::new(),
    &mut challenger,
  );
  let proof_bundle_bytes =
    encode_bundle(&ArithmeticProofBundle { commitment, proof })?;
  if proof_bundle_bytes.len() > MAX_BUNDLE_BYTES {
    bail!("Flock arithmetic proof bundle exceeds {MAX_BUNDLE_BYTES} bytes");
  }
  Ok(ArithmeticConformanceArtifactV1 {
    additions: additions.to_vec(),
    multiplications: multiplications.to_vec(),
    extension_multiplications: extension_multiplications.to_vec(),
    circuit_digest: relation.shape.circuit.digest(),
    proof_bundle_bytes,
  })
}

pub fn verify_arithmetic_conformance(
  artifact: &ArithmeticConformanceArtifactV1,
) -> Result<()> {
  validate_operations(
    &artifact.additions,
    &artifact.multiplications,
    &artifact.extension_multiplications,
  )?;
  let relation = ArithmeticRelation::build(
    artifact.additions.len(),
    artifact.multiplications.len(),
    artifact.extension_multiplications.len(),
  )?;
  relation.ensure_registry_order()?;
  if artifact.circuit_digest != relation.shape.circuit.digest() {
    bail!("Flock arithmetic conformance circuit digest mismatch");
  }
  let witness = relation.shape.run(
    &relation_inputs(
      &artifact.additions,
      &artifact.multiplications,
      &artifact.extension_multiplications,
    ),
    &[],
  );
  let bundle = decode_bundle(&artifact.proof_bundle_bytes)
    .context("decode Flock arithmetic conformance proof bundle")?;
  let add_r1cs = build_goldilocks_add_r1cs(relation.nu);
  let add_lincheck = add_r1cs.csc_lincheck_circuit();
  let mul_r1cs = build_goldilocks_mul_r1cs(relation.nu);
  let mul_lincheck = mul_r1cs.csc_lincheck_circuit();
  let repack_r1cs = build_lane_repack_r1cs(relation.nu);
  let repack_lincheck = repack_r1cs.csc_lincheck_circuit();
  let canonical_r1cs = build_canonical_pair_r1cs(relation.nu);
  let canonical_lincheck = canonical_r1cs.csc_lincheck_circuit();
  let linchecks: [&dyn flock_prover::lincheck::LincheckCircuit; 4] =
    [mul_lincheck, add_lincheck, repack_lincheck, canonical_lincheck];
  let union =
    UnionInstance::new(&relation.shape.registry, relation.shape.counts.clone());
  let params = pcs_params(&union);
  let mut challenger =
    FsChallenger::with_chained_blake3(ARITHMETIC_CONFORMANCE_TRANSCRIPT_DOMAIN);
  verifier::verify_ligerito_union_circuit(
    &union,
    &relation.shape.circuit,
    &witness.public,
    &linchecks,
    &bundle.commitment,
    &bundle.proof,
    &params,
    &mut challenger,
  )
  .map_err(|error| {
    anyhow::anyhow!("Flock arithmetic conformance proof rejected: {error:?}")
  })?;
  Ok(())
}

struct ArithmeticRelation {
  shape: CircuitShape,
  add_slot: SlotId,
  mul_slot: SlotId,
  canonical_slot: SlotId,
  repack_slot: SlotId,
  nu: usize,
}

impl ArithmeticRelation {
  fn build(
    addition_count: usize,
    multiplication_count: usize,
    extension_multiplication_count: usize,
  ) -> Result<Self> {
    validate_counts(
      addition_count,
      multiplication_count,
      extension_multiplication_count,
    )?;
    let row_bound = [
      addition_count + 5 * extension_multiplication_count,
      multiplication_count + 2 * extension_multiplication_count,
      3 * addition_count
        + 3 * multiplication_count
        + 9 * extension_multiplication_count,
      3 * extension_multiplication_count,
    ]
    .into_iter()
    .max()
    .unwrap();
    let nu = usize::try_from(row_bound.next_power_of_two().ilog2())
      .unwrap()
      .max(MIN_SECURE_NU);
    let mut builder = ShapeBuilder::new(nu);
    let slots = GoldilocksCircuitSlots::declare(&mut builder, nu);
    for _ in 0..addition_count {
      let left = builder.public_input();
      let right = builder.public_input();
      for value in [left, right] {
        slots.assert_canonical(&mut builder, value);
      }
      let result = slots.add(&mut builder, left, right);
      builder.publish(result);
    }
    for _ in 0..multiplication_count {
      let left = builder.public_input();
      let right = builder.public_input();
      for value in [left, right] {
        slots.assert_canonical(&mut builder, value);
      }
      let result = slots.mul(&mut builder, left, right);
      builder.publish(result);
    }
    for _ in 0..extension_multiplication_count {
      let left = builder.public_input();
      let right = builder.public_input();
      let result = slots.ext2_mul(&mut builder, left, right);
      builder.publish(result);
    }
    let shape = builder.finish().map_err(|error| {
      anyhow::anyhow!("build Flock arithmetic conformance circuit: {error:?}")
    })?;
    Ok(Self {
      shape,
      add_slot: slots.add,
      mul_slot: slots.mul,
      canonical_slot: slots.canonical,
      repack_slot: slots.repack,
      nu,
    })
  }

  fn ensure_registry_order(&self) -> Result<()> {
    // Registry::new sorts Boolean tables by descending k_log.
    if self.shape.registry_slot(self.mul_slot) != 0
      || self.shape.registry_slot(self.add_slot) != 1
      || self.shape.registry_slot(self.repack_slot) != 2
      || self.shape.registry_slot(self.canonical_slot) != 3
    {
      bail!("unexpected Flock arithmetic table registry order");
    }
    Ok(())
  }
}

fn relation_inputs(
  additions: &[GoldilocksAddPairV1],
  multiplications: &[GoldilocksMulPairV1],
  extension_multiplications: &[GoldilocksExt2MulV1],
) -> Vec<F128> {
  let mut inputs = Vec::with_capacity(
    1 + 2
      * (additions.len()
        + multiplications.len()
        + extension_multiplications.len()),
  );
  inputs.push(F128::ZERO);
  for addition in additions {
    inputs.push(F128::new(addition.left[0], addition.left[1]));
    inputs.push(F128::new(addition.right[0], addition.right[1]));
  }
  for multiplication in multiplications {
    inputs.push(F128::new(multiplication.left[0], multiplication.left[1]));
    inputs.push(F128::new(multiplication.right[0], multiplication.right[1]));
  }
  for multiplication in extension_multiplications {
    inputs.push(F128::new(multiplication.left[0], multiplication.left[1]));
    inputs.push(F128::new(multiplication.right[0], multiplication.right[1]));
  }
  inputs
}

fn validate_operations(
  additions: &[GoldilocksAddPairV1],
  multiplications: &[GoldilocksMulPairV1],
  extension_multiplications: &[GoldilocksExt2MulV1],
) -> Result<()> {
  validate_counts(
    additions.len(),
    multiplications.len(),
    extension_multiplications.len(),
  )?;
  for addition in additions {
    validate_operands(addition.left, addition.right)?;
  }
  for multiplication in multiplications {
    validate_operands(multiplication.left, multiplication.right)?;
  }
  for multiplication in extension_multiplications {
    validate_operands(multiplication.left, multiplication.right)?;
  }
  Ok(())
}

fn validate_counts(
  addition_count: usize,
  multiplication_count: usize,
  extension_multiplication_count: usize,
) -> Result<()> {
  if addition_count > MAX_ADDITIONS {
    bail!(
      "Flock arithmetic conformance has {addition_count} additions; maximum is {MAX_ADDITIONS}"
    );
  }
  if multiplication_count > MAX_MULTIPLICATIONS {
    bail!(
      "Flock arithmetic conformance has {multiplication_count} multiplications; maximum is {MAX_MULTIPLICATIONS}"
    );
  }
  if extension_multiplication_count > MAX_EXTENSION_MULTIPLICATIONS {
    bail!(
      "Flock arithmetic conformance has {extension_multiplication_count} extension multiplications; maximum is {MAX_EXTENSION_MULTIPLICATIONS}"
    );
  }
  if addition_count + multiplication_count + extension_multiplication_count == 0
  {
    bail!("Flock arithmetic conformance requires at least one operation");
  }
  Ok(())
}

fn validate_operands(left: [u64; 2], right: [u64; 2]) -> Result<()> {
  if left.iter().chain(&right).any(|&word| word >= GOLDILOCKS_MODULUS) {
    bail!("Flock arithmetic operand is not canonical Goldilocks");
  }
  Ok(())
}

fn encode_operands(bytes: &mut Vec<u8>, left: [u64; 2], right: [u64; 2]) {
  for word in [left[0], left[1], right[0], right[1]] {
    bytes.extend_from_slice(&word.to_le_bytes());
  }
}

fn decode_operands(encoded: &[u8; OPERAND_BYTES]) -> ([u64; 2], [u64; 2]) {
  let words: [u64; 4] = std::array::from_fn(|index| {
    let offset = index * 8;
    u64::from_le_bytes(encoded[offset..offset + 8].try_into().unwrap())
  });
  ([words[0], words[1]], [words[2], words[3]])
}

fn encode_bundle(bundle: &ArithmeticProofBundle) -> Result<Vec<u8>> {
  bincode::DefaultOptions::new()
    .with_fixint_encoding()
    .serialize(bundle)
    .context("encode Flock arithmetic conformance proof bundle")
}

fn decode_bundle(bytes: &[u8]) -> Result<ArithmeticProofBundle> {
  bincode::DefaultOptions::new()
    .with_fixint_encoding()
    .with_limit(MAX_BUNDLE_BYTES as u64)
    .reject_trailing_bytes()
    .deserialize(bytes)
    .context("invalid Flock arithmetic conformance proof bundle")
}

#[cfg(test)]
mod tests {
  use super::*;

  fn addition_fixture() -> Vec<GoldilocksAddPairV1> {
    (0..8u64)
      .map(|index| GoldilocksAddPairV1 {
        left: [index, GOLDILOCKS_MODULUS - 1 - index],
        right: [GOLDILOCKS_MODULUS - 1 - index, index + 1],
      })
      .collect()
  }

  fn multiplication_fixture() -> Vec<GoldilocksMulPairV1> {
    (0..4u64)
      .map(|index| GoldilocksMulPairV1 {
        left: [index + 1, GOLDILOCKS_MODULUS - 1 - index],
        right: [GOLDILOCKS_MODULUS - 2 - index, index + 3],
      })
      .collect()
  }

  fn extension_multiplication_fixture() -> Vec<GoldilocksExt2MulV1> {
    vec![
      GoldilocksExt2MulV1 { left: [3, 5], right: [7, 11] },
      GoldilocksExt2MulV1 {
        left: [GOLDILOCKS_MODULUS - 1, 17],
        right: [23, GOLDILOCKS_MODULUS - 2],
      },
    ]
  }

  #[test]
  fn artifact_parser_is_strict_before_crypto() {
    let artifact = ArithmeticConformanceArtifactV1 {
      additions: addition_fixture(),
      multiplications: multiplication_fixture(),
      extension_multiplications: extension_multiplication_fixture(),
      circuit_digest: [7; 32],
      proof_bundle_bytes: vec![1, 2, 3],
    };
    let mut bytes = artifact.to_bytes();
    assert!(ArithmeticConformanceArtifactV1::from_bytes(&bytes).is_err());
    bytes[0] ^= 1;
    assert!(ArithmeticConformanceArtifactV1::from_bytes(&bytes).is_err());
  }

  #[test]
  #[ignore = "real Flock arithmetic circuit proof; run explicitly"]
  fn real_goldilocks_arithmetic_round_trip_and_mutations() {
    let artifact = prove_arithmetic_conformance(
      &addition_fixture(),
      &multiplication_fixture(),
      &extension_multiplication_fixture(),
    )
    .expect("prove arithmetic");
    eprintln!(
      "Flock Goldilocks-arithmetic conformance bundle: {} bytes",
      artifact.proof_bundle_bytes().len()
    );
    verify_arithmetic_conformance(&artifact).expect("verify arithmetic");

    let bytes = artifact.to_bytes();
    let decoded = ArithmeticConformanceArtifactV1::from_bytes(&bytes).unwrap();
    verify_arithmetic_conformance(&decoded).expect("verify decoded arithmetic");

    let mut wrong_operand = decoded.clone();
    wrong_operand.additions[0].left[0] ^= 1;
    assert!(verify_arithmetic_conformance(&wrong_operand).is_err());

    let mut wrong_multiplication = decoded.clone();
    wrong_multiplication.multiplications[0].right[1] ^= 1;
    assert!(verify_arithmetic_conformance(&wrong_multiplication).is_err());

    let mut wrong_extension = decoded.clone();
    wrong_extension.extension_multiplications[0].left[1] ^= 1;
    assert!(verify_arithmetic_conformance(&wrong_extension).is_err());

    let mut wrong_proof = decoded;
    let flip_at = wrong_proof.proof_bundle_bytes.len() / 2;
    wrong_proof.proof_bundle_bytes[flip_at] ^= 1;
    assert!(verify_arithmetic_conformance(&wrong_proof).is_err());
  }
}
