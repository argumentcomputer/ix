//! Host side of the range-sum recursion (`Ix/Aggr/Circuit.lean`, shapes
//! 10–12): the advice a recursion node needs to verify shards `[lo, hi)` of
//! one batch, and the statement it publishes about them.
//!
//! A batch proof is `preamble ‖ proofs` on the wire (bincode, fixed-width
//! little-endian integers). The preamble — every shard's header and the
//! verifier-side messages — is what fixes the batch challenges, so a node
//! binds the batch by the preamble's Blake3 digest and re-derives the
//! challenges from the preamble bytes it hashes; the proofs of its range are
//! plain advice.

use bincode::serde::encode_to_vec;
use multi_stark::p3_field::{BasedVectorSpace, PrimeField64};
use multi_stark::types::ExtVal;

use crate::{G, synthesis::AiurProof};

/// The byte every range statement opens with. `Ix.Claim` tags live in
/// `0xE0..=0xF?`, so a range statement never parses as a `CheckEnv` claim.
pub const RANGE_STATEMENT_TAG: u8 = 0x52;

/// The batch preamble as the in-circuit stream readers expect it: the
/// headers vector, then the messages vector — the prefix of the batch's
/// own wire encoding.
pub fn preamble_bytes(proof: &AiurProof) -> Result<Vec<u8>, String> {
  encode_to_vec(
    &proof.preamble,
    bincode::config::standard()
      .with_little_endian()
      .with_fixed_int_encoding(),
  )
  .map_err(|e| format!("batch preamble serialization failed: {e}"))
}

/// The proofs of shards `[lo, hi)` as one length-prefixed vector, each
/// canonicalized exactly as the whole batch's encoding canonicalizes it.
pub fn proofs_slice_bytes(
  proof: &AiurProof,
  lo: usize,
  hi: usize,
) -> Result<Vec<u8>, String> {
  let shards = proof.proofs.get(lo..hi).ok_or_else(|| {
    format!(
      "shard range {lo}..{hi} exceeds the batch's {} shards",
      proof.proofs.len()
    )
  })?;
  let mut bytes = (shards.len() as u64).to_le_bytes().to_vec();
  for shard in shards {
    bytes.extend(
      shard
        .to_bytes()
        .map_err(|e| format!("shard proof serialization failed: {e}"))?,
    );
  }
  Ok(bytes)
}

/// The residual sum of shards `[lo, hi)`: each shard's last intermediate
/// accumulator, added in the challenge field.
pub fn range_residual(proof: &AiurProof, lo: usize, hi: usize) -> ExtVal {
  proof.proofs[lo..hi]
    .iter()
    .map(|shard| {
      shard
        .intermediate_accumulators
        .last()
        .copied()
        .expect("a shard proof has at least one active circuit")
    })
    .sum()
}

/// An extension-field element as two canonical little-endian `u64` limbs.
pub fn ext_bytes(value: ExtVal) -> Vec<u8> {
  let coefficients: &[G] = value.as_basis_coefficients_slice();
  coefficients
    .iter()
    .flat_map(|c| c.as_canonical_u64().to_le_bytes())
    .collect()
}

/// A range node's statement:
/// `tag ‖ blake3(preamble)(32) ‖ lo(u64 LE) ‖ hi(u64 LE) ‖ residual(16)`.
pub fn range_statement(
  preamble_digest: &[u8; 32],
  lo: usize,
  hi: usize,
  residual: ExtVal,
) -> Vec<u8> {
  let mut bytes = Vec::with_capacity(65);
  bytes.push(RANGE_STATEMENT_TAG);
  bytes.extend_from_slice(preamble_digest);
  bytes.extend((lo as u64).to_le_bytes());
  bytes.extend((hi as u64).to_le_bytes());
  bytes.extend(ext_bytes(residual));
  bytes
}

#[cfg(test)]
mod tests {
  use super::*;
  use multi_stark::p3_field::PrimeCharacteristicRing;

  #[test]
  fn statement_layout_is_fixed_width() {
    let digest = [7u8; 32];
    let residual = ExtVal::new([G::from_u64(5), G::from_u64(9)]);
    let bytes = range_statement(&digest, 3, 11, residual);
    assert_eq!(bytes.len(), 65);
    assert_eq!(bytes[0], RANGE_STATEMENT_TAG);
    assert_eq!(&bytes[1..33], &digest);
    assert_eq!(&bytes[33..41], &3u64.to_le_bytes());
    assert_eq!(&bytes[41..49], &11u64.to_le_bytes());
    assert_eq!(&bytes[49..57], &5u64.to_le_bytes());
    assert_eq!(&bytes[57..65], &9u64.to_le_bytes());
  }
}
