//! SP1 terminal guest for one converged Ix aggregate root.
//!
//! The prover supplies one Aiur recursion verifying key, its five FRI
//! parameters, the uniform 18-word `ix_aggr` outer claim, and the compact
//! Multi-STARK proof. The guest decodes and verifies all four values, then
//! commits a domain-separated public statement:
//!
//! `IXROOT01 || blake3(aiur_vk) || fri_parameters || outer_claim`.
//!
//! A failed decode, parameter mismatch, non-canonical field word, or invalid
//! proof aborts execution and therefore cannot produce an SP1 proof.

#![no_main]
sp1_zkvm::entrypoint!(main);

use aiur::{G, synthesis::AiurProof, vk_codec::AiurVerifyingKey};
use multi_stark::{
  p3_field::{PrimeCharacteristicRing, PrimeField64},
  types::FriParameters,
};

const PUBLIC_VALUES_DOMAIN: &[u8; 8] = b"IXROOT01";
const OUTER_CLAIM_ELEMENTS: usize = 18;

pub fn main() {
  let vk_bytes = sp1_zkvm::io::read_vec();
  let fri_bytes = sp1_zkvm::io::read_vec();
  let claim_bytes = sp1_zkvm::io::read_vec();
  let proof_bytes = sp1_zkvm::io::read_vec();

  assert_eq!(fri_bytes.len(), 40, "FRI parameters must be five u64 words");
  let fri_word = |i: usize| {
    let word = u64::from_le_bytes(
      fri_bytes[8 * i..8 * (i + 1)].try_into().expect("FRI word"),
    );
    usize::try_from(word).expect("FRI parameter exceeds usize")
  };
  let fri_parameters = FriParameters {
    log_final_poly_len: fri_word(0),
    max_log_arity: fri_word(1),
    num_queries: fri_word(2),
    commit_proof_of_work_bits: fri_word(3),
    query_proof_of_work_bits: fri_word(4),
  };

  assert_eq!(
    claim_bytes.len(),
    OUTER_CLAIM_ELEMENTS * 8,
    "ix_aggr outer claim must contain exactly 18 Goldilocks words"
  );
  let claim: Vec<G> = claim_bytes
    .as_chunks::<8>()
    .0
    .iter()
    .map(|chunk| {
      let word = u64::from_le_bytes(*chunk);
      let value = G::from_u64(word);
      assert_eq!(
        value.as_canonical_u64(),
        word,
        "claim contains a non-canonical Goldilocks word"
      );
      value
    })
    .collect();

  println!("cycle-tracker-report-start: decode-vk");
  let vk = AiurVerifyingKey::from_bytes(&vk_bytes).expect("invalid Aiur vk");
  println!("cycle-tracker-report-end: decode-vk");

  let vk_fri = vk.fri_parameters();
  assert_eq!(fri_parameters.log_final_poly_len, vk_fri.log_final_poly_len);
  assert_eq!(fri_parameters.max_log_arity, vk_fri.max_log_arity);
  assert_eq!(fri_parameters.num_queries, vk_fri.num_queries);
  assert_eq!(
    fri_parameters.commit_proof_of_work_bits,
    vk_fri.commit_proof_of_work_bits
  );
  assert_eq!(
    fri_parameters.query_proof_of_work_bits,
    vk_fri.query_proof_of_work_bits
  );

  println!("cycle-tracker-report-start: decode-proof");
  let proof = AiurProof::from_bytes(&proof_bytes).expect("invalid Aiur proof");
  println!("cycle-tracker-report-end: decode-proof");

  println!("cycle-tracker-report-start: verify-root");
  vk.verify(&claim, &proof).expect("aggregate root verification failed");
  println!("cycle-tracker-report-end: verify-root");

  let mut public_values =
    Vec::with_capacity(8 + 32 + 40 + OUTER_CLAIM_ELEMENTS * 8);
  public_values.extend_from_slice(PUBLIC_VALUES_DOMAIN);
  public_values.extend_from_slice(blake3::hash(&vk_bytes).as_bytes());
  public_values.extend_from_slice(&fri_bytes);
  for value in claim {
    public_values.extend_from_slice(&value.as_canonical_u64().to_le_bytes());
  }
  sp1_zkvm::io::commit_slice(&public_values);
}
