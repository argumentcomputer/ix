//! SP1 guest that re-verifies a batch of Aiur multi-STARK proofs in-circuit.
//!
//! Reads length-delimited inputs from the prover (all untrusted):
//!   1. verifying-key bytes (`aiur::vk_codec::aiur_system_to_bytes` format;
//!      includes the commitment parameters). ONE vk for the whole batch —
//!      every Ix shard proof is a statement of the same `verify_claim`
//!      system.
//!   2. FRI parameters, 5 u64 LE values
//!   3. batch size `n`, u32 LE (4 bytes)
//!   4. then `n` times: claim (one canonical u64 LE per Goldilocks
//!      element), proof bytes (`multi_stark::prover::Proof::to_bytes`)
//!
//! On success commits
//!   `blake3(vk) || fri params || n || (claim_len_u32 || claim)*`
//! re-encoded from the parsed values so no non-canonical byte encoding of
//! the same statement exists. Any verification failure panics, which fails
//! the SP1 proof — the batch is all-or-nothing.
//!
//! The vk is decoded ONCE; per-proof work is deserialization + the
//! multi-stark verifier (Fiat-Shamir transcript + FRI at the vk's own
//! parameters — the secure regime, nothing relaxed for recursion).

#![no_main]
sp1_zkvm::entrypoint!(main);

use aiur::{G, synthesis::AiurProof, vk_codec::AiurVerifyingKey};
use multi_stark::{
  p3_field::{PrimeCharacteristicRing, PrimeField64},
  types::FriParameters,
};

pub fn main() {
  let vk_bytes = sp1_zkvm::io::read_vec();
  let fri_bytes = sp1_zkvm::io::read_vec();
  let n_bytes = sp1_zkvm::io::read_vec();

  assert_eq!(fri_bytes.len(), 40, "fri parameters must be 5 u64 LE values");
  let fri = |i: usize| {
    u64::from_le_bytes(fri_bytes[8 * i..8 * (i + 1)].try_into().unwrap())
      as usize
  };
  let fri_parameters = FriParameters {
    log_final_poly_len: fri(0),
    max_log_arity: fri(1),
    num_queries: fri(2),
    commit_proof_of_work_bits: fri(3),
    query_proof_of_work_bits: fri(4),
  };

  assert_eq!(n_bytes.len(), 4, "batch size must be u32 LE");
  let n = u32::from_le_bytes(n_bytes.try_into().unwrap());
  assert!(n > 0, "empty batch");

  println!("cycle-tracker-report-start: decode-vk");
  let vk = AiurVerifyingKey::from_bytes(&vk_bytes).expect("bad verifying key");
  println!("cycle-tracker-report-end: decode-vk");

  // The FRI parameters are serialized inside the vk (and thus covered by
  // its digest); the separately-supplied input values must agree with them,
  // so the pinned public values below describe the parameters actually used.
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

  // Public statement: which vk, under which FRI parameters, proved which
  // batch of claims. The vk digest covers the commitment and FRI
  // parameters (serialized inside the vk bytes); the FRI input values are
  // additionally pinned after the equality check above. Consumers must
  // check the digest and parameters against known-good values.
  let mut public_values = Vec::with_capacity(32 + 40 + 4);
  public_values.extend_from_slice(blake3::hash(&vk_bytes).as_bytes());
  for i in 0..5 {
    public_values.extend_from_slice(&(fri(i) as u64).to_le_bytes());
  }
  public_values.extend_from_slice(&n.to_le_bytes());

  for k in 0..n {
    let claim_bytes = sp1_zkvm::io::read_vec();
    let proof_bytes = sp1_zkvm::io::read_vec();

    assert_eq!(claim_bytes.len() % 8, 0, "claim must be u64 LE elements");
    let claim: Vec<G> = claim_bytes
      .chunks_exact(8)
      .map(|c| G::from_u64(u64::from_le_bytes(c.try_into().unwrap())))
      .collect();

    println!("cycle-tracker-report-start: decode-proof-{k}");
    let proof = AiurProof::from_bytes(&proof_bytes).expect("bad proof");
    println!("cycle-tracker-report-end: decode-proof-{k}");

    println!("cycle-tracker-report-start: verify-{k}");
    vk.verify(&claim, &proof).expect("Aiur proof verification failed");
    println!("cycle-tracker-report-end: verify-{k}");

    public_values.extend_from_slice(&(claim.len() as u32).to_le_bytes());
    for g in &claim {
      public_values.extend_from_slice(&g.as_canonical_u64().to_le_bytes());
    }
  }

  sp1_zkvm::io::commit_slice(&public_values);
}
