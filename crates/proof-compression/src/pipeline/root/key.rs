//! The trusted key of the aggregation backend whose roots compress: the
//! formal Aiur aggregation artifact (`crates/aiur`). Its batch policy, the
//! conditions beyond the STARK under which a batch proves one execution of
//! the artifact, decides which roots verify and which verifier circuits are
//! derived.
use super::Result;
use aiur::trace::stark::{MEMSEG_CHANNEL, VerifyingKey};
use multi_stark::{
  batch::{BatchPreamble, BatchProof},
  system::System,
  types::{CommitmentParameters, FriParameters, GoldilocksBlake3Config, Val},
};
use p3_field::PrimeCharacteristicRing;

/// A trusted aggregation backend key under the formal Aiur batch policy.
pub struct RootKey(VerifyingKey);

impl RootKey {
  pub fn from_bytes(bytes: &[u8]) -> Result<Self> {
    Ok(Self(VerifyingKey::from_bytes(bytes)?))
  }

  pub fn to_bytes(&self) -> Vec<u8> {
    self.0.to_bytes()
  }

  pub fn system(&self) -> &System<GoldilocksBlake3Config> {
    self.0.system()
  }

  pub fn num_circuits(&self) -> usize {
    self.system().circuits.len()
  }

  pub const fn commitment_parameters(&self) -> CommitmentParameters {
    self.0.commitment_parameters()
  }

  pub const fn fri_parameters(&self) -> FriParameters {
    self.0.fri_parameters()
  }

  /// Verify a batch proof of the single public `claim` under the policy.
  pub fn verify(
    &self,
    claim: &[Val],
    proof: &BatchProof<GoldilocksBlake3Config>,
  ) -> Result<()> {
    Ok(self.0.verify(&[claim.to_vec()], proof)?)
  }

  /// Check the policy for `preamble` with the single public `claim`,
  /// without a proof.
  pub fn validate_preamble(
    &self,
    claim: &[Val],
    preamble: &BatchPreamble<GoldilocksBlake3Config>,
  ) -> Result<()> {
    Ok(self.0.validate_preamble(&[claim.to_vec()], preamble)?)
  }

  /// The channel of the memory boundary messages the policy admits.
  pub fn memseg_channel(&self) -> Val {
    Val::from_u64(MEMSEG_CHANNEL)
  }

  /// Parameters of the FRI stage's outer proof: blowup 4, 100 queries and
  /// 20 query proof-of-work bits, fixed so that the first KZG stage, which
  /// verifies this proof, does not depend on the root key's parameters.
  /// The lowered verifier's degree-4 constraints need a blowup of at least 4.
  pub(in crate::pipeline) fn fri_stage_config(&self) -> GoldilocksBlake3Config {
    GoldilocksBlake3Config::new(
      CommitmentParameters { log_blowup: 2, cap_height: 0 },
      FriParameters {
        log_final_poly_len: 0,
        max_log_arity: 1,
        num_queries: 100,
        commit_proof_of_work_bits: 0,
        query_proof_of_work_bits: 20,
      },
    )
  }
}

impl From<VerifyingKey> for RootKey {
  fn from(key: VerifyingKey) -> Self {
    Self(key)
  }
}
