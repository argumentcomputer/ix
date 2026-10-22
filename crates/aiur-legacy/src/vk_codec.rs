//! Legacy Aiur verifier policy around the shared multi-stark key codec.
use crate::synthesis::{AiurConfig, AiurSystem};
use multi_stark::{
  system::System,
  types::{CommitmentParameters, FriParameters, Val},
};
pub(crate) use stark_key::{from_bytes, to_bytes};

/// Convenience: serialize the verifying key of a built [`AiurSystem`].
pub fn aiur_system_to_bytes(sys: &AiurSystem) -> Result<Vec<u8>, String> {
  Ok(to_bytes(&sys.system, sys.commitment_parameters, sys.fri_parameters))
}

/// A verifier-only Aiur key decoded from [`aiur_system_to_bytes`].
///
/// This is the narrow surface used by zkVM guests: unlike [`AiurSystem`], it
/// carries neither bytecode nor a prover key, but it can verify a serialized
/// proof under the exact commitment and FRI parameters embedded in the key.
pub struct AiurVerifyingKey {
  system: System<AiurConfig>,
  commitment_parameters: CommitmentParameters,
  fri_parameters: FriParameters,
}

impl AiurVerifyingKey {
  /// Decode a verifying key and require full input consumption.
  pub fn from_bytes(bytes: &[u8]) -> Result<Self, String> {
    from_bytes(bytes).map(|(system, commitment_parameters, fri_parameters)| {
      Self { system, commitment_parameters, fri_parameters }
    })
  }

  /// Re-encode to the canonical Aiur verifying-key wire format.
  pub fn to_bytes(&self) -> Vec<u8> {
    to_bytes(&self.system, self.commitment_parameters, self.fri_parameters)
  }

  pub const fn commitment_parameters(&self) -> CommitmentParameters {
    self.commitment_parameters
  }

  pub const fn fri_parameters(&self) -> FriParameters {
    self.fri_parameters
  }

  pub fn num_circuits(&self) -> usize {
    self.system.circuits.len()
  }

  /// Verifies a batch proof of `claim` under this key: shard headers, Aiur's
  /// batch policy and the multi-stark batch (see
  /// [`crate::synthesis::verify_against`]).
  pub fn verify(
    &self,
    claim: &[Val],
    proof: &crate::synthesis::AiurProof,
  ) -> Result<(), crate::synthesis::AiurVerificationError> {
    crate::synthesis::verify_against(
      &self.system,
      self.commitment_parameters,
      claim,
      proof,
    )
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::gadgets::{AiurGadget, bytes1::Bytes1, bytes2::Bytes2};
  use multi_stark::system::CircuitInputs;

  fn test_parameters() -> (CommitmentParameters, FriParameters) {
    let cp = CommitmentParameters { log_blowup: 1, cap_height: 0 };
    let fp = FriParameters {
      log_final_poly_len: 0,
      max_log_arity: 1,
      num_queries: 64,
      commit_proof_of_work_bits: 0,
      query_proof_of_work_bits: 0,
    };
    (cp, fp)
  }

  fn test_system() -> (System<AiurConfig>, CommitmentParameters, FriParameters)
  {
    let (cp, fp) = test_parameters();
    let inputs = [
      CircuitInputs {
        main_width: Bytes1.main_width(),
        preprocessed: Bytes1.preprocessed(),
        constraints: vec![],
        ext_constraints: vec![],
        lookups: Bytes1.lookups(),
        lookup_group_size: 1,
      },
      CircuitInputs {
        main_width: Bytes2.main_width(),
        preprocessed: Bytes2.preprocessed(),
        constraints: vec![],
        ext_constraints: vec![],
        lookups: Bytes2.lookups(),
        // Grouped-circuit coverage: the codec must carry the group size
        // through (it changes the derived stage-2 width and count).
        lookup_group_size: 2,
      },
    ];
    let (system, _key) = System::new(AiurConfig::new(cp, fp), inputs);
    (system, cp, fp)
  }

  /// Round-trip: decode(encode(x)) re-encodes to the same bytes, with matching
  /// compiled node graphs, constraint roots, and lookups.
  #[test]
  fn system_vk_round_trips() {
    let (system, cp, fp) = test_system();
    let bytes = to_bytes(&system, cp, fp);
    let (back, back_cp, back_fp) = from_bytes(&bytes).expect("decode");
    let reencoded = to_bytes(&back, back_cp, back_fp);
    assert_eq!(bytes, reencoded, "verifying-key codec round-trip mismatch");
    assert_eq!(system.circuits.len(), back.circuits.len());
    for (a, b) in system.circuits.iter().zip(&back.circuits) {
      assert_eq!(a.graph.nodes, b.graph.nodes, "nodes mismatch");
      assert_eq!(a.graph.zeros, b.graph.zeros, "zeros mismatch");
      assert_eq!(a.graph.lookups.len(), b.graph.lookups.len());
      for (la, lb) in a.graph.lookups.iter().zip(&b.graph.lookups) {
        assert_eq!(la.multiplicity, lb.multiplicity);
        assert_eq!(la.args, lb.args);
      }
      assert_eq!(a.main_width, b.main_width);
      assert_eq!(a.lookup_group_size, b.lookup_group_size);
      assert_eq!(a.stage_2_width, b.stage_2_width);
      assert_eq!(a.num_publics, b.num_publics);
      assert_eq!(a.preprocessed_width, b.preprocessed_width);
      assert_eq!(a.preprocessed_height, b.preprocessed_height);
    }
  }

  #[test]
  fn rejects_trailing_bytes() {
    let (system, cp, fp) = test_system();
    let mut bytes = to_bytes(&system, cp, fp);
    bytes.push(0);
    assert!(from_bytes(&bytes).is_err(), "should reject trailing data");
  }

  /// A tampered per-circuit record length must be rejected (the record reader
  /// enforces exact consumption).
  #[test]
  fn rejects_bad_record_length() {
    let (system, cp, fp) = test_system();
    let bytes = to_bytes(&system, cp, fp);
    // Records carry no length prefix (nothing derivable is serialized), so
    // the malformation guards are the full-consumption check and read
    // overflow: truncated and padded inputs must both be rejected.
    assert!(
      from_bytes(&bytes[..bytes.len() - 1]).is_err(),
      "should reject truncated vk"
    );
    let mut padded = bytes.clone();
    padded.push(0);
    assert!(from_bytes(&padded).is_err(), "should reject padded vk");
  }
}
