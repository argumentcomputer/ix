//! A byte-oriented Blake3 Fiat-Shamir transcript for the KZG backend.
//!
//! Absorb/squeeze over a hash chain: observations append canonical
//! bytes to a buffer; each sample hashes `state ‖ buffer` with Blake3,
//! reads 64 bytes of XOF output for a negligibly-biased field element
//! (wide reduction mod the ~2^255 modulus) plus a fresh 32-byte chain
//! state, and clears the buffer. Every observation therefore influences
//! every later sample, and consecutive samples differ through the
//! chained state.

use ark_bls12_381::Fr;
use ark_ff::PrimeField;
use ark_serialize::CanonicalSerialize;

use multi_stark::traits::Transcript;

use super::field::Scalar;
use super::pcs::KzgCommitment;

/// See the module docs.
#[derive(Clone)]
pub struct Blake3Transcript {
  state: [u8; 32],
  buffer: Vec<u8>,
}

impl Blake3Transcript {
  /// A fresh transcript. Domain separation and parameter binding are
  /// the configuration's job (it observes a seed right away).
  pub fn new() -> Self {
    Self { state: [0; 32], buffer: Vec::new() }
  }

  pub fn observe_bytes(&mut self, bytes: &[u8]) {
    self.buffer.extend_from_slice(bytes);
  }

  /// Absorb a canonically-serializable arkworks value (compressed).
  pub fn observe_canonical(&mut self, value: &impl CanonicalSerialize) {
    value
      .serialize_compressed(&mut self.buffer)
      .expect("serialization into a Vec cannot fail");
  }

  fn squeeze(&mut self) -> Fr {
    let mut hasher = blake3::Hasher::new();
    hasher.update(&self.state);
    hasher.update(&self.buffer);
    self.buffer.clear();
    let mut output = hasher.finalize_xof();
    let mut wide = [0u8; 64];
    output.fill(&mut wide);
    output.fill(&mut self.state);
    Fr::from_le_bytes_mod_order(&wide)
  }
}

impl Default for Blake3Transcript {
  fn default() -> Self {
    Self::new()
  }
}

impl Transcript for Blake3Transcript {
  type F = Scalar;
  type Challenge = Scalar;
  type Commitment = KzgCommitment;

  fn observe_field(&mut self, x: Scalar) {
    self.observe_canonical(&x.0);
  }

  fn observe_field_slice(&mut self, xs: &[Scalar]) {
    for x in xs {
      self.observe_field(*x);
    }
  }

  fn observe_challenge(&mut self, x: Scalar) {
    self.observe_field(x);
  }

  fn observe_commitment(&mut self, c: KzgCommitment) {
    self.observe_canonical(&c.0);
    self.observe_canonical(&c.1);
  }

  fn sample_challenge(&mut self) -> Scalar {
    Scalar(self.squeeze())
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use multi_stark::traits::Field;

  #[test]
  fn deterministic_and_sensitive() {
    let run = |values: &[u64]| {
      let mut t = Blake3Transcript::new();
      for &v in values {
        t.observe_field(Scalar::from_u64(v));
      }
      t.sample_challenge()
    };
    assert_eq!(run(&[1, 2, 3]), run(&[1, 2, 3]));
    assert_ne!(run(&[1, 2, 3]), run(&[1, 2, 4]));
    assert_ne!(run(&[1, 2, 3]), run(&[1, 2]));
  }

  #[test]
  fn consecutive_samples_differ() {
    let mut t = Blake3Transcript::new();
    t.observe_field(Scalar::from_u64(7));
    assert_ne!(t.sample_challenge(), t.sample_challenge());
  }

  /// Slice observation must equal element-wise observation (trait
  /// contract).
  #[test]
  fn slice_observation_flat() {
    let xs = [Scalar::from_u64(5), Scalar::from_u64(6)];
    let mut a = Blake3Transcript::new();
    a.observe_field_slice(&xs);
    let mut b = Blake3Transcript::new();
    b.observe_field(xs[0]);
    b.observe_field(xs[1]);
    assert_eq!(a.sample_challenge(), b.sample_challenge());
  }
}
