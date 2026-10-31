//! Fiat-Shamir transcripts over the BLS12-381 scalar field.
//!
//! BLAKE3 samples hash the chain state and buffered canonical observations,
//! reduce 64 XOF bytes little-endian into the scalar field, take 32 more
//! bytes as the next state, and clear the buffer. Keccak-256 uses separate
//! digest domains for its wide challenge and next state.

use ark_bls12_381::Fr;
use ark_ff::PrimeField;
use ark_serialize::CanonicalSerialize;
use tiny_keccak::{Hasher, Keccak};

use multi_stark::traits::Transcript;

use super::field::Scalar;
use super::pcs::KzgCommitment;

/// The hash and challenge expansion used by the native KZG verifier.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TranscriptKind {
  Blake3,
  Keccak256,
}

/// A native transcript whose hash is selected by the verifier configuration.
#[derive(Clone)]
pub enum KzgTranscript {
  Blake3(Blake3Transcript),
  Keccak256(Keccak256Transcript),
}

impl KzgTranscript {
  pub fn new(kind: TranscriptKind) -> Self {
    match kind {
      TranscriptKind::Blake3 => Self::Blake3(Blake3Transcript::new()),
      TranscriptKind::Keccak256 => Self::Keccak256(Keccak256Transcript::new()),
    }
  }

  pub fn kind(&self) -> TranscriptKind {
    match self {
      Self::Blake3(_) => TranscriptKind::Blake3,
      Self::Keccak256(_) => TranscriptKind::Keccak256,
    }
  }

  pub fn observe_bytes(&mut self, bytes: &[u8]) {
    match self {
      Self::Blake3(t) => t.observe_bytes(bytes),
      Self::Keccak256(t) => t.observe_bytes(bytes),
    }
  }

  /// Absorb a canonically-serializable arkworks value (compressed).
  pub fn observe_canonical(&mut self, value: &impl CanonicalSerialize) {
    match self {
      Self::Blake3(t) => t.observe_canonical(value),
      Self::Keccak256(t) => t.observe_canonical(value),
    }
  }
}

impl Default for KzgTranscript {
  fn default() -> Self {
    Self::new(TranscriptKind::Blake3)
  }
}

impl Transcript for KzgTranscript {
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
  }

  fn sample_challenge(&mut self) -> Scalar {
    match self {
      Self::Blake3(t) => t.sample_challenge(),
      Self::Keccak256(t) => t.sample_challenge(),
    }
  }
}

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
  }

  fn sample_challenge(&mut self) -> Scalar {
    Scalar(self.squeeze())
  }
}

const KECCAK256_DOMAIN: &[u8] = b"multi-stark/kzg/keccak256/v1";

fn keccak256(parts: &[&[u8]]) -> [u8; 32] {
  let mut hasher = Keccak::v256();
  for part in parts {
    hasher.update(part);
  }
  let mut digest = [0u8; 32];
  hasher.finalize(&mut digest);
  digest
}

/// Keccak-256 transcript with 512-bit challenge reduction.
///
/// For counters 0, 1, and 2, hash `domain || counter:u8 || state:bytes32 ||
/// observations`. The first two digests form a 64-byte big-endian integer,
/// reduced modulo Fr; the third becomes the next state. Every digest uses
/// the old state and the same observations, which are cleared afterwards.
/// Canonical observations retain arkworks' compressed byte encoding.
#[derive(Clone)]
pub struct Keccak256Transcript {
  state: [u8; 32],
  buffer: Vec<u8>,
}

impl Keccak256Transcript {
  /// A fresh transcript. The configuration must observe its parameter seed.
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

  fn digest(&self, counter: u8) -> [u8; 32] {
    keccak256(&[KECCAK256_DOMAIN, &[counter], &self.state, &self.buffer])
  }

  fn squeeze(&mut self) -> Fr {
    let mut wide = [0u8; 64];
    wide[..32].copy_from_slice(&self.digest(0));
    wide[32..].copy_from_slice(&self.digest(1));
    self.state = self.digest(2);
    self.buffer.clear();
    Fr::from_be_bytes_mod_order(&wide)
  }
}

impl Default for Keccak256Transcript {
  fn default() -> Self {
    Self::new()
  }
}

impl Transcript for Keccak256Transcript {
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
  }

  fn sample_challenge(&mut self) -> Scalar {
    Scalar(self.squeeze())
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use ark_bls12_381::G1Affine;
  use ark_ec::AffineRepr;
  use ark_ff::BigInteger;
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

  fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
  }

  #[test]
  fn keccak256_known_answers() {
    assert_eq!(
      hex(&keccak256(&[b""])),
      "c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470"
    );
    assert_eq!(
      hex(&keccak256(&[b"abc"])),
      "4e03657aea45a94fc7d47ba826c8d667c0d1e6e33a64a036ec44f58fa12d6c45"
    );
  }

  #[test]
  fn keccak_transcript_matches_independent_vectors() {
    // PyCryptodome 3.23.0 Crypto.Hash.keccak, digest_bits=256, independently
    // generates each digest from the documented concatenation. Challenges
    // are int.from_bytes(digest0 + digest1, "big") % Fr::MODULUS; the field
    // observations 7 and 42 are 32-byte little-endian canonical encodings.
    let mut t = Keccak256Transcript::new();
    t.observe_bytes(b"kzg-vector-v1");
    t.observe_field(Scalar::from_u64(7));
    t.observe_bytes(&(0u8..160).collect::<Vec<_>>());

    let vectors = [
      (
        "2e3429e71d42335d9ea681622711b7ef2468c1db8c0245dd805deed360bbcf25",
        "c400066185add659881d303d8b0cd914429b2b1ba9e0addc4a50dacaf049d608",
      ),
      (
        "1f261b89afb3b219e30be06c7518ccb5038337b3168ed83bdba29a36699b5c27",
        "510f0c6412d976b7224d04cac918bd5fcbef2ca2dfe08f7aa371be709e9a71e5",
      ),
      (
        "67e1777e4d2a526c9c905e84eaf3cc6b6e0764c42dc7bcff1c8e6dee350e6fdc",
        "64c9ce0b0dc5ff29a58487ebd39827848fae8c0e46e7850c64e2e2f5cbbd2475",
      ),
    ];
    for (round, (challenge, state)) in vectors.iter().enumerate() {
      if round == 2 {
        t.observe_bytes(b"after-squeeze");
        t.observe_canonical(&Fr::from(42u64));
      }
      assert_eq!(
        hex(&t.sample_challenge().0.into_bigint().to_bytes_be()),
        *challenge,
        "round {round} challenge"
      );
      assert_eq!(hex(&t.state), *state, "round {round} state");
      assert!(t.buffer.is_empty());
    }
  }

  #[test]
  fn hash_kinds_and_expansion_domains_are_distinct() {
    let mut blake3 = KzgTranscript::new(TranscriptKind::Blake3);
    let mut keccak = KzgTranscript::new(TranscriptKind::Keccak256);
    assert_eq!(blake3.kind(), TranscriptKind::Blake3);
    assert_eq!(keccak.kind(), TranscriptKind::Keccak256);
    blake3.observe_bytes(b"same observations");
    keccak.observe_bytes(b"same observations");
    for _ in 0..3 {
      assert_ne!(blake3.sample_challenge(), keccak.sample_challenge());
    }

    let t = Keccak256Transcript::new();
    assert_ne!(t.digest(0), t.digest(1));
    assert_ne!(t.digest(0), t.digest(2));
    assert_ne!(t.digest(1), t.digest(2));
    assert_ne!(t.digest(0), keccak256(&[&[0], &t.state]));
  }

  #[test]
  fn blake3_enum_preserves_legacy_transcript() {
    let mut legacy = Blake3Transcript::new();
    let mut selected = KzgTranscript::default();
    assert_eq!(selected.kind(), TranscriptKind::Blake3);
    assert_eq!(legacy.sample_challenge(), selected.sample_challenge());

    let xs = [Scalar::from_u64(5), Scalar::from_u64(6)];
    let commitment = KzgCommitment(vec![
      vec![G1Affine::generator(), G1Affine::default()],
      vec![],
    ]);
    legacy.observe_bytes(b"parameter seed");
    selected.observe_bytes(b"parameter seed");
    legacy.observe_canonical(&Fr::from(123u64));
    selected.observe_canonical(&Fr::from(123u64));
    legacy.observe_field_slice(&xs);
    selected.observe_field_slice(&xs);
    legacy.observe_commitment(commitment.clone());
    selected.observe_commitment(commitment);
    for _ in 0..3 {
      let challenge = legacy.sample_challenge();
      assert_eq!(challenge, selected.sample_challenge());
      legacy.observe_challenge(challenge);
      selected.observe_challenge(challenge);
      legacy.observe_field(xs[0]);
      selected.observe_field(xs[0]);
    }
  }

  #[test]
  fn keccak_incremental_observations_are_equivalent() {
    let bytes: Vec<_> = (0u8..200).collect();
    let xs = [Scalar::from_u64(7), Scalar::from_u64(9)];
    let mut whole = Keccak256Transcript::new();
    let mut incremental = KzgTranscript::new(TranscriptKind::Keccak256);
    whole.observe_bytes(&bytes);
    for chunk in bytes.chunks(13) {
      incremental.observe_bytes(chunk);
    }
    whole.observe_field_slice(&xs);
    incremental.observe_field(xs[0]);
    incremental.observe_canonical(&xs[1].0);
    assert_eq!(whole.sample_challenge(), incremental.sample_challenge());
    assert_eq!(whole.sample_challenge(), incremental.sample_challenge());
    whole.observe_challenge(xs[0]);
    incremental.observe_bytes(&7u64.to_le_bytes());
    incremental.observe_bytes(&[0u8; 24]);
    assert_eq!(whole.sample_challenge(), incremental.sample_challenge());
  }
}
