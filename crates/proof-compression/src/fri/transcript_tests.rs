use p3_blake3::Blake3;
use p3_challenger::{
  CanObserve, CanSample, CanSampleBits, HashChallenger, SerializingChallenger64,
};
use p3_symmetric::CryptographicHasher;

use super::*;

/// Supply a chosen FIRST digest to exercise rare retries deterministically.
/// Later digest chaining is real BLAKE3. The circuit starts just after that
/// first flush, with private constrained bytes (no production escape hatch).
#[derive(Clone)]
struct FirstDigest([u8; 32]);

impl CryptographicHasher<u8, [u8; 32]> for FirstDigest {
  fn hash_iter<I: IntoIterator<Item = u8>>(&self, input: I) -> [u8; 32] {
    let input: Vec<_> = input.into_iter().collect();
    if input == b"initial" { self.0 } else { Blake3.hash_iter(input) }
  }
}

fn digest(words: [u64; 4]) -> [u8; 32] {
  let mut bytes: Vec<_> =
    words.into_iter().flat_map(u64::to_le_bytes).collect();
  bytes.reverse();
  bytes.try_into().unwrap()
}

fn buffered(
  b: &mut CircuitBuilder<Goldilocks>,
  bytes: &ByteGadgets,
  retries: usize,
) -> (Blake3Challenger, [ByteValue; 32]) {
  let input = std::array::from_fn(|_| bytes.input(b, "forced first digest"));
  let mut challenger =
    Blake3Challenger::with_retry_limit(b, bytes, &[], retries);
  challenger.input = input.to_vec();
  challenger.output = input.to_vec();
  (challenger, input)
}

#[test]
fn retries_select_first_valid_candidate_and_preserve_native_transcript_state() {
  let mut b = CircuitBuilder::new();
  let bytes = ByteGadgets::new(&mut b);
  let (mut challenger, input) = buffered(&mut b, &bytes, 2);
  let first = challenger.sample_field(&mut b, &bytes);
  let second = challenger.sample_field(&mut b, &bytes);
  let bits = challenger.sample_bits(&mut b, &bytes, 17);
  challenger.observe_bytes(&[]); // Must not discard a partially used digest.
  let third = challenger.sample_field(&mut b, &bytes);
  let observed = b.constant(Goldilocks::from_u8(42));
  challenger.observe_field(&mut b, &bytes, observed);
  let fourth = challenger.sample_field(&mut b, &bytes);
  let circuit = b.finish();
  let p = Goldilocks::ORDER_U64;
  for words in [
    [0, 17, 19, 23],
    [p - 1, p, 19, 23],
    [p, 17, 19, 23],
    [p, u64::MAX, 19, 23],
  ] {
    let digest = digest(words);
    let mut native = SerializingChallenger64::<Goldilocks, _>::from_hasher(
      b"initial".to_vec(),
      FirstDigest(digest),
    );
    let expected_first: Goldilocks = native.sample();
    let expected_second: Goldilocks = native.sample();
    let expected_bits = native.sample_bits(17);
    let expected_third: Goldilocks = native.sample();
    native.observe(Goldilocks::from_u8(42));
    let expected_fourth: Goldilocks = native.sample();
    let mut witness = circuit.witness();
    for (wire, value) in input.iter().zip(digest) {
      witness.set(wire.value(), Goldilocks::from_u8(value)).unwrap();
    }
    let assignment = witness.generate().unwrap();
    for (wire, expected) in [first, second, third, fourth].into_iter().zip([
      expected_first,
      expected_second,
      expected_third,
      expected_fourth,
    ]) {
      assert_eq!(assignment.value(wire).unwrap(), expected);
    }
    let actual: u64 = bits
      .iter()
      .enumerate()
      .map(|(i, bit)| {
        assignment.value(bit.value()).unwrap().as_canonical_u64() << i
      })
      .sum();
    assert_eq!(actual, u64::try_from(expected_bits).unwrap());
  }
  // A third rejection exceeds this circuit's budget, even though native
  // sampling would eventually find a valid field element.
  let mut witness = circuit.witness();
  for (wire, value) in input.iter().zip(digest([p, p + 1, u64::MAX, 7])) {
    witness.set(wire.value(), Goldilocks::from_u8(value)).unwrap();
  }
  assert!(witness.generate().is_err());
}

#[test]
fn byte_reads_after_conditional_retries_cross_digest_boundaries_correctly() {
  let mut b = CircuitBuilder::new();
  let bytes = ByteGadgets::new(&mut b);
  let (mut challenger, input) = buffered(&mut b, &bytes, 3);
  let field = challenger.sample_field(&mut b, &bytes);
  let sampled: Vec<_> =
    (0..39).map(|_| challenger.sample_byte(&mut b, &bytes)).collect();
  let next_field = challenger.sample_field(&mut b, &bytes); // unaligned read
  let circuit = b.finish();
  for rejects in 0..=3 {
    let mut words = [17, 19, 23, 29];
    words[..rejects].fill(Goldilocks::ORDER_U64);
    let digest = digest(words);
    let mut native = HashChallenger::<u8, _, 32>::new(
      b"initial".to_vec(),
      FirstDigest(digest),
    );
    let sample_field = |native: &mut HashChallenger<u8, FirstDigest, 32>| loop {
      let value = u64::from_le_bytes(std::array::from_fn(|_| native.sample()));
      if value < Goldilocks::ORDER_U64 {
        break Goldilocks::from_u64(value);
      }
    };
    let expected = sample_field(&mut native);
    let tail: Vec<u8> = (0..39).map(|_| native.sample()).collect();
    let expected_next = sample_field(&mut native);
    let mut witness = circuit.witness();
    for (wire, value) in input.iter().zip(digest) {
      witness.set(wire.value(), Goldilocks::from_u8(value)).unwrap();
    }
    let assignment = witness.generate().unwrap();
    assert_eq!(assignment.value(field).unwrap(), expected);
    assert_eq!(assignment.value(next_field).unwrap(), expected_next);
    for (wire, expected) in sampled.iter().zip(tail) {
      assert_eq!(
        assignment.value(wire.value()).unwrap(),
        Goldilocks::from_u8(expected)
      );
    }
  }
}

#[test]
fn conditional_retry_circuit_proves_multiple_paths_under_one_outer_key() {
  use multi_stark::system::System;
  use multi_stark::system::SystemWitness;
  use multi_stark::types::CommitmentParameters;
  use multi_stark::types::FriParameters;
  use multi_stark::types::GoldilocksBlake3Config;

  let mut b = CircuitBuilder::new();
  let bytes = ByteGadgets::new(&mut b);
  let (mut challenger, input) = buffered(&mut b, &bytes, 2);
  for byte in input {
    b.expose_public(byte.value());
  }
  let field = challenger.sample_field(&mut b, &bytes);
  b.expose_public(field);
  let buffer = challenger.buffer(&mut b, &bytes);
  let circuit = b.finish();
  let compiled =
    circuit.lower_to_multi_stark(Goldilocks::from_u8(105)).unwrap();
  let config = GoldilocksBlake3Config::new(
    CommitmentParameters { log_blowup: 1, cap_height: 0 },
    FriParameters {
      log_final_poly_len: 0,
      max_log_arity: 1,
      num_queries: 4,
      commit_proof_of_work_bits: 0,
      query_proof_of_work_bits: 0,
    },
  );
  let (system, key) = System::new(config, compiled.circuit_inputs());
  for rejects in 0..=2 {
    let mut words = [17, 19, 23, 29];
    words[..rejects].fill(Goldilocks::ORDER_U64);
    let digest = digest(words);
    let expected = Goldilocks::from_u64(words[rejects]);
    let mut witness = compiled.witness();
    for (wire, value) in input.iter().zip(digest) {
      witness.set(wire.value(), Goldilocks::from_u8(value)).unwrap();
    }
    let assignment = witness.generate().unwrap();
    let public: Vec<_> =
      digest.into_iter().map(Goldilocks::from_u8).chain([expected]).collect();
    let claims = compiled.claims(&public).unwrap();
    let refs: Vec<_> = claims.iter().map(Vec::as_slice).collect();
    let proof = system.prove_multiple_claims(
      &key,
      &refs,
      SystemWitness::from_stage_1(
        compiled.traces(&assignment).unwrap(),
        &system,
      ),
    );
    system.verify_multiple_claims(&refs, &proof).unwrap();

    let mut wrong_public = public;
    *wrong_public.last_mut().unwrap() += Goldilocks::ONE;
    let wrong_claims = compiled.claims(&wrong_public).unwrap();
    assert!(
      system
        .verify_multiple_claims(
          &wrong_claims.iter().map(Vec::as_slice).collect::<Vec<_>>(),
          &proof
        )
        .is_err()
    );

    // Bypass witness recipes: a forged cursor/result still violates the
    // actual relation. The cursor is never implicitly trusted hint data.
    for wire in [
      field,
      buffer.remaining[8].value(),
      buffer.remaining[16].value(),
      buffer.remaining[24].value(),
    ] {
      let mut forged =
        assignment.values(compiled.circuit().id()).unwrap().to_vec();
      forged[wire.index()] += Goldilocks::ONE;
      assert!(compiled.circuit().check_values(&forged).is_err());
    }
  }
}
