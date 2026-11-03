use ix_proof_compression::fri::Blake3Challenger;
use ix_proof_compression::fri::ByteGadgets;
use ix_proof_compression::fri::blake3;
use multi_stark::p3_field::PrimeCharacteristicRing;
use multi_stark::p3_field::PrimeField64;
use multi_stark::plonkish::CircuitBuilder;
use multi_stark::plonkish::WitnessError;
use multi_stark::types::Challenger;
use multi_stark::types::Val;
use p3_blake3::Blake3;
use p3_challenger::{
  CanObserve, CanSample, CanSampleBits, GrindingChallenger, HashChallenger,
};
use p3_symmetric::CryptographicHasher;

#[test]
fn blake3_matches_native_at_block_and_tree_boundaries() {
  for len in [0, 1, 63, 64, 65, 1023, 1024, 1025, 2048, 2049] {
    let mut builder = CircuitBuilder::<Val>::new();
    let bytes = ByteGadgets::new(&mut builder);
    let input: Vec<_> = (0..len)
      .map(|i| bytes.input(&mut builder, &format!("byte {i}")))
      .collect();
    let output = blake3(&mut builder, &bytes, &input);
    let circuit = builder.finish();
    for seed in [0u8, 197] {
      let message: Vec<_> = (0..len)
        .map(|i| u8::try_from(i % 251).unwrap().wrapping_add(seed))
        .collect();
      let expected: [u8; 32] = Blake3.hash_iter(message.iter().copied());
      let mut witness = circuit.witness();
      for (&wire, &value) in input.iter().zip(&message) {
        witness.set(wire.value(), Val::from_u8(value)).unwrap();
      }
      let assignment = witness.generate().unwrap();
      let actual = output.map(|byte| {
        u8::try_from(assignment.value(byte.value()).unwrap().as_canonical_u64())
          .unwrap()
      });
      assert_eq!(actual, expected, "length {len}, seed {seed}");
    }
  }
}

#[test]
fn byte_range_and_field_encoding_are_canonical() {
  let mut builder = CircuitBuilder::<Val>::new();
  let bytes = ByteGadgets::new(&mut builder);
  let input = bytes.input(&mut builder, "byte");
  let circuit = builder.finish();
  for x in [256, 511, 65536] {
    let mut witness = circuit.witness();
    witness.set(input.value(), Val::from_u32(x)).unwrap();
    assert!(witness.generate().is_err());
  }
  let mut builder = CircuitBuilder::<Val>::new();
  let bytes = ByteGadgets::new(&mut builder);
  let input = builder.input("field element");
  let encoded = bytes.encode_field64(&mut builder, input);
  let circuit = builder.finish();
  for x in [0, 1, 0xffff_ffff, 1 << 32, Val::ORDER_U64 - 1] {
    let mut witness = circuit.witness();
    witness.set(input, Val::from_u64(x)).unwrap();
    let assignment = witness.generate().unwrap();
    let actual = encoded.map(|v| {
      u8::try_from(assignment.value(v.value()).unwrap().as_canonical_u64())
        .unwrap()
    });
    assert_eq!(actual, x.to_le_bytes());
  }
  // Model sampled hash bytes, including candidates whose reduction would
  // alias 0 or 1. They must fail, not get accepted modulo Goldilocks p.
  let mut builder = CircuitBuilder::<Val>::new();
  let bytes = ByteGadgets::new(&mut builder);
  let input =
    std::array::from_fn(|i| bytes.input(&mut builder, &format!("sample[{i}]")));
  bytes.assert_at_most_u64(&mut builder, input, Val::ORDER_U64 - 1);
  let circuit = builder.finish();
  for x in [0, Val::ORDER_U64 - 1, Val::ORDER_U64, Val::ORDER_U64 + 1, u64::MAX]
  {
    let mut witness = circuit.witness();
    for (wire, value) in input.iter().zip(x.to_le_bytes()) {
      witness.set(wire.value(), Val::from_u8(value)).unwrap();
    }
    assert_eq!(witness.generate().is_ok(), x < Val::ORDER_U64, "candidate {x}");
  }
}

#[test]
fn challenger_matches_digest_pop_order_chaining_and_observation_reset() {
  let mut builder = CircuitBuilder::<Val>::new();
  let bytes = ByteGadgets::new(&mut builder);
  let mut challenger =
    Blake3Challenger::new(&mut builder, &bytes, b"transcript test");
  let observed = bytes.input(&mut builder, "observe after partial sample");
  let mut wires: Vec<_> =
    (0..7).map(|_| challenger.sample_byte(&mut builder, &bytes)).collect();
  challenger.observe_bytes(&[]);
  wires.extend((0..3).map(|_| challenger.sample_byte(&mut builder, &bytes)));
  challenger.observe_bytes(&[observed]);
  wires.extend((0..70).map(|_| challenger.sample_byte(&mut builder, &bytes)));
  let circuit = builder.finish();
  for value in [0u8, 255] {
    let mut native = HashChallenger::<u8, Blake3, 32>::new(
      b"transcript test".to_vec(),
      Blake3,
    );
    let mut expected: Vec<u8> = (0..7).map(|_| native.sample()).collect();
    CanObserve::<u8>::observe_slice(&mut native, &[]);
    expected.extend((0..3).map(|_| native.sample()));
    native.observe(value);
    expected.extend((0..70).map(|_| native.sample()));
    let mut witness = circuit.witness();
    witness.set(observed.value(), Val::from_u8(value)).unwrap();
    let assignment = witness.generate().unwrap();
    for (wire, expected) in wires.iter().zip(expected) {
      assert_eq!(
        assignment.value(wire.value()).unwrap(),
        Val::from_u8(expected)
      );
    }
  }
}

#[test]
fn challenger_bit_sampling_matches_native_across_byte_and_digest_boundaries() {
  let mut builder = CircuitBuilder::<Val>::new();
  let bytes = ByteGadgets::new(&mut builder);
  let seed = b"bit sampling";
  let mut challenger = Blake3Challenger::new(&mut builder, &bytes, seed);
  let mut native = Challenger::from_hasher(seed.to_vec(), Blake3);
  let mut samples = Vec::new();
  for count in [0, 1, 7, 8, 9, 31, 32, 63, 0, 8] {
    samples.push((
      challenger.sample_bits(&mut builder, &bytes, count),
      native.sample_bits(count),
    ));
  }
  let field = builder.constant(Val::from_u32(123));
  challenger.observe_field(&mut builder, &bytes, field);
  native.observe(Val::from_u32(123));
  samples.push((
    challenger.sample_bits(&mut builder, &bytes, 17),
    native.sample_bits(17),
  ));
  let circuit = builder.finish();
  let assignment = circuit.witness().generate().unwrap();
  for (bits, expected) in samples {
    let actual: u64 = bits
      .iter()
      .enumerate()
      .map(|(i, bit)| {
        assignment.value(bit.value()).unwrap().as_canonical_u64() << i
      })
      .sum();
    assert_eq!(actual, u64::try_from(expected).unwrap());
  }
}

#[test]
fn grinding_matches_native_including_zero_bit_noop_and_twenty_bits() {
  for bits in [0, 3, 20] {
    let seed = b"root profile grinding";
    let initial = Challenger::from_hasher(seed.to_vec(), Blake3);
    let mut native = initial.clone();
    let valid = native.grind(bits);
    let expected = native.sample_bits(17);
    let mut builder = CircuitBuilder::<Val>::new();
    let bytes = ByteGadgets::new(&mut builder);
    let mut challenger = Blake3Challenger::new(&mut builder, &bytes, seed);
    let pow = builder.input("grinding witness");
    challenger.check_witness(&mut builder, &bytes, bits, pow);
    let next = challenger.sample_bits(&mut builder, &bytes, 17);
    let circuit = builder.finish();
    let mut witness = circuit.witness();
    witness.set(pow, valid).unwrap();
    let assignment = witness.generate().unwrap();
    let actual: u64 = next
      .iter()
      .enumerate()
      .map(|(i, bit)| {
        assignment.value(bit.value()).unwrap().as_canonical_u64() << i
      })
      .sum();
    assert_eq!(actual, u64::try_from(expected).unwrap());

    let mut wrong = valid + Val::ONE;
    if bits != 0 {
      // Select a genuinely invalid nonce rather than assuming +1 fails.
      while initial.clone().check_witness(bits, wrong) {
        wrong += Val::ONE;
      }
    }
    let mut witness = circuit.witness();
    witness.set(pow, wrong).unwrap();
    assert_eq!(witness.generate().is_ok(), bits == 0);
  }
}

#[test]
fn wrong_digest_is_rejected_by_relations_not_just_host_hashing() {
  let mut builder = CircuitBuilder::<Val>::new();
  let bytes = ByteGadgets::new(&mut builder);
  let input = bytes.input(&mut builder, "byte");
  let output = blake3(&mut builder, &bytes, &[input]);
  let expected: [_; 32] =
    std::array::from_fn(|i| builder.public_input(format!("digest[{i}]")));
  for (byte, expected) in output.iter().zip(expected) {
    builder.assert_equal(byte.value(), expected);
  }
  let circuit = builder.finish();
  let digest: [u8; 32] = Blake3.hash_iter([42]);
  for bad_index in 0..32 {
    let mut witness = circuit.witness();
    witness.set(input.value(), Val::from_u8(42)).unwrap();
    for (i, &wire) in expected.iter().enumerate() {
      witness
        .set(wire, Val::from_u8(digest[i] ^ u8::from(i == bad_index)))
        .unwrap();
    }
    assert!(matches!(
      witness.generate(),
      Err(WitnessError::UnsatisfiedGate { .. })
    ));
  }
}
