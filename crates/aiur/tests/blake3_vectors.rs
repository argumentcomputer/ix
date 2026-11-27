use multi_stark::{
  p3_field::PrimeCharacteristicRing,
  plonkish::{
    CircuitBuilder,
    gadgets::{Blake3Domain, ByteGadgets, blake3_domain},
  },
  types::Val,
};

fn pattern(len: usize) -> Vec<u8> {
  (0..len).map(|i| u8::try_from(i % 251).unwrap()).collect()
}

fn check_in_circuit_blake3(domain: Blake3Domain, msg: &[u8]) {
  let mut builder = CircuitBuilder::<Val>::new();
  builder.enable_compact_blake3();
  let bytes = ByteGadgets::new(&mut builder);
  let input: Vec<_> = (0..msg.len())
    .map(|i| bytes.input(&mut builder, &format!("b{i}")))
    .collect();
  let digest = blake3_domain(&mut builder, &bytes, domain, &input);
  for byte in digest {
    builder.expose_public(byte.value());
  }
  let circuit = builder.finish();
  let mut witness = circuit.witness();
  for (wire, &byte) in input.iter().zip(msg) {
    witness.set(wire.value(), Val::from_u8(byte)).unwrap();
  }
  let assignment = witness.generate().unwrap();
  let expected_bytes = domain.hash_bytes(msg);
  let expected: Vec<Val> =
    expected_bytes.into_iter().map(Val::from_u8).collect();
  assert_eq!(
    assignment.public_values(),
    expected.as_slice(),
    "in-circuit BLAKE3 mismatch for {domain:?} len {}",
    msg.len()
  );
  if matches!(domain, Blake3Domain::Plain) {
    assert_eq!(expected_bytes, *blake3::hash(msg).as_bytes());
  }
}

#[test]
fn blake3_third_merkle_level_eight_plus_chunks_plain_and_derive_key() {
  for domain in [
    Blake3Domain::Plain,
    Blake3Domain::MerkleLeaf,
    Blake3Domain::TranscriptBatch,
  ] {
    for &length in &[7168usize, 8191, 8192, 8193, 9216, 9217] {
      check_in_circuit_blake3(domain, &pattern(length));
    }
  }
}

#[test]
fn blake3_derive_key_chunk_and_block_boundaries() {
  let domains = [
    Blake3Domain::MerkleLeaf,
    Blake3Domain::MerkleCompress,
    Blake3Domain::TranscriptSingle,
    Blake3Domain::TranscriptBatch,
  ];
  let lengths = [
    0usize, 1, 63, 64, 65, 128, 1023, 1024, 1025, 2047, 2048, 2049, 4096, 4097,
  ];
  for &length in &lengths {
    let msg = pattern(length);
    for domain in domains {
      check_in_circuit_blake3(domain, &msg);
    }
    // Domain separation: distinct domains produce distinct digests on the same input.
    let plain = Blake3Domain::Plain.hash_bytes(&msg);
    let leaf = Blake3Domain::MerkleLeaf.hash_bytes(&msg);
    let batch = Blake3Domain::TranscriptBatch.hash_bytes(&msg);
    assert_ne!(plain, leaf, "plain vs merkle leaf at len {length}");
    assert_ne!(plain, batch, "plain vs transcript batch at len {length}");
    assert_ne!(leaf, batch, "merkle leaf vs transcript batch at len {length}");
  }
}

#[test]
fn blake3_cross_chunk_boundary_row_payloads() {
  // Multi-row payloads serialized as little-endian 8-byte words that straddle
  // 64-byte blocks, 1024-byte chunks, and the 8-chunk (8192-byte) boundary.
  let row_shapes: &[&[usize]] = &[
    &[7, 2],        // 56 + 16 = 72 bytes crossing first 64-byte block
    &[127, 2],      // 1016 + 16 = 1032 bytes crossing chunk 0 -> 1
    &[128, 128, 1], // 2056 bytes crossing chunk 0 -> 1 -> 2
    &[383, 2, 128], // 4104 bytes crossing chunk 3 -> 4
    &[512, 511, 2], // 8200 bytes crossing 8-chunk third Merkle level
    &[1023, 130],   // 9224 bytes crossing 8-chunk and 9-chunk boundaries
  ];
  for &widths in row_shapes {
    let mut payload = Vec::new();
    let mut state = 0x517c_c1b7_2722_0a95u64;
    for &width in widths {
      for _ in 0..width {
        payload.extend_from_slice(&state.to_le_bytes());
        state = state
          .wrapping_mul(6364136223846793005)
          .wrapping_add(1442695040888963407);
      }
    }
    check_in_circuit_blake3(Blake3Domain::Plain, &payload);
    check_in_circuit_blake3(Blake3Domain::MerkleLeaf, &payload);
  }
}
