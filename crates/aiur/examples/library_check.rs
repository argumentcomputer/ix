//! Check the shared modules exported by `lake exe library_tests PACKAGE.ixa`.
use aiur::{
  artifact::Package,
  bytecode::Type,
  hints::HintChannels,
  maps::MapOverrides,
  trace::{
    TracePlan,
    stark::{Backend, Parameters},
  },
};
use std::error::Error;

fn bytes(word: u64) -> Vec<u64> {
  word.to_le_bytes().into_iter().map(u64::from).collect()
}

fn main() -> Result<(), Box<dyn Error>> {
  let path =
    std::env::args().nth(1).ok_or("usage: library_check PACKAGE.ixa")?;
  let (package, digest) = Package::load(path.as_ref())?;
  eprintln!("artifact {path}: blake3 {digest}");
  let (program, trace) = package.traced()?;
  let mut program = program.check()?;
  program.track_depth(&trace)?;
  let mut channels = HintChannels::new();
  aiur::library::u32::register(&mut channels, program.field())?;
  aiur::library::u64::register(&mut channels, program.field())?;
  let mut maps = MapOverrides::new();
  aiur::library::u8::register_maps(&program, &mut maps)?;
  let tables = program.prepare_hint_channels(&[], &channels)?;
  let accelerated =
    program.prepare_hint_channels(&[], &channels)?.with_map_overrides(&maps)?;
  let plan = TracePlan::new(&program, trace)?;
  // Sanity-check STARK soundness and witness equality without paying for
  // production PoW grinding or 100 FRI queries.
  let parameters = Parameters {
    num_queries: 2,
    commit_proof_of_work_bits: 0,
    query_proof_of_work_bits: 0,
    ..Parameters::default()
  };
  let backend = Backend::new_below_floor(&plan, parameters)?;
  let mut checks = 0;
  let mut check = |entry: &str,
                   args: Vec<u64>,
                   expected: Vec<u64>|
   -> Result<_, Box<dyn Error>> {
    let record = accelerated.execute(entry, args.clone())?;
    assert_eq!(record.output, expected, "{entry}({args:?})");
    let fallback = tables.execute(entry, args.clone())?;
    assert_eq!(record.output, fallback.output);
    assert_eq!(record.queries, fallback.queries);
    let trace = plan.generate(&record, entry, &args, true)?;
    plan.check(&record, &trace, entry, &args)?;
    assert_eq!(trace, plan.generate_reference(&record, entry, &args, true)?);
    checks += 1;
    Ok(())
  };
  check("InterfaceBytes::run", vec![173, 99], vec![206])?;
  check("InterfaceWords::run", vec![u64::from(u32::MAX), 1], vec![0])?;
  for byte in 0..256 {
    check("ByteChecks::checked", vec![byte], vec![byte])?;
  }
  for sum in 0..768 {
    check("ByteChecks::split", vec![sum], vec![sum % 256, sum / 256])?;
  }
  for a in [0, 1, 15, 16, 127, 128, 254, 255] {
    for b in [0, 1, 15, 16, 127, 128, 254, 255] {
      check("ByteChecks::less_than", vec![a, b], vec![u64::from(a < b)])?;
      check("ByteChecks::and", vec![a, b], vec![a & b])?;
      check("ByteChecks::or", vec![a, b], vec![a | b])?;
      check("ByteChecks::add", vec![a, b], vec![(a + b) % 256, (a + b) / 256])?;
      check(
        "ByteChecks::sub",
        vec![a, b],
        vec![(a + 256 - b) % 256, u64::from(a < b)],
      )?;
      check("ByteChecks::mul", vec![a, b], vec![(a * b) % 256, (a * b) / 256])?;
      check("ByteChecks::join4", vec![a, b], vec![a / 16 + (b % 16) * 16])?;
      check("ByteChecks::join7", vec![a, b], vec![a / 128 + (b % 128) * 2])?;
    }
  }
  let mut values = vec![
    0,
    1,
    255,
    256,
    65535,
    65536,
    1 << 32,
    1 << 56,
    1 << 63,
    u64::MAX - 1,
    u64::MAX,
  ];
  let mut seed = 0x93c4_18bd_u64;
  for _ in 0..16 {
    seed =
      seed.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
    values.push(seed);
  }
  for a in values {
    check("Wide::wrapping_succ", bytes(a), bytes(a.wrapping_add(1)))?;
    check("Wide::saturating_pred", bytes(a), bytes(a.saturating_sub(1)))?;
    check("Wide::is_zero", bytes(a), vec![u64::from(a == 0)])?;
    for b in [0, 1, u64::MAX, a, a.rotate_left(13)] {
      let args = [bytes(a), bytes(b)].concat();
      let (sum, carry) = a.overflowing_add(b);
      check(
        "Wide::add",
        args.clone(),
        [bytes(sum), vec![u64::from(carry)]].concat(),
      )?;
      let (diff, borrow) = a.overflowing_sub(b);
      check(
        "Wide::sub",
        args.clone(),
        [bytes(diff), vec![u64::from(borrow)]].concat(),
      )?;
      let product = u128::from(a) * u128::from(b);
      check(
        "Wide::mul",
        args.clone(),
        [
          bytes(u64::try_from(product & u128::from(u64::MAX)).unwrap()),
          bytes(u64::try_from(product >> 64).unwrap()),
        ]
        .concat(),
      )?;
      check("Wide::eq", args.clone(), vec![u64::from(a == b)])?;
      for (op, result) in [("and", a & b), ("or", a | b), ("xor", a ^ b)] {
        check(&format!("Wide::{op}"), args.clone(), bytes(result))?;
      }
    }
  }
  for word in [0, 1, 255, 256, (1 << 56) - 1] {
    check("Wide::from_field", vec![word], bytes(word))?;
    check("Wide::to_field", bytes(word), vec![word])?;
  }
  // Block/chunk boundaries and odd Merkle layers, compared with the Rust
  // Blake3 crate. This tests the library, not a copied hash implementation.
  // The block loop takes 64 bytes while 64 are left and hands the last 0 to
  // 63 to the byte loop, so lengths around each 64 and 1024 multiple matter.
  let hash_expected = |length: u64| -> Vec<u64> {
    let input: Vec<u8> =
      (0..length).map(|i| u8::try_from(i % 256).unwrap()).collect();
    blake3::hash(&input).as_bytes().iter().copied().map(u64::from).collect()
  };
  for length in [0, 1, 63, 64, 65, 128, 1023, 1024, 1025, 2048, 2049] {
    check("Benchmark::hash", vec![length], hash_expected(length))?;
  }
  // Deeper multi-chunk inputs, including the 8-chunk third Merkle level and
  // cross-chunk boundaries, compared against the Rust blake3 crate.
  for length in
    [3072, 3073, 4096, 4097, 7167, 7168, 7169, 8191, 8192, 8193, 9216, 9217]
  {
    let record = accelerated.execute("Benchmark::hash", vec![length])?;
    assert_eq!(
      record.output,
      hash_expected(length),
      "Benchmark::hash({length})"
    );
  }
  // Verify full trace population and constraint satisfaction across the
  // 8-chunk / third-level Merkle boundary.
  for length in [8192, 8193] {
    let record = accelerated.execute("Benchmark::hash", vec![length])?;
    assert_eq!(
      record.output,
      hash_expected(length),
      "Benchmark::hash({length})"
    );
    let trace = plan.generate(&record, "Benchmark::hash", &[length], true)?;
    plan.check(&record, &trace, "Benchmark::hash", &[length])?;
    checks += 1;
  }
  // Exercise in-circuit BLAKE3 derive_key domains across block, chunk, and
  // 8-chunk third-level Merkle boundaries, as well as cross-chunk row payloads.
  check_derive_key_and_cross_chunk_blake3()?;
  println!(
    "Passed {checks} native/table execution and reference-trace comparisons."
  );

  for (entry, args) in [
    ("ByteChecks::checked", vec![256]),
    ("ByteChecks::checked", vec![program.field().modulus() - 1]),
    ("ByteChecks::less_than", vec![256, 0]),
    ("ByteChecks::less_than", vec![0, 256]),
    ("ByteChecks::less_than", vec![program.field().modulus() - 1, 0]),
    ("ByteChecks::less_than", vec![0, program.field().modulus() - 1]),
    ("ByteChecks::split", vec![768]),
    ("ByteChecks::split", vec![program.field().modulus() - 1]),
    ("ByteChecks::add", vec![256, 0]),
    ("ByteChecks::add", vec![0, 256]),
    ("ByteChecks::sub", vec![0, 256]),
    ("ByteChecks::join4", vec![256, 0]),
    ("ByteChecks::join7", vec![0, 256]),
    ("Wide::add", [vec![256, 0, 0, 0, 0, 0, 0, 0], bytes(0)].concat()),
    ("Wide::from_field", vec![1 << 56]),
    ("Wide::to_field", bytes(1 << 56)),
  ] {
    assert!(
      accelerated.execute(entry, args.clone()).is_err(),
      "{entry}({args:?})"
    );
    assert!(tables.execute(entry, args.clone()).is_err(), "{entry}({args:?})");
  }
  // Wrong raw advice still executes under constrain_eq!, but its proof fails.
  let mut dishonest = HintChannels::new();
  dishonest.insert(
    "bytes_le",
    Type::Field,
    Type::Tuple { items: vec![Type::Field; 8] },
    |_, out| {
      out.fill(0);
      Ok(())
    },
  )?;
  let bad = program.prepare_hint_channels(&[], &dishonest)?;
  for (entry, args) in [
    ("Wide::from_field", vec![1]),
    ("Wide::mul", [bytes(1), bytes(1)].concat()),
  ] {
    let record = bad.execute(entry, args.clone())?;
    let witness = backend.generate(&record, entry, &args)?;
    let proof = backend.prove(entry, &args, &record.output, witness)?;
    assert!(backend.verify(entry, &args, &record.output, &proof).is_err());
  }
  for (entry, args) in [
    ("Wide::mul", [bytes(u64::MAX), bytes(u64::MAX)].concat()),
    ("Benchmark::hash", vec![1025]),
  ] {
    let record = accelerated.execute(entry, args.clone())?;
    let trace = plan.generate(&record, entry, &args, true)?;
    let witness = backend.generate(&record, entry, &args)?;
    let reference = backend.witness(&record, &trace)?;
    for (a, b) in witness.traces.iter().zip(&reference.traces) {
      assert_eq!(a.width, b.width);
      assert_eq!(a.values, b.values);
    }
    let proof = backend.prove(entry, &args, &record.output, witness)?;
    backend.verify(entry, &args, &record.output, &proof)?;
  }
  println!(
    "Passed invalid-domain checks, 2 rejected dishonest-hint proofs and 2 verified U64/Blake3 proofs."
  );
  Ok(())
}

fn check_blake3_gadget_vector(
  domain: multi_stark::plonkish::gadgets::Blake3Domain,
  msg: &[u8],
) -> Result<(), Box<dyn Error>> {
  use multi_stark::{
    p3_field::PrimeCharacteristicRing,
    plonkish::{
      CircuitBuilder,
      gadgets::{ByteGadgets, blake3_domain},
    },
    types::Val,
  };
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
    witness.set(wire.value(), Val::from_u8(byte))?;
  }
  let assignment = witness.generate()?;
  let expected: Vec<Val> =
    domain.hash_bytes(msg).into_iter().map(Val::from_u8).collect();
  assert_eq!(
    assignment.public_values(),
    expected.as_slice(),
    "in-circuit BLAKE3 mismatch for {domain:?} len {}",
    msg.len()
  );
  Ok(())
}

fn check_derive_key_and_cross_chunk_blake3() -> Result<(), Box<dyn Error>> {
  use multi_stark::plonkish::gadgets::Blake3Domain;
  let pattern = |len: usize| -> Vec<u8> {
    (0..len).map(|i| u8::try_from(i % 251).unwrap()).collect()
  };
  for domain in [
    Blake3Domain::Plain,
    Blake3Domain::MerkleLeaf,
    Blake3Domain::MerkleCompress,
    Blake3Domain::TranscriptSingle,
    Blake3Domain::TranscriptBatch,
  ] {
    for &length in &[0usize, 1, 63, 64, 65, 1023, 1024, 1025, 2048, 2049] {
      check_blake3_gadget_vector(domain, &pattern(length))?;
    }
  }
  // Third Merkle level (>= 8 chunks) for both plain and derive_key modes.
  for domain in [Blake3Domain::Plain, Blake3Domain::MerkleLeaf] {
    for &length in &[8191usize, 8192, 8193, 9217] {
      check_blake3_gadget_vector(domain, &pattern(length))?;
    }
  }
  // Cross-chunk-boundary row encodings (8-byte little-endian words spanning
  // 64-byte block and 1024-byte chunk boundaries).
  let row_chunks: &[&[usize]] = &[
    &[127, 2],      // 1016 + 16 = 1032 bytes crossing chunk 0 -> 1
    &[128, 128, 1], // 1024 + 1024 + 8 = 2056 bytes across 2 chunk boundaries
    &[512, 513],    // 4096 + 4104 = 8200 bytes crossing 8-chunk boundary
  ];
  for &row_widths in row_chunks {
    let mut payload = Vec::new();
    let mut word = 0x1020_3040_5060_7080u64;
    for &width in row_widths {
      for _ in 0..width {
        payload.extend_from_slice(&word.to_le_bytes());
        word = word.wrapping_mul(6364136223846793005).wrapping_add(1);
      }
    }
    check_blake3_gadget_vector(Blake3Domain::MerkleLeaf, &payload)?;
  }
  Ok(())
}
