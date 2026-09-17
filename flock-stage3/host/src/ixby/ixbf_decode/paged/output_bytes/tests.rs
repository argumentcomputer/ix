use super::*;
use crate::{
  hash::pack_bytes,
  ixby::{
    auth_memory::{MemoryDepth, SparseMemory},
    bits::{fill_words, read_words},
    paged_value::{DYNAMIC_BYTES, INPUT_BYTES, PROGRAM_BYTES},
  },
};
use flock_prover::{circuit::builder::GateType, union::UnionInstance};
fn header(length: u64) -> Vec<u8> {
  let mut bytes = b"IXFO\x01\0\0\0\x02\0\0\0\0\x06".to_vec();
  let mut n = length;
  loop {
    let byte = (n & 127) as u8;
    n >>= 7;
    bytes.push(byte | if n > 0 { 128 } else { 0 });
    if n == 0 {
      break;
    }
  }
  bytes
}
fn payload(n: usize) -> Vec<u8> {
  (0..n).map(|i| (i.wrapping_mul(197) ^ (i >> 9)) as u8).collect()
}
fn image(bytes: &[u8], bank: u64, offset: usize) -> (SparseMemory, [F128; 2]) {
  let mut buffer = vec![0x5a; offset];
  buffer.extend(bytes);
  buffer.resize(buffer.len() + 32, 0xa5);
  let cells = buffer.chunks(32).enumerate().map(|(i, slice)| {
    let mut cell = [0; 32];
    cell[..slice.len()].copy_from_slice(slice);
    (bank + i as u64, [pack_bytes(&cell[..16]), pack_bytes(&cell[16..])])
  });
  (
    SparseMemory::from_cells(MemoryDepth::new(40).unwrap(), cells).unwrap(),
    [
      F128::new(6, 0),
      F128::new(
        if bytes.is_empty() { 0 } else { (bank << 5) + offset as u64 },
        bytes.len() as u64,
      ),
    ],
  )
}
fn eval(g: &OutputBytesGate, input: &[F128]) -> Vec<F128> {
  let mut out = Vec::new();
  g.eval(input, &(), &mut out);
  out
}
fn fixture(
  n: usize,
  bank: u64,
  offset: usize,
  setup: &CompiledOutputBytes,
) -> Vec<OutputBytesAdvice> {
  let data = payload(n);
  let mut source = header(n as u64);
  source.extend(&data);
  let (mut memory, value) = image(&data, bank, offset);
  let root = memory.root();
  let mut walk = OutputBytesWitness::new(&source, value).unwrap();
  let mut batches: Vec<OutputBytesAdvice> = Vec::new();
  while let Some(a) = walk.next_batch(&mut memory).unwrap() {
    setup.check_advice(&a).unwrap();
    if let Some(prev) = batches.last() {
      assert_eq!(prev.statement.shared(), a.statement.shared());
      assert_eq!(prev.statement.final_state(), a.statement.initial());
    }
    batches.push(a);
  }
  assert_eq!(memory.root(), root);
  assert_eq!(
    batches.iter().map(|a| a.steps).sum::<usize>(),
    n.div_ceil(32).max(1)
  );
  let mut whole = *batches[0].statement.words();
  whole[8] = batches.last().unwrap().statement.final_state();
  OutputBytesStatement::from_words(&whole).unwrap().check_complete().unwrap();
  batches
}
#[test]
fn output_bytes_cover_empty_unaligned_boundaries_and_reject_private_changes() {
  let setup = CompiledOutputBytes::compile().unwrap();
  for (n, bank, offset) in [
    (0, PROGRAM_BYTES, 0),
    (1, INPUT_BYTES, 31),
    (32, DYNAMIC_BYTES, 0),
    (33, DYNAMIC_BYTES, 31),
    (127, INPUT_BYTES, 17),
    (128, PROGRAM_BYTES, 3),
    (1024, DYNAMIC_BYTES, 31),
    (2049, INPUT_BYTES, 29),
  ] {
    let batches = fixture(n, bank, offset, &setup);
    if n == 2049 {
      assert_eq!(batches.len(), 3);
      for at in [0, 1, 3, 5, 6, 7, 8, 9, 101, 377, 379, 536, 539, 541] {
        let mut bad = batches[0].clone();
        bad.private[at] += F128::ONE;
        assert!(setup.check_advice(&bad).is_err(), "private word {at}");
      }
      let union =
        UnionInstance::new(&setup.shape.registry, setup.shape.counts.clone());
      eprintln!(
        "output bytes M={} dense={} batches={}",
        union.dense_m(),
        union.dense_words(),
        batches.len()
      );
    }
  }
  // A byte mismatch anywhere in a final short window is rejected, including
  // the second memory cell and a source chunk boundary.
  for at in [0, 31, 32, 1009, 1010, 2048] {
    let data = payload(2049);
    let mut source = header(data.len() as u64);
    source.extend(&data);
    let (mut memory, value) = image(&data, DYNAMIC_BYTES, 31);
    let h = source.len() - data.len();
    source[h + at] ^= 1;
    let mut walk = OutputBytesWitness::new(&source, value).unwrap();
    let mut rejected = false;
    while let Some(a) = walk.next_batch(&mut memory).unwrap() {
      rejected |= setup.check_advice(&a).is_err();
    }
    assert!(rejected, "payload byte {at}");
  }
}
#[test]
fn output_header_and_windows_have_exact_canonical_rows_and_padding() {
  for op in [OutputBytesOp::Header, OutputBytesOp::Step] {
    let g = OutputBytesGate::new(3, op).unwrap();
    let table = g.r1cs();
    let mut rows = Vec::new();
    let inputs = if op == OutputBytesOp::Header {
      [0u64, 127, 128, 16383, 16384, 1 << 21, (1 << 24) - 18]
        .into_iter()
        .map(|n| {
          let mut h = header(n);
          let size = h.len() as u64 + n;
          h.resize(32, 0);
          vec![
            F128::new(size, 0),
            F128::new(6, 0),
            F128::new(if n == 0 { 0 } else { (DYNAMIC_BYTES << 5) + 31 }, n),
            pack_bytes(&h[..16]),
            pack_bytes(&h[16..]),
            F128::ZERO,
          ]
        })
        .collect::<Vec<_>>()
    } else {
      (0..32)
        .map(|offset| {
          vec![
            F128::new(6, 0),
            F128::new((INPUT_BYTES << 5) + offset, 33),
            F128::new(15, 0),
            F128::new(48, 0),
            F128::ONE,
            F128::ONE,
            F128::new(0x123456789abcdef, 0xfedcba9876543210),
            F128::new(!0, 0x5678),
            F128::new(7, 9),
            F128::new(11, 13),
          ]
        })
        .collect()
    };
    for input in &inputs {
      let out = eval(&g, input);
      assert_eq!(out.last(), Some(&F128::ZERO));
      if op == OutputBytesOp::Step {
        let memory = input[6..]
          .iter()
          .flat_map(|v| {
            v.lo.to_le_bytes().into_iter().chain(v.hi.to_le_bytes())
          })
          .collect::<Vec<_>>();
        let offset = (input[1].lo & 31) as usize;
        assert_eq!(out[0], F128::new(2, 0));
        assert_eq!(out[1], F128::new(47, 48));
        assert_eq!(out[2], F128::ONE);
        assert_eq!(out[3], F128::new(INPUT_BYTES + 1, 0));
        assert_eq!(out[4], F128::ZERO);
        assert_eq!(out[5], F128::new(u64::from(memory[offset]), 0));
        assert_eq!(out[6], F128::ZERO);
      }
      let mut bits = vec![false; table.n()];
      g.plan().fill_row(&mut bits[..g.plan().k()], |b| fill_words(input, b));
      assert!(table.satisfies(&bits));
      assert_eq!(read_words(&bits, input.len(), out.len()), out);
      for at in input.len()..input.len() + out.len() {
        for bit in [0, 63, 64, 127] {
          bits[at * 128 + bit] ^= true;
          assert!(!table.satisfies(&bits));
          bits[at * 128 + bit] ^= true;
        }
      }
      rows.push(OutputBytesRow(input.clone()));
    }
    for at in if op == OutputBytesOp::Header {
      vec![0, 1, 2, 5]
    } else {
      vec![2, 3, 4, 5]
    } {
      let mut bad = inputs[1].clone();
      bad[at].hi |= 1 << 63;
      assert_eq!(eval(&g, &bad).last(), Some(&F128::ONE), "{op:?} high {at}");
    }
    let rows = rows.into_iter().take(7).collect::<Vec<_>>();
    crate::ixby::test_support::padding(
      g.plan(),
      &rows,
      |r, b| fill_words(&r.0, b),
      |dst| g.generate_witness_into(&rows, dst),
    );
  }
  let g = OutputBytesGate::new(3, OutputBytesOp::Header).unwrap();
  let mut h = header(128);
  h.resize(32, 0);
  let good = vec![
    F128::new(144, 0),
    F128::new(6, 0),
    F128::new(DYNAMIC_BYTES << 5, 128),
    pack_bytes(&h[..16]),
    pack_bytes(&h[16..]),
    F128::ZERO,
  ];
  for byte in 0..16 {
    let mut wrong = h.clone();
    wrong[byte] ^= 1;
    let mut bad = good.clone();
    bad[3] = pack_bytes(&wrong[..16]);
    bad[4] = pack_bytes(&wrong[16..]);
    assert_eq!(eval(&g, &bad).last(), Some(&F128::ONE), "header byte {byte}");
  }
  let mut trailing = good;
  trailing[0] += F128::ONE;
  assert_eq!(eval(&g, &trailing).last(), Some(&F128::ONE));
}

fn fresh_verify(statement: &OutputBytesStatement, proof: &[u8]) {
  use std::{
    io::Write,
    process::{Command, Stdio},
  };
  let mut child = Command::new(std::env::current_exe().unwrap())
    .args(["--ignored", "--exact", TEST, "--test-threads=1", "--nocapture"])
    .current_dir(std::env::temp_dir())
    .env_clear()
    .env(CHILD, "1")
    .env("RAYON_NUM_THREADS", "4")
    .stdin(Stdio::piped())
    .stdout(Stdio::piped())
    .stderr(Stdio::piped())
    .spawn()
    .unwrap();
  let mut stdin = child.stdin.take().unwrap();
  for v in statement.words() {
    stdin.write_all(&v.lo.to_le_bytes()).unwrap();
    stdin.write_all(&v.hi.to_le_bytes()).unwrap();
  }
  stdin.write_all(proof).unwrap();
  drop(stdin);
  let output = child.wait_with_output().unwrap();
  assert!(
    output.status.success(),
    "{}{}",
    String::from_utf8_lossy(&output.stdout),
    String::from_utf8_lossy(&output.stderr)
  );
}
const CHILD: &str = "IXBY_OUTPUT_BYTES_VERIFY_CHILD";
const TEST: &str = "ixby::ixbf_decode::paged::output_bytes::tests::output_bytes_prove_fresh_and_reject_recomputed_ranges";
#[test]
#[ignore = "real output/source/memory proofs, fresh verifier, locally valid hostile rows"]
fn output_bytes_prove_fresh_and_reject_recomputed_ranges() {
  use flock_prover::prover::UnionSlotProverInput;
  use std::{io::Read, time::Instant};
  let start = Instant::now();
  let setup = CompiledOutputBytes::compile().unwrap();
  let setup_time = start.elapsed();
  if std::env::var_os(CHILD).is_some() {
    let mut bytes = Vec::new();
    std::io::stdin()
      .take(8 * 1024 * 1024 + 16 * PUBLIC_WORDS as u64 + 1)
      .read_to_end(&mut bytes)
      .unwrap();
    assert!(bytes.len() >= 16 * PUBLIC_WORDS);
    let expected = bytes[..16 * PUBLIC_WORDS]
      .as_chunks::<16>()
      .0
      .iter()
      .map(|v| pack_bytes(v))
      .collect::<Vec<_>>();
    setup
      .verify(
        &OutputBytesStatement::from_words(&expected).unwrap(),
        &bytes[16 * PUBLIC_WORDS..],
      )
      .unwrap();
    return;
  }
  let batch = fixture(2049, DYNAMIC_BYTES, 31, &setup).remove(0);
  for (i, advice) in
    [batch.clone(), fixture(0, INPUT_BYTES, 0, &setup).remove(0)]
      .into_iter()
      .enumerate()
  {
    let start = Instant::now();
    let proof = setup.prove(&advice).unwrap();
    let elapsed = start.elapsed();
    setup.verify(&advice.statement, &proof).unwrap();
    fresh_verify(&advice.statement, &proof);
    eprintln!(
      "output bytes {i}: proof={} setup={setup_time:?} witness+prove={elapsed:?} fresh verify passed",
      proof.len()
    );
    for at in 0..PUBLIC_WORDS {
      let mut wrong = *advice.statement.words();
      wrong[at] += F128::ONE;
      if let Ok(statement) = OutputBytesStatement::from_words(&wrong) {
        assert!(setup.verify(&statement, &proof).is_err(), "public {at}");
      }
    }
    let mut bad = proof.clone();
    bad.push(0);
    assert!(setup.verify(&advice.statement, &bad).is_err());
    let mut bad = proof.clone();
    bad[0] ^= 1;
    assert!(setup.verify(&advice.statement, &bad).is_err());
  }
  let witness = setup.witness(&batch).unwrap();
  for attack in 0..6 {
    let op = if attack < 2 { 0 } else { 1 };
    let (slot, g) = &setup.emission.gates[op];
    let mut rows = witness.rows::<OutputBytesGate>(*slot).to_vec();
    let row = &mut rows[0].0;
    match attack {
      0 => row[2].lo += 1,
      1 => {
        row[2].hi += 1;
        row[0].lo += 1;
        row[3].hi ^= 3 << 48;
      },
      2 => row[1].lo += 1,
      3 => row[4].lo += 1,
      4 => row[5] = F128::ZERO,
      5 => row[7].hi ^= 1 << 56,
      _ => unreachable!(),
    }
    assert_eq!(
      eval(g, row).last(),
      Some(&F128::ZERO),
      "attack {attack} must be locally valid"
    );
    let gate = g.clone();
    let table = gate.r1cs();
    let mut inputs =
      setup.drivers.iter().map(|d| d.prover(&witness)).collect::<Vec<_>>();
    inputs[setup.shape.registry_slot(*slot)] = UnionSlotProverInput::in_place(
      move |dst| gate.generate_witness_into(&rows, dst),
      table.csc_lincheck_circuit(),
    );
    let forged = setup.prove_rows(&witness, inputs).unwrap();
    let err = setup.verify(&batch.statement, &forged).unwrap_err();
    assert!(format!("{err:?}").contains("Wiring"), "attack {attack}: {err:?}");
    eprintln!("output bytes attack {attack} rejected at Wiring");
  }
}
#[test]
#[ignore = "original expected IXFO output against authenticated result memory; set IXBY_PAGED_OUTPUT"]
fn original_output_bytes_prove_against_authenticated_result_memory() {
  let bytes = std::fs::read(
    std::env::var_os("IXBY_PAGED_OUTPUT").expect("IXBY_PAGED_OUTPUT"),
  )
  .unwrap();
  assert_eq!(bytes.len(), 49);
  assert_eq!(&bytes[..15], header(34));
  let (mut memory, value) = image(&bytes[15..], DYNAMIC_BYTES, 31);
  let setup = CompiledOutputBytes::compile().unwrap();
  let mut walk = OutputBytesWitness::new(&bytes, value).unwrap();
  let advice = walk.next_batch(&mut memory).unwrap().unwrap();
  assert!(walk.done());
  assert_eq!(advice.steps, 2);
  let proof = setup.prove(&advice).unwrap();
  fresh_verify(&advice.statement, &proof);
  advice.statement.check_complete().unwrap();
  eprintln!(
    "original output 49 bytes/34-byte result: proof={} fresh verifier passed; memory/value still conditional on execution endpoint",
    proof.len()
  );
}
