use super::*;
use crate::{
  hash::pack_bytes,
  ixby::{
    auth_memory::{MemoryDepth, SparseMemory},
    ixbf::{self, DecodeLimits},
    ixbf_decode::paged::{
      code_capture::{
        CodeCaptureGate, FIELDS, GRAMMAR_INDICES, NATURAL, RANGE, tests::sample,
      },
      source_bytes::{SourceBank, SourceBytesWitness},
    },
    paged_code::PackedProgram,
  },
};
use flock_prover::{
  circuit::builder::GateType, field::F128, union::UnionInstance,
};
fn initial(bytes: &[u8]) -> SparseMemory {
  let mut memory = SparseMemory::new(MemoryDepth::new(40).unwrap());
  let mut source = SourceBytesWitness::new(SourceBank::Program, bytes).unwrap();
  while source.next_batch(&mut memory).unwrap().is_some() {}
  memory
}
fn batches(bytes: &[u8]) -> (SparseMemory, Vec<CodeCaptureAdvice>) {
  let mut memory = initial(bytes);
  let root = memory.root();
  let mut source = CodeCaptureWitness::new(bytes).unwrap();
  let mut batches: Vec<CodeCaptureAdvice> = Vec::new();
  while let Some(advice) = source.next_batch(&mut memory).unwrap() {
    if let Some(previous) = batches.last() {
      assert_eq!(advice.statement.initial(), previous.statement.final_state());
    }
    batches.push(advice);
    assert!(batches.len() < 100_000);
  }
  assert!(source.done());
  let mut whole = *batches.first().unwrap().statement.words();
  whole[42..].copy_from_slice(batches.last().unwrap().statement.final_state());
  CodeCaptureStatement::from_words(&whole)
    .unwrap()
    .check_complete(root)
    .unwrap();
  (memory, batches)
}
#[test]
fn source_parser_code_and_memory_batches_match_the_complete_packed_image() {
  let bytes = sample();
  let expected = PackedProgram::from_artifact(
    &ixbf::decode_program(&bytes, DecodeLimits::default()).unwrap(),
  )
  .unwrap();
  let (memory, batches) = batches(&bytes);
  let setup = CompiledCodeCapture::compile().unwrap();
  for advice in &batches {
    setup.check_advice(advice).unwrap();
  }
  let expected =
    SparseMemory::from_cells(MemoryDepth::new(40).unwrap(), expected.cells)
      .unwrap();
  assert_eq!(memory.root(), expected.root());
  let first = &batches[0];
  let tree = 44 + 3 * (64 + 2 * DEPTH) + 2;
  for at in [
    0,
    1,
    3,
    33,
    34,
    35,
    39,
    40,
    42,
    43,
    44,
    44 + 64,
    tree,
    tree + 3,
    tree + 5 * CELLS + 2,
  ] {
    let mut bad = first.clone();
    bad.private[at] += F128::ONE;
    assert!(setup.check_advice(&bad).is_err(), "accepted private word {at}");
  }
  let union =
    UnionInstance::new(&setup.shape.registry, setup.shape.counts.clone());
  eprintln!(
    "code capture fixture: batches={} M={} dense={}",
    batches.len(),
    union.dense_m(),
    union.dense_words()
  );
}
#[test]
#[ignore = "full original source-authenticated code/memory batch evaluation; set IXBY_PAGED_PROGRAM"]
fn original_program_all_code_batches_match_native_packing() {
  let bytes = std::fs::read(
    std::env::var_os("IXBY_PAGED_PROGRAM").expect("IXBY_PAGED_PROGRAM"),
  )
  .unwrap();
  let expected = PackedProgram::from_artifact(
    &ixbf::decode_program(&bytes, DecodeLimits::default()).unwrap(),
  )
  .unwrap();
  let setup = CompiledCodeCapture::compile().unwrap();
  let mut memory = initial(&bytes);
  let initial_root = memory.root();
  let mut source = CodeCaptureWitness::new(&bytes).unwrap();
  let mut first = None;
  let mut last = None;
  let mut count = 0;
  let mut steps = 0;
  let start = std::time::Instant::now();
  while let Some(advice) = source.next_batch(&mut memory).unwrap() {
    setup.check_advice(&advice).unwrap();
    if let Some(last) = &last {
      assert_eq!(advice.statement.initial(), last);
    }
    first.get_or_insert(advice.statement.clone());
    last = Some(*advice.statement.final_state());
    count += 1;
    steps += advice.steps;
    if count % 200 == 0 {
      eprintln!(
        "original code capture batches={count} events={steps} cursor={} elapsed={:?}",
        source.parser()[0].lo,
        start.elapsed()
      );
    }
  }
  let mut whole = *first.unwrap().words();
  whole[42..].copy_from_slice(&last.unwrap());
  CodeCaptureStatement::from_words(&whole)
    .unwrap()
    .check_complete(initial_root)
    .unwrap();
  assert_eq!(
    memory.root(),
    SparseMemory::from_cells(MemoryDepth::new(40).unwrap(), expected.cells)
      .unwrap()
      .root()
  );
  eprintln!(
    "complete original code batches={count} events={steps} elapsed={:?}",
    start.elapsed()
  );
}
#[test]
#[ignore = "joint parser/capture/memory proofs with fresh receivers and valid recomputed event substitutions"]
fn code_capture_proves_fresh_and_rejects_recomputed_events() {
  use flock_prover::prover::UnionSlotProverInput;
  use std::{
    io::{Read, Write},
    process::{Command, Stdio},
    time::Instant,
  };
  const CHILD: &str = "IXBY_CODE_CAPTURE_VERIFY_CHILD";
  const TEST: &str = "ixby::ixbf_decode::paged::code_capture::batch::tests::code_capture_proves_fresh_and_rejects_recomputed_events";
  let start = Instant::now();
  let setup = CompiledCodeCapture::compile().unwrap();
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
        &CodeCaptureStatement::from_words(&expected).unwrap(),
        &bytes[16 * PUBLIC_WORDS..],
      )
      .unwrap();
    return;
  }
  let (_memory, batches) = batches(&sample());
  let (slot, g) = setup.emission.capture.capture_gate();
  // Choose by actual row contents for this malicious-witness test only;
  // production verifier topology and its expected statement are already fixed.
  let mut candidates = Vec::new();
  for advice in &batches {
    let witness = setup.witness(advice).unwrap();
    let phases = witness
      .rows::<CodeCaptureGate>(slot)
      .iter()
      .map(|r| r.0[1].lo as u8)
      .collect::<Vec<_>>();
    if candidates.is_empty() || phases.contains(&14) || phases.contains(&18) {
      candidates.push((advice, witness));
    }
  }
  for (index, (advice, witness)) in candidates.iter().enumerate() {
    let start = Instant::now();
    let proof = setup.prove(advice).unwrap();
    let elapsed = start.elapsed();
    setup.verify(&advice.statement, &proof).unwrap();
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
    for word in advice.statement.words() {
      stdin.write_all(&word.lo.to_le_bytes()).unwrap();
      stdin.write_all(&word.hi.to_le_bytes()).unwrap();
    }
    stdin.write_all(&proof).unwrap();
    drop(stdin);
    let output = child.wait_with_output().unwrap();
    assert!(
      output.status.success(),
      "{} {}",
      String::from_utf8_lossy(&output.stdout),
      String::from_utf8_lossy(&output.stderr)
    );
    eprintln!(
      "joint code capture {index}: proof={} setup={setup_time:?} witness+prove={elapsed:?}",
      proof.len()
    );
    for at in 0..PUBLIC_WORDS {
      let mut words = *advice.statement.words();
      words[at] += F128::ONE;
      if let Ok(bad) = CodeCaptureStatement::from_words(&words) {
        assert!(
          setup.verify(&bad, &proof).is_err(),
          "accepted expected word {at}"
        );
      }
    }
    assert!(
      setup.verify(&advice.statement, &proof[..proof.len() - 1]).is_err()
    );
    let mut extra = proof.clone();
    extra.push(0);
    assert!(setup.verify(&advice.statement, &extra).is_err());
    for attack in 0..4 {
      let mut rows = witness.rows::<CodeCaptureGate>(slot).to_vec();
      let phase = match attack {
        0 | 1 => 1,
        2 => 14,
        _ => 18,
      };
      let Some(row) = rows.iter_mut().find(|r| r.0[1].lo as u8 == phase) else {
        continue;
      };
      match attack {
        0 => row.0[FIELDS] += F128::ONE,
        1 => {
          let at = GRAMMAR_INDICES.iter().position(|&i| i == 2).unwrap();
          row.0[at] += F128::ONE;
        },
        2 => row.0[NATURAL] += F128::new(0, 1 << 63),
        _ => {
          row.0[RANGE].lo += 1;
          row.0[0].lo += 1;
          row.0[10].lo += 1;
        },
      }
      let mut output = Vec::new();
      g.eval(&row.0, &(), &mut output);
      assert_eq!(output.last(), Some(&F128::ZERO));
      let table = g.r1cs();
      let boolean = setup
        .drivers
        .iter()
        .map(|d| {
          if d.slot() == slot {
            let rows = rows.clone();
            UnionSlotProverInput::in_place(
              move |dst| g.generate_witness_into(&rows, dst),
              table.csc_lincheck_circuit(),
            )
          } else {
            d.prover(witness)
          }
        })
        .collect();
      let bad = setup.prove_rows(witness, boolean).unwrap();
      let error = setup.verify(&advice.statement, &bad).unwrap_err();
      eprintln!("recomputed capture attack {attack} rejected: {error}");
      assert!(format!("{error}").contains("Wiring"));
    }
  }
}
