use super::*;
use crate::{
  hash::pack_bytes,
  ixby::{
    auth_memory::{MemoryDepth, SparseMemory},
    bits::{fill_words, read_words},
    ixbf::{self, DecodeLimits, Instruction},
    ixbf_decode::paged::code_capture::tests::sample,
    paged_code::PackedProgram,
  },
};
use flock_prover::{circuit::builder::GateType, union::UnionInstance};
fn image(bytes: &[u8]) -> (SparseMemory, [F128; 3], Vec<u64>) {
  let a = ixbf::decode_program(bytes, DecodeLimits::default()).unwrap();
  let context = [
    F128::new(a.functions().len() as u64, 0),
    F128::new(a.constructors().len() as u64, 0),
    F128::new(a.entry() as u64, 0),
  ];
  let mut expected = Vec::new();
  for (i, f) in a.functions().iter().enumerate() {
    expected.push((i as u64) << 8);
    for (j, b) in f.blocks.iter().enumerate() {
      let position = ((i as u64) << 8) | ((j as u64) << 24);
      expected.push(position | 1);
      if let Instruction::CaseConstructor(_, alternatives) = &b.instruction {
        for k in 0..alternatives.len() {
          expected.push(position | 2 | ((k as u64) << 32));
        }
      }
    }
  }
  let memory = SparseMemory::from_cells(
    MemoryDepth::new(40).unwrap(),
    PackedProgram::from_artifact(&a).unwrap().cells,
  )
  .unwrap();
  (memory, context, expected)
}
fn eval(g: &ReferenceGate, r: &[F128]) -> Vec<F128> {
  let mut out = Vec::new();
  g.eval(r, &(), &mut out);
  out
}
fn batches(bytes: &[u8], setup: &CompiledReferences) -> Vec<ReferenceAdvice> {
  let (mut memory, context, expected) = image(bytes);
  let initial_root = memory.root();
  let mut walk = ReferenceWitness::new(context).unwrap();
  let mut batches: Vec<ReferenceAdvice> = Vec::new();
  let mut steps = 0;
  let mut actual = Vec::new();
  while let Some(a) = walk.next_batch(&mut memory).unwrap() {
    let witness = setup.witness(&a).unwrap();
    actual.extend(
      witness
        .rows::<ReferenceGate>(setup.emission.reference.0)
        .iter()
        .filter(|r| r.0[6] == F128::ONE)
        .map(|r| r.0[3].lo),
    );
    steps += a.steps;
    if let Some(prev) = batches.last() {
      assert_eq!(prev.statement.shared(), a.statement.shared());
      assert_eq!(prev.statement.final_state(), a.statement.initial());
    }
    batches.push(a);
    assert!(batches.len() < 100_000);
  }
  assert!(walk.done());
  assert_eq!(expected.len(), steps);
  assert_eq!(actual, expected);
  assert_eq!(memory.root(), initial_root);
  let mut whole = *batches[0].statement.words();
  whole[8..].copy_from_slice(batches.last().unwrap().statement.final_state());
  ReferenceStatement::from_words(&whole).unwrap().check_complete().unwrap();
  for at in 5..11 {
    let mut bad = whole;
    bad[at] += F128::ONE;
    assert!(
      ReferenceStatement::from_words(&bad).unwrap().check_complete().is_err()
    );
  }
  batches
}
#[test]
fn complete_walk_covers_all_functions_blocks_and_alternatives() {
  let setup = CompiledReferences::compile().unwrap();
  let batches = batches(&sample(), &setup);
  let union =
    UnionInstance::new(&setup.shape.registry, setup.shape.counts.clone());
  eprintln!(
    "references batches={} M={} dense={}",
    batches.len(),
    union.dense_m(),
    union.dense_words()
  );
  for at in [
    0,
    1,
    2,
    3,
    5,
    6,
    7,
    8,
    9,
    10,
    16,
    8 + 9 * STEPS,
    8 + 9 * STEPS + 3,
    8 + 9 * STEPS + 5 * CELLS + 2,
  ] {
    let mut bad = batches[0].clone();
    bad.private[at] += F128::ONE;
    assert!(setup.check_advice(&bad).is_err(), "private word {at}");
  }
}
#[test]
fn reference_rows_reject_invalid_arities_frames_aliases_and_constrain_padding()
{
  let setup = CompiledReferences::compile().unwrap();
  let batches = batches(&sample(), &setup);
  let (slot, g) = &setup.emission.reference;
  let mut rows = Vec::new();
  for a in &batches {
    rows.extend_from_slice(
      setup.witness(a).unwrap().rows::<ReferenceGate>(*slot),
    );
  }
  let mut checked = [0usize; 8];
  for row in rows.iter().filter(|r| r.0[6] == F128::ONE) {
    let r = &row.0;
    let phase = r[3].lo as u8;
    let inst = (r[7].lo >> 8) as u8;
    let op = (r[7].lo >> 16) as u8;
    for at in [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14] {
      let mut bad = r.clone();
      bad[at].hi |= 1 << 63;
      assert_eq!(
        eval(g, &bad).last(),
        Some(&F128::ONE),
        "alias phase={phase} at={at}"
      );
    }
    let mut pad = r.clone();
    pad[6..].fill(F128::ZERO);
    let out = eval(g, &pad);
    assert_eq!(out[..3], r[3..6]);
    assert_eq!(out[3..], [F128::ZERO; OUTPUTS - 3]);
    let check = |at: usize, category: usize, checked: &mut [usize; 8]| {
      let mut bad = r.clone();
      bad[at] += F128::ONE;
      assert_eq!(
        eval(g, &bad).last(),
        Some(&F128::ONE),
        "frame phase={phase} inst={inst} op={op} at={at}"
      );
      checked[category] += 1;
    };
    if phase == 0 {
      check(9, 0, &mut checked);
    }
    if phase == 1 {
      if inst == 2 || (inst == 0 && matches!(op, 2 | 5)) {
        check(9, 1, &mut checked);
      }
      if inst == 0 && op == 4 {
        let mut bad = r.clone();
        bad[9].lo &= !255;
        assert_eq!(eval(g, &bad).last(), Some(&F128::ONE));
        checked[2] += 1;
      }
      if inst == 3 || (inst == 0 && op == 6) {
        let mut bad = r.clone();
        bad[7].lo += 1 << 40;
        assert_eq!(eval(g, &bad).last(), Some(&F128::ONE));
        checked[3] += 1;
      }
      if matches!(inst, 0 | 6 | 7) {
        check(11, 4, &mut checked);
      }
      if matches!(inst, 6 | 7) {
        check(13, 5, &mut checked);
      }
    }
    if phase == 2 {
      check(9, 6, &mut checked);
      check(11, 7, &mut checked);
    }
  }
  assert!(checked.iter().all(|n| *n > 0), "{checked:?}");
  let gate = ReferenceGate::new(3).unwrap();
  let table = gate.r1cs();
  for phase in 0..3 {
    let r = &rows
      .iter()
      .find(|r| r.0[6] == F128::ONE && r.0[3].lo as u8 == phase)
      .unwrap()
      .0;
    let mut bits = vec![false; table.n()];
    gate.plan().fill_row(&mut bits[..gate.plan().k()], |b| fill_words(r, b));
    assert!(table.satisfies(&bits));
    assert_eq!(read_words(&bits, INPUTS, OUTPUTS), eval(&gate, r));
    for at in INPUTS..INPUTS + OUTPUTS {
      for bit in [0, 63, 64, 127] {
        bits[at * 128 + bit] ^= true;
        assert!(!table.satisfies(&bits));
        bits[at * 128 + bit] ^= true;
      }
    }
  }
  let rows = rows.into_iter().take(7).collect::<Vec<_>>();
  crate::ixby::test_support::padding(
    gate.plan(),
    &rows,
    |r, b| fill_words(&r.0, b),
    |dst| gate.generate_witness_into(&rows, dst),
  );
}
#[test]
#[ignore = "complete original semantic reference circuit walk; set IXBY_PAGED_PROGRAM"]
fn original_program_all_reference_batches() {
  let bytes = std::fs::read(
    std::env::var_os("IXBY_PAGED_PROGRAM").expect("IXBY_PAGED_PROGRAM"),
  )
  .unwrap();
  let setup = CompiledReferences::compile().unwrap();
  let start = std::time::Instant::now();
  let batches = batches(&bytes, &setup);
  eprintln!(
    "complete original references batches={} steps={} elapsed={:?}",
    batches.len(),
    batches.iter().map(|a| a.steps).sum::<usize>(),
    start.elapsed()
  );
}

#[test]
#[ignore = "reference/memory proofs with fresh receivers and valid recomputed read substitutions"]
fn references_prove_fresh_and_reject_recomputed_reads() {
  use flock_prover::prover::UnionSlotProverInput;
  use std::{
    io::{Read, Write},
    process::{Command, Stdio},
    time::Instant,
  };
  const CHILD: &str = "IXBY_REFERENCES_VERIFY_CHILD";
  const TEST: &str = "ixby::ixbf_decode::paged::references::tests::references_prove_fresh_and_reject_recomputed_reads";
  let start = Instant::now();
  let setup = CompiledReferences::compile().unwrap();
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
        &ReferenceStatement::from_words(&expected).unwrap(),
        &bytes[16 * PUBLIC_WORDS..],
      )
      .unwrap();
    return;
  }
  let batches = batches(&sample(), &setup);
  let (slot, g) = &setup.emission.reference;
  let slot = *slot;
  let mut candidates = Vec::new();
  let mut found = [false; 3];
  for advice in &batches {
    let witness = setup.witness(advice).unwrap();
    let rows = witness.rows::<ReferenceGate>(slot);
    let matches = [
      candidates.is_empty(),
      rows.iter().any(|r| {
        r.0[6] == F128::ONE
          && r.0[3].lo as u8 == 1
          && (r.0[7].lo >> 8) as u8 == 0
          && (r.0[7].lo >> 16) as u8 == 5
      }),
      rows.iter().any(|r| r.0[6] == F128::ONE && r.0[3].lo as u8 == 2),
    ];
    let mut take = false;
    for i in 0..3 {
      if matches[i] && !found[i] {
        found[i] = true;
        take = true;
      }
    }
    if take {
      candidates.push((advice, witness));
    }
  }
  assert!(found.into_iter().all(|v| v));
  let mut attacked = [false; 5];
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
      "joint references {index}: proof={} setup={setup_time:?} witness+prove={elapsed:?}",
      proof.len()
    );
    for at in 0..PUBLIC_WORDS {
      let mut words = *advice.statement.words();
      words[at] += F128::ONE;
      if let Ok(bad) = ReferenceStatement::from_words(&words) {
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
    for (attack, done) in attacked.iter_mut().enumerate() {
      if *done {
        continue;
      }
      let mut rows = witness.rows::<ReferenceGate>(slot).to_vec();
      let Some(row) = rows.iter_mut().find(|r| {
        if r.0[6] != F128::ONE {
          return false;
        }
        let phase = r.0[3].lo as u8;
        let inst = (r.0[7].lo >> 8) as u8;
        let op = (r.0[7].lo >> 16) as u8;
        match attack {
          0 | 1 => phase == 0,
          2 => phase == 1 && inst == 0 && op == 5,
          3 => phase == 1 && inst == 0,
          4 => phase == 2,
          _ => false,
        }
      }) else {
        continue;
      };
      match attack {
        0 => row.0[2] += F128::ONE,
        1 => row.0[3].lo += 1 << 8,
        2 => {
          row.0[7].lo += 1 << 40;
          row.0[9].lo += 1;
        },
        3 => {
          row.0[7].lo += 1;
          row.0[11].lo += 1;
        },
        _ => {
          row.0[9].lo += 1;
          row.0[11].lo += 1;
        },
      }
      *done = true;
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
      eprintln!("recomputed reference attack {attack} rejected: {error}");
      assert!(format!("{error}").contains("Wiring"));
    }
  }
  assert!(attacked.into_iter().all(|v| v));
}
